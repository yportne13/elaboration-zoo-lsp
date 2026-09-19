use std::{collections::HashMap, rc::Rc};

use crate::{list::List, parser_lib::Span};
use smol_str::SmolStr;

use super::{
    Env, Infer, Ix, Lvl, Tm, Ty, Val, VTy,
    empty_span,
    parser::syntax::Icit,
    syntax::{Locals, Pruning},
};

/// 全局 decl 表：名字 → (类型值, WHNF 值)。
///
/// 顶层定义（def / enum / 构造子）都登记在这里；项层引用用 `Tm::Decl(名字)`，
/// 求值时查表取缓存的 WHNF。递归通过"先插入指向自身的占位值、检查完再覆盖"实现。
///
/// 条目按 `Rc` 共享：`decl_insert` 的写时复制只需重建哈希桶 + 逐条 Rc 递增，
/// 不再深拷贝 `DeclEntry` 里的值（`Val` 的 clone 对 `Lam`/`Pi` 是整棵
/// `Box<Tm>` 闭包树的深拷贝、对 `LiteralIntro` 是 String 分配）。插入频次
/// 随 decl 数增长（每 def 一次），值深拷贝是其中的主项——L07 的 `strchain`
/// 参考版曾因此到 O(n²) 字节量级。
///
/// `ver` = 实例代数（性能评审 P1-2 的旁表缓存键）：`decl_insert` 每次 COW
/// 出的新实例取全局单调的唯一代数——**同 ver ⟹ 同实例**（表创建后不可变，
/// COW 只出新实例），`simpl_decl` 缓存以此判"同实例同内容"；`ver == 0` 的
/// 手工空表内容恒等（空），命中同样安全。简化表继承源的 ver——`simpl` 对
/// 自身幂等（非 Sum 条目归一为 `Decl(自身名, [])`），对简化表再简化内容
/// 不变，命中缓存的简化表语义一致。
#[derive(Debug, Clone, Default)]
pub struct Decls {
    /// crate 内可构造（mod.rs 的 simpl_decl 组装）；常规读写走 Deref(Mut)
    /// 与 `decl_insert`。
    pub(crate) map: HashMap<SmolStr, Rc<DeclEntry>>,
    /// 实例代数（见上）：同 ver ⟹ 同实例同内容。crate 内可读
    /// （simpl_decl 缓存键），写入只经 `decl_insert`。
    pub(crate) ver: u64,
}

impl Decls {
    pub fn new() -> Self {
        Self::default()
    }
}

impl std::ops::Deref for Decls {
    type Target = HashMap<SmolStr, Rc<DeclEntry>>;
    fn deref(&self) -> &HashMap<SmolStr, Rc<DeclEntry>> {
        &self.map
    }
}

impl std::ops::DerefMut for Decls {
    fn deref_mut(&mut self) -> &mut HashMap<SmolStr, Rc<DeclEntry>> {
        &mut self.map
    }
}

/// [`Decls`] 实例代数发生器（全局单调，进程级；单线程语义下仅用于保证
/// ver 不重复）。
static DECL_VERSION: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

fn next_decl_version() -> u64 {
    std::sync::atomic::AtomicU64::fetch_add(&DECL_VERSION, 1, std::sync::atomic::Ordering::Relaxed) + 1
}

#[derive(Debug, Clone)]
pub struct DeclEntry {
    pub ty: VTy,
    pub val: Val,
}

#[derive(Debug, Clone)]
pub struct Cxt {
    pub env: Env, // 求值环境（局部变量，内层在前）
    pub lvl: Lvl, // 下一个 fresh 层级（unify / quote 用）
    pub locals: Locals,
    pub pruning: Pruning, // 与 env 一一对应：Some(icit) = 该槽是待插入的隐式参数
    /// 源码变量名 → (绑定层级, 类型值)。两层 Rc（性能评审 P1-3）：
    /// - 值 `Rc<(Lvl, VTy)>`：条目克隆 = 引用计数，不再深拷贝 `Val` 类型树；
    /// - 表 `Rc<HashMap>`：`new_binder` / `decl_insert` 等不改表的派生是
    ///   O(1) 指针共享；`bind` / `define` 经 `Rc::make_mut` 写时复制——
    ///   Cxt 全程按持久风格派生（无 &mut 改写点），共享不可观测。
    pub src_names: Rc<HashMap<String, Rc<(Lvl, VTy)>>>,
    pub decl: Rc<Decls>,
}

/// `(name : dom) -> cod` 的 Tm 层 Π 链（builtin 注册期类型描述用）。
fn tm_pi(name: &str, dom: Tm, cod: Tm) -> Tm {
    Tm::Pi(
        empty_span(name.to_owned()),
        Icit::Expl,
        Box::new(dom),
        Box::new(cod),
    )
}

/// `(String ->)^n ret` 的 Tm 层 Π 链——builtin 参数类型全部是 String。
fn str_pi(params: &[&str], ret: Tm) -> Tm {
    params
        .iter()
        .rev()
        .fold(ret, |cod, name| tm_pi(name, Tm::LiteralType, cod))
}

/// `string_to_global_type Var(ix)`——de Bruijn 引用第 ix 个前导参数
/// （动态类型：check 期求值时查 decl 表取登记类型；未登记名 → 卡住
/// Decl 逃逸舱口）。
fn st2g_app(ix: u32) -> Tm {
    Tm::App(
        Box::new(Tm::Decl(SmolStr::new("string_to_global_type"))),
        Box::new(Tm::Var(Ix(ix))),
        Icit::Expl,
    )
}

impl Cxt {
    /// builtin 注册表（L06 全组移植）：`String` 类型 + string /
    /// report_check_issue / string_to_global_type / 可变全局族 / 文件 IO
    /// 族。归约统一在 `Infer::force` 的 `prim_reduce`（L07 的 force 触发
    /// 语义；L06 是应用时触发）。
    ///
    /// 注册顺序敏感：`string_to_global_type` 必须先于引用它的 global 族
    /// （其类型的闭包体在 check 期才查表，但防御性保持 L06 顺序）。
    pub fn new(infer: &Infer) -> Self {
        let cxt = Self::empty().decl_insert(
            "String",
            DeclEntry {
                ty: Val::U,
                val: Val::LiteralType,
            },
        );
        cxt.add_builtin(infer, "string_concat", str_pi(&["x", "y"], Tm::LiteralType))
            .add_builtin(infer, "str_eq", str_pi(&["x", "y"], Tm::LiteralType))
            .add_builtin(infer, "str_indent2", str_pi(&["x"], Tm::LiteralType))
            .add_builtin(
                infer,
                "report_check_issue",
                str_pi(&["code", "module", "signal", "message"], Tm::U),
            )
            .add_builtin(infer, "string_to_global_type", str_pi(&["x"], Tm::U))
            .add_builtin(
                infer,
                "create_global",
                tm_pi("x", Tm::LiteralType, tm_pi("y", st2g_app(0), Tm::U)),
            )
            .add_builtin(
                infer,
                "change_mutable",
                tm_pi(
                    "x",
                    Tm::LiteralType,
                    tm_pi("f", tm_pi("_", st2g_app(0), st2g_app(1)), Tm::U),
                ),
            )
            .add_builtin(
                infer,
                "get_global",
                tm_pi("x", Tm::LiteralType, st2g_app(0)),
            )
            .add_builtin(
                infer,
                "get_global_default",
                tm_pi(
                    "x",
                    Tm::LiteralType,
                    tm_pi("z", st2g_app(0), st2g_app(1)),
                ),
            )
            .add_builtin(
                infer,
                "change_mutable_default",
                tm_pi(
                    "x",
                    Tm::LiteralType,
                    tm_pi(
                        "f",
                        tm_pi("_", st2g_app(0), st2g_app(1)),
                        tm_pi("z", st2g_app(1), Tm::U),
                    ),
                ),
            )
            .add_builtin(
                infer,
                "file_read_all_text",
                str_pi(&["path"], Tm::LiteralType),
            )
            .add_builtin(
                infer,
                "file_write_all_text",
                str_pi(&["path", "content"], Tm::U),
            )
            .add_builtin(
                infer,
                "file_append_all_text",
                str_pi(&["path", "content"], Tm::U),
            )
            .add_builtin(infer, "file_exists", str_pi(&["path"], Tm::LiteralType))
            .add_builtin(infer, "file_delete", str_pi(&["path"], Tm::U))
    }

    /// 注册一个 builtin：类型在 Tm 层描述，经 `infer.eval` 求值成 Π 链值
    /// （只有最外层域被立即求值——恒为 String 常量；引用参数的内层域留在
    /// 闭包里到 check 期才解）；值 = λ 参数链 → **App 链**重新应用参数到
    /// `Tm::Prim(name)` 零元头，应用满元数后由 `force` 的 `prim_reduce`
    /// 归约。
    fn add_builtin(self, infer: &Infer, name: &str, ty_tm: Tm) -> Self {
        let ty = infer.eval(&self.decl, &List::new(), &ty_tm);
        // 值 = λ 参数链 → ((Prim 名 p1) p2 …)；参数名从类型的 Π 链取（与
        // 域同序）。实参经 App 显式应用而非 env 隐式收集——`Tm::Prim` 从
        // 此是零元卡住头，quote → eval 往返在任意 env 下 spine 保真（旧
        // 形态在非 builtin-λ 环境里重求值会把无关 env 槽拼进 spine）
        let mut names = Vec::new();
        let mut cur = &ty_tm;
        while let Tm::Pi(n, _, _, body) = cur {
            names.push(n.data.clone());
            cur = body;
        }
        let n = names.len() as u32;
        let mut val = Tm::Prim(SmolStr::new(name));
        for k in 0..n {
            // 第 k 个参数（应用序在前）在 λ 链体内的 de Bruijn 索引 = n-1-k
            val = Tm::App(
                Box::new(val),
                Box::new(Tm::Var(Ix(n - 1 - k))),
                Icit::Expl,
            );
        }
        for p in names.iter().rev() {
            val = Tm::Lam(empty_span(p.clone()), Icit::Expl, Box::new(val));
        }
        let val = infer.eval(&self.decl, &List::new(), &val);
        self.decl_insert(SmolStr::new(name), DeclEntry { ty, val })
    }
    pub fn empty() -> Self {
        Cxt {
            env: List::new(),
            lvl: Lvl(0),
            locals: Locals::Here,
            pruning: List::new(),
            src_names: Rc::new(HashMap::new()),
            decl: Rc::new(Decls::new()),
        }
    }

    pub fn decl(&self) -> &Decls {
        &self.decl
    }

    pub fn decl_get(&self, k: &str) -> Option<&DeclEntry> {
        self.decl.get(k).map(|e| &**e)
    }

    /// 写入一个 decl。写时复制：Rc 共享时才克隆整表，父上下文不受影响——
    /// 这正是递归定义需要的"占位只对本定义的检查可见"。表克隆是逐条 `Rc`
    /// 递增 + 重建哈希桶（条目本身共享，不深拷贝值）。新实例取唯一代数
    /// （`ver`，见 [`Decls`] 文档）。
    pub fn decl_insert(&self, k: impl Into<SmolStr>, e: DeclEntry) -> Self {
        let mut decl = self.decl.clone();
        let d = Rc::make_mut(&mut decl);
        d.ver = next_decl_version();
        d.insert(k.into(), Rc::new(e));
        Cxt {
            decl,
            env: self.env.clone(),
            lvl: self.lvl,
            locals: self.locals.clone(),
            pruning: self.pruning.clone(),
            src_names: self.src_names.clone(),
        }
    }

    pub fn names(&self) -> List<String> {
        fn go(locals: &Locals) -> List<String> {
            match locals {
                Locals::Here => List::new(),
                Locals::Define(locals, name, _, _) => go(locals).prepend(name.data.clone()),
                Locals::Bind(locals, name, _) => go(locals).prepend(name.data.clone()),
            }
        }
        go(&self.locals)
    }

    /// 引入一个源码变量（模式绑定 / λ 参数 / Π 域）：env 压入 fresh rigid。
    ///
    /// 注：`src_names` 表写时复制（每次 bind O(上下文) 的条目引用计数）——
    /// n 个绑定器的检查仍是 O(n²)，但条目值共享后无 `Val` 深拷贝；参考版取
    /// "可读优先"的写法，孪生版用 name map + 轨迹回滚等价实现
    /// （`L06_NO_NAME_MAP` 消融口径）。此表只服务名字解析与报错显示。
    pub fn bind(&self, x: Span<String>, a_quote: Tm, a: VTy) -> Self {
        let mut src_names = Rc::clone(&self.src_names);
        Rc::make_mut(&mut src_names).insert(x.data.clone(), Rc::new((self.lvl, a)));
        Cxt {
            env: self.env.prepend(Val::vvar(self.lvl)),
            lvl: self.lvl + 1,
            locals: Locals::Bind(Box::new(self.locals.clone()), x, a_quote),
            pruning: self.pruning.prepend(Some(Icit::Expl)),
            src_names,
            decl: self.decl.clone(),
        }
    }

    /// 引入一个"编译器插入"的绑定器（非 λ 项 against 隐式 Π 时）：不进 src_names。
    pub fn new_binder(&self, x: Span<String>, a_quote: Tm) -> Self {
        Cxt {
            env: self.env.prepend(Val::vvar(self.lvl)),
            lvl: self.lvl + 1,
            locals: Locals::Bind(Box::new(self.locals.clone()), x, a_quote),
            pruning: self.pruning.prepend(Some(Icit::Expl)),
            src_names: Rc::clone(&self.src_names),
            decl: self.decl.clone(),
        }
    }

    /// let 绑定：env 压入定义的值，pruning 对应槽为 None（后续隐式插入不再经过它）。
    pub fn define(&self, x: Span<String>, t: Tm, vt: Val, a: Ty, va: VTy) -> Self {
        let mut src_names = Rc::clone(&self.src_names);
        Rc::make_mut(&mut src_names).insert(x.data.clone(), Rc::new((self.lvl, va)));
        Cxt {
            env: self.env.prepend(vt),
            lvl: self.lvl + 1,
            locals: Locals::Define(Box::new(self.locals.clone()), x, a, t),
            pruning: self.pruning.prepend(None),
            src_names,
            decl: self.decl.clone(),
        }
    }

    /// 把精化替换 σ 施加到上下文（dpm-nbe `subst sub ctx`）：env 槽与
    /// src_names 的类型包 `VSub`；lvl / locals / pruning / decl 不动——
    /// **槽位布局（= 运行时布局）不变**，被解变量仍在原槽位，读点经
    /// force 展开看到解。σ 为空时零开销直通。
    pub fn subst_cxt(&self, sub: &Rc<super::Subst>) -> Self {
        if sub.is_empty() {
            return self.clone();
        }
        let wrap = |v: &super::Val| super::Val::VSub(Box::new(v.clone()), sub.clone());
        Cxt {
            env: self.env.map(wrap),
            lvl: self.lvl,
            locals: self.locals.clone(),
            pruning: self.pruning.clone(),
            // 类型值逐条包 VSub（值变 → 新条目 Rc；键名照旧克隆）
            src_names: Rc::new(
                self.src_names
                    .iter()
                    .map(|(k, e)| (k.clone(), Rc::new((e.0, wrap(&e.1)))))
                    .collect(),
            ),
            decl: self.decl.clone(),
        }
    }

    /// 当前上下文里"真变量"（bind 槽，env 槽仍指向自身 vvar）的层级集合：
    /// 这些是模式特化方程可以求解的对象。let 定义槽（槽里是值不是
    /// vvar）天然不在其中。嵌套 match 的入口上下文可能已被外层精化
    /// 包裹（`subst_cxt`）——解包 VSub 看**槽的原始形态**；外层已解变量
    /// 也按 raw 层级进入基线（无害：方程里它不再以 bare rigid 出现，
    /// force 在读点已展开）。
    pub fn bind_slots(&self) -> Vec<Lvl> {
        let n = self.lvl.0;
        self.env
            .iter()
            .enumerate()
            .filter_map(|(i, v)| {
                let mut raw = v;
                while let Val::VSub(inner, _) = raw {
                    raw = inner;
                }
                match raw {
                    Val::Rigid(l, sp) if sp.is_empty() && l.0 + (i as u32) + 1 == n => Some(*l),
                    _ => None,
                }
            })
            .collect()
    }
}
