use std::cell::RefCell;
use std::rc::Rc;

use rustc_hash::FxHashMap;

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
    pub(crate) map: FxHashMap<SmolStr, Rc<DeclEntry>>,
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
    type Target = FxHashMap<SmolStr, Rc<DeclEntry>>;
    fn deref(&self) -> &FxHashMap<SmolStr, Rc<DeclEntry>> {
        &self.map
    }
}

impl std::ops::DerefMut for Decls {
    fn deref_mut(&mut self) -> &mut FxHashMap<SmolStr, Rc<DeclEntry>> {
        &mut self.map
    }
}

/// [`Decls`] 实例代数发生器（全局单调，进程级；单线程语义下仅用于保证
/// ver 不重复）。
static DECL_VERSION: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

fn next_decl_version() -> u64 {
    std::sync::atomic::AtomicU64::fetch_add(&DECL_VERSION, 1, std::sync::atomic::Ordering::Relaxed) + 1
}

#[derive(Clone)]
pub struct PrimFunc(pub Rc<dyn Fn(&Infer, &Decls, &[Val]) -> Option<Val>>);

impl std::fmt::Debug for PrimFunc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "PrimFunc")
    }
}

#[derive(Debug, Clone)]
pub struct DeclEntry {
    pub ty: VTy,
    pub val: Val,
    /// L13 式 prim：builtin 的归约函数挂在 decl 条目上，而不是
    /// `Tm::Prim`/`Val::Prim` 特例。`force` 在 `Val::Decl` 上按 spine 调用。
    pub prim: Option<PrimFunc>,
    /// builtin 的 η 展示壳（仅 quote/pretty 用；不求值、不参与应用）。
    pub eta: Option<Tm>,
    /// builtin 的 Π 参数名（partial application 的 η 展开显示用）。
    pub prim_names: Option<Rc<Vec<Span<String>>>>,
}

/// 源码名表 + 撤销轨迹（L08 孪生 `bump_spine_iter.rs` 的 `name_map` +
/// `name_trail` 的参考版对应物）。
///
/// 旧实现是 `Rc<FxHashMap>` 持久表：`bind` 里 `Rc::clone` + `Rc::make_mut`
/// ——强计数恒为 2，`make_mut` 于是每次**深拷整张表**（逐键 String 分配 +
/// 逐条 Rc 递增），n 个绑定器的精化是 O(n²)。
///
/// 新实现改为"单张表 + 撤销轨迹 + 按 mark 惰性回退"：`bind`/`define` 只做
/// 一次哈希插入 + 追加一条 (名字, 旧值) 轨迹，O(1)；上下文退出不显式
/// 撤销，而在**下一次访问名字表前**把轨迹裁回本上下文的 `name_mark`——
/// 语义与持久表一致（每个 Cxt 看到的名字集 = 创建时的快照），但不再有
/// 整表拷贝。轨迹是单线程深度优先遍历的日志，(mark, 轨迹长度) 一一对应
/// 地标识一个名字表版本。
#[derive(Debug, Default)]
pub struct NameState {
    map: FxHashMap<String, Rc<(Lvl, VTy)>>,
    /// (名字, 旧值)；旧值 `None` = 该名字此前不在表里。
    trail: Vec<(String, Option<Rc<(Lvl, VTy)>>)>,
}

impl NameState {
    /// 把轨迹裁回 `mark`（= 某个上下文的基线）：逆序还原被覆盖/删除的
    /// 条目。调用方保证 `mark <= trail.len()`（mark 只会取自已发生过的
    /// 轨迹长度，且深度优先下不会访问比自身更浅的上下文之后再用更深上下文
    /// ——见 `Cxt::unwind_names` 的 debug_assert）。
    fn unwind(&mut self, mark: u32) {
        debug_assert!(
            mark as usize <= self.trail.len(),
            "unwind: mark {} 超出轨迹长度 {}",
            mark,
            self.trail.len()
        );
        while self.trail.len() > mark as usize {
            let (k, prev) = self.trail.pop().expect("unwind: 轨迹为空");
            match prev {
                Some(v) => {
                    self.map.insert(k, v);
                }
                None => {
                    self.map.remove(&k);
                }
            }
        }
    }

    /// 插入一条（名字, 层级, 类型），旧值入轨迹。
    fn insert(&mut self, k: String, v: Rc<(Lvl, VTy)>) {
        let prev = self.map.insert(k.clone(), v);
        self.trail.push((k, prev));
    }
}

#[derive(Debug, Clone)]
pub struct Cxt {
    pub env: Env, // 求值环境（局部变量，内层在前）
    pub lvl: Lvl, // 下一个 fresh 层级（unify / quote 用）
    pub locals: Locals,
    pub pruning: Pruning, // 与 env 一一对应：Some(icit) = 该槽是待插入的隐式参数
    /// 源码变量名 → (绑定层级, 类型值)，共享可变表（见 [`NameState`]）。
    /// 每次访问前先把轨迹裁回 `name_mark`，因此本上下文看到的名字集合
    /// 恒等于创建时的快照；`bind` 条目值仍是 `Rc<(Lvl, VTy)>`（O(1)）。
    names: Rc<RefCell<NameState>>,
    /// 本上下文的名字表基线（轨迹长度）。
    name_mark: u32,
    pub decl: Rc<Decls>,
}

/// `(name : dom) -> cod` 的 Tm 层 Π 链（builtin 注册期类型描述用）。
fn tm_pi(name: &str, dom: Tm, cod: Tm) -> Tm {
    Tm::Pi(
        empty_span(name.to_owned()),
        Icit::Expl,
        Rc::new(dom),
        Rc::new(cod),
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
        let mut cxt = Self::empty();
        cxt.decl_insert_mut(
            "String",
            DeclEntry { prim: None, eta: None, prim_names: None,
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

    /// 注册一个 builtin（L13 式）：类型求值后挂在 decl 条目上，归约函数
    /// `PrimFunc` 也挂在同一张表；值只是 `Val::Decl(自身名)` 的中性占位。
    /// 应用后的实参由 spine 到达 `force`，由 `prim_reduce` 直接消费；
    /// 不再生成 `Tm::Prim`/`Val::Prim` 特例。
    fn add_builtin(mut self, infer: &Infer, name: &str, ty_tm: Tm) -> Self {
        // Π 链参数名（η 展示壳用）先取出来。
        let mut names = Vec::new();
        let mut cur = &ty_tm;
        while let Tm::Pi(n, _, _, body) = cur {
            names.push(n.clone());
            cur = body.as_ref();
        }
        let ty = infer.eval(&self.decl, &List::new(), &ty_tm);
        let nm = SmolStr::new(name);
        let prim_name = nm.clone();
        let prim = PrimFunc(Rc::new(move |infer: &Infer, decl: &Decls, args: &[Val]| {
            infer.prim_reduce(decl, &prim_name, args)
        }));
        // η 展示壳：`λ p1 … pn. ((Decl 名 p1) … pn)`，仅 quote/pretty 用。
        let mut eta = Tm::Decl(nm.clone());
        let n = names.len() as u32;
        for k in 0..n {
            eta = Tm::App(
                Box::new(eta),
                Box::new(Tm::Var(Ix(n - 1 - k))),
                Icit::Expl,
            );
        }
        for p in names.iter().rev() {
            eta = Tm::Lam(p.clone(), Icit::Expl, Rc::new(eta));
        }
        let val = Val::Decl(nm.clone(), List::new());
        self.decl_insert_mut(
            nm,
            DeclEntry { ty, val, prim: Some(prim), eta: Some(eta), prim_names: Some(Rc::new(names)) },
        );
        self
    }
    pub fn empty() -> Self {
        Cxt {
            env: List::new(),
            lvl: Lvl(0),
            locals: Locals::Here,
            pruning: List::new(),
            names: Rc::new(RefCell::new(NameState::default())),
            name_mark: 0,
            decl: Rc::new(Decls::new()),
        }
    }

    /// 名字表访问前统一入口：把共享轨迹裁回本上下文的基线（惰性回滚）。
    /// 深度优先遍历下这是幂等的零/常数开销；跨兄弟作用域时把对方残留的
    /// 绑定逐条还原（每条只还原一次，均摊 O(1)）。
    #[inline]
    fn unwind_names(&self) {
        self.names.borrow_mut().unwind(self.name_mark);
    }

    /// 查一个源码局部名（局部 binder 优先于 decl 表）：返回
    /// `(绑定层级, 类型值)` 的共享条目（克隆 = 一次 Rc 递增）。
    pub fn lookup_src(&self, n: &str) -> Option<Rc<(Lvl, VTy)>> {
        self.unwind_names();
        self.names.borrow().map.get(n).cloned()
    }

    /// 源码名是否已在本作用域绑定（`Enum.case` 限定构造子快捷路径的
    /// 局部遮蔽判定用）。
    pub fn has_src(&self, n: &str) -> bool {
        self.unwind_names();
        self.names.borrow().map.contains_key(n)
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
    /// 就地写入一个 decl（顺序声明路径专用）：调用方持有 `Cxt` 所有权，
    /// 表的 `Rc` 强计数为 1，`Rc::make_mut` 原地写，不深拷整表。
    ///
    /// 这是 L13 参考版 `fake_bind`/`decl` 就地写模式在 L07 的对应物。
    /// 旧 [`Cxt::decl_insert`] 先 `self.decl.clone()` 再 `Rc::make_mut`，
    /// 强计数恒为 2 ⇒ 每个顶层 def 都深拷一次整张 decl 表（strchain/global
    /// 这类每 k 翻倍生成 2^(k+1) 个 def 的负载上是 O(D²) 放大器）。
    pub fn decl_insert_mut(&mut self, k: impl Into<SmolStr>, e: DeclEntry) {
        let d = Rc::make_mut(&mut self.decl);
        d.ver = next_decl_version();
        d.insert(k.into(), Rc::new(e));
    }

    /// 持久化插入包装（保持 `&Cxt` 调用方兼容）：浅克隆上下文后就地写。
    pub fn decl_insert(&self, k: impl Into<SmolStr>, e: DeclEntry) -> Self {
        let mut cxt = self.clone();
        cxt.decl_insert_mut(k, e);
        cxt
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
    /// 名字表 O(1)：先裁轨迹回本上下文基线（丢弃兄弟作用域残留），插入
    /// `(名字 → 本层级/类型)` 并把旧值追加进轨迹；子上下文只带新的
    /// `name_mark`（= 轨迹长度）。语义等价于旧持久表（条目仍是共享 Rc，
    /// 无 `Val` 深拷贝），但不再每次 `Rc::make_mut` 深拷整张表。
    pub fn bind(&self, x: Span<String>, a_quote: Tm, a: VTy) -> Self {
        let name_mark = {
            let mut s = self.names.borrow_mut();
            s.unwind(self.name_mark);
            s.insert(x.data.clone(), Rc::new((self.lvl, a)));
            s.trail.len() as u32
        };
        Cxt {
            env: self.env.prepend(Val::vvar(self.lvl)),
            lvl: self.lvl + 1,
            locals: Locals::Bind(Rc::new(self.locals.clone()), x, a_quote),
            pruning: self.pruning.prepend(Some(Icit::Expl)),
            names: Rc::clone(&self.names),
            name_mark,
            decl: self.decl.clone(),
        }
    }

    /// 引入一个"编译器插入"的绑定器（非 λ 项 against 隐式 Π 时）：不进名字表。
    pub fn new_binder(&self, x: Span<String>, a_quote: Tm) -> Self {
        Cxt {
            env: self.env.prepend(Val::vvar(self.lvl)),
            lvl: self.lvl + 1,
            locals: Locals::Bind(Rc::new(self.locals.clone()), x, a_quote),
            pruning: self.pruning.prepend(Some(Icit::Expl)),
            names: Rc::clone(&self.names),
            name_mark: self.name_mark,
            decl: self.decl.clone(),
        }
    }

    /// let 绑定：env 压入定义的值，pruning 对应槽为 None（后续隐式插入不再经过它）。
    pub fn define(&self, x: Span<String>, t: Tm, vt: Val, a: Ty, va: VTy) -> Self {
        let name_mark = {
            let mut s = self.names.borrow_mut();
            s.unwind(self.name_mark);
            s.insert(x.data.clone(), Rc::new((self.lvl, va)));
            s.trail.len() as u32
        };
        Cxt {
            env: self.env.prepend(vt),
            lvl: self.lvl + 1,
            locals: Locals::Define(Rc::new(self.locals.clone()), x, a, t),
            pruning: self.pruning.prepend(None),
            names: Rc::clone(&self.names),
            name_mark,
            decl: self.decl.clone(),
        }
    }

    /// 把精化替换 σ 施加到上下文（dpm-nbe `subst sub ctx`）：env 槽与
    /// 名字表类型包 `VSub`；lvl / locals / pruning / decl 不动——
    /// **槽位布局（= 运行时布局）不变**，被解变量仍在原槽位，读点经
    /// force 展开看到解。σ 为空时零开销直通。
    ///
    /// 名字表按轨迹改写：现有条目（父链 + 本作用域）逐条换成包了 `VSub`
    /// 的新条目并记录旧值，`name_mark` 指到轨迹新长度；父上下文下次访问
    /// 时惰性还原（与 `bind`/`define` 同一机制）。
    pub fn subst_cxt(&self, sub: &Rc<super::Subst>) -> Self {
        if sub.is_empty() {
            return self.clone();
        }
        let wrap = |v: &super::Val| super::Val::VSub(Box::new(v.clone()), sub.clone());
        let name_mark = {
            let mut s = self.names.borrow_mut();
            s.unwind(self.name_mark);
            let entries: Vec<(String, Rc<(Lvl, VTy)>)> =
                s.map.iter().map(|(k, v)| (k.clone(), v.clone())).collect();
            for (k, e) in entries {
                let new_e = Rc::new((e.0, wrap(&e.1)));
                let prev = s.map.insert(k.clone(), new_e);
                s.trail.push((k, prev));
            }
            s.trail.len() as u32
        };
        Cxt {
            env: self.env.map(wrap),
            lvl: self.lvl,
            locals: self.locals.clone(),
            pruning: self.pruning.clone(),
            names: Rc::clone(&self.names),
            name_mark,
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
