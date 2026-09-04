//! L08 核心机（eval / quote / unify / force / rename / solve / prune / check /
//! infer / decl 表 / builtin prim / enum 注册 / 模式编译）的极致性能版：
//! L07 冠军配方（`bump_spine_iter`）向 product-type 层的移植。继承 L05/L06/L07
//! 的全部机制（见 L06 版模块注释与 readme）：
//!
//! 1. bump arena；打包值 [`V`]（低 3 位 tag）；扁平中性 + spine 栈；
//! 2. 复合环境（平坦 def 区域 + 持久 binder 链）；
//! 3. 迭代内核：eval 双栈 / quote 任务栈 / unify 工作表 / rename 任务栈 /
//!    force 循环；
//! 4. quote 记忆化（println 输出口径）+ unify 判等记忆化（`L06_NO_CONV_MEMO=1`
//!    消融）+ O(1) 名字解析（`L06_NO_NAME_MAP=1` 消融）；
//! 5. `Tycker` 稳态复用（跨轮 `Bump::reset`）、热路径草稿常驻、
//!    `Pruning` 跳段（none-run）、`RenBuf` 换代缓冲、fresh meta 免 eval 快捷路径。
//!
//! L07 的增量（sum-type 层语义的落地）原样继承，不在此赘述——参考版 =
//! `super` 的分文件实现，语义以其为准。**L08 自己的增量极薄**：积类型是
//! 解析器侧语法糖（`struct` 脱糖成单 `mk` 构造子 enum、`new` 脱糖成限定
//! 构造子应用），核心机变体/编码不动。镜像点两处：`infer_expr` 的
//! `Raw::Obj` 臂——接收者类型是 `XCell::Sum`（struct 只有类型没有实例值）
//! 且单 case 名字带 `.mk` 时，剥 `mk` 的构造子类型链取字段类型，前字段
//! binder 以接收者卡住投影实例化，与参考版 elaboration 逐句对应；
//! `unify_iter` 的 `(Obj, Obj)` 合同统一臂——对位参考版为剥链精确化补的
//! 合一臂（L07 潜伏缺口，见 L08 README §2），裸 XCell 单元与带实参 spine
//! 链两种形态同臂处理。
//!
//! 以下为 L07 增量机制的原始说明（保留备查）：
//!
//! - **值编码**：tag 7 的 [`XCell`] 从 Lit/Decl 扩到 `Prim`（卡住内建应用
//!   头）、`Obj`（卡住投影）、`Sum` / `SumCase`（和类型与构造子值）、
//!   `Match`（卡住 match：scrutinee + 捕获 env + 编译分支 + pending 实参）。
//!   带实参的 Prim/Obj/Decl 与 Rigid/Flex 一样表示为 spine 栈上的链（头 =
//!   `Entry.hk` 记录的头种类，push 时随函数侧传播，O(1) 判定）。
//! - **builtin 触发点后移**：L06 在应用时触发（`decl_apply`）；L07 参考版
//!   的 builtin 值是 `λ 参数链 → Tm::Prim(名)`，实参经 env 全槽进入
//!   `Val::Prim(名, spine)`（链头 = 最后应用的实参），归约统一在 force
//!   的 [`prim_reduce`]（L06 cxt.rs 函数体的逐句移植）。
//! - **模式特化事实表**：`pm_defs`（子句变量 := 值）+ `pm_solvable`（当前
//!   子句的可解 bind 槽）+ `pm_mark`/`pm_restore`（truncate 回滚）；force
//!   在裸 Rigid 读点惰性展开；[`force_arg`] 不展开 pm_defs、不重选 Match
//!   （invert / prune_vflex 专用——槽位引用是作用域事实）。
//! - **unify_fuel**：force 的每次展开与 unify 的每次递归各消耗 1；耗尽即把
//!   值当未解处理 / Err。充值点与参考版一致（unify_catch / 编译入口 / nf）。
//! - **卡住 match 的三处特殊处理**：unify 的 Match/Match（struct_eq 快路径
//!   + 逐分支在 fresh rigid 槽下用简化 decl 表重求值再比）、quote/rename
//!   的分支体重求值（[`simpl_decl`] 防递归重展开）、v_app 的 pending 累积
//!   （分支选中后在值层逐个应用——项层 splice 会把实参自由变量引到错误
//!   上下文，参考版 `v_app` 的 Match 臂同款）。
//! - **decl 表写时复制**：`Rc<FxHashMap>` + `Rc::make_mut` 镜像参考版
//!   `Cxt::decl_insert`——递归 def 的"占位 → 覆盖"只对本定义可见；源码
//!   名字解析 = 局部 name_map 之后查 decl 表（参考版 `Raw::Var` 同序）。
//!
//! 与参考版共用 parser / pretty / preprocess，**Ok 输出逐字节一致**（互检
//! 测试 + `tests/l08_fast_parity.rs`）。已知偏差（仅错误消息内容，不影响
//! 判定与 Ok 输出）：快版导出项的名字 Span 全零，参考版错误文案里的
//! Debug-Span 携带源码偏移，同构但数字不同。unify 的位相等捷径对 tag 7
//! 与 **Obj 头的链**关闭：`(Lit, Lit)` 参考版无自反臂（同字面量也 Err），
//! `(Obj, Obj)` 走专门合同臂（比较接收者 + 实参）——两者都不做字面
//! 自反放行；捷径放行会误 Accept。

use bumpalo::Bump;
use rustc_hash::{FxHashMap, FxHashSet};
use smol_str::SmolStr;
use std::cell::{Cell, RefCell};
use std::rc::Rc;

use super::parser::syntax::{Decl, Either, Icit, Pattern, Raw};
use super::pretty::pretty_tm;
use super::{empty_span, Error, Ix, MetaVar, PatternDetail, Tm as CTm};

// syntax（bump 内的项表示）
// --------------------------------------------------------------------------------

/// bump 内分配的核心项。名字只服务 pretty（`Var` 无名，索引寻址）。
/// L07 增量：`Prim`（builtin 体标记）、`Obj`（投影）、`Sum` / `SumCase`
/// （enum 本体与构造子值）、`Match`（编译后的分支列表）。
pub(crate) enum Tm<'a> {
    Var(u32),
    Lam(&'a str, Icit, &'a Tm<'a>),
    App(&'a Tm<'a>, &'a Tm<'a>, Icit),
    /// 把头按掩码应用到求值环境：`Some(icit)` 槽位以该 icit 应用实参，
    /// `None` 槽位跳过。
    AppPruning(&'a Tm<'a>, Option<&'a PrCons<'a>>),
    U,
    Pi(&'a str, Icit, &'a Tm<'a>, &'a Tm<'a>),
    Let(&'a str, &'a Tm<'a>, &'a Tm<'a>, &'a Tm<'a>),
    Meta(u32),
    /// String 字面量的类型（`String`）。
    LiteralType,
    /// 字符串字面量（内容即值）。
    LiteralIntro(&'a str),
    /// 按名 decl 表查找：命中给登记值，miss panic（"unbound global"，两版
    /// 一致——参考版 eval 的 Tm::Decl 臂）。
    Decl(&'a str),
    /// builtin 体标记：求值时把 env 全部槽当作实参卡成 `Prim(名, spine)`，
    /// 归约统一在 force。
    Prim(&'a str),
    /// `x.field` 投影（参考版 `Tm::Obj`；字段名只服务 pretty/查表）。
    Obj(&'a Tm<'a>, &'a str),
    /// enum 类型本体（enum 声明 λ 链的体）。params = (参数名, 值项, 类型项,
    /// icit)，声明处值项即参数自身；实例化后值槽携带当前实参。
    Sum(&'a str, &'a [SumParamT<'a>], &'a [&'a str]),
    /// 构造子值：typ 求值后必须是其所属的（已实例化的）`Sum`。
    SumCase {
        typ: &'a Tm<'a>,
        case_name: &'a str,
        datas: &'a [SumDataT<'a>],
    },
    /// 已编译的 match：分支体是检查过的项，运行时按模式首匹配。
    Match(&'a Tm<'a>, &'a [(PatternDetail, &'a Tm<'a>)]),
}

/// `Tm::Sum` 的参数槽（bump 内）。
pub(crate) struct SumParamT<'a> {
    pub(crate) name: &'a str,
    pub(crate) val: &'a Tm<'a>,
    pub(crate) ty: &'a Tm<'a>,
    pub(crate) icit: Icit,
}

/// `Tm::SumCase` 的字段槽（bump 内）。
pub(crate) struct SumDataT<'a> {
    pub(crate) name: &'a str,
    pub(crate) val: &'a Tm<'a>,
    pub(crate) icit: Icit,
}

/// `AppPruning` 的掩码链表（bump 持久，头 = 最内层绑定）。
pub(crate) struct PrCons<'a> {
    /// `Some(icit)` = 绑定槽位（应用实参，icit 随槽）；`None` = define 槽
    /// （跳过）。
    slot: Option<Icit>,
    /// 本节点向外（next 方向）连续 `None`（define 槽）的个数；Some 槽为 0。
    none_run: u32,
    /// 本 none-run 之后的第一个槽（Some 槽或链尾）——跳段的落点。
    after_run: Option<&'a PrCons<'a>>,
    next: Option<&'a PrCons<'a>>,
}

impl<'a> PrCons<'a> {
    /// 入链构造（新槽恒为链头，最内层）。run 统计只读既有节点。
    fn new(slot: Option<Icit>, next: Option<&'a PrCons<'a>>) -> Self {
        let (none_run, after_run) = match (slot, next) {
            (Some(_), _) => (0, next),
            (None, Some(n)) if n.slot.is_none() => (n.none_run + 1, n.after_run),
            (None, _) => (1, next),
        };
        PrCons {
            slot,
            none_run,
            after_run,
            next,
        }
    }
}

/// 局部 telescope 节点（`fresh_meta` 闭类型用）：`Bind` 槽存引好的类型项，
/// `Define` 槽再存定义项。
struct LCons<'a> {
    name: &'a str,
    a_t: &'a Tm<'a>,
    /// `Some` = define（闭成 Let），`None` = binder（闭成显式 Π）。
    t_t: Option<&'a Tm<'a>>,
    next: Option<&'a LCons<'a>>,
}

// values（打包值）
// --------------------------------------------------------------------------------

/// 打包值：tag 在低 3 位。`0=Rigid(level<<3)`、`1=Clo(ptr|1)`、
/// `2=Spine(idx<<3|2)`、`3=U`（立即数）、`4=Pi(ptr|4)`、`5=Meta(m<<3|5)`
/// （未解 meta 立即数）、`6=LiteralType`（立即数）、`7=XCell(ptr|7)`
/// （字面量 / Decl / Prim / Obj / Sum / SumCase / Match）。icit 不进打包
/// 字——由 Clo/Pi 单元与 spine 槽携带（打包字是 quote/unify 记忆化的键，
/// icit 随值结构唯一确定）。
#[derive(Clone, Copy)]
pub(crate) struct V(pub(crate) u64);

#[inline]
pub(crate) fn v_lvl(level: u32) -> V {
    V(((level as u64) << 3) | 0)
}
#[inline]
pub(crate) fn v_clo<'a>(p: &'a CloCell<'a>) -> V {
    V((p as *const _ as u64) | 1)
}
#[inline]
pub(crate) fn v_spine(idx: usize) -> V {
    V(((idx as u64) << 3) | 2)
}
#[inline]
pub(crate) fn v_u() -> V {
    V(3)
}
#[inline]
pub(crate) fn v_pi<'a>(p: &'a PiCell<'a>) -> V {
    V((p as *const _ as u64) | 4)
}
#[inline]
pub(crate) fn v_meta(m: u32) -> V {
    V(((m as u64) << 3) | 5)
}
/// `LiteralType` 立即数（同 `U` 的编码方式：tag 本身即值）。
#[inline]
pub(crate) fn v_lit_ty() -> V {
    V(6)
}
#[inline]
pub(crate) fn v_xcell<'a>(p: &'a XCell<'a>) -> V {
    V((p as *const _ as u64) | 7)
}
#[inline]
pub(crate) fn v_tag(v: V) -> u64 {
    v.0 & 7
}
#[inline]
pub(crate) fn v_lvl_of(v: V) -> u32 {
    (v.0 >> 3) as u32
}
#[inline]
pub(crate) fn v_clo_of<'a>(v: V) -> &'a CloCell<'a> {
    unsafe { &*((v.0 & !7) as *const CloCell) }
}
#[inline]
pub(crate) fn v_spine_of(v: V) -> usize {
    (v.0 >> 3) as usize
}
#[inline]
pub(crate) fn v_pi_of<'a>(v: V) -> &'a PiCell<'a> {
    unsafe { &*((v.0 & !7) as *const PiCell) }
}
#[inline]
pub(crate) fn v_meta_of(v: V) -> u32 {
    (v.0 >> 3) as u32
}
/// tag 7 单元解引用（bump 内分配，本轮内有效）。
#[inline]
pub(crate) fn v_xcell_of<'a>(v: V) -> &'a XCell<'a> {
    unsafe { &*((v.0 & !7) as *const XCell) }
}

/// `Val::Sum` 的参数槽（值层，bump 内）。
pub(crate) struct SumParamV<'a> {
    name: &'a str,
    val: V,
    ty: V,
    icit: Icit,
}

/// `Val::SumCase` 的字段槽（值层，bump 内）。
pub(crate) struct SumDataV<'a> {
    name: &'a str,
    val: V,
    icit: Icit,
}

/// tag 7 的载体：字面量值、卡住的按名 Decl 头、builtin 体标记、卡住投影、
/// 和类型本体、构造子值、卡住 match。判等按单元指针（同内容不同次求值各
/// 造单元——与参考版每次构造新值同构）；**位相等捷径对 tag 7 关闭**（见
/// 模块注释），其中 Obj 头的链在 unify 里单独排除。
pub(crate) enum XCell<'a> {
    Lit(&'a str),
    Decl(&'a str),
    /// builtin 体标记（空实参；带实参的卡住内建是 spine 链，头 = 本单元）。
    Prim(&'a str),
    /// 卡住投影：被投影者 + 字段名。带实参的卡住投影 = spine 链（头 =
    /// 本单元），与参考版 `Val::Obj(v, name, sp)` 同构。
    Obj { val: V, name: &'a str },
    /// 和类型本体：名 + 参数槽（名/实参/实参类型/icit）+ 构造子名表。
    Sum {
        name: &'a str,
        params: &'a [SumParamV<'a>],
        cases: &'a [&'a str],
    },
    /// 构造子值：typ 求值后是其所属的已实例化 `Sum`。
    SumCase {
        typ: V,
        case_name: &'a str,
        datas: &'a [SumDataV<'a>],
    },
    /// 卡住 match：scrutinee（创建时已 force）+ 捕获 env + 编译分支 +
    /// 卡住期累积的应用实参（应用序；分支选中后在值层逐个应用）。
    Match {
        scrutinee: V,
        env: Env<'a>,
        cases: &'a [(PatternDetail, &'a Tm<'a>)],
        pending: &'a [(V, Icit)],
    },
}

/// 复合环境：**平坦 def 区域**（elaborator 的 define 链，指入每轮
/// [`Machine::defs`]；tip 环境原地追加，`nth` O(1)；**非 tip 环境**
/// （λ 体内的 define 先占位后、外层再 define）回落到 binder 链——索引
/// 语义一致，仅查链 O(链深)）+ **持久 binder 链表**。机制与论证同 L03-L06。
#[derive(Clone, Copy)]
pub(crate) struct Env<'a> {
    flat_base: u32,
    flat_len: u32,
    binds: Option<&'a EnvCons<'a>>,
}

const EMPTY_ENV: Env<'static> = Env {
    flat_base: 0,
    flat_len: 0,
    binds: None,
};

/// 环境链表节点（bump 内持久链表，头 = 最内层绑定）。
pub(crate) struct EnvCons<'a> {
    val: V,
    next: Option<&'a EnvCons<'a>>,
}

/// `i < binds 深度` → 走链；否则读平坦 def 区域。
#[inline]
pub(crate) fn env_nth(defs: &[V], env: Env<'_>, i: u32) -> V {
    let mut nb = env.binds;
    let mut j = 0u32;
    while let Some(e) = nb {
        if j == i {
            return e.val;
        }
        j += 1;
        nb = e.next;
    }
    defs[(env.flat_base + env.flat_len - 1 - (i - j)) as usize]
}

/// 环境总槽数（链深 + 平坦区）。`Tm::Prim` 的 env 全槽收集与
/// struct_eq / val_mentions_lvl 的 env 遍历用。
#[inline]
pub(crate) fn env_len(env: Env<'_>) -> u32 {
    let mut n = env.flat_len;
    let mut nb = env.binds;
    while let Some(e) = nb {
        n += 1;
        nb = e.next;
    }
    n
}

/// 环境扩展（**binder 链**：bind / β / 瞬时求值扩展）——O(1)。
#[inline]
pub(crate) fn env_ext<'a>(bump: &'a Bump, env: Env<'a>, v: V) -> Env<'a> {
    Env {
        flat_base: env.flat_base,
        flat_len: env.flat_len,
        binds: Some(bump.alloc(EnvCons { val: v, next: env.binds })),
    }
}

/// 环境扩展（**平坦 def 区域**：elaborator 的 define）。tip 环境原地追加
/// （chain 负载的 O(1) 线性保证）；其余回落 binder 链。tip 判定要求 binds
/// 为空：λ 体内 define 比链上 binder 更新，必须落在链头——追加平坦区会被
/// env_nth/AppPrun 的链优先序排到 binder 之后（de Bruijn 次序互换，错位值
/// 流进 solve 即错解/误报）。
#[inline]
pub(crate) fn env_ext_defs<'a>(
    bump: &'a Bump,
    defs: &mut Vec<V>,
    env: Env<'a>,
    v: V,
) -> Env<'a> {
    if env.binds.is_none() && env.flat_base + env.flat_len == defs.len() as u32 {
        defs.push(v);
        Env {
            flat_base: env.flat_base,
            flat_len: env.flat_len + 1,
            binds: env.binds,
        }
    } else {
        Env {
            flat_base: env.flat_base,
            flat_len: env.flat_len,
            binds: Some(bump.alloc(EnvCons { val: v, next: env.binds })),
        }
    }
}

/// 闭包单元：λ 的名字 + icit（quote 产出带 icit 的 `Lam`）+ env + 体。
pub(crate) struct CloCell<'a> {
    name: &'a str,
    icit: Icit,
    env: Env<'a>,
    body: &'a Tm<'a>,
}

/// Π 值单元：名字 + icit + 定义域值 + 余定义域闭包（内联，一次分配）。
pub(crate) struct PiCell<'a> {
    name: &'a str,
    icit: Icit,
    dom: V,
    env: Env<'a>,
    body: &'a Tm<'a>,
}

// spine 栈（扁平中性）
// --------------------------------------------------------------------------------

/// 链头种类（`Entry.hk`）：push 时随函数侧传播，O(1) 判定链头是 Decl /
/// Prim / Obj（force 的三分派）还是其它（Rigid/Flex/Lit——直接中性）。
const HK_OTHER: u8 = 0;
const HK_DECL: u8 = 1;
const HK_PRIM: u8 = 2;
const HK_OBJ: u8 = 3;

/// spine 栈槽：一次中性应用（icit 随槽携带）。`len`/`base` 支撑流式右链
/// quote；`hk` 记录链头种类（push 时随函数侧传播）。
struct Entry {
    f: V,
    a: V,
    icit: Icit,
    len: u32,
    base: u32,
    hk: u8,
}

/// 求值机持有的扁平中性栈（只增不减，槽位下标即句柄）。
pub(crate) struct Spine {
    stack: Vec<Entry>,
}

impl Spine {
    /// 中性应用 `f a`（icit i）压栈，返回句柄值。`hk` 随函数侧传播：
    /// 裸 XCell 直查种类，既有链延伸保持原种类。
    #[inline]
    fn push(&mut self, f: V, a: V, icit: Icit) -> V {
        let idx = self.stack.len();
        let hk = match v_tag(f) {
            7 => match v_xcell_of(f) {
                XCell::Decl(_) => HK_DECL,
                XCell::Prim(_) => HK_PRIM,
                XCell::Obj { .. } => HK_OBJ,
                _ => HK_OTHER,
            },
            2 => self.stack[v_spine_of(f)].hk,
            _ => HK_OTHER,
        };
        let (len, base) = if v_tag(a) == 2 {
            let prev = &self.stack[v_spine_of(a)];
            (prev.len + 1, prev.base)
        } else {
            (1, idx as u32)
        };
        self.stack.push(Entry {
            f,
            a,
            icit,
            len,
            base,
            hk,
        });
        v_spine(idx)
    }

    /// 沿 `f` 指针走到链的最底层头（f 指针严格指向更早的槽位，必终止）。
    #[inline]
    fn spine_head(&self, h: usize) -> V {
        let mut cur = h;
        loop {
            let f = self.stack[cur].f;
            if v_tag(f) == 2 {
                cur = v_spine_of(f);
            } else {
                return f;
            }
        }
    }

    /// 收集链的**引用语义实参**（逆应用序：先 `h.a` 再沿 `f` 下行）。
    #[inline]
    fn collect_args(&self, h: usize, out: &mut Vec<(V, Icit)>) {
        let mut cur = h;
        loop {
            let e = &self.stack[cur];
            out.push((e.a, e.icit));
            if v_tag(e.f) == 2 {
                cur = v_spine_of(e.f);
            } else {
                return;
            }
        }
    }

    /// 链长（元数预检：长度失配 / 元数不足时不收集、零分配）。
    #[inline]
    fn spine_len(&self, h: usize) -> usize {
        let mut cur = h;
        let mut n = 1;
        loop {
            let e = &self.stack[cur];
            if v_tag(e.f) == 2 {
                cur = v_spine_of(e.f);
                n += 1;
            } else {
                return n;
            }
        }
    }

    /// force 后的未解 flex 探测：`tag 5`（空 spine）或 spine 头是 `Meta`。
    /// 返回 meta 号并把逆应用序实参（带 icit）收进 `out`。要求调用方先 force。
    fn flex_of(&self, v: V, out: &mut Vec<(V, Icit)>) -> Option<u32> {
        match v_tag(v) {
            5 => Some(v_meta_of(v)),
            2 => {
                let h = v_spine_of(v);
                let hd = self.spine_head(h);
                if v_tag(hd) != 5 {
                    return None;
                }
                self.collect_args(h, out);
                Some(v_meta_of(hd))
            }
            _ => None,
        }
    }
}

/// 值侧头种类判定（裸单元直查；链查顶端槽的 `hk` 标志，O(1)）。
#[inline]
fn head_kind(spine: &Spine, v: V) -> u8 {
    match v_tag(v) {
        7 => match v_xcell_of(v) {
            XCell::Decl(_) => HK_DECL,
            XCell::Prim(_) => HK_PRIM,
            XCell::Obj { .. } => HK_OBJ,
            _ => HK_OTHER,
        },
        2 => spine.stack[v_spine_of(v)].hk,
        _ => HK_OTHER,
    }
}

/// 链（或裸单元）是否 Obj 头——unify 的位相等捷径对它关闭（`(Obj, Obj)`
/// 走专门合同臂比较接收者 + 实参；捷径关闭使同单元也进专臂而非字面放行）。
#[inline]
fn is_objheaded(spine: &Spine, v: V) -> bool {
    head_kind(spine, v) == HK_OBJ
}

/// 取链（或裸单元）头的 Decl / Prim 名（调用方已判定头种类）。
#[inline]
fn xcell_head_name<'a>(spine: &Spine, v: V) -> &'a str {
    let head = if v_tag(v) == 7 {
        v
    } else {
        spine.spine_head(v_spine_of(v))
    };
    match v_xcell_of(head) {
        XCell::Decl(n) => n,
        XCell::Prim(n) => n,
        _ => unreachable!("头名只对 Decl/Prim 链取"),
    }
}

/// 值是否 Flex（裸未解 meta 立即数或 meta 头的链）。unify 的 pm 特化臂
/// 要求另一侧"非 Flex"（交给 Flex 规则 meta := 值）。
#[inline]
fn is_flex(spine: &Spine, v: V) -> bool {
    match v_tag(v) {
        5 => true,
        2 => v_tag(spine.spine_head(v_spine_of(v))) == 5,
        _ => false,
    }
}

// metacontext
// --------------------------------------------------------------------------------

/// metacontext 条目（与参考版同构）：**类型一律保留**（pruning 检查与
/// `lams` 都要读），解是 bump 内的打包值。Clone 供 flex_flex 的快照回滚。
#[derive(Clone)]
pub(crate) enum MetaEntry {
    Solved(V, V),
    Unsolved(V),
}

/// `vMeta` 的打包版：已解给解值，未解给 Meta 立即数。
#[inline]
fn meta_val_of(metas: &[MetaEntry], m: u32) -> V {
    match &metas[m as usize] {
        MetaEntry::Solved(v, _) => *v,
        MetaEntry::Unsolved(_) => v_meta(m),
    }
}

// decl 表与 builtin prim（L07：值 = λ 链 → Prim 标记；归约在 force）
// --------------------------------------------------------------------------------

/// decl 表条目（参考版 `DeclEntry` 的快版）：定义的类型值与 WHNF 值。
/// builtin 无需 prim 标志——其值就是 λ 链求值出的闭包，应用满元数后环境里
/// 出现 `Tm::Prim` 体，force 时按名触发 [`prim_reduce`]。
#[derive(Clone, Copy)]
pub(crate) struct DeclEntryF {
    pub(crate) ty: V,
    pub(crate) val: V,
}

/// 可变全局表（参考版 `Infer.mutable_map`；单线程 RefCell）。
pub(crate) type MutableMap = RefCell<FxHashMap<SmolStr, V>>;

/// force 的展开燃料池（与 unify 递归共享；参考版 `Infer.unify_fuel`）。
pub(crate) type Fuel = Cell<u32>;

const UNIFY_FUEL: u32 = 4096;

/// 消耗 1 燃料；耗尽即 false（调用方把值当未解处理 / Err）。
#[inline]
fn burn(fuel: &Fuel) -> bool {
    let f = fuel.get();
    if f == 0 {
        return false;
    }
    fuel.set(f - 1);
    true
}

/// 从实参值取字面量内容（非字面量 → None）。返回值的 `'a` 与入参无
/// link——健全性依赖全局不变式：所有 `V` 的 XCell 都指向**当前轮的
/// bump**或 `'static` 钉串（builtin 的 "true"/"false" 等），跨轮
/// `bump.reset()` 前一切句柄已消亡（`clear_round` 清空 mutable_map，
/// decl 表的 Rc 随 Cxt 消亡）。
#[inline]
fn lit_of<'a>(v: V) -> Option<&'a str> {
    match v_tag(v) {
        7 => match v_xcell_of(v) {
            XCell::Lit(s) => Some(s),
            _ => None,
        },
        _ => None
    }
}

/// 递归 def 的自引用占位守卫：`Decl(自身名, 空)`（占位值与 simpl_decl 的
/// 中性条目）——unfold 永无进展只会自旋烧光 fuel 池，直接按中性返回
/// （参考版 force 的 Decl 臂同款守卫）。
#[inline]
fn is_selfref_val(v: V, name: &str) -> bool {
    v_tag(v) == 7 && matches!(v_xcell_of(v), XCell::Decl(n) if *n == name)
}

/// 卡住内建的归约体（参考版 `Infer::prim_reduce` 的逐句移植；L06 的
/// builtin 注册表全部函数体）。`args` 是 [`Spine::collect_args`] 的产出
/// （**逆应用序**，内层在前），`arg` 闭包按自然序（应用序）取第 k 个。
/// 元数 / 字面量检查不满足即 None 保持卡住；文件族失败 panic（两版一致）。
#[allow(clippy::too_many_arguments)]
fn prim_reduce<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    fuel: &Fuel,
    pm_defs: &[(u32, V)],
    name: &str,
    args: &[(V, Icit)], // collect_args 产出（逆应用序）
) -> Option<V> {
    let n = args.len();
    let arg = |k: usize| args[n - 1 - k].0; // 自然序（应用序）第 k 个
    match name {
        "string_concat" => {
            if n < 2 {
                return None;
            }
            match (lit_of(arg(0)), lit_of(arg(1))) {
                (Some(a), Some(b)) => {
                    // 一次 bump 分配 + 两段 memcpy（format! 走 fmt 机器且
                    // String → alloc_str 双份拷贝）
                    let len = a.len() + b.len();
                    let ptr = bump
                        .alloc_layout(std::alloc::Layout::from_size_align(len, 1).unwrap())
                        .as_ptr();
                    // SAFETY: a/b 都是 &str（合法 UTF-8）；两段完整序列按
                    // 字节拼接仍是合法 UTF-8，不会引入跨边界截断的码点
                    let s = unsafe {
                        std::ptr::copy_nonoverlapping(a.as_ptr(), ptr, a.len());
                        std::ptr::copy_nonoverlapping(b.as_ptr(), ptr.add(a.len()), b.len());
                        std::str::from_utf8_unchecked(std::slice::from_raw_parts(ptr, len))
                    };
                    Some(v_xcell(bump.alloc(XCell::Lit(s))))
                }
                _ => None,
            }
        }
        "str_eq" => {
            if n < 2 {
                return None;
            }
            match (lit_of(arg(0)), lit_of(arg(1))) {
                (Some(a), Some(b)) => {
                    let s = if a == b { "true" } else { "false" };
                    Some(v_xcell(bump.alloc(XCell::Lit(bump.alloc_str(s)))))
                }
                _ => None,
            }
        }
        "str_indent2" => {
            if n == 0 {
                return None;
            }
            match lit_of(arg(0)) {
                Some(s) => {
                    let indented = s.replace('\n', "\n  ");
                    Some(v_xcell(bump.alloc(XCell::Lit(bump.alloc_str(&indented)))))
                }
                _ => None,
            }
        }
        "report_check_issue" => {
            if n < 4 {
                return None;
            }
            let get = |i: usize| lit_of(arg(i)).unwrap_or("").to_string();
            let (code, module, signal, message) = (get(0), get(1), get(2), get(3));
            if code.is_empty() || module.is_empty() {
                return Some(v_u());
            }
            let line = format!("{}|{}|{}|{}", code, module, signal, message);
            let mut map = mmap.borrow_mut();
            let existing = match map.get("CheckIssues") {
                Some(v) => lit_of(*v).unwrap_or("").to_string(),
                None => String::new(),
            };
            if !existing.split('\n').any(|l| l == line) {
                let next = if existing.is_empty() {
                    line
                } else {
                    format!("{}\n{}", existing, line)
                };
                map.insert(
                    "CheckIssues".into(),
                    v_xcell(bump.alloc(XCell::Lit(bump.alloc_str(&next)))),
                );
            }
            Some(v_u())
        }
        "string_to_global_type" => {
            if n == 0 {
                return None;
            }
            match lit_of(arg(0)) {
                // 登记名给登记**类型**；未登记名返回以其自身名字的卡住
                // Decl——动态类型的逃逸舱口（后续 unify 的宽松臂处理）
                Some(a) => Some(match decls.get(a) {
                    Some(e) => e.ty,
                    None => v_xcell(bump.alloc(XCell::Decl(bump.alloc_str(a)))),
                }),
                _ => None,
            }
        }
        "create_global" => {
            if n < 2 {
                return None;
            }
            match lit_of(arg(0)) {
                Some(a) => {
                    mmap.borrow_mut().insert(SmolStr::new(a), arg(1));
                    Some(v_u())
                }
                _ => None,
            }
        }
        "change_mutable" => {
            if n < 2 {
                return None;
            }
            match lit_of(arg(0)) {
                Some(a) => {
                    // 同参考版:先取旧值并结束借用,再求值 f——f 的求值可能
                    // 再触发任何 prim,持有 borrow_mut 会 BorrowError panic
                    let old = mmap.borrow().get(a).copied();
                    if let Some(old) = old {
                        let new = vapp1(
                            bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel,
                            pm_defs, arg(1), old, Icit::Expl,
                        );
                        mmap.borrow_mut().insert(SmolStr::new(a), new);
                    }
                    Some(v_u())
                }
                _ => None,
            }
        }
        "get_global" => {
            if n == 0 {
                return None;
            }
            match lit_of(arg(0)) {
                // 缺名不再 panic:None 保持卡住的 Prim 头(参考版同款修改)
                Some(a) => mmap.borrow().get(a).copied(),
                _ => None,
            }
        }
        "get_global_default" => {
            if n < 2 {
                return None;
            }
            match lit_of(arg(0)) {
                Some(a) => Some(mmap.borrow().get(a).copied().unwrap_or(arg(1))),
                _ => None,
            }
        }
        "change_mutable_default" => {
            if n < 3 {
                return None;
            }
            match lit_of(arg(0)) {
                Some(a) => {
                    // 同 change_mutable:先取旧值并结束借用,再求值 f(重入安全)
                    let existing = mmap.borrow().get(a).copied();
                    match existing {
                        Some(old) => {
                            let new = vapp1(
                                bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel,
                                pm_defs, arg(1), old, Icit::Expl,
                            );
                            mmap.borrow_mut().insert(SmolStr::new(a), new);
                        }
                        None => {
                            mmap.borrow_mut().insert(SmolStr::new(a), arg(2));
                        }
                    }
                    Some(v_u())
                }
                _ => None,
            }
        }
        "file_read_all_text" => {
            if n == 0 {
                return None;
            }
            match lit_of(arg(0)) {
                Some(path) => {
                    let content = std::fs::read_to_string(path).unwrap_or_else(|e| {
                        panic!("file_read_all_text: failed to read '{}': {}", path, e)
                    });
                    Some(v_xcell(bump.alloc(XCell::Lit(bump.alloc_str(&content)))))
                }
                _ => None,
            }
        }
        "file_write_all_text" => {
            if n < 2 {
                return None;
            }
            match (lit_of(arg(0)), lit_of(arg(1))) {
                (Some(path), Some(content)) => {
                    std::fs::write(path, content).unwrap_or_else(|e| {
                        panic!("file_write_all_text: failed to write '{}': {}", path, e)
                    });
                    Some(v_u())
                }
                _ => None,
            }
        }
        "file_append_all_text" => {
            if n < 2 {
                return None;
            }
            match (lit_of(arg(0)), lit_of(arg(1))) {
                (Some(path), Some(content)) => {
                    use std::io::Write;
                    let mut file = std::fs::OpenOptions::new()
                        .append(true)
                        .create(true)
                        .open(path)
                        .unwrap_or_else(|e| {
                            panic!("file_append_all_text: failed to open '{}': {}", path, e)
                        });
                    write!(file, "{}", content).unwrap_or_else(|e| {
                        panic!("file_append_all_text: failed to append to '{}': {}", path, e)
                    });
                    Some(v_u())
                }
                _ => None,
            }
        }
        "file_exists" => {
            if n == 0 {
                return None;
            }
            match lit_of(arg(0)) {
                Some(path) => {
                    let exists = std::path::Path::new(path).exists();
                    let s = if exists { "true" } else { "false" };
                    Some(v_xcell(bump.alloc(XCell::Lit(bump.alloc_str(s)))))
                }
                _ => None,
            }
        }
        "file_delete" => {
            if n == 0 {
                return None;
            }
            match lit_of(arg(0)) {
                Some(path) => {
                    std::fs::remove_file(path).unwrap_or_else(|e| {
                        panic!("file_delete: failed to delete '{}': {}", path, e)
                    });
                    Some(v_u())
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// 独立应用（eval_iter 之外的 v_app：force 的解值/pending 应用、prim 的
/// `change_mutable`）。λ → β；卡住 match → pending 累积（值层保存，分支
/// 选中后逐个应用——项层 splice 会把实参自由变量引到错误上下文）；其余
/// → spine 压栈（Rigid/Flex/Decl/Prim/Obj 头的链）。参考版对 Π/U/字面量/
/// Sum/SumCase 的应用 panic（"impossible apply"）——快版照做（两版同时
/// 不可达 / 同时 panic，判定一致）。
#[allow(clippy::too_many_arguments)]
fn vapp1<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    fuel: &Fuel,
    pm_defs: &[(u32, V)],
    f: V,
    a: V,
    i: Icit,
) -> V {
    if v_tag(f) == 1 {
        let c = v_clo_of(f);
        let env = env_ext(bump, c.env, a);
        eval_iter(
            bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, pm_defs, env, c.body,
        )
    } else if v_tag(f) == 7 {
        match v_xcell_of(f) {
            XCell::Match {
                scrutinee,
                env,
                cases,
                pending,
            } => {
                // 卡住 match 吸收实参进 pending（新单元——bump 内不可变）
                let mut p: Vec<(V, Icit)> = Vec::with_capacity(pending.len() + 1);
                p.extend_from_slice(pending);
                p.push((a, i));
                v_xcell(bump.alloc(XCell::Match {
                    scrutinee: *scrutinee,
                    env: *env,
                    cases,
                    pending: bump.alloc_slice_fill_iter(p),
                }))
            }
            // Lit / Sum / SumCase 不可应用（参考版 panic）；Decl/Prim/Obj
            // 压栈成链
            XCell::Lit(_) | XCell::Sum { .. } | XCell::SumCase { .. } => {
                panic!("impossible apply")
            }
            _ => spine.push(f, a, i),
        }
    } else if v_tag(f) == 3 || v_tag(f) == 4 || v_tag(f) == 6 {
        // U / Π / LiteralType 不可应用（参考版 panic）
        panic!("impossible apply")
    } else {
        spine.push(f, a, i)
    }
}

/// `v.field` 的值级投影：Sum 取索引参数的值；SumCase 先查 typ 的参数（索引）
/// 再查构造子字段。其余（Rigid / Flex / Decl / 卡住的 Obj / 函数……）返回
/// None → 卡住成 `Obj`。（参考版 mod.rs `project` 同款。）
fn project<'a>(v: V, name: &str) -> Option<V> {
    match v_tag(v) {
        7 => match v_xcell_of(v) {
            XCell::Sum { params, .. } => {
                params.iter().find(|p| p.name == name).map(|p| p.val)
            }
            XCell::SumCase { typ, datas, .. } => {
                let params = match v_xcell_of(*typ) {
                    XCell::Sum { params, .. } => params,
                    _ => return None,
                };
                params
                    .iter()
                    .find(|p| p.name == name)
                    .map(|p| p.val)
                    .or_else(|| datas.iter().find(|d| d.name == name).map(|d| d.val))
            }
            _ => None,
        },
        _ => None,
    }
}

/// 值树里是否出现某层级（浅层结构扫描；闭包跳过——那里的环由 force 的
/// fuel 兜底）。特化解的环守卫（`pm_solve`）用。（参考版
/// `val_mentions_lvl` 同款遍历面。）
pub(crate) fn val_mentions_lvl(spine: &Spine, defs: &[V], v: V, x: u32) -> bool {
    match v_tag(v) {
        // Rigid 裸头
        0 => v_lvl_of(v) == x,
        2 => {
            let mut args: Vec<(V, Icit)> = Vec::new();
            spine.collect_args(v_spine_of(v), &mut args);
            args.iter().any(|(a, _)| val_mentions_lvl(spine, defs, *a, x))
        }
        // Flex 裸头（链在 tag 2）
        5 => false,
        1 | 4 => false, // Lam/Pi 闭包跳过（参考版同）
        3 | 6 => false,
        7 => match v_xcell_of(v) {
            XCell::Lit(_) => false,
            XCell::Decl(_) | XCell::Prim(_) => false, // 空实参（链在 tag 2）
            XCell::Obj { val, .. } => val_mentions_lvl(spine, defs, *val, x),
            XCell::Sum { params, .. } => params
                .iter()
                .any(|p| val_mentions_lvl(spine, defs, p.val, x) || val_mentions_lvl(spine, defs, p.ty, x)),
            XCell::SumCase { typ, datas, .. } => {
                val_mentions_lvl(spine, defs, *typ, x)
                    || datas.iter().any(|d| val_mentions_lvl(spine, defs, d.val, x))
            }
            XCell::Match {
                scrutinee,
                env,
                pending,
                ..
            } => {
                val_mentions_lvl(spine, defs, *scrutinee, x)
                    || (0..env_len(*env)).any(|i| {
                        val_mentions_lvl(spine, defs, env_nth(defs, *env, i), x)
                    })
                    || pending.iter().any(|(u, _)| val_mentions_lvl(spine, defs, *u, x))
            }
        },
        _ => false,
    }
}
// force（迭代）
// --------------------------------------------------------------------------------

/// **force**：把值更新到 metacontext / 模式特化的当前状态。L07 增量（参考
/// 版 `Infer::force` 的迭代化——保序语义）：
/// - Flex 已解 → 展开应用（burn fuel）；
/// - 裸 Rigid → 查 pm_defs，命中且 burn → force(解值)（惰性精化读点展开）；
/// - Match → force scrutinee；是 SumCase 且 burn → eval_aux 选分支：选中 →
///   值 = eval(分支体) 后逐个 v_app(pending)，再 force；否则原样卡住返回；
/// - Decl → 查表 unfold（burn，自引用占位直接按中性返回）；
/// - Prim → prim_reduce（15 个 builtin；字面量/元数检查不满足保持卡住；
///   空实参同样烧 1 fuel——与参考版逐 force 调用消耗对齐）；
/// - Obj → force 被投影者 → project 命中且 burn → 应用链上实参，否则卡回
///   Obj（参考版返回 forced 内层的新单元，快版同款重建）。
///
/// 内部的 eval_iter 调用用**本调用私有的草稿栈**（外层 eval/unify 循环的
/// work/vals 不能被清空——force 可能在它们循环体中途被调用）。
#[allow(clippy::too_many_arguments)]
fn force<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    fuel: &Fuel,
    pm_defs: &[(u32, V)],
    v0: V,
) -> V {
    let mut v = v0;
    // 实参缓冲在本次 force 调用内的展开轮间复用（clear 保容量）
    let mut work: Vec<W<'a>> = Vec::new();
    let mut vals: Vec<V> = Vec::new();
    let mut icits: Vec<Icit> = Vec::new();
    let mut args: Vec<(V, Icit)> = Vec::new();
    loop {
        match v_tag(v) {
            5 => match &metas[v_meta_of(v) as usize] {
                MetaEntry::Solved(sol, _) if burn(fuel) => v = *sol,
                _ => return v,
            },
            2 => {
                let h = v_spine_of(v);
                let hd = spine.spine_head(h);
                if v_tag(hd) == 5 {
                    // flex 链：解应用到全部实参（应用序 = 收集序的逆序）；
                    // 每步都可能 β / 触发 prim / 吸收进 pending——参考版
                    // vAppSp 逐步 vApp 同款
                    match &metas[v_meta_of(hd) as usize] {
                        MetaEntry::Unsolved(_) => return v,
                        MetaEntry::Solved(sol, _) => {
                            if !burn(fuel) {
                                return v;
                            }
                            args.clear();
                            spine.collect_args(h, &mut args);
                            let mut t = *sol;
                            for &(a, i) in args.iter().rev() {
                                t = vapp1(
                                    bump, spine, &mut work, &mut vals, &mut icits, defs, metas,
                                    decls, mmap, fuel, pm_defs, t, a, i,
                                );
                            }
                            v = t;
                        }
                    }
                } else {
                    match spine.stack[h].hk {
                        HK_DECL => {
                            let name = xcell_head_name(spine, hd);
                            match decls.get(name) {
                                Some(e) if !is_selfref_val(e.val, name) && burn(fuel) => {
                                    args.clear();
                                    spine.collect_args(h, &mut args);
                                    let mut t = e.val;
                                    for &(a, i) in args.iter().rev() {
                                        t = vapp1(
                                            bump, spine, &mut work, &mut vals, &mut icits, defs,
                                            metas, decls, mmap, fuel, pm_defs, t, a, i,
                                        );
                                    }
                                    v = t;
                                }
                                _ => return v,
                            }
                        }
                        HK_PRIM => {
                            // 卡住的内建：实参按自然序交给 builtin 体归约；
                            // 元数不足 / 实参不合 / 缺名时保持卡住。参考版对
                            // 每次 force 调用烧 1 fuel（归约成功与否皆然）。
                            // 实参先逐个 force 再交给 prim_reduce（与参考版
                            // Val::Prim 分支对齐）：spine 槽可能存着未归约的
                            // 嵌套 prim，不 force 外层永远过不了字面量检查。
                            if !burn(fuel) {
                                return v;
                            }
                            let name = xcell_head_name(spine, hd);
                            args.clear();
                            spine.collect_args(h, &mut args);
                            for i in 0..args.len() {
                                let a = args[i].0;
                                args[i].0 =
                                    force(bump, spine, defs, metas, decls, mmap, fuel, pm_defs, a);
                            }
                            match prim_reduce(
                                bump, spine, &mut work, &mut vals, &mut icits, defs, metas,
                                decls, mmap, fuel, pm_defs, name, &args,
                            ) {
                                Some(r) => v = r,
                                None => return v,
                            }
                        }
                        HK_OBJ => {
                            // 卡住投影：先 force 被投影者，project 命中 →
                            // 应用链上实参；miss → 重建 forced 内层的卡住
                            // Obj（参考版 `Val::Obj(Box::new(v), name, sp)`）
                            let (inner, oname) = match v_xcell_of(hd) {
                                XCell::Obj { val, name } => (*val, *name),
                                _ => unreachable!("hk=Obj 的链头必是 Obj 单元"),
                            };
                            let v2 = force(
                                bump, spine, defs, metas, decls, mmap, fuel, pm_defs, inner,
                            );
                            match project(v2, oname) {
                                Some(p) if burn(fuel) => {
                                    args.clear();
                                    spine.collect_args(h, &mut args);
                                    let mut t = p;
                                    for &(a, i) in args.iter().rev() {
                                        // 命中路径须走 vapp1（参考版 vAppSp
                                        // 逐步 vApp 同款）：字段值可能是 Lam
                                        // 闭包（β）或卡住 Match（吸收 pending）
                                        // ——spine.push 只压中性槽，会搁浅
                                        t = vapp1(
                                            bump, spine, &mut work, &mut vals, &mut icits,
                                            defs, metas, decls, mmap, fuel, pm_defs, t, a,
                                            i,
                                        );
                                    }
                                    v = t;
                                }
                                _ => {
                                    args.clear();
                                    spine.collect_args(h, &mut args);
                                    let mut t =
                                        v_xcell(bump.alloc(XCell::Obj { val: v2, name: oname }));
                                    for &(a, i) in args.iter().rev() {
                                        t = spine.push(t, a, i);
                                    }
                                    return t;
                                }
                            }
                        }
                        _ => return v,
                    }
                }
            }
            // 裸 Rigid：模式精化在读点展开（层级/槽位一概不动）
            0 => {
                let x = v_lvl_of(v);
                match pm_defs.iter().rev().find(|(l, _)| *l == x) {
                    Some((_, pv)) if burn(fuel) => v = *pv,
                    _ => return v,
                }
            }
            7 => match v_xcell_of(v) {
                XCell::Lit(_) | XCell::Sum { .. } | XCell::SumCase { .. } => return v,
                XCell::Decl(n) => match decls.get(*n) {
                    Some(e) if !is_selfref_val(e.val, n) && burn(fuel) => {
                        v = e.val; // 空实参：直接继续 force 展开值
                    }
                    _ => return v,
                },
                XCell::Prim(_) => {
                    // 空实参：prim_reduce 元数检查必败；与参考版一致仍按
                    // force 调用消耗 1 fuel
                    if !burn(fuel) {
                        return v;
                    }
                    return v;
                }
                XCell::Obj { val, name } => {
                    let v2 = force(bump, spine, defs, metas, decls, mmap, fuel, pm_defs, *val);
                    match project(v2, name) {
                        Some(p) if burn(fuel) => v = p,
                        _ => {
                            return v_xcell(bump.alloc(XCell::Obj { val: v2, name }));
                        }
                    }
                }
                XCell::Match {
                    scrutinee,
                    env,
                    cases,
                    pending,
                } => {
                    // 卡住的 match：scrutinee 在创建之后才被特化/解出时，
                    // 这里重新尝试选分支（精化传播进"卡住 match 里面"）。
                    // 选中 → eval 分支体 → 值层逐个应用 pending → 继续
                    // force；否则原样卡住返回（pending 原样保留）。
                    let s2 = force(bump, spine, defs, metas, decls, mmap, fuel, pm_defs, *scrutinee);
                    let mut matched = false;
                    if v_tag(s2) == 7 && matches!(v_xcell_of(s2), XCell::SumCase { .. }) {
                        if burn(fuel) {
                            if let Some((body_tm, env2)) = eval_aux(
                                bump, spine, defs, metas, decls, mmap, fuel, pm_defs, s2, *env,
                                cases,
                            ) {
                                let mut vb = eval_iter(
                                    bump, spine, &mut work, &mut vals, &mut icits, defs, metas,
                                    decls, mmap, fuel, pm_defs, env2, body_tm,
                                );
                                for &(u, i) in *pending {
                                    vb = vapp1(
                                        bump, spine, &mut work, &mut vals, &mut icits, defs,
                                        metas, decls, mmap, fuel, pm_defs, vb, u, i,
                                    );
                                }
                                v = vb;
                                matched = true;
                            }
                        }
                    }
                    if !matched {
                        return v;
                    }
                }
            },
            _ => return v,
        }
    }
}

/// 合一器**参数视角**的 WHNF：与 force 相同，但不展开 pm_defs 精化、不做
/// Match 重选。`invert` / `prune_vflex` 关心的是"元变量被应用在哪些槽位
/// 上"——槽位引用（裸 Rigid）本身就是作用域事实，分支内的精化等式不改变
/// 槽位的存在；在它们身上展开反而会把可逆 spine 变成含构造子值的不可逆
/// spine。（参考版 `Infer::force_arg` 同款守卫。）
#[allow(clippy::too_many_arguments)]
fn force_arg<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    fuel: &Fuel,
    pm_defs: &[(u32, V)],
    v: V,
) -> V {
    match v_tag(v) {
        0 => v,
        7 if matches!(v_xcell_of(v), XCell::Match { .. }) => v,
        _ => force(bump, spine, defs, metas, decls, mmap, fuel, pm_defs, v),
    }
}

// 运行时分支选择（值层首匹配，无合一）
// --------------------------------------------------------------------------------

/// 按模式首匹配。返回 (分支体, 扩展后的 env)。任何 head 都不会 panic——
/// 不命中就返回 None，由调用方停成卡住 Match。（参考版
/// `Compiler::eval_aux` 同款：Any/Bind → 命中；Con → head 是同名 SumCase
/// （ctor 名在 typ 的 Sum cases 里）→ 逐 datas×子模式递归；名字不在 typ
/// 的 ctor 表里 → 按变量模式命中（保守兼容）；同类型不同构造子 → 试下一
/// 分支。入口 force(head)。）
#[allow(clippy::too_many_arguments)]
fn eval_aux<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    fuel: &Fuel,
    pm_defs: &[(u32, V)],
    head: V,
    env: Env<'a>,
    cases: &'a [(PatternDetail, &'a Tm<'a>)],
) -> Option<(&'a Tm<'a>, Env<'a>)> {
    let head = force(bump, spine, defs, metas, decls, mmap, fuel, pm_defs, head);
    for (pat, body) in cases.iter() {
        if let Some(r) = eval_aux_case(
            bump, spine, defs, metas, decls, mmap, fuel, pm_defs, head, env, pat, *body,
        ) {
            return Some(r);
        }
    }
    None
}

/// 单 (模式, 分支体) 的匹配（`eval_aux` 的内层；返回 None = 试下一分支）。
#[allow(clippy::too_many_arguments)]
fn eval_aux_case<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    fuel: &Fuel,
    pm_defs: &[(u32, V)],
    head: V,
    env: Env<'a>,
    pat: &PatternDetail,
    body: &'a Tm<'a>,
) -> Option<(&'a Tm<'a>, Env<'a>)> {
    match pat {
        PatternDetail::Any(_) | PatternDetail::Bind(_) => {
            Some((body, env_ext(bump, env, head)))
        }
        PatternDetail::Con(name, subs) => {
            let (case_name, typ, datas) = match v_tag(head) {
                7 => match v_xcell_of(head) {
                    XCell::SumCase {
                        typ,
                        case_name,
                        datas,
                    } => (*case_name, *typ, *datas),
                    _ => return None, // 非 SumCase：试下一分支
                },
                _ => return None,
            };
            let ctor_names = match v_xcell_of(typ) {
                XCell::Sum { cases, .. } => *cases,
                _ => return None, // typ 不是 Sum：试下一分支
            };
            let in_type = ctor_names.iter().any(|c| *c == name.data);
            if in_type && case_name == name.data {
                if subs.len() != datas.len() {
                    return None; // 子模式数失配：试下一分支（参考版 continue）
                }
                // datas 与子模式按声明序 zip，逐个下钻；先 prepend 被匹配值
                // 本身（head 槽，编译期 walk_con 入口同序绑定），再逐字段
                // prepend 子模式槽值（编译期字段槽在后）
                let mut cur_body = body;
                let mut cur_env = env_ext(bump, env, head);
                for (d, sub) in datas.iter().zip(subs.iter()) {
                    let df = force(bump, spine, defs, metas, decls, mmap, fuel, pm_defs, d.val);
                    match eval_aux_case(
                        bump, spine, defs, metas, decls, mmap, fuel, pm_defs, df, cur_env, sub,
                        cur_body,
                    ) {
                        Some((b, e)) => {
                            cur_body = b;
                            cur_env = e;
                        }
                        None => return None, // 子模式失配：试下一分支
                    }
                }
                Some((cur_body, cur_env))
            } else if !in_type {
                // 不是该类型的构造子名 → 变量模式（保守兼容）
                Some((body, env_ext(bump, env, head)))
            } else {
                None // 同类型不同构造子 → 试下一分支
            }
        }
    }
}

// eval（双栈迭代 + 右链快速路径 + AppPruning 实参应用 + decl 表 + L07 变体）
// --------------------------------------------------------------------------------

/// eval 的 work 栈条目。
enum W<'a> {
    Tm(&'a Tm<'a>, Env<'a>),
    /// 应用（icit 来自 `Tm::App`）：vals 顶两个（先函数后实参）——β、
    /// pending 累积或入栈。
    Apply(Icit),
    /// vals 顶上是实参；函数值已知是闭包（β 岔路下降时已 `env_nth` 出来），
    /// 直接 β（icit 无关）。
    ApplyKnown(V),
    /// vals 顶上是 base 值，其下 `k` 个是待应用的链头（内层最上；每个链头
    /// 的 icit 在 `icits` 侧栈平行压弹）。
    ChainWrap(u32),
    /// vals 顶是 let 绑定的值：弹出压进环境，继续求值体。
    LetBody(&'a Tm<'a>, Env<'a>),
    /// vals 顶是 Π 定义域值：弹出配余定义域闭包，压 Π 值。
    PiBody(&'a str, Icit, &'a Tm<'a>, Env<'a>),
    /// vals 顶是 `vAppPruning` 的当前值；沿 (env, pr) 平行走完剩余槽位
    /// （外层先应用，icit 取自掩码；`None` 槽跳过）。
    AppPrun(Env<'a>, Option<&'a PrCons<'a>>),
    /// vals 顶是 `vAppPruning` 的当前值；本步把 `arg` 以 `icit` 应用上去
    /// （Clo → β；卡住 match → pending；其它 → spine.push）。
    AppPrunOne(V, Icit),
    /// vals 顶是投影接收者的值：project 命中给投影值，miss 卡成 Obj。
    ObjSel(&'a str),
    /// vals 顶自底向上是 (v0,t0,...,v_{n-1},t_{n-1})（求值序）：装配 Sum。
    SumAsm {
        name: &'a str,
        params: &'a [SumParamT<'a>],
        cases: &'a [&'a str],
    },
    /// vals 顶自底向上是 (typ, d0..d_{nd-1})：装配 SumCase。
    SumCaseAsm {
        case_name: &'a str,
        datas: &'a [SumDataT<'a>],
    },
    /// vals 顶是 scrutinee 的值：force 后是 SumCase → eval_aux 选分支
    /// （选中 → 尾推分支体）；否则卡成 Match（pending 空）。
    MatchSel {
        cases: &'a [(PatternDetail, &'a Tm<'a>)],
        env: Env<'a>,
    },
}

/// 双栈迭代 eval（L06 版 + L07 增量：decl 表 panic 语义、Prim 体、投影、
/// Sum/SumCase 装配、match 的编译期选择与卡住停等）。
#[allow(clippy::too_many_arguments)]
fn eval_iter<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    fuel: &Fuel,
    pm_defs: &[(u32, V)],
    env0: Env<'a>,
    tm0: &'a Tm<'a>,
) -> V {
    work.clear();
    vals.clear();
    icits.clear();
    work.push(W::Tm(tm0, env0));
    while let Some(w) = work.pop() {
        match w {
            W::Tm(Tm::Var(i), env) => vals.push(env_nth(defs, env, *i)),
            W::Tm(Tm::Lam(name, icit, body), env) => {
                let c = bump.alloc(CloCell {
                    name,
                    icit: *icit,
                    env,
                    body,
                });
                vals.push(v_clo(c));
            }
            W::Tm(Tm::U, _) => vals.push(v_u()),
            W::Tm(Tm::LiteralType, _) => vals.push(v_lit_ty()),
            W::Tm(Tm::LiteralIntro(s), _) => vals.push(v_xcell(bump.alloc(XCell::Lit(s)))),
            // 按名查 decl 表：命中给登记值；miss panic（"unbound global"，
            // 参考版 eval 的 Tm::Decl 臂同款——良型项不可达）
            W::Tm(Tm::Decl(name), _) => vals.push(match decls.get(*name) {
                Some(e) => e.val,
                None => panic!("unbound global {}", name),
            }),
            // builtin 体：实参 = env 全部槽（应用序 = 外层槽先应用）→ 链头
            // = 最后应用 = 最内槽。归约统一在 force（不在求值点按 env 触发
            // ——quote → eval 往返时项已改成 `Prim 实参` 的应用形态，按
            // 现场 env 触发会把无关的字面量拼进来；参考版注释同款论证）
            W::Tm(Tm::Prim(name), env) => {
                let n = env_len(env);
                let mut acc = v_xcell(bump.alloc(XCell::Prim(name)));
                let mut i = n;
                while i > 0 {
                    i -= 1;
                    acc = spine.push(acc, env_nth(defs, env, i), Icit::Expl);
                }
                vals.push(acc);
            }
            W::Tm(Tm::Pi(name, icit, dom, cod), env) => {
                work.push(W::PiBody(name, *icit, cod, env));
                work.push(W::Tm(dom, env));
            }
            W::Tm(Tm::Let(_, _, t, u), env) => {
                work.push(W::LetBody(u, env));
                work.push(W::Tm(t, env));
            }
            W::Tm(Tm::Meta(m), _) => vals.push(meta_val_of(metas, *m)),
            W::Tm(Tm::AppPruning(head, pr), env) => {
                work.push(W::AppPrun(env, *pr));
                work.push(W::Tm(head, env));
            }
            // 投影：求值接收者（不 force——参考版同），project 命中给投影
            // 值，miss 卡成 `Obj`
            W::Tm(Tm::Obj(h, name), env) => {
                work.push(W::ObjSel(name));
                work.push(W::Tm(h, env));
            }
            // enum 本体：逐参数求值（值 + 类型）后装配
            W::Tm(Tm::Sum(name, params, cases), env) => {
                work.push(W::SumAsm { name, params, cases });
                for p in params.iter().rev() {
                    work.push(W::Tm(p.ty, env));
                    work.push(W::Tm(p.val, env));
                }
            }
            W::Tm(
                Tm::SumCase {
                    typ,
                    case_name,
                    datas,
                },
                env,
            ) => {
                work.push(W::SumCaseAsm { case_name, datas });
                for d in datas.iter().rev() {
                    work.push(W::Tm(d.val, env));
                }
                work.push(W::Tm(typ, env));
            }
            // match：求值 scrutinee → force → 选分支 / 卡住（参考版 eval 的
            // Tm::Match 臂：SumCase + eval_aux 命中给分支体（eval_aux 是值
            // 层首匹配，无合一）；其它 neutral 卡 Match，pending 空）
            W::Tm(Tm::Match(s, cases), env) => {
                work.push(W::MatchSel { cases, env });
                work.push(W::Tm(s, env));
            }
            W::Tm(app @ Tm::App(..), env) => {
                // 右链下钻：头为非闭包变量时头值直接进 vals（icit 进侧栈）
                let mut tm = app;
                let mut heads: u32 = 0;
                loop {
                    let (f, a, i) = match tm {
                        Tm::App(f, a, i) => (f, a, i),
                        base => {
                            if heads > 0 {
                                work.push(W::ChainWrap(heads));
                            }
                            work.push(W::Tm(base, env));
                            break;
                        }
                    };
                    let i = *i;
                    match f {
                        Tm::Var(ix) => {
                            let vf = env_nth(defs, env, *ix);
                            if v_tag(vf) == 1 {
                                // β 岔路：函数值已在手上（闭包），ApplyKnown
                                // 直接管 β（icit 无关）；heads>0 时 ChainWrap
                                // 照旧收拢
                                if heads > 0 {
                                    work.push(W::ChainWrap(heads));
                                }
                                work.push(W::ApplyKnown(vf));
                                work.push(W::Tm(a, env));
                                break;
                            }
                            vals.push(vf);
                            icits.push(i);
                            heads += 1;
                            tm = a;
                        }
                        _ => {
                            // 复合函数头：通用三推（同样先收已收的头）
                            if heads > 0 {
                                work.push(W::ChainWrap(heads));
                            }
                            work.push(W::Apply(i));
                            work.push(W::Tm(a, env));
                            work.push(W::Tm(f, env));
                            break;
                        }
                    }
                }
            }
            W::Apply(i) => {
                let va = vals.pop().expect("eval 栈：Apply 缺实参");
                let vf = vals.pop().expect("eval 栈：Apply 缺函数");
                if v_tag(vf) == 1 {
                    // β 归约是尾调用：直接推入体，继续循环
                    let c = v_clo_of(vf);
                    let env = env_ext(bump, c.env, va);
                    work.push(W::Tm(c.body, env));
                } else {
                    let r = vapp1(
                        bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, pm_defs,
                        vf, va, i,
                    );
                    vals.push(r);
                }
            }
            W::ApplyKnown(vf) => {
                let va = vals.pop().expect("eval 栈：ApplyKnown 缺实参");
                let c = v_clo_of(vf);
                let env = env_ext(bump, c.env, va);
                work.push(W::Tm(c.body, env));
            }
            W::ChainWrap(k) => {
                let mut v = vals.pop().expect("eval 栈：ChainWrap 缺 base");
                for _ in 0..k {
                    let vf = vals.pop().expect("eval 栈：ChainWrap 缺链头");
                    let i = icits.pop().expect("eval 栈：ChainWrap 缺 icit");
                    v = vapp1(
                        bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, pm_defs,
                        vf, v, i,
                    );
                }
                vals.push(v);
            }
            W::LetBody(u, env) => {
                let vt = vals.pop().expect("eval 栈：LetBody 缺绑定值");
                work.push(W::Tm(u, env_ext(bump, env, vt)));
            }
            W::PiBody(name, icit, cod, env) => {
                let dom = vals.pop().expect("eval 栈：PiBody 缺定义域");
                let cell = bump.alloc(PiCell {
                    name,
                    icit,
                    dom,
                    env,
                    body: cod,
                });
                vals.push(v_pi(cell));
            }
            W::AppPrun(env, bds) => match bds {
                None => {
                    // 与 reference 的 (None, None) 对齐：掩码先行耗尽
                    debug_assert!(env.binds.is_none() && env.flat_len == 0);
                }
                Some(b) if env.binds.is_none() && b.slot.is_none() => {
                    // O(1) 跳段：binds 耗尽后剩余链只剩 define 槽。
                    assert!(env.flat_len >= b.none_run);
                    work.push(W::AppPrun(
                        Env {
                            flat_len: env.flat_len - b.none_run,
                            ..env
                        },
                        b.after_run,
                    ));
                }
                Some(b) => {
                    // 内层绑定 = 链头；链耗尽后走平坦 def 区域末端。先跑
                    // 余下槽位（外层），再应用本槽（内层最后应用）
                    let (arg, rest) = if let Some(e) = env.binds {
                        (
                            b.slot.map(|_| e.val),
                            Env {
                                binds: e.next,
                                ..env
                            },
                        )
                    } else if env.flat_len > 0 {
                        let v = defs[(env.flat_base + env.flat_len - 1) as usize];
                        (
                            b.slot.map(|_| v),
                            Env {
                                flat_len: env.flat_len - 1,
                                ..env
                            },
                        )
                    } else {
                        panic!("impossible") // env 与 pr 错位
                    };
                    match (arg, b.slot) {
                        (Some(a), Some(i)) => work.push(W::AppPrunOne(a, i)),
                        (None, Some(_)) => panic!("impossible"), // env 短于 pr
                        _ => {}
                    }
                    work.push(W::AppPrun(rest, b.next));
                }
            },
            W::AppPrunOne(arg, i) => {
                let v = vals.pop().expect("eval 栈：AppPrunOne 缺值");
                if v_tag(v) == 1 {
                    let c = v_clo_of(v);
                    let env = env_ext(bump, c.env, arg);
                    work.push(W::Tm(c.body, env));
                } else {
                    let r = vapp1(
                        bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, pm_defs,
                        v, arg, i,
                    );
                    vals.push(r);
                }
            }
            W::ObjSel(name) => {
                let v = vals.pop().expect("eval 栈：ObjSel 缺接收者");
                match project(v, name) {
                    Some(p) => vals.push(p),
                    None => vals.push(v_xcell(bump.alloc(XCell::Obj { val: v, name }))),
                }
            }
            W::SumAsm { name, params, cases } => {
                let total = 2 * params.len();
                let mut items: Vec<V> = Vec::with_capacity(total);
                for _ in 0..total {
                    items.push(vals.pop().expect("eval 栈：SumAsm 缺参数"));
                }
                items.reverse(); // [v0, t0, v1, t1, ...]
                let mut ps: Vec<SumParamV<'_>> = Vec::with_capacity(params.len());
                for (k, p) in params.iter().enumerate() {
                    ps.push(SumParamV {
                        name: p.name,
                        val: items[2 * k],
                        ty: items[2 * k + 1],
                        icit: p.icit,
                    });
                }
                vals.push(v_xcell(bump.alloc(XCell::Sum {
                    name,
                    params: bump.alloc_slice_fill_iter(ps),
                    cases,
                })));
            }
            W::SumCaseAsm { case_name, datas } => {
                let nd = datas.len();
                let mut items: Vec<V> = Vec::with_capacity(nd);
                for _ in 0..nd {
                    items.push(vals.pop().expect("eval 栈：SumCaseAsm 缺字段"));
                }
                items.reverse(); // [d0, d1, ...]
                let typ = vals.pop().expect("eval 栈：SumCaseAsm 缺 typ");
                let mut ds: Vec<SumDataV<'_>> = Vec::with_capacity(nd);
                for (k, d) in datas.iter().enumerate() {
                    ds.push(SumDataV {
                        name: d.name,
                        val: items[k],
                        icit: d.icit,
                    });
                }
                vals.push(v_xcell(bump.alloc(XCell::SumCase {
                    typ,
                    case_name,
                    datas: bump.alloc_slice_fill_iter(ds),
                })));
            }
            W::MatchSel { cases, env } => {
                let sv = vals.pop().expect("eval 栈：MatchSel 缺 scrutinee");
                let s2 = force(bump, spine, defs, metas, decls, mmap, fuel, pm_defs, sv);
                let mut stuck = true;
                if v_tag(s2) == 7 && matches!(v_xcell_of(s2), XCell::SumCase { .. }) {
                    if burn(fuel) {
                        if let Some((body_tm, env2)) = eval_aux(
                            bump, spine, defs, metas, decls, mmap, fuel, pm_defs, s2, env, cases,
                        ) {
                            // 分支选中：体在本 eval 循环里尾推（pending 空）
                            work.push(W::Tm(body_tm, env2));
                            stuck = false;
                        }
                    }
                }
                if stuck {
                    vals.push(v_xcell(bump.alloc(XCell::Match {
                        scrutinee: s2,
                        env,
                        cases,
                        pending: &[],
                    })));
                }
            }
        }
    }
    vals.pop().expect("eval 必须恰有一个根值")
}

// quote（任务栈迭代 + 流式右链；flex/Decl/Prim 头共享节点 + L07 变体）
// --------------------------------------------------------------------------------

/// quote 任务。`ChainRun` 的「断点续跑」语义见 L01/L04/L05/L06；quote 不产
/// `AppPruning`（项层洞形态，值层不存在）。L07 增量：`Obj1` / `SumAsm` /
/// `SumCaseAsm` 装配任务；`Match` 直接内联处理（分支体在"捕获 env + fresh
/// rigid 槽"下用**简化 decl 表**重求值再 quote——quote → eval 往返恒等；
/// pending 实参按应用序包在 Match 外）。
enum QJob<'a> {
    /// 引一个值（先 force）。
    Q(V, u32),
    /// done 栈顶是体，包一层 Lam（名字与 icit 随闭包携带）。
    Lam1(&'a str, Icit),
    /// done 栈顶两个（先 cod 后 dom），合一个 Pi（icit 在 PiCell 里）。
    Pi1(&'a PiCell<'a>),
    /// 先 eval（引出闭包/余定义域的体）再引。
    EvalQ(&'a Tm<'a>, Env<'a>, u32),
    /// done 栈顶两个（先 f 后 a），合一个 App（icit 随任务携带）——
    /// 二叉 fallback 用。
    App1(Icit),
    /// 记忆化屏障：done 栈顶是刚完成的 `Q(key, level)` 结果，入表后放回。
    MemoStore(u64, u32),
    /// 流式右链：next..=end 逐层 App 自底向上；f 与 f0 同一变量 / 同一未解
    /// meta / 同一 Decl / Prim 名时用共享节点，否则挂起（Q 引 f）后续跑。
    ChainRun {
        level: u32,
        next: usize,
        end: usize,
        f0: V,
        idx_node: Option<&'a Tm<'a>>,
        prev: Option<&'a Tm<'a>>,
    },
    /// done 栈顶是投影接收者的引读：包 `Tm::Obj`。
    Obj1(&'a str),
    /// done 栈顶自底向上是 (v0,t0,...)：装配 Tm::Sum（元数据取值层槽）。
    SumAsm {
        name: &'a str,
        params: &'a [SumParamV<'a>],
        cases: &'a [&'a str],
    },
    /// done 栈顶自底向上是 (typ, d0..)：装配 Tm::SumCase（元数据取值层槽）。
    SumCaseAsm {
        case_name: &'a str,
        datas: &'a [SumDataV<'a>],
    },
}

/// (值打包字, quote level) → 已引结果子树。icit 不进键：它随 `V` 指向的
/// 单元/槽位携带，同一打包字在同一 level 的 quote 产出（含 icit）唯一。
/// tag 7 的 L07 变体（Match/Sum/…）不进表：它们的引读依赖简化 decl 表与
/// 精化状态，且同指针重引同结果的场景极少（参考版无 quote 记忆化，保守
/// 起见对新增值形态保持无记忆化口径）。
type QuoteMemo<'a> = FxHashMap<(u64, u32), &'a Tm<'a>>;

/// 任务栈 quote（L06 版 + LiteralType/LiteralIntro/Decl/Prim/Obj/Sum/
/// SumCase/Match 臂）。
#[allow(clippy::too_many_arguments)]
fn quote_iter<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    tasks: &mut Vec<QJob<'a>>,
    done: &mut Vec<&'a Tm<'a>>,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    fuel: &Fuel,
    pm_defs: &[(u32, V)],
    level0: u32,
    v0: V,
    mut memo: Option<&mut QuoteMemo<'a>>,
) -> &'a Tm<'a> {
    tasks.clear();
    done.clear();
    tasks.push(QJob::Q(v0, level0));
    while let Some(job) = tasks.pop() {
        match job {
            QJob::Q(v0, level) => {
                // 先 force（metacontext / 精化在 quote 期间冻结，同键同结果）
                let v = force(
                    bump, spine, defs, metas, decls, mmap, fuel, pm_defs, v0,
                );
                match v_tag(v) {
                    0 => done.push(bump.alloc(Tm::Var(level - v_lvl_of(v) - 1))),
                    1 => {
                        if let Some(t) = memo.as_deref_mut().and_then(|m| m.get(&(v.0, level))) {
                            done.push(*t);
                            continue;
                        }
                        let c = v_clo_of(v);
                        if memo.is_some() {
                            tasks.push(QJob::MemoStore(v.0, level));
                        }
                        let env = env_ext(bump, c.env, v_lvl(level));
                        tasks.push(QJob::Lam1(c.name, c.icit));
                        tasks.push(QJob::EvalQ(c.body, env, level + 1));
                    }
                    5 => done.push(bump.alloc(Tm::Meta(v_meta_of(v)))),
                    3 => done.push(bump.alloc(Tm::U)),
                    // 字面量类型与字面量值（叶子，无 memo 收益）
                    6 => done.push(bump.alloc(Tm::LiteralType)),
                    7 => match v_xcell_of(v) {
                        XCell::Lit(s) => done.push(bump.alloc(Tm::LiteralIntro(s))),
                        XCell::Decl(s) => done.push(bump.alloc(Tm::Decl(s))),
                        XCell::Prim(s) => done.push(bump.alloc(Tm::Prim(s))),
                        XCell::Obj { val, name } => {
                            tasks.push(QJob::Obj1(name));
                            tasks.push(QJob::Q(*val, level));
                        }
                        XCell::Sum {
                            name,
                            params,
                            cases,
                        } => {
                            tasks.push(QJob::SumAsm {
                                name,
                                params,
                                cases,
                            });
                            for p in params.iter().rev() {
                                tasks.push(QJob::Q(p.ty, level));
                                tasks.push(QJob::Q(p.val, level));
                            }
                        }
                        XCell::SumCase {
                            typ,
                            case_name,
                            datas,
                        } => {
                            tasks.push(QJob::SumCaseAsm { case_name, datas });
                            for d in datas.iter().rev() {
                                tasks.push(QJob::Q(d.val, level));
                            }
                            tasks.push(QJob::Q(*typ, level));
                        }
                        XCell::Match {
                            scrutinee,
                            env: menv,
                            cases,
                            pending,
                        } => {
                            // 分支体在"捕获 env + fresh rigid 槽"下重新求值
                            // 再 quote：quote → eval 往返恒等（参考版
                            // quote 的 Match 臂）。求值与 quote 都用简化
                            // decl 表：全局值换成中性 Decl 引用，防止分支
                            // 体里的递归调用被重展开——eval 产生的中性
                            // Decl(f, spine) 若用真实表 quote，入口 force
                            // 会再展开一层，递归函数的卡住 match 直接发散。
                            let declb = simpl_decl(bump, decls);
                            let mut qc: Vec<(PatternDetail, &'a Tm<'a>)> =
                                Vec::with_capacity(cases.len());
                            for (p, b) in cases.iter() {
                                let count = p.bind_count();
                                let mut env2 = *menv;
                                for i in 0..count {
                                    env2 = env_ext(bump, env2, v_lvl(level + i));
                                }
                                let tv = eval_iter(
                                    bump, spine, work, vals, icits, defs, metas, &declb, mmap,
                                    fuel, pm_defs, env2, b,
                                );
                                let q = quote_iter(
                                    bump,
                                    spine,
                                    &mut Vec::new(),
                                    &mut Vec::new(),
                                    work,
                                    vals,
                                    icits,
                                    defs,
                                    metas,
                                    &declb,
                                    mmap,
                                    fuel,
                                    pm_defs,
                                    level + count,
                                    tv,
                                    None,
                                );
                                qc.push(((*p).clone(), q));
                            }
                            let cs: &'a [(PatternDetail, &'a Tm<'a>)] =
                                bump.alloc_slice_fill_iter(qc);
                            // scrutinee 与 pending 用真实表（调用方的 l 下正确）
                            let sq = quote_iter(
                                bump,
                                spine,
                                &mut Vec::new(),
                                &mut Vec::new(),
                                work,
                                vals,
                                icits,
                                defs,
                                metas,
                                decls,
                                mmap,
                                fuel,
                                pm_defs,
                                level,
                                *scrutinee,
                                None,
                            );
                            let mut acc: &'a Tm<'a> = bump.alloc(Tm::Match(sq, cs));
                            for &(u, i) in *pending {
                                let uq = quote_iter(
                                    bump,
                                    spine,
                                    &mut Vec::new(),
                                    &mut Vec::new(),
                                    work,
                                    vals,
                                    icits,
                                    defs,
                                    metas,
                                    decls,
                                    mmap,
                                    fuel,
                                    pm_defs,
                                    level,
                                    u,
                                    None,
                                );
                                acc = bump.alloc(Tm::App(acc, uq, i));
                            }
                            done.push(acc);
                        }
                    },
                    4 => {
                        if let Some(t) = memo.as_deref_mut().and_then(|m| m.get(&(v.0, level))) {
                            done.push(*t);
                            continue;
                        }
                        let cell = v_pi_of(v);
                        if memo.is_some() {
                            tasks.push(QJob::MemoStore(v.0, level));
                        }
                        let env = env_ext(bump, cell.env, v_lvl(level));
                        tasks.push(QJob::Pi1(cell));
                        tasks.push(QJob::EvalQ(cell.body, env, level + 1));
                        tasks.push(QJob::Q(cell.dom, level));
                    }
                    _ => {
                        // spine 链（Rigid / Flex / Decl / Prim / Obj 头）
                        if let Some(t) = memo.as_deref_mut().and_then(|m| m.get(&(v.0, level))) {
                            done.push(*t);
                            continue;
                        }
                        if memo.is_some() {
                            tasks.push(QJob::MemoStore(v.0, level));
                        }
                        // 先拷出标量再继续（后续任务会 push spine，Vec 可能扩容）
                        let h = v_spine_of(v);
                        let (ea, len, base, top_icit) = {
                            let e = &spine.stack[h];
                            (e.a, e.len, e.base, e.icit)
                        };
                        if len > 1 && base as usize + len as usize - 1 == h {
                            // 连续右链：先引 base，再 ChainRun 自底向上扫
                            let f0 = spine.stack[base as usize].f;
                            let idx_node = match v_tag(f0) {
                                0 => Some(
                                    &*bump.alloc(Tm::Var(level - v_lvl_of(f0) - 1)) as &Tm<'a>,
                                ),
                                // flex 链头：未解 meta 立即数（已解的在
                                // force 里早已展开），共享单一 ?m 节点
                                5 => Some(&*bump.alloc(Tm::Meta(v_meta_of(f0))) as &Tm<'a>),
                                // Decl / Prim 链头：共享单一名字节点
                                7 => match v_xcell_of(f0) {
                                    XCell::Decl(s) => {
                                        Some(&*bump.alloc(Tm::Decl(s)) as &Tm<'a>)
                                    }
                                    XCell::Prim(s) => {
                                        Some(&*bump.alloc(Tm::Prim(s)) as &Tm<'a>)
                                    }
                                    // Obj 头的链（内层值要按 level 引读）与
                                    // Lit 头（不可达）挂起走 Q
                                    _ => None,
                                },
                                _ => None,
                            };
                            let base_v = spine.stack[base as usize].a;
                            tasks.push(QJob::ChainRun {
                                level,
                                next: base as usize,
                                end: h,
                                f0,
                                idx_node,
                                prev: None,
                            });
                            tasks.push(QJob::Q(base_v, level));
                        } else {
                            tasks.push(QJob::App1(top_icit));
                            tasks.push(QJob::Q(ea, level));
                            tasks.push(QJob::Q(spine.stack[h].f, level));
                        }
                    }
                }
            }
            QJob::Lam1(name, icit) => {
                let body = done.pop().expect("quote 栈：Lam 缺体");
                done.push(bump.alloc(Tm::Lam(name, icit, body)));
            }
            QJob::Pi1(cell) => {
                let cod = done.pop().expect("quote 栈：Pi 缺余定义域");
                let dom = done.pop().expect("quote 栈：Pi 缺定义域");
                done.push(bump.alloc(Tm::Pi(cell.name, cell.icit, dom, cod)));
            }
            QJob::EvalQ(body, env, level) => {
                let v = eval_iter(
                    bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, pm_defs,
                    env, body,
                );
                tasks.push(QJob::Q(v, level));
            }
            QJob::App1(icit) => {
                let a = done.pop().expect("quote 栈：App 缺实参");
                let f = done.pop().expect("quote 栈：App 缺函数");
                done.push(bump.alloc(Tm::App(f, a, icit)));
            }
            QJob::MemoStore(key, level) => {
                let m = memo
                    .as_deref_mut()
                    .expect("quote 栈：MemoStore 缺 memo 表");
                let t = done.pop().expect("quote 栈：MemoStore 缺结果");
                m.insert((key, level), t);
                done.push(t);
            }
            QJob::Obj1(name) => {
                let inner = done.pop().expect("quote 栈：Obj 缺接收者");
                done.push(bump.alloc(Tm::Obj(inner, name)));
            }
            QJob::SumAsm {
                name,
                params,
                cases,
            } => {
                let n = params.len();
                let mut items: Vec<&'a Tm<'a>> = Vec::with_capacity(2 * n);
                for _ in 0..2 * n {
                    items.push(done.pop().expect("quote 栈：Sum 缺参数"));
                }
                items.reverse(); // [v0, t0, v1, t1, ...]
                let mut ps: Vec<SumParamT<'_>> = Vec::with_capacity(n);
                for (k, p) in params.iter().enumerate() {
                    ps.push(SumParamT {
                        name: p.name,
                        val: items[2 * k],
                        ty: items[2 * k + 1],
                        icit: p.icit,
                    });
                }
                done.push(bump.alloc(Tm::Sum(name, bump.alloc_slice_fill_iter(ps), cases)));
            }
            QJob::SumCaseAsm { case_name, datas } => {
                let nd = datas.len();
                let mut items: Vec<&'a Tm<'a>> = Vec::with_capacity(nd);
                for _ in 0..nd {
                    items.push(done.pop().expect("quote 栈：SumCase 缺字段"));
                }
                items.reverse(); // [d0, d1, ...]
                let typ = done.pop().expect("quote 栈：SumCase 缺 typ");
                let mut ds: Vec<SumDataT<'_>> = Vec::with_capacity(nd);
                for (k, d) in datas.iter().enumerate() {
                    ds.push(SumDataT {
                        name: d.name,
                        val: items[k],
                        icit: d.icit,
                    });
                }
                done.push(bump.alloc(Tm::SumCase {
                    typ,
                    case_name,
                    datas: bump.alloc_slice_fill_iter(ds),
                }));
            }
            QJob::ChainRun {
                level,
                next,
                end,
                f0,
                idx_node,
                prev,
            } => {
                let mut prev = match prev {
                    Some(p) => {
                        // 恢复点：非平凡 f 刚引完在 done 栈顶，合掉一层
                        // （悬挂槽位 = next-1，其 icit 即本层应用的 icit）
                        let f_node = done.pop().expect("quote 栈：链缺函数头");
                        let icit = spine.stack[next - 1].icit;
                        bump.alloc(Tm::App(f_node, p, icit))
                    }
                    None => done.pop().expect("quote 栈：链缺 base"),
                };
                let mut i = next;
                loop {
                    if i > end {
                        done.push(prev);
                        break;
                    }
                    let fi = spine.stack[i].f;
                    match idx_node {
                        Some(n) if fi.0 == f0.0 => {
                            prev = bump.alloc(Tm::App(n, prev, spine.stack[i].icit));
                            i += 1;
                        }
                        _ => {
                            // 非平凡链头：挂起引 f，ChainRun 续跑
                            tasks.push(QJob::ChainRun {
                                level,
                                next: i + 1,
                                end,
                                f0,
                                idx_node,
                                prev: Some(prev),
                            });
                            tasks.push(QJob::Q(fi, level));
                            break;
                        }
                    }
                }
            }
        }
    }
    done.pop().expect("quote 必须恰有一个根")
}

// unify（工作表迭代 + force 前置 + 模式求解 + intersect/flex-flex + L07 臂）
// --------------------------------------------------------------------------------

/// A/B 实验开关（unify 工作表的判等记忆化消融）：置 `L06_NO_CONV_MEMO=1`
/// 关闭（`=0` 不关闭）。
static NO_CONV_MEMO: std::sync::LazyLock<std::sync::atomic::AtomicBool> =
    std::sync::LazyLock::new(|| {
        std::sync::atomic::AtomicBool::new(std::env::var("L06_NO_CONV_MEMO").is_ok_and(|v| v != "0"))
    });

/// pm 特化方程求解（参考版 `Infer::pm_solve`）：环守卫——v 不得（结构上）
/// 提及 x（闭包内部不探查，那里的环由 force 的 fuel 兜底）。
fn pm_solve_into(pm_defs: &mut Vec<(u32, V)>, spine: &Spine, defs: &[V], x: u32, v: V) -> bool {
    if val_mentions_lvl(spine, defs, v, x) {
        return false;
    }
    pm_defs.push((x, v));
    true
}

#[inline]
fn pm_solvable_contains(pm_solvable: &[u32], x: u32) -> bool {
    pm_solvable.contains(&x)
}

/// unify 工作表条目：待比较子对、Π 余定义域的惰性比较屏障、判等记忆化
/// 屏障、或卡住 match 分支对的惰性求值屏障（简化 decl 表下重求值后压
/// `l+count` 层的体对）。
enum UItem<'a> {
    /// 待比较子对（level 相同的一对值；弹出时先 force 双方再分派）。
    Pair(u32, V, V),
    /// Π 余定义域的惰性比较（排在 dom 对之下——dom 不等即失败，cod 的
    /// eval 整个省掉）。
    EvalCod2(&'a Tm<'a>, Env<'a>, &'a Tm<'a>, Env<'a>, u32),
    /// 判等记忆化屏障（LIFO；健壮性论证同 L03——solve 写一次、成功单调）。
    Store((u64, u64)),
    /// 卡住 match 的一个分支对：两侧体在"各自捕获 env + fresh rigid 槽"
    /// 下用简化 decl 表重求值，再压 `l + count` 层的体对。
    MatchBranch {
        b1: &'a Tm<'a>,
        e1: Env<'a>,
        b2: &'a Tm<'a>,
        e2: Env<'a>,
        declb: Rc<FxHashMap<String, DeclEntryF>>,
        l: u32,
        count: u32,
    },
    /// Match/Match 的结构展开屏障（弹出时执行）：scrutinee 对比完后到达
    /// ——cases 长度检查、简化 decl 表重建、分支对与 pending 对的展开
    /// （参考版 scrutinee unify 之后的余下步骤；此前实现把检查前置，
    /// 失败路径的 meta 求解副作用时序与参考版分叉，错误消息正文可能
    /// 不同——Err parity 升级为正文比对后按参考版时序归位）。
    MatchStruct {
        e1: Env<'a>,
        e2: Env<'a>,
        c1: &'a [(PatternDetail, &'a Tm<'a>)],
        c2: &'a [(PatternDetail, &'a Tm<'a>)],
        pd1: &'a [(V, Icit)],
        pd2: &'a [(V, Icit)],
        l: u32,
    },
    /// 分支 pattern 相等检查（参考版逐分支在分支体之前）。
    MatchPattern(&'a PatternDetail, &'a PatternDetail),
    /// pending 长度检查（参考版在分支体全部比完之后）。
    MatchPendingLen(usize, usize),
    /// pending 对的 icit 检查（参考版逐对在分支体之后）。
    MatchIcit(Icit, Icit),
}

/// `?m args ≡ ?m args'`（同头 flex）：上游 `intersect`。逐槽（内→外）
/// 都取到裸变量则产出掩码（槽位相等 → 其 icit、不等 → None）；有 None 即
/// 剪枝（`pruneMeta`），全相等即成立。长度不等直接失败（参考版
/// intersect_go 的 `_ => None` → unify_sp 长度失配分支：失配即败、零比较）。
/// 任一对含非变量 → 回落 `unify_sp` 逐实参比较。
#[allow(clippy::too_many_arguments)]
fn intersect_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    fuel: &Fuel,
    pm_defs: &[(u32, V)],
    stack: &mut Vec<UItem<'a>>,
    l: u32,
    m: u32,
    args1: &[(V, Icit)], // 内先（collect_args 的产出序）
    args2: &[(V, Icit)],
) -> bool {
    let n1 = args1.len();
    let n2 = args2.len();
    if n1 != n2 {
        return false; // 长度失配：直败零比较（连 force/压栈都省）
    }
    let common = n1;
    let mut pr: Vec<Option<Icit>> = Vec::with_capacity(common);
    let mut fallback = false;
    for k in 0..common {
        let f1 = force(
            bump, spine, defs, metas, decls, mmap, fuel, pm_defs, args1[k].0,
        );
        let f2 = force(
            bump, spine, defs, metas, decls, mmap, fuel, pm_defs, args2[k].0,
        );
        if v_tag(f1) == 0 && v_tag(f2) == 0 {
            pr.push(if v_lvl_of(f1) == v_lvl_of(f2) {
                Some(args1[k].1)
            } else {
                None
            });
        } else {
            fallback = true; // 上游 go 的 None：回落 unify_sp
            break;
        }
    }
    if !fallback {
        if pr.iter().any(|x| x.is_none()) {
            return prune_meta_bump(
                bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, pm_defs, &pr, m,
            )
            .is_some();
        }
        return true; // 两 spine 逐槽相等
    }
    // unify_sp 回落：前缀对压栈（内先压 → 弹出外先，对齐 unify_sp 的递归序）。
    // tag 7 不跳过：参考版对字面量实参照走 unify（恒败）、对 Decl/Prim 实参
    // 照走同名逐参——位相等的同单元也须分派（见 unify 的 tag 7 守卫）。
    for k in 0..common {
        let (a1, _) = args1[k];
        let (a2, _) = args2[k];
        if a1.0 != a2.0 || v_tag(a1) == 7 {
            stack.push(UItem::Pair(l, a1, a2));
        }
    }
    true
}

/// 异头 flex-flex（上游 `flexFlex`）：**短 spine 一侧优先**反演求解；反演
/// 失败则用另一侧求解（rhs 是整条 flex 值）。第一次尝试可能已 solve 部分
/// meta 才失败，反向尝试前回滚（参考版 meta 快照同款）。
#[allow(clippy::too_many_arguments)]
fn flex_flex_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    fuel: &Fuel,
    pm_defs: &[(u32, V)],
    ren: &mut RenBuf,
    gamma: u32,
    m1: u32,
    args1: &[(V, Icit)],
    v1: V,
    m2: u32,
    args2: &[(V, Icit)],
    v2: V,
) -> bool {
    // 方向选择与参考版一致：`sp.len() <= sp_prime.len()` → (m, sp) 先
    let (fa, aa, va, fb, ab, vb) = if args1.len() <= args2.len() {
        (m1, args1, v1, m2, args2, v2)
    } else {
        (m2, args2, v2, m1, args1, v1)
    };
    let snap = metas.clone();
    match invert_bump(bump, spine, defs, metas, decls, mmap, fuel, pm_defs, ren, gamma, aa) {
        Some(mask) => {
            if solve_with_pren_bump(
                bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, pm_defs, ren,
                gamma, fa, aa.len() as u32, mask, va,
            ) {
                return true;
            }
        }
        None => {
            // 一侧非模式：落另一侧（solve = invert + solve_with_pren）
            match invert_bump(
                bump, spine, defs, metas, decls, mmap, fuel, pm_defs, ren, gamma, ab,
            ) {
                Some(mask) => {
                    if solve_with_pren_bump(
                        bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, pm_defs,
                        ren, gamma, fb, ab.len() as u32, mask, vb,
                    ) {
                        return true;
                    }
                }
                None => return false,
            }
        }
    }
    // 首选方向失败：回滚 meta 快照，反向再试一次
    *metas = snap;
    match invert_bump(bump, spine, defs, metas, decls, mmap, fuel, pm_defs, ren, gamma, ab) {
        Some(mask) => solve_with_pren_bump(
            bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, pm_defs, ren, gamma,
            fb, ab.len() as u32, mask, vb,
        ),
        None => false,
    }
}

/// 同头链（unify_sp）的实参 lockstep 比较：长度失配即败；实参 icit 不比
/// （类型已定，上游同款）。位相等的实参对免比（tag 7 与 Obj 头链除外——
/// 字面量恒败、Decl/Prim 走同名分派、Obj 走 `(Obj, Obj)` 专臂）。
#[allow(clippy::too_many_arguments)]
fn unify_sp_lockstep<'a>(
    spine: &Spine,
    stack: &mut Vec<UItem<'a>>,
    l: u32,
    h1: usize,
    h2: usize,
) -> bool {
    if spine.spine_len(h1) != spine.spine_len(h2) {
        return false;
    }
    let mut i1 = h1;
    let mut i2 = h2;
    loop {
        let (f1, a1) = {
            let e = &spine.stack[i1];
            (e.f, e.a)
        };
        let (f2, a2) = {
            let e = &spine.stack[i2];
            (e.f, e.a)
        };
        // 位相等后缀：实参对免比（tag 7 除外）；函数部分对仍须入栈。
        // Obj 头的链（tag 2 + hk=Obj）同样不免——接收者锁在头单元里，
        // lockstep 看不见，须交回 (Obj, Obj) 专臂。
        let skip1 = a1.0 == a2.0 && v_tag(a1) != 7 && !(v_tag(a1) == 2 && spine.stack[v_spine_of(a1)].hk == HK_OBJ);
        if skip1 {
            if f1.0 != f2.0 {
                stack.push(UItem::Pair(l, f1, f2));
            }
            break;
        }
        if v_tag(a1) == 2 && v_tag(a2) == 2 {
            // 下钻门控：两侧的实参链顶层 f 与本层 f 同字（纯 ChainWrap 同头
            // 延续）；实参若是另一条中性链（Apply 惯例：`f` = partial 句柄
            // ≠ 头字）则停下，把子对交回完整分派。派发序与参考版 unify_sp
            // 同序：停钻时先压实参对、后压函数部分对。
            let cont = spine.stack[v_spine_of(a1)].f.0 == f1.0
                && spine.stack[v_spine_of(a2)].f.0 == f2.0;
            if cont {
                if f1.0 != f2.0 {
                    stack.push(UItem::Pair(l, f1, f2));
                }
                i1 = v_spine_of(a1);
                i2 = v_spine_of(a2);
                continue;
            }
        }
        stack.push(UItem::Pair(l, a1, a2));
        if f1.0 != f2.0 {
            stack.push(UItem::Pair(l, f1, f2));
        }
        break;
    }
    true
}

/// unification：结构比较 + 模式求解（含 intersect / flex-flex / 剪枝），
/// 工作表迭代。臂序与参考版 `Infer::unify` 逐项对应（顺序敏感处：pm 特化
/// 臂在 Flex/λ/η 臂之前；λ/η 在 Flex 求解之前；Flex 求解在
/// LiteralType/Prim/Sum/SumCase/Match 臂之前）：
/// U → Π（icit 相等）→ pm 特化（双侧）→ Decl/Decl 同名 → λ/η → 中性链
/// （双 flex = intersect/flex_flex、同头 lockstep、异头单 flex = solve）→
/// flex 求解 → LiteralType/宽松臂 → Prim/Prim → Sum/Sum → SumCase/SumCase
/// → Match/Match → Match 严格 η → 失配。
/// **位相等捷径与实参跳过对 tag 7 与 Obj 头链关闭**：`(Lit, Lit)` 参考版
/// 无自反臂——同字面量也 Err；`(Obj, Obj)` 走专门合同臂——同单元也须比
/// 接收者 + 实参，不做字面自反放行。
#[allow(clippy::too_many_arguments)]
fn unify_iter<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    stack: &mut Vec<UItem<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    ren: &mut RenBuf,
    conv: &mut ConvScratch,
    fuel: &Fuel,
    pm_defs: &mut Vec<(u32, V)>,
    pm_solvable: &[u32],
    l0: u32,
    t0: V,
    u0: V,
) -> bool {
    let memo_on = !NO_CONV_MEMO.load(std::sync::atomic::Ordering::Relaxed);
    // 草稿复用（Machine 常驻）：清空保容量，热路径零分配
    conv.memo.clear();
    conv.scratch1.clear();
    conv.scratch2.clear();
    let memo = &mut conv.memo;
    // UItem 工作栈由调用方常驻复用（入口已 clear）；失败早退会留下非空
    // 栈，靠下次入口 clear 兜住（Rc 随 clear 正确减计，引用无 Drop）
    debug_assert!(stack.is_empty());
    stack.push(UItem::Pair(l0, t0, u0));
    while let Some(item) = stack.pop() {
        let (l, t, u) = match item {
            UItem::Store(key) => {
                memo.insert(key);
                continue;
            }
            UItem::EvalCod2(b1, e1, b2, e2, l) => {
                let vt = {
                    let env = env_ext(bump, e1, v_lvl(l));
                    eval_iter(
                        bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, pm_defs,
                        env, b1,
                    )
                };
                let vu = {
                    let env = env_ext(bump, e2, v_lvl(l));
                    eval_iter(
                        bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, pm_defs,
                        env, b2,
                    )
                };
                stack.push(UItem::Pair(l + 1, vt, vu));
                continue;
            }
            UItem::MatchBranch {
                b1,
                e1,
                b2,
                e2,
                declb,
                l,
                count,
            } => {
                // 分支体：两侧各自"捕获 env + fresh rigid 槽（count = 
                // bind_count，lvl 从 l 起）"下用简化 decl 表重求值，再在
                // l+count 层比较（参考版 unify 的 Match/Match 全路径同款）
                let mut env1 = e1;
                let mut env2 = e2;
                for i in 0..count {
                    env1 = env_ext(bump, env1, v_lvl(l + i));
                    env2 = env_ext(bump, env2, v_lvl(l + i));
                }
                let v1 = eval_iter(
                    bump, spine, work, vals, icits, defs, metas, &declb, mmap, fuel, pm_defs,
                    env1, b1,
                );
                let v2 = eval_iter(
                    bump, spine, work, vals, icits, defs, metas, &declb, mmap, fuel, pm_defs,
                    env2, b2,
                );
                stack.push(UItem::Pair(l + count, v1, v2));
                continue;
            }
            UItem::MatchStruct {
                e1,
                e2,
                c1,
                c2,
                pd1,
                pd2,
                l,
            } => {
                // scrutinee 已比完（参考版 :766 之后）：cases 长度检查 →
                // 简化 decl 表 → 展开分支与 pending（检查本身不烧 fuel，
                // 与参考版一致——fuel 只随子 unify 调用/Pair 消耗）
                if c1.len() != c2.len() {
                    return false;
                }
                let declb = Rc::new(simpl_decl(bump, decls));
                // 展开序 = 参考版执行序：逐分支 pattern 检查 → 分支体 →
                // pending 长度检查 → 逐 pending icit 检查 → 对。LIFO 按执行
                // 序的逆序压：pending（对 → icit，反序）→ pending 长度 →
                // 分支（体 → pattern，反序）
                for ((u1, _), (u2, _)) in pd1.iter().zip(pd2.iter()).rev() {
                    stack.push(UItem::Pair(l, *u1, *u2));
                }
                for i in (0..pd1.len()).rev() {
                    stack.push(UItem::MatchIcit(pd1[i].1, pd2[i].1));
                }
                stack.push(UItem::MatchPendingLen(pd1.len(), pd2.len()));
                for (i, ((p1, b1), (_, b2))) in
                    c1.iter().zip(c2.iter()).enumerate().rev()
                {
                    stack.push(UItem::MatchBranch {
                        b1: *b1,
                        e1,
                        b2: *b2,
                        e2,
                        declb: declb.clone(),
                        l,
                        count: p1.bind_count(),
                    });
                    stack.push(UItem::MatchPattern(p1, &c2[i].0));
                }
                continue;
            }
            UItem::MatchPattern(p1, p2) => {
                if p1 != p2 {
                    return false;
                }
                continue;
            }
            UItem::MatchPendingLen(n1, n2) => {
                if n1 != n2 {
                    return false;
                }
                continue;
            }
            UItem::MatchIcit(i1, i2) => {
                if i1 != i2 {
                    return false;
                }
                continue;
            }
            UItem::Pair(l, t, u) => (l, t, u),
        };
        // 递归深度防护：每个子对一次（参考版 unify 每次调用消耗 1）
        let f = fuel.get();
        if f == 0 {
            return false;
        }
        fuel.set(f - 1);
        // 位相等：同一值。tag 7 与 Obj 头链例外（见函数注释——参考版对
        // 字面量无自反性、Obj 走专臂，Decl/Prim 需同名分派）
        if t.0 == u.0 && v_tag(t) != 7 && !is_objheaded(spine, t) {
            continue;
        }
        if memo_on && memo.contains(&(t.0, u.0)) {
            continue; // 本轮已判等过的子对（命中连 force 都省——成功单调）
        }
        let t = force(
            bump, spine, defs, metas, decls, mmap, fuel, pm_defs, t,
        );
        let u = force(
            bump, spine, defs, metas, decls, mmap, fuel, pm_defs, u,
        );
        if t.0 == u.0 && v_tag(t) != 7 && !is_objheaded(spine, t) {
            continue; // force 展开后同值（同一解的两处引用）
        }

        // —— 宇宙（参考臂 1）——
        if v_tag(t) == 3 && v_tag(u) == 3 {
            continue;
        }
        // —— Π：icit 相等才比（参考臂 2）；icit 失配落到后续臂 ——
        if v_tag(t) == 4 && v_tag(u) == 4 {
            let p = v_pi_of(t);
            let q = v_pi_of(u);
            if p.icit == q.icit {
                if memo_on {
                    stack.push(UItem::Store((t.0, u.0)));
                }
                // 先比定义域，再惰性 eval 两侧余定义域
                stack.push(UItem::EvalCod2(p.body, p.env, q.body, q.env, l));
                stack.push(UItem::Pair(l, p.dom, q.dom));
                continue;
            }
        }
        // —— pm 特化臂（参考臂 4/5，**在 Flex/λ/η 之前**——顺序敏感）：
        // 可解 rigid（当前子句的 bind 槽）与非 Flex 值相遇 → 记入 pm_defs
        // 事实表（惰性精化，层级与槽位一概不动）。调用侧"头部一侧在前"，
        // 双侧都可解时解的方向是"头部变量 := 构造子侧值"。
        if v_tag(t) == 0 && pm_solvable_contains(pm_solvable, v_lvl_of(t)) && !is_flex(spine, u) {
            if pm_solve_into(pm_defs, spine, defs, v_lvl_of(t), u) {
                continue;
            }
            return false;
        }
        if v_tag(u) == 0 && pm_solvable_contains(pm_solvable, v_lvl_of(u)) && !is_flex(spine, t) {
            if pm_solve_into(pm_defs, spine, defs, v_lvl_of(u), t) {
                continue;
            }
            return false;
        }
        // —— Decl/Decl 同名（参考臂 6）：同名比 spine（裸单元自反成立），
        // 异名落到后续臂（λ/η 等仍可命中）——
        if head_kind(spine, t) == HK_DECL && head_kind(spine, u) == HK_DECL {
            if xcell_head_name(spine, t) == xcell_head_name(spine, u) {
                if memo_on {
                    stack.push(UItem::Store((t.0, u.0)));
                }
                match (v_tag(t), v_tag(u)) {
                    (7, 7) => continue, // 双裸单元：unify_sp([][]) 自反成立
                    (2, 2) => {
                        if !unify_sp_lockstep(spine, stack, l, v_spine_of(t), v_spine_of(u)) {
                            return false;
                        }
                        continue;
                    }
                    _ => return false, // 裸×带实参：长度失配（参考版 unify_sp 同败）
                }
            }
        }
        // —— λ / η（参考臂 9/10/11；在 Flex 求解之前：Flex vs λ 走 η）——
        if v_tag(t) == 1 && v_tag(u) == 1 {
            let c1 = v_clo_of(t);
            let c2 = v_clo_of(u);
            let vt = {
                let env = env_ext(bump, c1.env, v_lvl(l));
                eval_iter(
                    bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, pm_defs,
                    env, c1.body,
                )
            };
            let vu = {
                let env = env_ext(bump, c2.env, v_lvl(l));
                eval_iter(
                    bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, pm_defs,
                    env, c2.body,
                )
            };
            if memo_on {
                stack.push(UItem::Store((t.0, u.0)));
            }
            stack.push(UItem::Pair(l + 1, vt, vu));
            continue;
        }
        // η：中性一侧按 λ 一侧的 icit 应用（Decl/Prim/Obj 头的应用压链；
        // 卡住 match 吸收进 pending）
        if v_tag(u) == 1 {
            let c = v_clo_of(u);
            let vu = {
                let env = env_ext(bump, c.env, v_lvl(l));
                eval_iter(
                    bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, pm_defs,
                    env, c.body,
                )
            };
            let vt = vapp1(
                bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, pm_defs, t,
                v_lvl(l), c.icit,
            );
            if memo_on {
                stack.push(UItem::Store((t.0, u.0)));
            }
            stack.push(UItem::Pair(l + 1, vt, vu));
            continue;
        }
        if v_tag(t) == 1 {
            let c = v_clo_of(t);
            let vt = {
                let env = env_ext(bump, c.env, v_lvl(l));
                eval_iter(
                    bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, pm_defs,
                    env, c.body,
                )
            };
            let vu = vapp1(
                bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, pm_defs, u,
                v_lvl(l), c.icit,
            );
            if memo_on {
                stack.push(UItem::Store((t.0, u.0)));
            }
            stack.push(UItem::Pair(l + 1, vt, vu));
            continue;
        }
        // —— (Obj, Obj) 合同（对位参考版新臂，评审修复）：字段名相同 ⇒
        // 比接收者，再比 spine 实参（裸×裸接收者对入栈即完；链×链加
        // lockstep；裸×链长度失配即败——与参考版 (Obj, Obj) 臂语义一致）。
        // 卡住投影的两种形态（裸 XCell 单元 / 带实参 spine 链）统一在此
        // 处理，接收者住在头单元里、lockstep 看不见，单独入栈。tag 预门控
        // （head_kind 只对 tag 7/2 可能给 HK_OBJ）把每 Pair 的固定税从
        // 两次 head_kind 降为位比较。——
        if (v_tag(t) == 7 || v_tag(t) == 2)
            && (v_tag(u) == 7 || v_tag(u) == 2)
            && head_kind(spine, t) == HK_OBJ
            && head_kind(spine, u) == HK_OBJ
        {
            let (hc1, hc2) = (
                if v_tag(t) == 7 { t } else { spine.spine_head(v_spine_of(t)) },
                if v_tag(u) == 7 { u } else { spine.spine_head(v_spine_of(u)) },
            );
            let (o1, n1, o2, n2) = match (v_xcell_of(hc1), v_xcell_of(hc2)) {
                (
                    XCell::Obj { val: a1, name: m1 },
                    XCell::Obj { val: a2, name: m2 },
                ) => (*a1, *m1, *a2, *m2),
                _ => return false, // 防御（head_kind 已保证 Obj 头）
            };
            if n1 != n2 {
                return false;
            }
            if memo_on {
                stack.push(UItem::Store((t.0, u.0)));
            }
            stack.push(UItem::Pair(l, o1, o2));
            match (v_tag(t), v_tag(u)) {
                (7, 7) => {}
                (2, 2) => {
                    if !unify_sp_lockstep(spine, stack, l, v_spine_of(t), v_spine_of(u)) {
                        return false;
                    }
                }
                _ => return false, // 裸×带实参：spine 长度失配
            }
            continue;
        }
        // —— 中性链 vs 中性链（参考臂 3/6/7/8/12/13 的链形态全在此分派）——
        if v_tag(t) == 2 && v_tag(u) == 2 {
            let h1 = v_spine_of(t);
            let h2 = v_spine_of(u);
            let hd1 = spine.spine_head(h1);
            let hd2 = spine.spine_head(h2);
            let f1 = v_tag(hd1) == 5;
            let f2 = v_tag(hd2) == 5;
            if f1 && f2 {
                // 双 flex：同头 intersect、异头 flex_flex（参考臂 7/8）
                let mut a1 = std::mem::take(&mut conv.scratch1);
                a1.clear();
                spine.collect_args(h1, &mut a1);
                let mut a2 = std::mem::take(&mut conv.scratch2);
                a2.clear();
                spine.collect_args(h2, &mut a2);
                let m1 = v_meta_of(hd1);
                let m2 = v_meta_of(hd2);
                let ok = if m1 == m2 {
                    intersect_bump(
                        bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, pm_defs,
                        stack, l, m1, &a1, &a2,
                    )
                } else {
                    flex_flex_bump(
                        bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, pm_defs,
                        ren, l, m1, &a1, u, m2, &a2, t,
                    )
                };
                conv.scratch1 = a1;
                conv.scratch2 = a2;
                if ok {
                    if memo_on {
                        memo.insert((t.0, u.0));
                    }
                    continue;
                }
                return false;
            }
            // 同头判定：位相等（同变量 / 同 meta / 同单元）或同名 Decl/Prim
            // 头（参考版比较 Span——名字全部来自 empty_span 构造，等价于名
            // 内容相等）。Obj 头走上文 (Obj, Obj) 专臂，不进同头
            // （排除为防御性保留）。
            let same_head = (hd1.0 == hd2.0
                && !(v_tag(hd1) == 7 && matches!(v_xcell_of(hd1), XCell::Obj { .. })))
                || (v_tag(hd1) == 7
                    && v_tag(hd2) == 7
                    && matches!(
                        (v_xcell_of(hd1), v_xcell_of(hd2)),
                        (XCell::Decl(n1), XCell::Decl(n2)) if n1 == n2
                    ))
                || (v_tag(hd1) == 7
                    && v_tag(hd2) == 7
                    && matches!(
                        (v_xcell_of(hd1), v_xcell_of(hd2)),
                        (XCell::Prim(n1), XCell::Prim(n2)) if n1 == n2
                    ));
            if same_head {
                // 同头刚性/Decl/Prim：逐实参比较（lockstep，长度失配即败）
                if memo_on {
                    stack.push(UItem::Store((t.0, u.0)));
                }
                if !unify_sp_lockstep(spine, stack, l, h1, h2) {
                    return false;
                }
                continue;
            }
            // 异头：一侧 flex 头（f1/f2 已排除双 flex）→ 该侧 solve（参考
            // 臂 12/13 的链形态）；双刚性/Decl/Prim 异头 → 失配。
            let (mv, h, rhs) = if f1 {
                (v_meta_of(hd1), h1, u)
            } else if f2 {
                (v_meta_of(hd2), h2, t)
            } else {
                return false;
            };
            let mut args = std::mem::take(&mut conv.scratch1);
            args.clear();
            spine.collect_args(h, &mut args);
            let solved = solve_bump(
                bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, pm_defs, ren, l,
                mv, &args, rhs,
            );
            conv.scratch1 = args;
            if solved {
                if memo_on {
                    memo.insert((t.0, u.0));
                }
                continue;
            }
            return false;
        }
        // —— 单侧（或双侧）裸 flex：solve（参考臂 7/8/12/13）。**在
        // LiteralType/Prim/Sum/SumCase/Match 臂之前**——flex vs 那些形态走
        // 求解而非失配 ——
        {
            let mut a1 = std::mem::take(&mut conv.scratch1);
            a1.clear();
            let ft = spine.flex_of(t, &mut a1);
            let mut a2 = std::mem::take(&mut conv.scratch2);
            a2.clear();
            let fu = spine.flex_of(u, &mut a2);
            match (ft, fu) {
                (Some(m1), Some(m2)) => {
                    let ok = if m1 == m2 {
                        intersect_bump(
                            bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel,
                            pm_defs, stack, l, m1, &a1, &a2,
                        )
                    } else {
                        flex_flex_bump(
                            bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel,
                            pm_defs, ren, l, m1, &a1, u, m2, &a2, t,
                        )
                    };
                    conv.scratch1 = a1;
                    conv.scratch2 = a2;
                    if ok {
                        if memo_on {
                            memo.insert((t.0, u.0));
                        }
                        continue;
                    }
                    return false;
                }
                (Some(m), None) => {
                    let ok = solve_bump(
                        bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, pm_defs,
                        ren, l, m, &a1, u,
                    );
                    conv.scratch1 = a1;
                    conv.scratch2 = a2;
                    if ok {
                        if memo_on {
                            memo.insert((t.0, u.0));
                        }
                        continue;
                    }
                    return false;
                }
                (None, Some(m)) => {
                    let ok = solve_bump(
                        bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, pm_defs,
                        ren, l, m, &a2, t,
                    );
                    conv.scratch1 = a1;
                    conv.scratch2 = a2;
                    if ok {
                        if memo_on {
                            memo.insert((t.0, u.0));
                        }
                        continue;
                    }
                    return false;
                }
                (None, None) => {
                    conv.scratch1 = a1;
                    conv.scratch2 = a2;
                    // 非 flex：落到字面量 / Prim / Sum / SumCase / Match 臂
                }
            }
        }
        // —— (LiteralType, LiteralType)（参考臂 14）——
        if v_tag(t) == 6 && v_tag(u) == 6 {
            continue;
        }
        // —— 宽松臂（参考臂 15）：String 与卡住内建 / 卡住 Decl 的宽松合一
        // 只对 decl 表**未登记名**放行——string_to_global_type 对未知名返回
        // 以其名字的卡住 Decl（动态类型的逃逸舱口）；已登记名按登记类型把关
        // （U 型返回的 builtin 卡住值不再冒充 String）——
        if v_tag(t) == 6 || v_tag(u) == 6 {
            let other = if v_tag(t) == 6 { u } else { t };
            let oname: Option<&str> = match v_tag(other) {
                7 => match v_xcell_of(other) {
                    XCell::Decl(n) => Some(n),
                    XCell::Prim(n) => Some(n),
                    // 字面量值与 String 类型:刚性失配(参考版同)
                    _ => None,
                },
                2 => {
                    let hd = spine.spine_head(v_spine_of(other));
                    match v_xcell_of(hd) {
                        XCell::Decl(n) => Some(n),
                        XCell::Prim(n) => Some(n),
                        _ => None,
                    }
                }
                _ => None,
            };
            match oname {
                Some(n) => match decls.get(n) {
                    None => continue, // 未登记名（可变全局等动态名）放行
                    Some(e) => {
                        stack.push(UItem::Pair(l, v_lit_ty(), e.ty));
                        continue;
                    }
                },
                None => return false, // (LitType, Lit) 等无宽松臂 → 失配
            }
        }
        // —— Prim/Prim（参考臂 16）：同名比实参 spine（异名失败）——不带
        // 实参的单元 Prim 会把 `x ++ y ≡ x ++ z` 判成相等 ——
        if head_kind(spine, t) == HK_PRIM && head_kind(spine, u) == HK_PRIM {
            if xcell_head_name(spine, t) != xcell_head_name(spine, u) {
                return false;
            }
            match (v_tag(t), v_tag(u)) {
                (7, 7) => continue, // 双裸单元：unify_sp([][]) 自反成立
                (2, 2) => {
                    if memo_on {
                        stack.push(UItem::Store((t.0, u.0)));
                    }
                    if !unify_sp_lockstep(spine, stack, l, v_spine_of(t), v_spine_of(u)) {
                        return false;
                    }
                    continue;
                }
                _ => return false, // 裸×带实参：长度失配
            }
        }
        // —— Sum/Sum（参考臂 17）：同名即逐参数（含索引）合一；zip 语义
        // （参数数不等取 min——参考版同款）；异名落到 Match 臂 / 失配 ——
        if v_tag(t) == 7 && v_tag(u) == 7 {
            let (xt, xu) = (v_xcell_of(t), v_xcell_of(u));
            if let (
                XCell::Sum { name: n1, params: p1, .. },
                XCell::Sum { name: n2, params: p2, .. },
            ) = (xt, xu)
            {
                if n1 == n2 {
                    for (a, b) in p1.iter().zip(p2.iter()).rev() {
                        stack.push(UItem::Pair(l, a.val, b.val));
                    }
                    continue;
                }
                return false; // 异名 Sum：参考版无后续可命中臂 → Err
            }
            // —— SumCase/SumCase（参考臂 18）：同构造子才比；**只比
            // datas**（typ 是 datas 的函数，比 typ 会在索引槽互相引用上深
            // 递归——索引等式在外层 Sum-Sum 的参数 zip 里建立）——
            if let (
                XCell::SumCase { case_name: c1, datas: d1, .. },
                XCell::SumCase { case_name: c2, datas: d2, .. },
            ) = (xt, xu)
            {
                if c1 == c2 {
                    for (a, b) in d1.iter().zip(d2.iter()).rev() {
                        stack.push(UItem::Pair(l, a.val, b.val));
                    }
                    continue;
                }
                return false; // 异 case：参考版无后续可命中臂 → Err
            }
            // —— Match/Match（参考臂 19）：先 struct_eq 快路径（不 force
            // 不展开的结构比较 + budget 封顶，超限按不等），再 scrutinee
            // 合一 + 逐分支（模式必须相同；各分支体在 fresh rigid 槽 env 下
            // 用**简化 decl 表** eval 再 unify，l+count 层）+ pending 逐对 ——
            if let (
                XCell::Match { scrutinee: s1, env: e1, cases: c1, pending: pd1 },
                XCell::Match { scrutinee: s2, env: e2, cases: c2, pending: pd2 },
            ) = (xt, xu)
            {
                // 快路径：scrutinee、捕获 env、模式与分支体、pending 全部
                // 结构相同 ⇒ 两个 match 值在所有实例化下行为一致，直接判
                // 等。逐分支重求值会把递归函数的分支体再展开一层卡住
                // match（fresh rigid 层级随深度递增，永不收敛）——同一
                // decl 值在合一两侧各展开一份时正是这种自比较，必须短路
                // （参考版 struct_eq 同款 + 同一 budget 口径）。
                if struct_val_eq(spine, defs, *s1, *s2)
                    && struct_env_eq(spine, defs, *e1, *e2)
                    && c1.len() == c2.len()
                    && c1
                        .iter()
                        .zip(c2.iter())
                        .all(|((p1, b1), (p2, b2))| p1 == p2 && struct_tm_eq(*b1, *b2))
                    && pd1.len() == pd2.len()
                    && pd1
                        .iter()
                        .zip(pd2.iter())
                        .all(|((a, i), (b, j))| i == j && struct_val_eq(spine, defs, *a, *b))
                {
                    continue;
                }
                // 比较顺序与参考版逐项对齐（含失败路径的副作用时序）：
                // scrutinee 最先比；cases/pending 的长度与 pattern 检查在
                // scrutinee 之后由 MatchStruct 屏障执行（简化 decl 表的
                // 重建同样推迟到检查通过）。——
                stack.push(UItem::MatchStruct {
                    e1: *e1,
                    e2: *e2,
                    c1,
                    c2,
                    pd1,
                    pd2,
                    l,
                });
                stack.push(UItem::Pair(l, *s1, *s2));
                continue;
            }
        }
        // —— 卡住的 match vs 其它（参考臂 20）：能归约的已在入口 force 消掉
        // （force 会在 scrutinee 上重试选分支），这里只接受严格 η——每个
        // 分支都是通配且分支体就是 scrutinee 本身。无条件接受会把 `f x` 证
        // 成 `x` ——
        let (ms, mcases, mpending, other) = match (v_tag(t), v_tag(u)) {
            (7, _) => match v_xcell_of(t) {
                XCell::Match {
                    scrutinee,
                    cases,
                    pending,
                    ..
                } => (*scrutinee, *cases, *pending, u),
                _ => return false, // 其余 (7,·) 形态失配（参考 `_` 臂）
            },
            (_, 7) => match v_xcell_of(u) {
                XCell::Match {
                    scrutinee,
                    cases,
                    pending,
                    ..
                } => (*scrutinee, *cases, *pending, t),
                _ => return false,
            },
            _ => return false,
        };
        // 带 pending 实参的卡住 match 不是 η 形态（分支体经实参应用后
        // 不再等于 scrutinee）
        if !mpending.is_empty() {
            return false;
        }
        let sf = force(
            bump, spine, defs, metas, decls, mmap, fuel, pm_defs, ms,
        );
        if v_tag(sf) == 0 && v_tag(other) == 0 && v_lvl_of(sf) == v_lvl_of(other) {
            let is_eta = !mcases.is_empty()
                && mcases.iter().all(|(pat, body)| {
                    matches!(pat, PatternDetail::Any(_) | PatternDetail::Bind(_))
                        && matches!(body, Tm::Var(0))
                });
            if is_eta {
                continue;
            }
        }
        return false;
    }
    true
}

// solve（invert + prune 验证 + rename + lams，全迭代）
// --------------------------------------------------------------------------------

/// solve 的偏置换缓冲（generational）：`val[x]` 在第 `epoch` 代里给出
/// level x → 新下标；`stamp[x] == epoch` 表示条目有效。`reset` 只推进
/// epoch（O(1) 换代）。`NONE_MARK` 哨兵标记**非线性（重复）变量**——
/// `get` 视其为缺项。
#[derive(Default)]
struct RenBuf {
    val: Vec<u32>,
    /// 各 level 槽位的生效代数（与 `val` 平行）；`== epoch` 才有效。
    stamp: Vec<u64>,
    epoch: u64,
}

/// 非线性（重复）变量的哨兵值。
const NONE_MARK: u32 = u32::MAX;

impl RenBuf {
    /// 换代即「清空」：旧条目的 gen 不等于新 epoch，全部失效。
    #[inline]
    fn reset(&mut self) {
        self.epoch += 1;
    }
    /// `NONE_MARK` 视同缺项（非线性变量不在 renaming 里）。
    #[inline]
    fn get(&self, x: usize) -> Option<u32> {
        match self.stamp.get(x).copied() {
            Some(g) if g == self.epoch => {
                let v = self.val[x];
                if v == NONE_MARK {
                    None
                } else {
                    Some(v)
                }
            }
            _ => None,
        }
    }
    /// 本代里 `x` 是否已标非线性哨兵。
    #[inline]
    fn has_mark(&self, x: usize) -> bool {
        self.stamp.get(x).copied() == Some(self.epoch) && self.val[x] == NONE_MARK
    }
    #[inline]
    fn set(&mut self, x: usize, v: u32) {
        if x >= self.val.len() {
            self.val.resize(x + 1, 0);
            self.stamp.resize(x + 1, 0); // 0 != epoch（epoch 从 1 起）
        }
        self.val[x] = v;
        self.stamp[x] = self.epoch;
    }
    /// 整表逐代克隆（卡住 match 分支体的嵌套 renaming 用——参考版按分支
    /// clone 整个 HashMap 的对应物；克隆保持同代，lift 只写进克隆）。
    fn clone_valid(&self) -> RenBuf {
        RenBuf {
            val: self.val.clone(),
            stamp: self.stamp.clone(),
            epoch: self.epoch,
        }
    }
}

/// 上游 `invert`：实参（应用序）逐个 force_arg 成**裸刚性变量**。非线性
/// （重复变量）移出 renaming、记 `NONE_MARK`，产出把重复变量的全部出现
/// 记为 `None` 的掩码（**与 args 逆序 = 应用序**：最外层实参的槽在前；
/// 消费端 [`prune_ty_bump`] rev 迭代配对 Π 层）；线性时返回空 vec。非变量
/// 实参（字面量 / Decl / 带链变量 / Match）即失败（`None`）。槽位探测用
/// `force_arg`（不展开 pm 精化 / 不重选 Match——参考版 `invert_go` 同款）。
#[allow(clippy::too_many_arguments)]
fn invert_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    fuel: &Fuel,
    pm_defs: &[(u32, V)],
    ren: &mut RenBuf,
    gamma: u32,
    args: &[(V, Icit)], // 内先序（spine 收集器的输出）
) -> Option<Vec<Option<Icit>>> {
    ren.reset(); // 换代：本反演的映射从空开始
    let mut lvs: Vec<u32> = Vec::with_capacity(args.len());
    let mut nonlinear = false;
    for &(a, _) in args.iter().rev() {
        // 应用序（外先）
        let f = force_arg(bump, spine, defs, metas, decls, mmap, fuel, pm_defs, a);
        if v_tag(f) != 0 {
            return None;
        }
        let x = v_lvl_of(f);
        if x >= gamma {
            return None;
        }
        let i = lvs.len() as u32;
        lvs.push(x);
        match ren.get(x as usize) {
            // 已标非线性哨兵：保持 NONE_MARK 不动（第 3+ 次出现不覆盖）
            None if ren.has_mark(x as usize) => {}
            None => ren.set(x as usize, i),
            Some(_) => {
                ren.set(x as usize, NONE_MARK);
                nonlinear = true;
            }
        }
    }
    if !nonlinear {
        return Some(Vec::new());
    }
    // 掩码：内先序（mask[0] ↔ 最内层实参，与 prune_ty_bump 的
    // mask_inner_first 契约一致——后者 .rev() 后外→内配对 Π 层）；重复变量
    // 整级剪除
    let mut mask: Vec<Option<Icit>> = Vec::with_capacity(args.len());
    for k in 0..args.len() {
        // args[k] 内先 ↔ 应用序 n-1-k ↔ lvs[n-1-k]
        let x = lvs[args.len() - 1 - k] as usize;
        mask.push(match ren.get(x) {
            Some(_) => Some(args[k].1),
            None => None, // 非线性或从未映射 → 剪
        });
    }
    Some(mask)
}

/// `Γ ⊢ ?m args ≡ rhs` 的求解（invert 已做）：非线性掩码先验证剪枝可行性，
/// 再 rename（occurs/scope check 在内），λ 包裹取自 **meta 类型**，空环境
/// 求值写表。失败即不改 metacontext。
#[allow(clippy::too_many_arguments)]
fn solve_with_pren_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    fuel: &Fuel,
    pm_defs: &[(u32, V)],
    ren: &mut RenBuf,
    gamma: u32,
    m: u32,
    dom: u32,
    mask: Vec<Option<Icit>>, // invert 的非线性掩码（空 vec = 线性）
    rhs: V,
) -> bool {
    let mty = match &metas[m as usize] {
        MetaEntry::Unsolved(a) => *a,
        _ => unreachable!(), // 只对未解 meta 求解
    };
    // 非线性 spine：检查非线性的变量槽位可以从 meta 类型里剪掉
    if !mask.is_empty()
        && prune_ty_bump(
            bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, pm_defs, &mask, mty,
        )
        .is_none()
    {
        return false;
    }
    let Some(tm) = rename_iter(
        bump, spine, work, vals, icits, defs, ren, metas, decls, mmap, fuel, pm_defs, Some(m),
        dom, gamma, rhs,
    ) else {
        return false;
    };
    let lam_tm = lams_from_ty(
        bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, pm_defs, dom, mty, tm,
    );
    let sol = eval_iter(
                    bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, pm_defs, EMPTY_ENV,
        lam_tm,
    );
    metas[m as usize] = MetaEntry::Solved(sol, mty);
    true
}

/// solve = invert + solve_with_pren。
#[allow(clippy::too_many_arguments)]
fn solve_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    fuel: &Fuel,
    pm_defs: &[(u32, V)],
    ren: &mut RenBuf,
    gamma: u32,
    m: u32,
    args: &[(V, Icit)],
    rhs: V,
) -> bool {
    match invert_bump(bump, spine, defs, metas, decls, mmap, fuel, pm_defs, ren, gamma, args) {
        Some(mask) => solve_with_pren_bump(
            bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, pm_defs, ren, gamma,
            m, args.len() as u32, mask, rhs,
        ),
        None => false,
    }
}

/// rename 任务。icit 记账同 L04/L05：**只有刚性 `spine_case` 预装载**
/// `done_icits`（按收集序入栈）；flex 链走 `prune_vflex`（自持 fold，
/// 不碰 icit 栈）。
enum RJob<'a> {
    /// 引一个值到解域（产生一个 Tm 到 done）。
    Ren { dom: u32, cod: u32, v: V },
    /// 实参（逆应用序）已由其上任务引完，头是 head_tm，折叠 App
    /// （每个 App 的 icit 从平行 done_icits 栈取）。
    SpineFold {
        head_tm: &'a Tm<'a>,
        n: u32,
    },
    /// done 栈顶是体，包 Lam（icit 随闭包携带）。
    Lam1(&'a str, Icit),
    /// done 栈顶两个（先 cod 后 dom），合 Pi（icit 随 PiCell 携带）。
    Pi2(&'a PiCell<'a>),
}

/// partial renaming 的迭代版（L06 版 + L07 增量：Prim/Obj/Sum/SumCase/
/// Match 的 rename 臂。Match 的分支体在"捕获 env + fresh rigid 槽"下用
/// **简化 decl 表**重求值，再在**独立克隆的 renaming**（lift 过 count 次）
/// 下 rename——参考版按分支 clone 整个 HashMap，这里逐代克隆 RenBuf）。
#[allow(clippy::too_many_arguments)]
fn rename_iter<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    ren: &mut RenBuf,
    metas: &mut Vec<MetaEntry>,
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    fuel: &Fuel,
    pm_defs: &[(u32, V)],
    occ: Option<u32>,
    dom0: u32,
    cod0: u32,
    v0: V,
) -> Option<&'a Tm<'a>> {
    let mut tasks: Vec<RJob<'a>> = vec![RJob::Ren {
        dom: dom0,
        cod: cod0,
        v: v0,
    }];
    let mut done: Vec<&'a Tm<'a>> = Vec::new();
    // SpineFold 的实参 icit 预装载栈
    let mut done_icits: Vec<Icit> = Vec::new();
    // 实参收集 / 折叠草稿：跨任务复用（clear 保容量）
    let mut args: Vec<(V, Icit)> = Vec::new();
    let mut popped: Vec<&'a Tm<'a>> = Vec::new();
    macro_rules! spine_case {
        ($dom:expr, $cod:expr, $h:expr, $head_tm:expr, $tasks:expr) => {{
            args.clear();
            spine.collect_args($h, &mut args);
            $tasks.push(RJob::SpineFold {
                head_tm: $head_tm,
                n: args.len() as u32,
            });
            for &(_, i) in args.iter() {
                done_icits.push(i);
            }
            for &(a, _) in args.iter() {
                $tasks.push(RJob::Ren {
                    dom: $dom,
                    cod: $cod,
                    v: a,
                });
            }
        }};
    }
    while let Some(job) = tasks.pop() {
        match job {
            RJob::Ren { dom, cod, v } => {
                let v = force(
                bump, spine, defs, metas, decls, mmap, fuel, pm_defs, v,
                );
                match v_tag(v) {
                    5 => {
                        let m = v_meta_of(v);
                        if occ == Some(m) {
                            return None; // occurs check
                        }
                        done.push(bump.alloc(Tm::Meta(m)));
                    }
                    0 => {
                        let x = v_lvl_of(v) as usize;
                        // scope check（x 不在 spine 映射里；非线性哨兵也算缺项）
                        let Some(xp) = ren.get(x) else {
                            return None;
                        };
                        done.push(bump.alloc(Tm::Var(dom - xp - 1)));
                    }
                    2 => {
                        let h = v_spine_of(v);
                        let hd = spine.spine_head(h);
                        match v_tag(hd) {
                            5 => {
                                // flex 链：pruneVFlex（occ 检查在内部先行）
                                let m = v_meta_of(hd);
                                if occ == Some(m) {
                                    return None; // occurs check
                                }
                                let t = prune_vflex_bump(
                                    bump, spine, work, vals, icits, defs, ren, metas, decls,
                                    mmap, fuel, pm_defs, occ, dom, cod, m, h,
                                )?;
                                done.push(t);
                            }
                            // Decl / Prim 头的链照参考版 rename_sp 重建 App 链
                            // （头名直出，实参逐个 rename）；Obj 头的链先
                            // rename 内层再以 Tm::Obj 为头节点折叠实参
                            7 => {
                                let head_tm: &'a Tm<'a> = bump.alloc(match v_xcell_of(hd) {
                                    XCell::Decl(s) => Tm::Decl(s),
                                    XCell::Prim(s) => Tm::Prim(s),
                                    XCell::Obj { val, name } => {
                                        let inner = rename_iter(
                                            bump, spine, work, vals, icits, defs, ren, metas,
                                            decls, mmap, fuel, pm_defs, occ, dom, cod, *val,
                                        )?;
                                        Tm::Obj(inner, name)
                                    }
                                    XCell::Lit(s) => Tm::LiteralIntro(s),
                                    _ => return None,
                                });
                                spine_case!(dom, cod, h, head_tm, tasks);
                            }
                            _ => {
                                let x = v_lvl_of(hd) as usize;
                                let Some(xp) = ren.get(x) else {
                                    return None; // scope check
                                };
                                let head_tm = bump.alloc(Tm::Var(dom - xp - 1));
                                spine_case!(dom, cod, h, head_tm, tasks);
                            }
                        }
                    }
                    1 => {
                        let c = v_clo_of(v);
                        let bv = {
                            let env = env_ext(bump, c.env, v_lvl(cod));
                            eval_iter(
                                bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel,
                                pm_defs, env, c.body,
                            )
                        };
                        // lift：binder 槽 (cod → dom)
                        ren.set(cod as usize, dom);
                        tasks.push(RJob::Lam1(c.name, c.icit));
                        tasks.push(RJob::Ren {
                            dom: dom + 1,
                            cod: cod + 1,
                            v: bv,
                        });
                    }
                    4 => {
                        let cell = v_pi_of(v);
                        let bv = {
                            let env = env_ext(bump, cell.env, v_lvl(cod));
                            eval_iter(
                                bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel,
                                pm_defs, env, cell.body,
                            )
                        };
                        // lift（同 Lam）
                        ren.set(cod as usize, dom);
                        tasks.push(RJob::Pi2(cell));
                        tasks.push(RJob::Ren {
                            dom: dom + 1,
                            cod: cod + 1,
                            v: bv,
                        });
                        tasks.push(RJob::Ren {
                            dom,
                            cod,
                            v: cell.dom,
                        });
                    }
                    3 => done.push(bump.alloc(Tm::U)),
                    // 字面量类型与裸单元（Lit / Decl / Prim 空链）直出
                    6 => done.push(bump.alloc(Tm::LiteralType)),
                    7 => match v_xcell_of(v) {
                        XCell::Lit(s) => done.push(bump.alloc(Tm::LiteralIntro(s))),
                        XCell::Decl(s) => done.push(bump.alloc(Tm::Decl(s))),
                        XCell::Prim(s) => done.push(bump.alloc(Tm::Prim(s))),
                        XCell::Obj { val, name } => {
                            // 卡住投影：rename 内层 → 包 Tm::Obj（空实参；
                            // 带实参的链在 tag 2 臂处理）
                            let inner = rename_iter(
                                bump, spine, work, vals, icits, defs, ren, metas, decls, mmap,
                                fuel, pm_defs, occ, dom, cod, *val,
                            )?;
                            done.push(bump.alloc(Tm::Obj(inner, name)));
                        }
                        XCell::Sum {
                            name,
                            params,
                            cases,
                        } => {
                            let mut ps: Vec<SumParamT<'_>> = Vec::with_capacity(params.len());
                            for p in params.iter() {
                                let pv = rename_iter(
                                    bump, spine, work, vals, icits, defs, ren, metas, decls,
                                    mmap, fuel, pm_defs, occ, dom, cod, p.val,
                                )?;
                                let pt = rename_iter(
                                    bump, spine, work, vals, icits, defs, ren, metas, decls,
                                    mmap, fuel, pm_defs, occ, dom, cod, p.ty,
                                )?;
                                ps.push(SumParamT {
                                    name: p.name,
                                    val: pv,
                                    ty: pt,
                                    icit: p.icit,
                                });
                            }
                            done.push(bump.alloc(Tm::Sum(
                                name,
                                bump.alloc_slice_fill_iter(ps),
                                cases,
                            )));
                        }
                        XCell::SumCase {
                            typ,
                            case_name,
                            datas,
                        } => {
                            let tt = rename_iter(
                                bump, spine, work, vals, icits, defs, ren, metas, decls, mmap,
                                fuel, pm_defs, occ, dom, cod, *typ,
                            )?;
                            let mut ds: Vec<SumDataT<'_>> = Vec::with_capacity(datas.len());
                            for d in datas.iter() {
                                let dv = rename_iter(
                                    bump, spine, work, vals, icits, defs, ren, metas, decls,
                                    mmap, fuel, pm_defs, occ, dom, cod, d.val,
                                )?;
                                ds.push(SumDataT {
                                    name: d.name,
                                    val: dv,
                                    icit: d.icit,
                                });
                            }
                            done.push(bump.alloc(Tm::SumCase {
                                typ: tt,
                                case_name,
                                datas: bump.alloc_slice_fill_iter(ds),
                            }));
                        }
                        XCell::Match {
                            scrutinee,
                            env: menv,
                            cases,
                            pending,
                        } => {
                            // 分支体是裸 Tm：先在"捕获 env + fresh rigid 槽"
                            // 下重新求值（简化 decl 表防重展开），再在 lift
                            // 过的独立 renaming 下 rename（参考版 rename 的
                            // Match 臂同款；scrutinee 与 pending 用真实表）
                            let val_tm = rename_iter(
                                bump, spine, work, vals, icits, defs, ren, metas, decls, mmap,
                                fuel, pm_defs, occ, dom, cod, *scrutinee,
                            )?;
                            let declb = simpl_decl(bump, decls);
                            let mut nc: Vec<(PatternDetail, &'a Tm<'a>)> =
                                Vec::with_capacity(cases.len());
                            for (pat, tm) in cases.iter() {
                                let count = pat.bind_count();
                                let mut ren2 = ren.clone_valid();
                                let mut env2 = *menv;
                                let (mut d2, mut c2) = (dom, cod);
                                for _ in 0..count {
                                    env2 = env_ext(bump, env2, v_lvl(c2));
                                    ren2.set(c2 as usize, d2);
                                    d2 += 1;
                                    c2 += 1;
                                }
                                let bv = eval_iter(
                                    bump, spine, work, vals, icits, defs, metas, &declb, mmap,
                                    fuel, pm_defs, env2, tm,
                                );
                                let bt = rename_iter(
                                    bump, spine, work, vals, icits, defs, &mut ren2, metas,
                                    &declb, mmap, fuel, pm_defs, occ, d2, c2, bv,
                                )?;
                                nc.push(((*pat).clone(), bt));
                            }
                            let cs: &'a [(PatternDetail, &'a Tm<'a>)] =
                                bump.alloc_slice_fill_iter(nc);
                            let mut acc: &'a Tm<'a> = bump.alloc(Tm::Match(val_tm, cs));
                            // 卡住期累积的实参：同 quote，包在 Match 外的
                            // App 链里（应用序）
                            for &(uu, ii) in *pending {
                                let ut = rename_iter(
                                    bump, spine, work, vals, icits, defs, ren, metas, decls,
                                    mmap, fuel, pm_defs, occ, dom, cod, uu,
                                )?;
                                acc = bump.alloc(Tm::App(acc, ut, ii));
                            }
                            done.push(acc);
                        }
                    },
                    _ => return None, // 病态（Π/U/字面量被应用等）
                }
            }
            RJob::SpineFold { head_tm, n } => {
                popped.clear();
                for _ in 0..n {
                    let t = done.pop()?;
                    popped.push(t);
                }
                let mut t = head_tm;
                for k in 0..n as usize {
                    let i = done_icits.pop()?;
                    let a = popped[n as usize - 1 - k];
                    t = bump.alloc(Tm::App(t, a, i));
                }
                done.push(t);
            }
            RJob::Lam1(name, icit) => {
                let body = done.pop()?; // 栈约定：子任务必已完成
                done.push(bump.alloc(Tm::Lam(name, icit, body)));
            }
            RJob::Pi2(cell) => {
                let cod = done.pop()?;
                let dom = done.pop()?;
                done.push(bump.alloc(Tm::Pi(cell.name, cell.icit, dom, cod)));
            }
        }
    }
    debug_assert_eq!(done_icits.len(), 0, "icit 预装载必须全部配对弹出");
    done.pop()
}

/// `pruneVFlex` 的 spine 状态（参考版 `SpinePruneStatus` 同构）。
#[derive(Debug, Clone, Copy, PartialEq)]
enum SpinePruneStatus {
    OKRenaming,
    OKNonRenaming,
    NeedsPruning,
}

/// `pruneVFlex`：meta + 纯变量 renaming 判定与剪枝（L06 版原样；非变量
/// 实参——含字面量/Decl/Prim/Obj/构造子值——嵌套 rename，与参考版
/// prune_vflex_go 的非 Rigid 臂一致；实参探测用 `force_arg`）。
#[allow(clippy::too_many_arguments)]
fn prune_vflex_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    ren: &mut RenBuf,
    metas: &mut Vec<MetaEntry>,
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    fuel: &Fuel,
    pm_defs: &[(u32, V)],
    occ: Option<u32>,
    dom: u32,
    cod: u32,
    m: u32,
    h: usize,
) -> Option<&'a Tm<'a>> {
    let mut args: Vec<(V, Icit)> = Vec::new();
    spine.collect_args(h, &mut args); // 内先序
    let mut slots: Vec<(Option<&'a Tm<'a>>, Icit)> = Vec::with_capacity(args.len());
    let mut status = SpinePruneStatus::OKRenaming;
    for &(a, i) in args.iter().rev() {
        // 应用序（外先）
        let f = force_arg(
                bump, spine, defs, metas, decls, mmap, fuel, pm_defs, a,
        );
        if v_tag(f) == 0 {
            match ren.get(v_lvl_of(f) as usize) {
                Some(xp) => slots.push((Some(bump.alloc(Tm::Var(dom - xp - 1))), i)),
                None if status == SpinePruneStatus::OKNonRenaming => return None,
                None => {
                    slots.push((None, i));
                    status = SpinePruneStatus::NeedsPruning;
                }
            }
        } else {
            if status == SpinePruneStatus::NeedsPruning {
                return None; // 上游：剪枝后 spine 必须全变量
            }
            let t = rename_iter(
                bump, spine, work, vals, icits, defs, ren, metas, decls, mmap, fuel, pm_defs,
                occ, dom, cod, f,
            )?;
            slots.push((Some(t), i));
            status = SpinePruneStatus::OKNonRenaming;
        }
    }
    let m_prime = if status == SpinePruneStatus::NeedsPruning {
        // 掩码内先序 = slots 反序
        let mut mask: Vec<Option<Icit>> = Vec::with_capacity(slots.len());
        for (st, i) in slots.iter().rev() {
            mask.push(if st.is_some() { Some(*i) } else { None });
        }
        prune_meta_bump(
            bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, pm_defs, &mask, m,
        )?
    } else {
        m
    };
    // 折叠：上游 foldr = 最外层实参先应用（外先迭代，内层包在最外）
    let mut t: &'a Tm<'a> = bump.alloc(Tm::Meta(m_prime));
    for (st, i) in slots {
        if let Some(u) = st {
            t = bump.alloc(Tm::App(t, u, i));
        }
    }
    Some(t)
}

/// `pruneMeta`：检查剪后类型良型、造新 meta（类型 = 剪后值），旧 meta 解为
/// `λ telescope. AppPruning ?m' pruned`。掩码内先序（同 cxt 惯例）。
#[allow(clippy::too_many_arguments)]
fn prune_meta_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    fuel: &Fuel,
    pm_defs: &[(u32, V)],
    mask: &[Option<Icit>], // 内先序
    m: u32,
) -> Option<u32> {
    let mty = match &metas[m as usize] {
        MetaEntry::Unsolved(a) => *a,
        _ => unreachable!(), // 只对未解 meta 剪枝
    };
    let pruned_tm = prune_ty_bump(
        bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, pm_defs, mask, mty,
    )?;
    let prunedty = eval_iter(
                    bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, pm_defs, EMPTY_ENV,
        pruned_tm,
    );
    let mp = metas.len() as u32;
    metas.push(MetaEntry::Unsolved(prunedty));
    // AppPruning 项：掩码外先入链（新槽恒链头 → 最终头 = 最内层）
    let mut pr: Option<&'a PrCons<'a>> = None;
    for slot in mask.iter().rev() {
        pr = Some(bump.alloc(PrCons::new(*slot, pr)));
    }
    let ap = bump.alloc(Tm::AppPruning(bump.alloc(Tm::Meta(mp)), pr));
    let lam_tm = lams_from_ty(
        bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, pm_defs,
        mask.len() as u32, mty, ap,
    );
    let sol = eval_iter(
                    bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, pm_defs, EMPTY_ENV,
        lam_tm,
    );
    metas[m as usize] = MetaEntry::Solved(sol, mty);
    Some(mp)
}

/// `pruneTy (revPruning pr) a`：掩码**外→内**配对 Π 层。自带换代缓冲。
#[allow(clippy::too_many_arguments)]
fn prune_ty_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    fuel: &Fuel,
    pm_defs: &[(u32, V)],
    mask_inner_first: &[Option<Icit>],
    mty: V,
) -> Option<&'a Tm<'a>> {
    let mut ren2 = RenBuf::default();
    ren2.reset(); // epoch 从 1 起（新槽 stamp 0 无效）
    let mut dom: u32 = 0;
    let mut cod: u32 = 0;
    let mut layers: Vec<(&'a str, Icit, &'a Tm<'a>)> = Vec::new();
    let mut cur = force(
                bump, spine, defs, metas, decls, mmap, fuel, pm_defs, mty,
    );
    for entry in mask_inner_first.iter().rev() {
        // 外→内
        if v_tag(cur) != 4 {
            return None; // 上游 impossible：掩码与类型层不匹配
        }
        let p = v_pi_of(cur);
        let (name, icit, pdom, env, body) = (p.name, p.icit, p.dom, p.env, p.body);
        if entry.is_some() {
            let dtm = rename_iter(
                bump, spine, work, vals, icits, defs, &mut ren2, metas, decls, mmap, fuel,
                pm_defs, None, dom, cod, pdom,
            )?;
            // lift：binder 进映射
            ren2.set(cod as usize, dom);
            layers.push((name, icit, dtm));
            dom += 1;
        }
        let next = eval_iter(
                    bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, pm_defs,
            env_ext(bump, env, v_lvl(cod)),
            body,
        );
        cod += 1;
        cur = force(
                bump, spine, defs, metas, decls, mmap, fuel, pm_defs, next,
        );
    }
    let mut t = rename_iter(
        bump, spine, work, vals, icits, defs, &mut ren2, metas, decls, mmap, fuel, pm_defs, None,
        dom, cod, cur,
    )?;
    // 保留层由内向外回包（layers 序 = 外→内，rev = 内→外 ✓）
    for (name, icit, dtm) in layers.iter().rev() {
        t = bump.alloc(Tm::Pi(name, *icit, dtm, t));
    }
    Some(t)
}

/// `lams l a t`：沿 **meta 类型**的 Π 层包 λ（名字与 icit 随 Π，`"_"` 改名
/// `x{l'}`；逐层用 `VVar l'` 剥闭包）。
#[allow(clippy::too_many_arguments)]
fn lams_from_ty<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    fuel: &Fuel,
    pm_defs: &[(u32, V)],
    l: u32,
    ty: V,
    body: &'a Tm<'a>,
) -> &'a Tm<'a> {
    let mut names: Vec<(&'a str, Icit)> = Vec::with_capacity(l as usize);
    let mut cur = force(
                bump, spine, defs, metas, decls, mmap, fuel, pm_defs, ty,
    );
    for lp in 0..l {
        if v_tag(cur) != 4 {
            unreachable!(); // 类型 Π 层数不足（上游同款不可能）
        }
        let p = v_pi_of(cur);
        let (name, icit, env, body_tm) = (p.name, p.icit, p.env, p.body);
        let name = if name == "_" {
            bump.alloc_str(&format!("x{}", lp))
        } else {
            name
        };
        names.push((name, icit));
        let next = eval_iter(
                    bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, pm_defs,
            env_ext(bump, env, v_lvl(lp)),
            body_tm,
        );
        cur = force(
                bump, spine, defs, metas, decls, mmap, fuel, pm_defs, next,
        );
    }
    let mut t = body;
    for (name, icit) in names.iter().rev() {
        t = bump.alloc(Tm::Lam(name, *icit, t));
    }
    t
}

// 结构相等（快路径专用）：不 force、不展开、不求值，忽略 span 名。
// budget 封顶（参考版 struct_eq 的 20_000 同口径），超限按"不相等"处理
// ——快路径只会把本可判等（但求值发散）的情形提前判等，回落路径保持
// 原行为。env 的解析需要 `defs`（平坦区域）与 `spine`（链实参收集）。
// --------------------------------------------------------------------------------

const EQ_BUDGET: usize = 20_000;

struct EqBudget(usize);

impl EqBudget {
    fn spend(&mut self) -> bool {
        if self.0 == 0 {
            return false;
        }
        self.0 -= 1;
        true
    }
}

/// `AppPruning` 掩码链的槽位快照（头 = 最内层）。
fn pr_slots(p: &Option<&PrCons<'_>>) -> Vec<Option<Icit>> {
    let mut out = Vec::new();
    let mut cur = *p;
    while let Some(b) = cur {
        out.push(b.slot);
        cur = b.next;
    }
    out
}

fn struct_tm_eq(a: &Tm<'_>, b: &Tm<'_>) -> bool {
    struct_tm_eq_go(&mut EqBudget(EQ_BUDGET), a, b)
}

fn struct_val_eq(spine: &Spine, defs: &[V], a: V, b: V) -> bool {
    struct_val_eq_go(&mut EqBudget(EQ_BUDGET), spine, defs, a, b)
}

fn struct_env_eq(spine: &Spine, defs: &[V], a: Env<'_>, b: Env<'_>) -> bool {
    struct_env_eq_go(&mut EqBudget(EQ_BUDGET), spine, defs, a, b)
}

fn struct_spine_eq_go(budget: &mut EqBudget, spine: &Spine, defs: &[V], h1: usize, h2: usize) -> bool {
    if spine.spine_len(h1) != spine.spine_len(h2) {
        return false;
    }
    let mut a1: Vec<(V, Icit)> = Vec::new();
    spine.collect_args(h1, &mut a1);
    let mut a2: Vec<(V, Icit)> = Vec::new();
    spine.collect_args(h2, &mut a2);
    // 头也要同（bit-equal 或同名 Decl/Prim/同 Obj 结构）
    if !struct_val_eq_go(budget, spine, defs, spine.spine_head(h1), spine.spine_head(h2)) {
        return false;
    }
    a1.iter()
        .zip(a2.iter())
        .all(|((x, i), (y, j))| i == j && struct_val_eq_go(budget, spine, defs, *x, *y))
}

fn struct_tm_eq_go(budget: &mut EqBudget, a: &Tm<'_>, b: &Tm<'_>) -> bool {
    if !budget.spend() {
        return false;
    }
    match (a, b) {
        (Tm::Var(x), Tm::Var(y)) => x == y,
        (Tm::Decl(x), Tm::Decl(y)) => x == y,
        (Tm::Prim(x), Tm::Prim(y)) => x == y,
        (Tm::Obj(x, n), Tm::Obj(y, m)) => n == m && struct_tm_eq_go(budget, x, y),
        (Tm::App(x, xu, i), Tm::App(y, yu, j)) => {
            i == j && struct_tm_eq_go(budget, x, y) && struct_tm_eq_go(budget, xu, yu)
        }
        (Tm::Lam(_, i, x), Tm::Lam(_, j, y)) => i == j && struct_tm_eq_go(budget, x, y),
        (Tm::U, Tm::U) => true,
        (Tm::Pi(_, i, xa, xb), Tm::Pi(_, j, ya, yb)) => {
            i == j && struct_tm_eq_go(budget, xa, ya) && struct_tm_eq_go(budget, xb, yb)
        }
        (Tm::Let(_, xa, xb, xc), Tm::Let(_, ya, yb, yc)) => {
            struct_tm_eq_go(budget, xa, ya)
                && struct_tm_eq_go(budget, xb, yb)
                && struct_tm_eq_go(budget, xc, yc)
        }
        (Tm::Meta(x), Tm::Meta(y)) => x == y,
        (Tm::AppPruning(x, p), Tm::AppPruning(y, q)) => {
            let (sp, sq) = (pr_slots(p), pr_slots(q));
            sp.len() == sq.len()
                && sp.iter().zip(sq.iter()).all(|(a, b)| a == b)
                && struct_tm_eq_go(budget, x, y)
        }
        (Tm::LiteralType, Tm::LiteralType) => true,
        (Tm::LiteralIntro(x), Tm::LiteralIntro(y)) => x == y,
        (Tm::Sum(xn, xp, _), Tm::Sum(yn, yp, _)) => {
            xn == yn
                && xp.len() == yp.len()
                && xp.iter().zip(yp.iter()).all(|(a, b)| {
                    a.icit == b.icit
                        && struct_tm_eq_go(budget, a.val, b.val)
                        && struct_tm_eq_go(budget, a.ty, b.ty)
                })
        }
        (
            Tm::SumCase {
                typ: xt,
                case_name: xn,
                datas: xd,
            },
            Tm::SumCase {
                typ: yt,
                case_name: yn,
                datas: yd,
            },
        ) => {
            xn == yn
                && struct_tm_eq_go(budget, xt, yt)
                && xd.len() == yd.len()
                && xd.iter().zip(yd.iter()).all(|(a, b)| {
                    a.icit == b.icit && struct_tm_eq_go(budget, a.val, b.val)
                })
        }
        (Tm::Match(xs, xc), Tm::Match(ys, yc)) => {
            struct_tm_eq_go(budget, xs, ys)
                && xc.len() == yc.len()
                && xc
                    .iter()
                    .zip(yc.iter())
                    .all(|((p, xb), (q, yb))| p == q && struct_tm_eq_go(budget, xb, yb))
        }
        _ => false,
    }
}

fn struct_val_eq_go(budget: &mut EqBudget, spine: &Spine, defs: &[V], x: V, y: V) -> bool {
    if !budget.spend() {
        return false;
    }
    match (v_tag(x), v_tag(y)) {
        (0, 0) => v_lvl_of(x) == v_lvl_of(y),
        (5, 5) => v_meta_of(x) == v_meta_of(y),
        (3, 3) | (6, 6) => true,
        (1, 1) => {
            let c1 = v_clo_of(x);
            let c2 = v_clo_of(y);
            c1.icit == c2.icit
                && struct_env_eq_go(budget, spine, defs, c1.env, c2.env)
                && struct_tm_eq_go(budget, c1.body, c2.body)
        }
        (4, 4) => {
            let p1 = v_pi_of(x);
            let p2 = v_pi_of(y);
            p1.icit == p2.icit
                && struct_val_eq_go(budget, spine, defs, p1.dom, p2.dom)
                && struct_env_eq_go(budget, spine, defs, p1.env, p2.env)
                && struct_tm_eq_go(budget, p1.body, p2.body)
        }
        (2, 2) => struct_spine_eq_go(budget, spine, defs, v_spine_of(x), v_spine_of(y)),
        (7, 7) => match (v_xcell_of(x), v_xcell_of(y)) {
            (XCell::Lit(a), XCell::Lit(b)) => a == b,
            (XCell::Decl(a), XCell::Decl(b)) => a == b,
            (XCell::Prim(a), XCell::Prim(b)) => a == b,
            (XCell::Obj { val: a, name: an }, XCell::Obj { val: b, name: bn }) => {
                an == bn && struct_val_eq_go(budget, spine, defs, *a, *b)
            }
            (
                XCell::Sum {
                    name: xn,
                    params: xp,
                    ..
                },
                XCell::Sum {
                    name: yn,
                    params: yp,
                    ..
                },
            ) => {
                xn == yn
                    && xp.len() == yp.len()
                    && xp.iter().zip(yp.iter()).all(|(a, b)| {
                        a.icit == b.icit
                            && struct_val_eq_go(budget, spine, defs, a.val, b.val)
                            && struct_val_eq_go(budget, spine, defs, a.ty, b.ty)
                    })
            }
            (
                XCell::SumCase {
                    typ: xt,
                    case_name: xn,
                    datas: xd,
                },
                XCell::SumCase {
                    typ: yt,
                    case_name: yn,
                    datas: yd,
                },
            ) => {
                xn == yn
                    && struct_val_eq_go(budget, spine, defs, *xt, *yt)
                    && xd.len() == yd.len()
                    && xd.iter().zip(yd.iter()).all(|(a, b)| {
                        a.icit == b.icit && struct_val_eq_go(budget, spine, defs, a.val, b.val)
                    })
            }
            (
                XCell::Match {
                    scrutinee: xs,
                    env: xe,
                    cases: xc,
                    pending: xp,
                },
                XCell::Match {
                    scrutinee: ys,
                    env: ye,
                    cases: yc,
                    pending: yp,
                },
            ) => {
                struct_val_eq_go(budget, spine, defs, *xs, *ys)
                    && struct_env_eq_go(budget, spine, defs, *xe, *ye)
                    && xc.len() == yc.len()
                    && xc
                        .iter()
                        .zip(yc.iter())
                        .all(|((p, xb), (q, yb))| p == q && struct_tm_eq_go(budget, xb, yb))
                    && xp.len() == yp.len()
                    && xp.iter().zip(yp.iter()).all(|((xv, xi), (yv, yi))| {
                        xi == yi && struct_val_eq_go(budget, spine, defs, *xv, *yv)
                    })
            }
            _ => false,
        },
        _ => false,
    }
}

fn struct_env_eq_go(
    budget: &mut EqBudget,
    spine: &Spine,
    defs: &[V],
    a: Env<'_>,
    b: Env<'_>,
) -> bool {
    let la = env_len(a);
    let lb = env_len(b);
    if la != lb {
        return false;
    }
    (0..la).all(|i| {
        struct_val_eq_go(
            budget,
            spine,
            defs,
            env_nth(defs, a, i),
            env_nth(defs, b, i),
        )
    })
}

// Machine（稳态复用）与 elaboration
// --------------------------------------------------------------------------------

/// unify 的跨调用草稿。
#[derive(Default)]
struct ConvScratch {
    memo: FxHashSet<(u64, u64)>,
    scratch1: Vec<(V, Icit)>,
    scratch2: Vec<(V, Icit)>,
}

const PI_NAME: &str = "x"; // infer App 非 Π 分支合成的闭包名（只服务 pretty）

/// 稳态复用机（L06 版 + L07 增量：unify_fuel 池、pm 特化事实表/可解集——
/// 分支局部的 (层级 → 值) 记录，`force` 在读点惰性展开；decl 表不在机上
/// ——它在 `Cxt.decl`（`Rc<FxHashMap>` 写时复制，随上下文传递，与参考版
/// `Infer` 方法逐点接收 `decl: &Decls` 同构））。
pub(crate) struct Machine {
    spine: Spine,
    vals: Vec<V>,
    /// icit 侧栈（eval 右链下降用；跨调用复用容量，进核前 clear）。
    icits: Vec<Icit>,
    /// unify 的判等记忆化 + 实参收集草稿（跨调用复用容量，进核前 clear）。
    conv: ConvScratch,
    /// 平坦环境区域（每轮 append-only，只增不减）。
    defs: Vec<V>,
    pub(crate) metas: Vec<MetaEntry>,
    /// solve 的偏置换换代缓冲（跨求解持久，epoch 换代免逐槽清零）。
    ren: RenBuf,
    /// 名字 → (绑定 lvl, 类型值)：`Raw::Var` 的 O(1) 解析。**只收源码
    /// binder**（bind/define）——inserted binder 与参考版 `new_binder`
    /// 一样不入 src_names。
    name_map: FxHashMap<SmolStr, (u32, V)>,
    /// bind/define 的撤销轨迹：(名字, 旧值)。
    name_trail: Vec<(SmolStr, Option<(u32, V)>)>,
    /// 可变全局（L06 同款）：builtin `create_global` / `change_mutable` 族
    /// 的存取目标。值指向本轮 bump——每轮清空（参考版每次调用新建 Infer）。
    mutable_map: MutableMap,
    /// force 展开与 unify 递归的共享燃料池（每次 unify_catch / 编译入口 /
    /// nf 充值；耗尽即把值当未解处理 / Err）。
    fuel: Fuel,
    /// 模式特化方程的解：子句变量 := 值（分支局部的事实表；层级、env 槽、
    /// 运行时布局都不动）。臂边界 / 可达性探测做快照回滚。
    pm_defs: Vec<(u32, V)>,
    /// 当前可被特化方程求解的 rigid 层级（= 当前子句的 bind 槽）。只在
    /// 模式走查与探测期间非空；分支体检查期间必须为空。
    pm_solvable: Vec<u32>,
    /// eval / quote / unify 的可复用工作栈。`'static` 仅是**存放口径**：
    /// 进核前 clear，借出期间写入的当轮条目不跨调用存活——与 `conv` /
    /// `icits` 的「进核前 clear」纪律同款。`W`/`QJob`/`UItem` 均为无 Drop
    /// 的 Copy 枚举，`Vec` 布局与元素生命周期参数无关，出借时按当次
    /// 生命周期重写指针类型（SAFETY 见各包装方法）。
    eval_work: Vec<W<'static>>,
    quote_tasks: Vec<QJob<'static>>,
    quote_done: Vec<&'static Tm<'static>>,
    quote_work: Vec<W<'static>>,
    unify_work: Vec<W<'static>>,
    /// unify 的 UItem 主工作栈（同上口径；`UItem::MatchBranch` 持
    /// `Rc`——失败早退留下的 Rc 随下次入口 clear 正确减计，非 Drop 项
    /// 是引用 Copy，'static 存放无析构风险）。
    unify_stack: Vec<UItem<'static>>,
    /// quote 记忆化表：容量跨调用复用，内容**每次调用 clear**——meta 可
    /// 能在两次调用之间被求解，跨调用保留条目会拿到过期中性项（表随
    /// 调用新鲜是口径的一部分，绝不跨 reset 持有）。
    quote_memo: QuoteMemo<'static>,
}

impl Machine {
    pub(crate) fn new() -> Self {
        Machine {
            spine: Spine {
                stack: Vec::with_capacity(4096),
            },
            vals: Vec::with_capacity(4096),
            icits: Vec::new(),
            conv: ConvScratch::default(),
            defs: Vec::with_capacity(4096),
            metas: Vec::new(),
            ren: RenBuf::default(),
            name_map: FxHashMap::default(),
            name_trail: Vec::new(),
            mutable_map: RefCell::new(FxHashMap::default()),
            fuel: Cell::new(UNIFY_FUEL),
            pm_defs: Vec::new(),
            pm_solvable: Vec::new(),
            eval_work: Vec::new(),
            quote_tasks: Vec::new(),
            quote_done: Vec::new(),
            quote_work: Vec::new(),
            unify_work: Vec::new(),
            unify_stack: Vec::new(),
            quote_memo: FxHashMap::default(),
        }
    }

    /// 每轮 reset：metacontext + 名字表/轨迹/环境区域 + 可变全局 + pm 事实
    /// 表全部清空（builtin 的重注册在 [`Machine::prime_round`]；decl 表随
    /// Cxt 的 Rc 释放）。spine 栈同轮清空（保容量）——tag-2 句柄只被当轮
    /// bump 值 / metas / defs / mutable_map / pm_defs 持有，轮边界后无任何
    /// 旧句柄可达，截断防稳态复用下的无界增长。
    fn clear_round(&mut self) {
        self.metas.clear();
        self.name_map.clear();
        self.name_trail.clear();
        self.defs.clear();
        self.mutable_map.borrow_mut().clear();
        self.pm_defs.clear();
        self.pm_solvable.clear();
        self.spine.stack.clear();
        self.fuel.set(UNIFY_FUEL);
    }

    // pm 特化状态（参考版 `Infer` 的 pm 族）
    // --------------------------------------------------------------------------------

    /// 模式精化状态的快照点（长度即可，回滚 = 截断）。
    fn pm_mark(&self) -> (usize, usize) {
        (self.pm_defs.len(), self.pm_solvable.len())
    }

    /// 回滚到快照点：臂边界 / 探测边界调用。本臂解出的 meta 不回滚（分支
    /// 体 Tm 引用着它们；解在 rename 时已把精化"烘焙"为无 def 形式）。
    fn pm_restore(&mut self, mark: (usize, usize)) {
        self.pm_defs.truncate(mark.0);
        self.pm_solvable.truncate(mark.1);
    }

    fn pm_def(&self, x: u32) -> Option<V> {
        self.pm_defs
            .iter()
            .rev()
            .find(|(l, _)| *l == x)
            .map(|(_, v)| *v)
    }

    fn is_flex_v(&self, v: V) -> bool {
        is_flex(&self.spine, v)
    }

    /// 记录一条特化解 `x := v`（环守卫见 `val_mentions_lvl`）。
    fn pm_solve(&mut self, x: u32, v: V) -> bool {
        if val_mentions_lvl(&self.spine, &self.defs, v, x) {
            return false;
        }
        self.pm_defs.push((x, v));
        true
    }

    // Extend Cxt（源码 binder / inserted binder / define）
    // --------------------------------------------------------------------------------

    /// Extend Cxt with a bound variable（源码 binder）。
    #[allow(clippy::too_many_arguments)]
    fn bind_name<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        x: &str,
        a_t: &'a Tm<'a>,
        ty: V,
    ) -> Cxt<'a> {
        debug_assert_eq!(self.name_trail.len(), cxt.mark as usize);
        let key = SmolStr::new(x);
        let prev = self.name_map.insert(key.clone(), (cxt.lvl, ty));
        self.name_trail.push((key, prev));
        let env = env_ext(bump, cxt.env, v_lvl(cxt.lvl));
        Cxt {
            env,
            types: Some(bump.alloc(TCons {
                name: bump.alloc_str(x),
                ty,
                source: true,
                next: cxt.types,
            })),
            locals: Some(bump.alloc(LCons {
                name: bump.alloc_str(x),
                a_t,
                t_t: None,
                next: cxt.locals,
            })),
            pruning: Some(bump.alloc(PrCons::new(Some(Icit::Expl), cxt.pruning))),
            binds: cxt.binds + 1,
            lvl: cxt.lvl + 1,
            mark: cxt.mark + 1,
            decl: cxt.decl.clone(),
        }
    }

    /// Extend Cxt with an inserted implicit binder：**不入名字表**、trail
    /// 不动、mark 不变——但 telescope/pruning 照常扩展。
    fn new_binder<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        x: &str,
        a_t: &'a Tm<'a>,
        ty: V,
    ) -> Cxt<'a> {
        debug_assert_eq!(self.name_trail.len(), cxt.mark as usize);
        let env = env_ext(bump, cxt.env, v_lvl(cxt.lvl));
        Cxt {
            env,
            types: Some(bump.alloc(TCons {
                name: bump.alloc_str(x),
                ty,
                source: false,
                next: cxt.types,
            })),
            locals: Some(bump.alloc(LCons {
                name: bump.alloc_str(x),
                a_t,
                t_t: None,
                next: cxt.locals,
            })),
            pruning: Some(bump.alloc(PrCons::new(Some(Icit::Expl), cxt.pruning))),
            binds: cxt.binds + 1,
            lvl: cxt.lvl + 1,
            mark: cxt.mark,
            decl: cxt.decl.clone(),
        }
    }

    /// Extend Cxt with a definition（pruning 记 `None`、telescope 记 Define
    /// 槽）。
    #[allow(clippy::too_many_arguments)]
    fn define_name<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        x: &str,
        a_t: &'a Tm<'a>,
        t_t: &'a Tm<'a>,
        val: V,
        ty: V,
    ) -> Cxt<'a> {
        debug_assert_eq!(self.name_trail.len(), cxt.mark as usize);
        let key = SmolStr::new(x);
        let prev = self.name_map.insert(key.clone(), (cxt.lvl, ty));
        self.name_trail.push((key, prev));
        let env = env_ext_defs(bump, &mut self.defs, cxt.env, val);
        Cxt {
            env,
            types: Some(bump.alloc(TCons {
                name: bump.alloc_str(x),
                ty,
                source: true,
                next: cxt.types,
            })),
            locals: Some(bump.alloc(LCons {
                name: bump.alloc_str(x),
                a_t,
                t_t: Some(t_t),
                next: cxt.locals,
            })),
            pruning: Some(bump.alloc(PrCons::new(None, cxt.pruning))),
            binds: cxt.binds, // define 槽不产生 Π 层
            lvl: cxt.lvl + 1,
            mark: cxt.mark + 1,
            decl: cxt.decl.clone(),
        }
    }

    /// 撤销轨迹当前长度（模式编译的臂边界用它取基线——臂内 walk 的绑定
    /// 不经 unwind_names 退出，需显式截断）。
    fn name_mark(&self) -> u32 {
        self.name_trail.len() as u32
    }

    /// 截断撤销轨迹到 `mark`（binder 作用域退出）。
    fn unwind_names(&mut self, mark: u32) {
        while self.name_trail.len() > mark as usize {
            let (key, prev) = self.name_trail.pop().expect("unwind_names: 轨迹为空");
            match prev {
                Some(entry) => {
                    self.name_map.insert(key, entry);
                }
                None => {
                    self.name_map.remove(&key);
                }
            }
        }
    }

    /// 挂新洞（上游 `freshMeta`）：物化闭类型、追加未解条目，产出
    /// `AppPruning ?m (cxt.pruning)`。快捷（L05 三级 + tag 6）：
    /// **`binds == 0`** 时常值类型（U / 裸未解 meta / LiteralType，tag
    /// 3/5/6）闭类型恒等（telescope 只剩 Define 的 Let 层——eval 只往 env
    /// 塞值不添 Π 层）；`quote` 无自由变量则跳过 Let 链直接空环境求值；
    /// 否则全构造（与参考版同形）。
    fn fresh_meta<'a>(&mut self, bump: &'a Bump, cxt: &Cxt<'a>, a: V) -> &'a Tm<'a> {
        let mty = if cxt.binds == 0 && matches!(v_tag(a), 3 | 5 | 6) {
            a
        } else {
            let q = self.quote(bump, &cxt.decl.borrow(), cxt.lvl, a);
            if cxt.binds == 0 && !has_free_var(q) {
                self.eval(bump, &cxt.decl.borrow(), EMPTY_ENV, q)
            } else {
                let closed = self.close_tm(bump, cxt.locals, q);
                self.eval(bump, &cxt.decl.borrow(), EMPTY_ENV, closed)
            }
        };
        let m = self.metas.len() as u32;
        self.metas.push(MetaEntry::Unsolved(mty));
        bump.alloc(Tm::AppPruning(bump.alloc(Tm::Meta(m)), cxt.pruning))
    }

    /// 沿 telescope 链闭包（Bind → 显式 Π、Define → Let）。
    fn close_tm<'a>(
        &self,
        bump: &'a Bump,
        mut ls: Option<&'a LCons<'a>>,
        q: &'a Tm<'a>,
    ) -> &'a Tm<'a> {
        let mut b = q;
        while let Some(n) = ls {
            b = match n.t_t {
                None => bump.alloc(Tm::Pi(n.name, Icit::Expl, n.a_t, b)),
                Some(t) => bump.alloc(Tm::Let(n.name, n.a_t, t, b)),
            };
            ls = n.next;
        }
        b
    }

    /// fresh meta 的求值快捷路径：掩码全为 define 槽（或空）时 AppPrun
    /// 走空转，结果恒为裸 meta 立即数——免一次 eval。
    fn eval_fresh(
        &mut self,
        bump: &Bump,
        decls: &FxHashMap<String, DeclEntryF>,
        env: Env,
        m: &Tm<'_>,
    ) -> V {
        if let Tm::AppPruning(head, pr) = m {
            // 头必须是裸 Meta 才有短路意义
            if let Tm::Meta(mm) = head {
                if pr.map_or(true, |p| p.slot.is_none() && p.after_run.is_none()) {
                    return v_meta(*mm);
                }
            }
        }
        self.eval(bump, decls, env, m)
    }

    // 内核包装（Machine 字段借出）
    // --------------------------------------------------------------------------------

    fn eval<'a>(
        &mut self,
        bump: &'a Bump,
        decls: &FxHashMap<String, DeclEntryF>,
        env: Env<'a>,
        tm: &'a Tm<'a>,
    ) -> V {
        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            mutable_map,
            fuel,
            pm_defs,
            eval_work,
            ..
        } = self;
        // SAFETY：'static 仅是存放口径（字段注释）。W 无 Drop、Vec 布局与
        // 生命周期参数无关；借出期 = 本次调用，槽内容下次借出前必 clear，
        // 任何 'a 条目都不会被以 'static 读到。
        let work: &mut Vec<W<'a>> =
            unsafe { &mut *(eval_work as *mut Vec<W<'static>> as *mut Vec<W<'a>>) };
        work.clear();
        eval_iter(
            bump,
            spine,
            work,
            vals,
            icits,
            defs,
            metas,
            decls,
            mutable_map,
            fuel,
            pm_defs,
            env,
            tm,
        )
    }

    fn quote<'a>(
        &mut self,
        bump: &'a Bump,
        decls: &FxHashMap<String, DeclEntryF>,
        level: u32,
        v: V,
    ) -> &'a Tm<'a> {
        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            mutable_map,
            fuel,
            pm_defs,
            quote_tasks,
            quote_done,
            quote_work,
            ..
        } = self;
        // SAFETY：同 eval_work——'static 存放口径，进核前 clear。
        let tasks: &mut Vec<QJob<'a>> =
            unsafe { &mut *(quote_tasks as *mut Vec<QJob<'static>> as *mut Vec<QJob<'a>>) };
        let done: &mut Vec<&'a Tm<'a>> = unsafe {
            &mut *(quote_done as *mut Vec<&'static Tm<'static>> as *mut Vec<&'a Tm<'a>>)
        };
        let work: &mut Vec<W<'a>> =
            unsafe { &mut *(quote_work as *mut Vec<W<'static>> as *mut Vec<W<'a>>) };
        tasks.clear();
        done.clear();
        work.clear();
        quote_iter(
            bump,
            spine,
            tasks,
            done,
            work,
            vals,
            icits,
            defs,
            metas,
            decls,
            mutable_map,
            fuel,
            pm_defs,
            level,
            v,
            None,
        )
    }

    /// quote 的记忆化口径（表容量跨调用复用、内容每次调用 clear，绝不跨
    /// reset 持有条目——meta 求解会让旧条目过期）。
    fn quote_memo<'a>(
        &mut self,
        bump: &'a Bump,
        decls: &FxHashMap<String, DeclEntryF>,
        level: u32,
        v: V,
    ) -> &'a Tm<'a> {
        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            mutable_map,
            fuel,
            pm_defs,
            quote_tasks,
            quote_done,
            quote_work,
            quote_memo,
            ..
        } = self;
        // SAFETY：同 eval_work——'static 存放口径，进核前 clear。
        let tasks: &mut Vec<QJob<'a>> =
            unsafe { &mut *(quote_tasks as *mut Vec<QJob<'static>> as *mut Vec<QJob<'a>>) };
        let done: &mut Vec<&'a Tm<'a>> = unsafe {
            &mut *(quote_done as *mut Vec<&'static Tm<'static>> as *mut Vec<&'a Tm<'a>>)
        };
        let work: &mut Vec<W<'a>> =
            unsafe { &mut *(quote_work as *mut Vec<W<'static>> as *mut Vec<W<'a>>) };
        let memo: &mut QuoteMemo<'a> = unsafe {
            &mut *(quote_memo as *mut QuoteMemo<'static> as *mut QuoteMemo<'a>)
        };
        tasks.clear();
        done.clear();
        work.clear();
        memo.clear();
        quote_iter(
            bump,
            spine,
            tasks,
            done,
            work,
            vals,
            icits,
            defs,
            metas,
            decls,
            mutable_map,
            fuel,
            pm_defs,
            level,
            v,
            Some(&mut *memo),
        )
    }

    fn unify<'a>(
        &mut self,
        bump: &'a Bump,
        decls: &FxHashMap<String, DeclEntryF>,
        l: u32,
        t: V,
        u: V,
    ) -> bool {
        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            mutable_map,
            ren,
            conv,
            fuel,
            pm_defs,
            pm_solvable,
            unify_work,
            unify_stack,
            ..
        } = self;
        // SAFETY：同 eval_work——'static 存放口径，进核前 clear（unify
        // 的失败早退会把非空栈留在槽里，靠入口 clear 兜住）。
        let work: &mut Vec<W<'a>> =
            unsafe { &mut *(unify_work as *mut Vec<W<'static>> as *mut Vec<W<'a>>) };
        let stack: &mut Vec<UItem<'a>> =
            unsafe { &mut *(unify_stack as *mut Vec<UItem<'static>> as *mut Vec<UItem<'a>>) };
        work.clear();
        stack.clear();
        unify_iter(
            bump,
            spine,
            work,
            stack,
            vals,
            icits,
            defs,
            metas,
            decls,
            mutable_map,
            ren,
            conv,
            fuel,
            pm_defs,
            pm_solvable,
            l,
            t,
            u,
        )
    }

    /// 错误消息（参考版 `unify_catch`：pretty + 上下文名字表 + fuel 耗尽
    /// 尾巴；快版导出项的 Span 全零，消息内容与参考版同构）。
    fn unify_catch(&mut self, bump: &Bump, cxt: &Cxt<'_>, t: V, t_prime: V) -> Result<(), Error> {
        let decls = cxt.decl.borrow();
        self.fuel.set(UNIFY_FUEL);
        if self.unify(bump, &decls, cxt.lvl, t, t_prime) {
            Ok(())
        } else {
            let fuel_note = if self.fuel.get() == 0 {
                " (fuel exhausted)"
            } else {
                ""
            };
            let tq = export(self.quote(bump, &decls, cxt.lvl, t));
            let uq = export(self.quote(bump, &decls, cxt.lvl, t_prime));
            let names = types_names_list(cxt.types);
            Err(Error(format!(
                "can't unify{} {} == {}",
                fuel_note,
                pretty_tm(0, names.clone(), &tq),
                pretty_tm(0, names, &uq),
            )))
        }
    }

    /// force 的方法包装（Machine 内 elaboration 侧的散装调用点用；解值
    /// 应用可能 β / 触发 prim / 吸收 pending——分配一律落本轮 bump）。
    fn force_v(&mut self, bump: &Bump, decls: &FxHashMap<String, DeclEntryF>, v: V) -> V {
        let Machine {
            spine,
            defs,
            metas,
            mutable_map,
            fuel,
            pm_defs,
            ..
        } = self;
        force(bump, spine, defs, metas, decls, mutable_map, fuel, pm_defs, v)
    }

    // 隐式插入（上游 Elaboration.hs 的 insert 族）
    // --------------------------------------------------------------------------------

    /// `insert'`：类型的隐式 Pi 前缀逐个补 fresh meta 实参。
    fn insert_go<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: &'a Tm<'a>,
        va: V,
    ) -> (&'a Tm<'a>, V) {
        let decls = cxt.decl.borrow();
        let va = self.force_v(bump, &decls, va);
        if v_tag(va) == 4 && v_pi_of(va).icit == Icit::Impl {
            let p = v_pi_of(va);
            let m = self.fresh_meta(bump, cxt, p.dom);
            let mv = self.eval_fresh(bump, &decls, cxt.env, m);
            let b = {
                let env = env_ext(bump, p.env, mv);
                self.eval(bump, &decls, env, p.body)
            };
            let t2 = bump.alloc(Tm::App(t, m, Icit::Impl));
            self.insert_go(bump, cxt, t2, b)
        } else {
            (t, va)
        }
    }

    /// infer 后无条件插入。
    fn insert_t<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: &'a Tm<'a>,
        va: V,
    ) -> Result<(&'a Tm<'a>, V), Error> {
        Ok(self.insert_go(bump, cxt, t, va))
    }

    /// infer 后插入，但隐式 lambda 本身免插。
    fn insert<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: &'a Tm<'a>,
        va: V,
    ) -> Result<(&'a Tm<'a>, V), Error> {
        if let Tm::Lam(_, Icit::Impl, _) = t {
            Ok((t, va))
        } else {
            self.insert_t(bump, cxt, t, va)
        }
    }

    /// `insertUntilName`：插入到名字匹配的隐式 Pi binder 为止。
    fn insert_until_name<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        name: &str,
        t: &'a Tm<'a>,
        mut va: V,
    ) -> Result<(&'a Tm<'a>, V), Error> {
        let decls = cxt.decl.borrow();
        let mut t = t;
        loop {
            let forced = self.force_v(bump, &decls, va);
            va = forced;
            if v_tag(va) == 4 && v_pi_of(va).icit == Icit::Impl {
                let p = v_pi_of(va);
                if p.name == name {
                    return Ok((t, va));
                }
                let m = self.fresh_meta(bump, cxt, p.dom);
                let mv = self.eval_fresh(bump, &decls, cxt.env, m);
                let b = {
                    let env = env_ext(bump, p.env, mv);
                    self.eval(bump, &decls, env, p.body)
                };
                t = bump.alloc(Tm::App(t, m, Icit::Impl));
                va = b;
            } else {
                return Err(Error(format!(
                    "no named implicit arg {:?}",
                    empty_span(name.to_owned())
                )));
            }
        }
    }

    // 主 check（与参考版 elaboration.rs `check` 逐臂对应）
    // --------------------------------------------------------------------------------

    fn check<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: &Raw,
        a: V,
    ) -> Result<&'a Tm<'a>, Error> {
        let decls = cxt.decl.borrow();
        // force 期望类型后分派（已解 meta 可能展开成 Pi）
        let a = self.force_v(bump, &decls, a);
        if let Raw::Lam(x, larg, tbody) = t {
            if v_tag(a) == 4 {
                let p = v_pi_of(a);
                // 参考版首臂的守卫：命名隐式 `[x = e]` 对准同名隐式 Π；
                // 显式对显式（Span 的 PartialEq 只比 data——命名 binder 按
                // 名字匹配，L06 同款语义）
                let matched = match larg {
                    Either::Name(n) => n.data == p.name && p.icit == Icit::Impl,
                    &Either::Icit(j) => j == p.icit,
                };
                if matched {
                    // 命中：按 λ 的 binder 名绑定（源码名，入名字表）
                    let name: &'a str = bump.alloc_str(&x.data);
                    let body_a = {
                        let env = env_ext(bump, p.env, v_lvl(cxt.lvl));
                        self.eval(bump, &decls, env, p.body)
                    };
                    let mark = cxt.mark;
                    let a_t = self.quote(bump, &decls, cxt.lvl, p.dom);
                    let cxt2 = self.bind_name(bump, cxt, &x.data, a_t, p.dom);
                    let body = self.check(bump, &cxt2, tbody, body_a)?;
                    self.unwind_names(mark);
                    Ok(bump.alloc(Tm::Lam(name, p.icit, body)))
                } else if p.icit == Icit::Impl {
                    // 检查到隐式 Π：补 inserted binder（Pi 侧名字，源码
                    // 不可见），整个项对余定义域重检
                    let name: &'a str = bump.alloc_str(p.name);
                    let body_a = {
                        let env = env_ext(bump, p.env, v_lvl(cxt.lvl));
                        self.eval(bump, &decls, env, p.body)
                    };
                    let mark = cxt.mark;
                    let a_t = self.quote(bump, &decls, cxt.lvl, p.dom);
                    let cxt2 = self.new_binder(bump, cxt, p.name, a_t, p.dom);
                    let body = self.check(bump, &cxt2, t, body_a)?;
                    self.unwind_names(mark);
                    Ok(bump.alloc(Tm::Lam(name, Icit::Impl, body)))
                } else {
                    // 显式 Π 上的 icit 失配：回落 general
                    let (t2, tty) = self.infer_expr(bump, cxt, t)?;
                    let (t2, tty) = self.insert(bump, cxt, t2, tty)?;
                    self.unify_catch(bump, cxt, a, tty)?;
                    Ok(t2)
                }
            } else {
                let (t2, tty) = self.infer_expr(bump, cxt, t)?;
                let (t2, tty) = self.insert(bump, cxt, t2, tty)?;
                self.unify_catch(bump, cxt, a, tty)?;
                Ok(t2)
            }
        } else if v_tag(a) == 4 && v_pi_of(a).icit == Icit::Impl {
            // 非 lambda 项检查到隐式 Π：插入隐式 binder
            let p = v_pi_of(a);
            let name: &'a str = bump.alloc_str(p.name);
            let body_a = {
                let env = env_ext(bump, p.env, v_lvl(cxt.lvl));
                self.eval(bump, &decls, env, p.body)
            };
            let mark = cxt.mark;
            let a_t = self.quote(bump, &decls, cxt.lvl, p.dom);
            let cxt2 = self.new_binder(bump, cxt, p.name, a_t, p.dom);
            let body = self.check(bump, &cxt2, t, body_a)?;
            self.unwind_names(mark);
            Ok(bump.alloc(Tm::Lam(name, Icit::Impl, body)))
        } else if let Raw::Let(x, a_ty, t2, u2) = t {
            let a_tm = self.check(bump, cxt, a_ty, v_u())?;
            let va = self.eval(bump, &decls, cxt.env, a_tm);
            let t_tm = self.check(bump, cxt, t2, va)?;
            let vt = self.eval(bump, &decls, cxt.env, t_tm);
            let name: &'a str = bump.alloc_str(&x.data);
            let mark = cxt.mark;
            let cxt2 = self.define_name(bump, cxt, &x.data, a_tm, t_tm, vt, va);
            let u_tm = self.check(bump, &cxt2, u2, a)?;
            self.unwind_names(mark);
            Ok(bump.alloc(Tm::Let(name, a_tm, t_tm, u_tm)))
        } else if let Raw::Hole = t {
            // hole：以 fresh meta 填充（类型 = 期望类型）
            Ok(self.fresh_meta(bump, cxt, a))
        } else if let Raw::Match(expr, clauses) = t {
            // match：编译（特化合一在编译期完成）+ 逐分支检查
            let (tm, typ) = self.infer_expr(bump, cxt, expr)?;
            let mut compiler = Compiler::new();
            compiler.compile(self, bump, typ, tm, clauses, cxt, a)?;
            let cs: &'a [(PatternDetail, &'a Tm<'a>)] =
                bump.alloc_slice_fill_iter(compiler.pats.into_iter());
            Ok(bump.alloc(Tm::Match(tm, cs)))
        } else {
            let (t2, tty) = self.infer_expr(bump, cxt, t)?;
            let (t2, tty) = self.insert(bump, cxt, t2, tty)?;
            self.unify_catch(bump, cxt, a, tty)?;
            Ok(t2)
        }
    }

    // 主 infer / infer_expr（与参考版 elaboration.rs 逐臂对应）
    // --------------------------------------------------------------------------------

    fn infer_expr<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: &Raw,
    ) -> Result<(&'a Tm<'a>, V), Error> {
        let decls = cxt.decl.borrow();
        match t {
            // 变量：先局部（src_names / name_map），再全局（decl 表）
            Raw::Var(x) => {
                if !NO_NAME_MAP.load(std::sync::atomic::Ordering::Relaxed) {
                    if let Some(&(blvl, ty)) = self.name_map.get(x.data.as_str()) {
                        return Ok((bump.alloc(Tm::Var(cxt.lvl - blvl - 1)), ty));
                    }
                } else {
                    // 消融口径：沿 types 链线性找名（跳过 inserted binder）
                    let mut i = 0u32;
                    let mut tys = cxt.types;
                    while let Some(tc) = tys {
                        if tc.source && tc.name == x.data {
                            return Ok((bump.alloc(Tm::Var(i)), tc.ty));
                        }
                        i += 1;
                        tys = tc.next;
                    }
                }
                if let Some(e) = cxt.decl.borrow().get(x.data.as_str()) {
                    return Ok((bump.alloc(Tm::Decl(bump.alloc_str(&x.data))), e.ty));
                }
                Err(Error(format!("name not in scope: {}", x.data)))
            }

            Raw::Obj(x, f) => {
                // 限定构造子引用 `Enum.case`——**局部遮蔽优先**：接收者名字
                // 已被局部 binder 占用时必须走正常投影（与 Raw::Var 的
                // 「局部先于全局」同序），否则同名局部会让 `Foo.c2` 静默
                // 解析成全局构造子（类型恰巧对上即是错误的 Ok）
                if let Raw::Var(n) = &**x {
                    let shadowed = if !NO_NAME_MAP.load(std::sync::atomic::Ordering::Relaxed)
                    {
                        self.name_map.contains_key(n.data.as_str())
                    } else {
                        // 消融口径：沿 types 链线性找名（跳过 inserted binder）
                        let mut tys = cxt.types;
                        loop {
                            match tys {
                                Some(tc) if tc.source && tc.name == n.data => break true,
                                Some(tc) => tys = tc.next,
                                None => break false,
                            }
                        }
                    };
                    if !shadowed {
                        let key = format!("{}.{}", n.data, f.data);
                        if let Some(e) = cxt.decl.borrow().get(key.as_str()) {
                            return Ok((bump.alloc(Tm::Decl(bump.alloc_str(&key))), e.ty));
                        }
                    }
                }
                let (tm, ty) = self.infer_expr(bump, cxt, x)?;
                let tyf = self.force_v(bump, &decls, ty);
                if v_tag(tyf) == 7 {
                    if let XCell::Sum {
                        name: sname,
                        params,
                        cases,
                    } = v_xcell_of(tyf)
                    {
                        // 接收者类型是 Sum：索引/参数槽优先取类型槽；未命中
                        // 且是 **struct**（单 case、名字形如 `{Name}.mk`）时
                        // 剥 `mk` 的构造子类型链取字段类型——与参考版
                        // elaboration 的 `Raw::Obj` 臂逐句对应。隐式参数用
                        // 头部 Sum 实参实例化；显式字段 binder 用接收者的
                        // **卡住投影值**实例化（`eval(Obj(接收者项, 字段名))`，
                        // 如 `Exists.proof` 剥出 `Eq e.witness two`）。旧实现
                        // 以 `U` 占位，依赖在前字段的在后字段在检查位会假拒，
                        // 修正于评审，两版同步。
                        if let Some(p) = params.iter().find(|p| p.name == f.data) {
                            return Ok((
                                bump.alloc(Tm::Obj(tm, bump.alloc_str(&f.data))),
                                p.ty,
                            ));
                        }
                        if cases.len() == 1 && cases[0].contains(".mk") {
                            let ctor_ty = cxt.decl.borrow().get(cases[0]).map(|e| e.ty);
                            if let Some(mut ty) = ctor_ty {
                                let impl_vals: Vec<V> = params
                                    .iter()
                                    .filter(|p| p.icit == Icit::Impl)
                                    .map(|p| p.val)
                                    .collect();
                                let mut impl_idx = 0;
                                loop {
                                    let tyf2 = self.force_v(bump, &decls, ty);
                                    if v_tag(tyf2) == 4 {
                                        let p = v_pi_of(tyf2);
                                        if p.name == f.data {
                                            return Ok((
                                                bump.alloc(Tm::Obj(tm, bump.alloc_str(&f.data))),
                                                p.dom,
                                            ));
                                        }
                                        let u = if impl_idx < impl_vals.len() {
                                            let v = impl_vals[impl_idx];
                                            impl_idx += 1;
                                            v
                                        } else {
                                            let obj =
                                                bump.alloc(Tm::Obj(tm, bump.alloc_str(p.name)));
                                            self.eval(bump, &decls, cxt.env, obj)
                                        };
                                        let env = env_ext(bump, p.env, u);
                                        ty = self.eval(bump, &decls, env, p.body);
                                    } else {
                                        break;
                                    }
                                }
                            }
                        }
                        return Err(Error(format!("{} has no field {}", sname, f.data)));
                    }
                    if let XCell::SumCase {
                        typ,
                        case_name,
                        datas,
                    } = v_xcell_of(tyf)
                    {
                        // 接收者类型是构造子值：索引参数优先，否则剥构造子
                        // 类型取字段真实类型
                        let (sname, sparams) = match v_xcell_of(*typ) {
                            XCell::Sum { name, params, .. } => (*name, *params),
                            _ => return Err(Error(" ill-scoped SumCase".to_owned())),
                        };
                        if let Some(p) = sparams.iter().find(|p| p.name == f.data) {
                            return Ok((
                                bump.alloc(Tm::Obj(tm, bump.alloc_str(&f.data))),
                                p.ty,
                            ));
                        }
                        let ctor_ty = cxt
                            .decl
                            .borrow()
                            .get(&format!("{}.{}", sname, case_name))
                            .ok_or_else(|| Error("missing constructor decl".to_owned()))?
                            .ty;
                        let impl_vals: Vec<V> = sparams
                            .iter()
                            .filter(|p| p.icit == Icit::Impl)
                            .map(|p| p.val)
                            .collect();
                        let mut ty = ctor_ty;
                        let mut impl_idx = 0;
                        loop {
                            let tyf2 = self.force_v(bump, &decls, ty);
                            if v_tag(tyf2) == 4 {
                                let p = v_pi_of(tyf2);
                                if p.name == f.data {
                                    return Ok((
                                        bump.alloc(Tm::Obj(tm, bump.alloc_str(&f.data))),
                                        p.dom,
                                    ));
                                }
                                let u = if impl_idx < impl_vals.len() {
                                    let v = impl_vals[impl_idx];
                                    impl_idx += 1;
                                    v
                                } else {
                                    match datas.iter().find(|d| d.name == p.name) {
                                        Some(d) => d.val,
                                        None => {
                                            return Err(Error(format!(
                                                "no field {} on {}",
                                                f.data, sname
                                            )))
                                        }
                                    }
                                };
                                let env = env_ext(bump, p.env, u);
                                ty = self.eval(bump, &decls, env, p.body);
                            } else {
                                return Err(Error(format!(
                                    "{} has no field {}",
                                    sname, f.data
                                )));
                            }
                        }
                    }
                }
                Err(Error(format!("cannot project field {}", f.data)))
            }

            // λ 推断：域用 fresh meta，值域闭包封口
            Raw::Lam(x, Either::Icit(i), tbody) => {
                let name: &'a str = bump.alloc_str(&x.data);
                let new_meta = self.fresh_meta(bump, cxt, v_u());
                let a = self.eval_fresh(bump, &decls, cxt.env, new_meta);
                let mark = cxt.mark;
                let a_t = self.quote(bump, &decls, cxt.lvl, a);
                let cxt2 = self.bind_name(bump, cxt, &x.data, a_t, a);
                let (t_inferred, b) = self.infer_expr(bump, &cxt2, tbody)?;
                let (t_inferred, b) = self.insert(bump, &cxt2, t_inferred, b)?;
                self.unwind_names(mark);
                // closeVal：quote 在 lvl+1——给即将到来的 binder 留第 0 槽
                let body = self.quote(bump, &decls, cxt.lvl + 1, b);
                let cell = bump.alloc(PiCell {
                    name,
                    icit: *i,
                    dom: a,
                    env: cxt.env,
                    body,
                });
                Ok((bump.alloc(Tm::Lam(name, *i, t_inferred)), v_pi(cell)))
            }

            Raw::Lam(x, Either::Name(_), _) => {
                Err(Error(format!("infer named lambda {:?}", x)))
            }

            // 应用
            Raw::App(t, u, arg) => {
                // 实参分派：命名 → insertUntilName 后按 Impl 应用；
                // 位置 Impl → 直接应用；位置 Expl → 先 insert_t
                let (i, t, tty) = match arg {
                    Either::Name(name) => {
                        let (t, tty) = self.infer_expr(bump, cxt, t)?;
                        let (t, tty) = self.insert_until_name(bump, cxt, &name.data, t, tty)?;
                        (Icit::Impl, t, tty)
                    }
                    Either::Icit(Icit::Impl) => {
                        let (t, tty) = self.infer_expr(bump, cxt, t)?;
                        (Icit::Impl, t, tty)
                    }
                    Either::Icit(Icit::Expl) => {
                        let (t, tty) = self.infer_expr(bump, cxt, t)?;
                        let (t, tty) = self.insert_t(bump, cxt, t, tty)?;
                        (Icit::Expl, t, tty)
                    }
                };
                let tty = self.force_v(bump, &decls, tty);
                let (a, bcell) = if v_tag(tty) == 4 {
                    let p = v_pi_of(tty);
                    if p.icit != i {
                        return Err(Error(format!("icit mismatch {:?} {:?}", i, p.icit)));
                    }
                    (p.dom, p)
                } else {
                    // 非 Π 头：合成 Π（定义域 + 余定义域挂洞）与之合一。
                    // 合成 binder（PI_NAME）不进名字表：只延伸 env/telescope/
                    // pruning。参数序：期望 = 合成 Π（参考版把合成 Π 放在
                    // unify_catch 的首位——忠实复刻，只影响报错文案方向）。
                    let new_meta = self.fresh_meta(bump, cxt, v_u());
                    let a = self.eval_fresh(bump, &decls, cxt.env, new_meta);
                    let a_t = self.quote(bump, &decls, cxt.lvl, a);
                    let cxt2 = Cxt {
                        env: env_ext(bump, cxt.env, v_lvl(cxt.lvl)),
                        types: cxt.types,
                        locals: Some(bump.alloc(LCons {
                            name: PI_NAME,
                            a_t,
                            t_t: None,
                            next: cxt.locals,
                        })),
                        pruning: Some(bump.alloc(PrCons::new(Some(Icit::Expl), cxt.pruning))),
                        binds: cxt.binds + 1, // 合成 binder 也是绑定槽
                        lvl: cxt.lvl + 1,
                        mark: cxt.mark,
                        decl: cxt.decl.clone(),
                    };
                    let cod_meta = self.fresh_meta(bump, &cxt2, v_u());
                    let cell = bump.alloc(PiCell {
                        name: PI_NAME,
                        icit: i,
                        dom: a,
                        env: cxt.env,
                        body: cod_meta,
                    });
                    self.unify_catch(bump, cxt, v_pi(cell), tty)?;
                    (a, &*cell)
                };
                let u_checked = self.check(bump, cxt, u, a)?;
                let arg_v = self.eval(bump, &decls, cxt.env, u_checked);
                // t u : B[x |-> u]
                let ty = {
                    let env = env_ext(bump, bcell.env, arg_v);
                    self.eval(bump, &decls, env, bcell.body)
                };
                Ok((bump.alloc(Tm::App(t, u_checked, i)), ty))
            }

            Raw::U => Ok((bump.alloc(Tm::U), v_u())),

            Raw::Pi(x, i, a, b) => {
                let a_tm = self.check(bump, cxt, a, v_u())?;
                let va = self.eval(bump, &decls, cxt.env, a_tm);
                let name: &'a str = bump.alloc_str(&x.data);
                let mark = cxt.mark;
                let a_t = self.quote(bump, &decls, cxt.lvl, va);
                let cxt2 = self.bind_name(bump, cxt, &x.data, a_t, va);
                let b_tm = self.check(bump, &cxt2, b, v_u())?;
                self.unwind_names(mark);
                Ok((bump.alloc(Tm::Pi(name, *i, a_tm, b_tm)), v_u()))
            }

            Raw::Let(x, a_ty, t2, u2) => {
                let a_tm = self.check(bump, cxt, a_ty, v_u())?;
                let va = self.eval(bump, &decls, cxt.env, a_tm);
                let t_tm = self.check(bump, cxt, t2, va)?;
                let vt = self.eval(bump, &decls, cxt.env, t_tm);
                let name: &'a str = bump.alloc_str(&x.data);
                let mark = cxt.mark;
                let cxt2 = self.define_name(bump, cxt, &x.data, a_tm, t_tm, vt, va);
                let (u_tm, uty) = self.infer_expr(bump, &cxt2, u2)?;
                self.unwind_names(mark);
                Ok((bump.alloc(Tm::Let(name, a_tm, t_tm, u_tm)), uty))
            }

            Raw::Hole => {
                let new_meta = self.fresh_meta(bump, cxt, v_u());
                let a = self.eval_fresh(bump, &decls, cxt.env, new_meta);
                let t = self.fresh_meta(bump, cxt, a);
                Ok((t, a))
            }

            Raw::LiteralIntro(literal) => Ok((
                bump.alloc(Tm::LiteralIntro(bump.alloc_str(&literal.data))),
                v_lit_ty(),
            )),

            // match 只能在检查模式下使用（期望类型决定分支体怎么查）
            Raw::Match(..) => Err(Error(
                "match cannot be inferred; give it an expected type".to_owned(),
            )),

            // enum 本体（Decl::Enum 注册期构造）：逐参数推断值 + 引读类型
            Raw::Sum(name, params, cases) => {
                let mut ps: Vec<SumParamT<'_>> = Vec::with_capacity(params.len());
                for (n, i, raw) in params {
                    let (value_checked, value_ty) = self.infer_expr(bump, cxt, raw)?;
                    let ty = self.quote(bump, &decls, cxt.lvl, value_ty);
                    ps.push(SumParamT {
                        name: bump.alloc_str(&n.data),
                        val: value_checked,
                        ty,
                        icit: *i,
                    });
                }
                let cs: Vec<&'a str> = cases.iter().map(|c| &*bump.alloc_str(&c.data)).collect();
                Ok((
                    bump.alloc(Tm::Sum(
                        bump.alloc_str(&name.data),
                        bump.alloc_slice_fill_iter(ps),
                        bump.alloc_slice_fill_iter(cs),
                    )),
                    v_u(),
                ))
            }

            // 构造子值（Decl::Enum 注册期构造）：typ 只推断不检查
            Raw::SumCase {
                typ,
                case_name,
                datas,
            } => {
                let (typ_checked, _) = self.infer_expr(bump, cxt, typ)?;
                let typ_val = self.eval(bump, &decls, cxt.env, typ_checked);
                let mut ds: Vec<SumDataT<'_>> = Vec::with_capacity(datas.len());
                for (n, raw, i) in datas {
                    let (tm, _) = self.infer_expr(bump, cxt, raw)?;
                    ds.push(SumDataT {
                        name: bump.alloc_str(&n.data),
                        val: tm,
                        icit: *i,
                    });
                }
                Ok((
                    bump.alloc(Tm::SumCase {
                        typ: typ_checked,
                        case_name: bump.alloc_str(&case_name.data),
                        datas: bump.alloc_slice_fill_iter(ds),
                    }),
                    typ_val,
                ))
            }
        }
    }

    /// decl 层的推断（参考版 `Infer::infer(Decl)`）：Def 折叠参数后检查，
    /// **占位 → 检查 → force 到 WHNF → 覆盖登记**（副作用在声明序上驱动
    /// ——递归自引用由 force 的占位守卫兜住）；Println 推断体；Enum 注册
    /// 类型本体 + 逐构造子（限定名 `Enum.case` + 裸名别名）。
    fn infer_decl<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        d: &Decl,
    ) -> Result<(DeclOut<'a>, Cxt<'a>), Error> {
        match d {
            Decl::Def {
                name,
                params,
                ret_type,
                body,
            } => {
                // 参数折叠：typ = Π 参数. 返回类型；bod = λ 参数. 体。
                // 无参时零克隆（借用直用），有参才构造包装层
                let mut typ = std::borrow::Cow::Borrowed(ret_type);
                for (n, a, i) in params.iter().rev() {
                    typ = std::borrow::Cow::Owned(Raw::Pi(
                        n.clone(),
                        *i,
                        Box::new(a.clone()),
                        Box::new(typ.into_owned()),
                    ));
                }
                let mut bod = std::borrow::Cow::Borrowed(body);
                for (n, _, i) in params.iter().rev() {
                    bod = std::borrow::Cow::Owned(Raw::Lam(
                        n.clone(),
                        Either::Icit(*i),
                        Box::new(bod.into_owned()),
                    ));
                }
                // 借用块化：Ref 带 Drop，作用域尾才释放——顶层的借力会压到
                // 整个 match，与后面的 decl_insert（borrow_mut）冲突
                let vtyp = {
                    let decls = cxt.decl.borrow();
                    let typ_tm = self.check(bump, cxt, &typ, v_u())?;
                    self.eval(bump, &decls, cxt.env, typ_tm)
                };
                // 递归：先把名字登记成指向自身的中性占位，检查体，再用真实
                // 值覆盖。占位只存在于克隆出来的 decl 表里，不影响外层。
                let fake = decl_insert(
                    cxt,
                    &name.data,
                    DeclEntryF {
                        ty: vtyp,
                        val: v_xcell(bump.alloc(XCell::Decl(bump.alloc_str(&name.data)))),
                    },
                );
                // decls_f 块化：Ref 带 Drop（作用域尾释放），必须在
                // 终值覆盖的 decl_insert 之前释放
                let vt = {
                    let decls_f = fake.decl.borrow();
                    let t_tm = self.check(bump, &fake, &bod, vtyp)?;
                    // 注册值归约到 WHNF：builtin 副作用（可变全局写 / 文件
                    // IO）在声明序上驱动——L06「应用时触发」的等价物（否则
                    // change_mutable 等只在别处 force 到它时才生效）。
                    let v = self.eval(bump, &decls_f, fake.env, t_tm);
                    self.force_v(bump, &decls_f, v)
                };
                let out = decl_insert(cxt, &name.data, DeclEntryF { ty: vtyp, val: vt });
                Ok((DeclOut::Def { name: bump.alloc_str(&name.data) }, out))
            }
            Decl::Println(t) => {
                let (tm, _) = self.infer_expr(bump, cxt, t)?;
                Ok((DeclOut::Println(tm), Cxt { env: cxt.env, types: cxt.types, locals: cxt.locals, pruning: cxt.pruning, binds: cxt.binds, lvl: cxt.lvl, mark: cxt.mark, decl: cxt.decl.clone() }))
            }
            Decl::Enum {
                name,
                params,
                cases,
            } => {
                // enum 类型本体：λ params → Sum(name, [(p, Var p, ?, icit)], cases)
                let new_params: Vec<(crate::parser_lib::Span<String>, Icit, Raw)> = params
                    .iter()
                    .map(|x| (x.0.clone(), x.2, Raw::Var(x.0.clone())))
                    .collect();
                // 构造子缺省返回类型：Name 逐个应用到隐式参数（显式索引留给
                // 构造子的 -> 给出）
                let default_ret = params
                    .iter()
                    .filter(|x| x.2 == Icit::Impl)
                    .fold(Raw::Var(name.clone()), |ret, x| {
                        Raw::App(
                            Box::new(ret),
                            Box::new(Raw::Var(x.0.clone())),
                            Either::Icit(Icit::Impl),
                        )
                    });
                // 构造子类型：Pi(枚举隐式参数 ++ 构造子绑定器) -> (用户 ret || 缺省)
                let new_cases: Vec<(crate::parser_lib::Span<String>, Raw)> = cases
                    .iter()
                    .map(|(case_name, p, bind)| {
                        let ty = params
                            .iter()
                            .filter(|x| x.2 == Icit::Impl)
                            .cloned()
                            .chain(p.clone())
                            .rev()
                            .fold(
                                bind.clone().unwrap_or(default_ret.clone()),
                                |ret, x| {
                                    Raw::Pi(x.0.clone(), x.2, Box::new(x.1.clone()), Box::new(ret))
                                },
                            );
                        (case_name.clone(), ty)
                    })
                    .collect::<Vec<_>>();
                let cases_spanned: Vec<crate::parser_lib::Span<String>> = new_cases
                    .iter()
                    .map(|(n, _)| n.clone())
                    .collect();
                let sum = Raw::Sum(name.clone(), new_params, cases_spanned);
                let typ = params
                    .iter()
                    .rev()
                    .fold(Raw::U, |a, b| {
                        Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a))
                    });
                let bod = params.iter().rev().fold(sum, |a, b| {
                    Raw::Lam(b.0.clone(), Either::Icit(b.2), Box::new(a))
                });
                let vtyp = {
                    let decls = cxt.decl.borrow();
                    let typ_tm = self.check(bump, cxt, &typ, v_u())?;
                    self.eval(bump, &decls, cxt.env, typ_tm)
                };
                // 先占位再检查本体（本体内部引用自身时报"指向自身的中性值"）
                let fake = decl_insert(
                    cxt,
                    &name.data,
                    DeclEntryF {
                        ty: vtyp,
                        val: v_xcell(bump.alloc(XCell::Decl(bump.alloc_str(&name.data)))),
                    },
                );
                // decls_f 块化（同 Def 臂：Ref 作用域尾释放）
                let vt = {
                    let decls_f = fake.decl.borrow();
                    let t_tm = self.check(bump, &fake, &bod, vtyp)?;
                    self.eval(bump, &decls_f, fake.env, t_tm)
                };
                let mut cxt = decl_insert(cxt, &name.data, DeclEntryF { ty: vtyp, val: vt });
                // 逐构造子注册：体 = λ(隐式参数, 字段) → SumCase{typ: ret, datas: 字段自身}
                for ((case_name, binders, ret), (ctor_name, ctor_ty)) in
                    cases.iter().zip(new_cases.iter())
                {
                    let body_ret = Raw::SumCase {
                        typ: Box::new(ret.clone().unwrap_or(default_ret.clone())),
                        case_name: case_name.clone(),
                        datas: binders
                            .iter()
                            .map(|(n, _, i)| (n.clone(), Raw::Var(n.clone()), *i))
                            .collect(),
                    };
                    let bod = params
                        .iter()
                        .filter(|x| x.2 == Icit::Impl)
                        .cloned()
                        .chain(binders.clone())
                        .rev()
                        .fold(body_ret, |a, b| {
                            Raw::Lam(b.0.clone(), Either::Icit(b.2), Box::new(a))
                        });
                    // 借用作用域化：decls_c 必须在 decl_insert（borrow_mut）
                    // 之前释放；entry 是 Copy 可逃逸
                    let entry = {
                        let decls_c = cxt.decl.borrow();
                        let typ_tm = self.check(bump, &cxt, ctor_ty, v_u())?;
                        let vtyp = self.eval(bump, &decls_c, cxt.env, typ_tm);
                        let t_tm = self.check(bump, &cxt, &bod, vtyp)?;
                        let vt = self.eval(bump, &decls_c, cxt.env, t_tm);
                        DeclEntryF { ty: vtyp, val: vt }
                    };
                    // 限定名 `Enum.case` + 裸名别名（后注册者覆盖同名裸名）
                    cxt = decl_insert(
                        &cxt,
                        &format!("{}.{}", name.data, ctor_name.data),
                        entry,
                    );
                    cxt = decl_insert(&cxt, &ctor_name.data, entry);
                }
                Ok((DeclOut::Enum, cxt))
            }
        }
    }
}

/// decl 层推断的产出：Def 带名（bench 的 nf 口径按名查表），Println 带
/// elaborated 体（run 的 nf 输出用）。
enum DeclOut<'a> {
    Def { name: &'a str },
    Println(&'a Tm<'a>),
    Enum,
}

/// 项里是否含自由 `Var`（按 binder 深度算）。`fresh_meta` 快捷路径 2 的
/// 判据（保守：自由 ⇒ 走全构造）。
fn has_free_var(t: &Tm<'_>) -> bool {
    let mut stack: Vec<(&Tm<'_>, u32)> = vec![(t, 0)];
    while let Some((x, d)) = stack.pop() {
        match x {
            Tm::Var(i) => {
                if *i >= d {
                    return true;
                }
            }
            Tm::Lam(_, _, b) => stack.push((b, d + 1)),
            Tm::App(f, a, _) => {
                stack.push((f, d));
                stack.push((a, d));
            }
            Tm::AppPruning(h, _) => stack.push((h, d)),
            Tm::U | Tm::Meta(_) | Tm::LiteralType | Tm::LiteralIntro(_) | Tm::Decl(_)
            | Tm::Prim(_) => {}
            Tm::Obj(h, _) => stack.push((h, d)),
            Tm::Pi(_, _, a, b) => {
                stack.push((a, d));
                stack.push((b, d + 1));
            }
            Tm::Let(_, a, t, u) => {
                stack.push((a, d));
                stack.push((t, d));
                stack.push((u, d + 1));
            }
            Tm::Sum(_, params, _) => {
                for p in params.iter() {
                    stack.push((p.val, d));
                    stack.push((p.ty, d));
                }
            }
            Tm::SumCase { typ, datas, .. } => {
                stack.push((typ, d));
                for dd in datas.iter() {
                    stack.push((dd.val, d));
                }
            }
            Tm::Match(s, cases) => {
                stack.push((s, d));
                for (_, b) in cases.iter() {
                    stack.push((b, d));
                }
            }
        }
    }
    false
}

// Elaboration 上下文与 decl 表（写时复制）
// --------------------------------------------------------------------------------

/// Elaboration 上下文（绑定量在 bump 里）。`decl` = Rc 写时复制的全局
/// decl 表（参考版 `Cxt::decl_insert` 的 `Rc::make_mut` 语义）。方法一律
/// 借用 `&Cxt`（Rc 非 Copy——扩展上下文返回**新的** Cxt 值）。
struct Cxt<'a> {
    env: Env<'a>,
    /// type of every variable in scope（头 = 最内层；`source` 标记源码
    /// binder——消融口径的线性找名跳过非源码条目；println 的 pretty 名
    /// 单也走这里，与参考版 `Cxt::names()` 的 locals 序一致）。
    types: Option<&'a TCons<'a>>,
    /// telescope（上游 `cxtLocals`）：fresh_meta 闭类型用。
    locals: Option<&'a LCons<'a>>,
    /// fresh meta 的 scope 掩码（与 env 平行；头 = 最内层）。
    pruning: Option<&'a PrCons<'a>>,
    /// 绑定层数（bind/new_binder/synth +1，define 不动）。
    binds: u32,
    lvl: u32,
    /// 名字撤销轨迹的本上下文基线（inserted binder 不留轨迹、不动 mark）。
    mark: u32,
    /// 全局 decl 表（名 → (类型值, WHNF 值)）：def / enum / 构造子都登记
    /// 在这里；项层引用 `Tm::Decl(名)` 求值时查表取缓存的 WHNF。
    /// RefCell 共享可变：decl_insert **平铺覆盖**（O(1)，不克隆整表）——
    /// 顶层 elaboration 的插入全部单调（占位 → 同名覆盖为终值），平铺表
    /// 与参考版写时复制在该使用形态下语义等价；检查期间无插入（插入只在
    /// decl 边界），borrow 纪律成立。
    decl: Rc<RefCell<FxHashMap<String, DeclEntryF>>>,
}

/// scope 里的一项：名字 + 类型值 + 来源（源码 binder / inserted binder）。
struct TCons<'a> {
    name: &'a str,
    ty: V,
    source: bool,
    next: Option<&'a TCons<'a>>,
}

impl<'a> Cxt<'a> {
    fn empty() -> Self {
        Cxt {
            env: EMPTY_ENV,
            types: None,
            locals: None,
            pruning: None,
            binds: 0,
            lvl: 0,
            mark: 0,
            decl: Rc::new(RefCell::new(FxHashMap::default())),
        }
    }
}

/// 写入一个 decl。**平铺覆盖**（O(1)）：顶层 elaboration 的插入全部
/// 单调（占位 → 同名覆盖为终值），RefCell 共享同一张表——递归定义的
/// "占位只对本定义的检查可见"由覆盖时序保证（占位先插、终值后插同名
/// 键，查表取后者）。写时复制克隆整表是 O(n)/次 → def 链 O(n²)
/// （strchain k=12 实测 830ms 的根因），平铺后 ~13ms。
fn decl_insert<'a>(cxt: &Cxt<'a>, k: &str, e: DeclEntryF) -> Cxt<'a> {
    {
        let mut d = cxt.decl.borrow_mut();
        // 覆盖写（占位 → 终值）不重分配键串
        match d.get_mut(k) {
            Some(slot) => *slot = e,
            None => {
                d.insert(k.to_string(), e);
            }
        }
    }
    Cxt {
        env: cxt.env,
        types: cxt.types,
        locals: cxt.locals,
        pruning: cxt.pruning,
        binds: cxt.binds,
        lvl: cxt.lvl,
        mark: cxt.mark,
        decl: cxt.decl.clone(),
    }
}

/// 当前上下文里"真变量"（bind 槽，env 槽仍指向自身 vvar）的层级集合：
/// 这些是模式特化方程可以求解的对象。let 定义槽（槽里是值不是 vvar）天然
/// 不在其中。（参考版 `Cxt::bind_slots` 同款过滤。）
fn bind_slots(defs: &[V], cxt: &Cxt<'_>) -> Vec<u32> {
    let n = cxt.lvl;
    let len = env_len(cxt.env);
    let mut out = Vec::new();
    for i in 0..len {
        let v = env_nth(defs, cxt.env, i);
        if v_tag(v) == 0 {
            let l = v_lvl_of(v);
            if l + i + 1 == n {
                out.push(l);
            }
        }
    }
    out
}

/// types 链 → 参考版 pretty 的名字 List（头 = 最内层；List::prepend 从尾
/// 起构回，序不变）。
fn types_names_list(tys: Option<&TCons<'_>>) -> crate::list::List<String> {
    let mut ns: Vec<String> = Vec::new();
    let mut cur = tys;
    while let Some(tc) = cur {
        ns.push(tc.name.to_owned());
        cur = tc.next;
    }
    let mut list = crate::list::List::new();
    for n in ns.into_iter().rev() {
        list = list.prepend(n);
    }
    list
}

// 模式匹配编译（参考版 pattern_match.rs 的逐句移植）
// --------------------------------------------------------------------------------

/// 把 `match` 的 (模式, 分支体) 列表编译成 `Vec<(PatternDetail, Tm)>`，
/// 并做覆盖性 / 可达性检查。特化方程解得出 = 分支可达且解就是精化；结构
/// 冲突 = 分支不可能（absurd）。逐臂下钻保持用户书写顺序，运行时首匹配 =
/// 用户语义；通配臂之后的所有臂不可达（跳过）。
struct Compiler<'a> {
    /// 收集所有错误（覆盖缺失 / 分支不可达），一次报全。
    errors: Vec<String>,
    pats: Vec<(PatternDetail, &'a Tm<'a>)>,
}

enum Walk<'a> {
    Matched(PatternDetail, Cxt<'a>),
    Unreachable,
}

/// `Sum` 值的构造子名表（覆盖检查用）。
fn sum_case_names(v: V) -> Vec<String> {
    match v_xcell_of(v) {
        XCell::Sum { cases, .. } => cases.iter().map(|c| c.to_string()).collect(),
        _ => Vec::new(),
    }
}

/// 顶层覆盖判定：通配 / 变量模式覆盖一切；Con 只覆盖同名构造子。
fn covers(pat: &Pattern, ctor: &str, ctor_names: &[String]) -> bool {
    match pat {
        Pattern::Any(..) => true,
        Pattern::Con(name, _, _) => {
            !ctor_names.iter().any(|c| c == &name.data) || name.data == ctor
        }
    }
}

/// 通配臂：覆盖所有取值的臂（其后的臂不可达）。
fn is_catch_all(pat: &Pattern, ctor_names: &[String]) -> bool {
    match pat {
        Pattern::Any(..) => true,
        Pattern::Con(name, subs, _) => {
            subs.is_empty() && !ctor_names.iter().any(|c| c == &name.data)
        }
    }
}

impl<'a> Compiler<'a> {
    fn new() -> Self {
        Compiler {
            errors: Vec::new(),
            pats: Vec::new(),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn compile(
        &mut self,
        mach: &mut Machine,
        bump: &'a Bump,
        scrut_ty: V,
        scrut: &'a Tm<'a>,
        arms: &[(Pattern, Raw)],
        cxt: &Cxt<'a>,
        expected: V,
    ) -> Result<(), Error> {
        let decls = cxt.decl.borrow();
        // 被匹配对象的值（在 match 现场求值）：用于把"被匹配的变量本身"
        // 写入精化事实表（见 walk_con 末尾）
        let head_val = mach.eval(bump, &decls, cxt.env, scrut);
        // 编译期间的所有合一共享一个 fuel 池（深层递归防护）
        mach.fuel.set(UNIFY_FUEL);
        let head_sum = mach.force_v(bump, &decls, scrut_ty);
        if !(v_tag(head_sum) == 7 && matches!(v_xcell_of(head_sum), XCell::Sum { .. })) {
            return Err(Error("match 的对象必须是和类型（enum）".to_owned()));
        }
        let ctor_names = sum_case_names(head_sum);
        // 可解集基线：当前上下文的全部 bind 槽（def 参数 / λ 参数 / 外层
        // 模式变量）。走查中新绑的模式槽在此基础上追加；臂边界与探测回滚。
        let entry = mach.pm_mark();
        for l in bind_slots(&mach.defs, cxt) {
            mach.pm_solvable.push(l);
        }
        // 覆盖检查：每个可达构造子必须被某个臂覆盖（通配臂覆盖全部）。
        // 可达性 = 在快照回滚下跑一次特化方程（与臂内走查同一套判定）。
        for ctor in sum_case_names(head_sum) {
            if Self::probe_accessible(mach, bump, cxt, head_sum, &ctor)
                && !arms.iter().any(|(pat, _)| covers(pat, &ctor, &ctor_names))
            {
                self.errors
                    .push(format!("match 不完整：缺少构造子 {}", ctor));
            }
        }
        // 逐臂下钻。一旦出现通配臂（覆盖所有取值），后续臂运行时永远不会
        // 被选中——保持用户顺序的首匹配语义即可，被遮蔽的臂跳过。
        let mut shadowed = false;
        for (pat, body) in arms {
            if shadowed {
                continue;
            }
            let mark = mach.pm_mark();
            // 臂边界同时是名字轨迹的基线：walk_con 经 bind_name 压入的
            // 模式绑定不在臂检查的 unwind 范围内，臂结束后显式截断
            // （参考版 src_names 随 Cxt 克隆天然隔离，快版轨迹需手动回滚）
            let name_mark = mach.name_mark();
            match self.walk(mach, bump, pat, scrut_ty, head_val, cxt)? {
                Walk::Matched(detail, cxt_arm) => {
                    // 分支体走**常规转换**检查（可解集摘走——体检查不得解
                    // 假设）。
                    let saved_solvable = std::mem::take(&mut mach.pm_solvable);
                    // 期望类型**重锚**到臂上下文：quote → eval 把其中所有
                    // rigid 引用重定向到臂 env（quote 时 defs 活跃，精化等
                    // 式一并烘焙进去）。语义上不重锚也正确（force 惰性展开
                    // defs），但值层面只有重锚后，期望里的卡住 match 与
                    // meta 解物化出来的副本才有同样的 env 布局——unify 的
                    // 结构快路径（struct_eq）才能命中。
                    let decls_arm = cxt_arm.decl.borrow();
                    let ret_type = {
                        let t = mach.force_v(bump, &decls_arm, expected);
                        if mach.is_flex_v(t) {
                            t
                        } else {
                            let tm = mach.quote(bump, &decls_arm, cxt_arm.lvl, t);
                            mach.eval(bump, &decls_arm, cxt_arm.env, tm)
                        }
                    };
                    let tm = mach.check(bump, &cxt_arm, body, ret_type)?;
                    mach.pm_solvable = saved_solvable;
                    self.pats.push((detail, tm));
                    if is_catch_all(pat, &ctor_names) {
                        shadowed = true;
                    }
                }
                Walk::Unreachable => {
                    self.errors
                        .push(format!("分支不可达：模式 {:?} 与被匹配类型不相容", pat));
                }
            }
            // 臂边界：回滚本臂的精化事实、可解集与名字轨迹（本臂解出的
            // meta 保留——分支体 Tm 引用着它们，且解在 rename 时已烘焙为
            // 无 def 形式）。
            mach.unwind_names(name_mark);
            mach.pm_restore(mark);
        }
        mach.pm_restore(entry);
        if self.errors.is_empty() {
            Ok(())
        } else {
            Err(Error(self.errors.join("\n")))
        }
    }

    /// 构造子可达性探测：在（meta + 精化状态）快照回滚下跑一次特化方程。
    /// 探测不产生真槽——构造子绑定器用超出上下文的 scratch 层级实例化
    /// （同为刚性、同可被方程解出，回滚即可）。成功 = 该构造子可能出现在
    /// 头部类型的值里；结构冲突（`Vec[A] zero` 上不可能有 `cons`）= absurd。
    fn probe_accessible(
        mach: &mut Machine,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        head_sum: V,
        ctor: &str,
    ) -> bool {
        let (sum_name, impl_vals) = match v_xcell_of(head_sum) {
            XCell::Sum { name, params, .. } => (
                *name,
                params
                    .iter()
                    .filter(|p| p.icit == Icit::Impl)
                    .map(|p| p.val)
                    .collect::<Vec<_>>(),
            ),
            _ => return false,
        };
        let entry = match cxt.decl.borrow().get(&format!("{}.{}", sum_name, ctor)) {
            Some(e) => *e,
            None => return false,
        };
        let snap = mach.metas.clone();
        let mark = mach.pm_mark();
        let decl = cxt.decl.borrow();
        let mut ty = entry.ty;
        let mut impl_idx = 0;
        let mut scratch = 0u32;
        let ok = loop {
            let tyf = mach.force_v(bump, &decl, ty);
            if v_tag(tyf) == 4 {
                let p = v_pi_of(tyf);
                let u = if impl_idx < impl_vals.len() {
                    let v = impl_vals[impl_idx];
                    impl_idx += 1;
                    v
                } else {
                    let l = cxt.lvl + scratch;
                    scratch += 1;
                    mach.pm_solvable.push(l);
                    v_lvl(l)
                };
                let env = env_ext(bump, p.env, u);
                ty = mach.eval(bump, &decl, env, p.body);
            } else {
                let ret_sum = mach.force_v(bump, &decl, tyf);
                if !(v_tag(ret_sum) == 7 && matches!(v_xcell_of(ret_sum), XCell::Sum { .. })) {
                    break false;
                }
                break Self::unify_indices(mach, bump, cxt, head_sum, ret_sum, ctor).is_ok();
            }
        };
        mach.pm_restore(mark);
        mach.metas = snap;
        ok
    }

    /// 特化方程：头部 Sum 的参数（含索引）与构造子返回 Sum 的参数逐槽合一，
    /// **头部一侧在前**——两侧都是可解变量时解的方向是"头部变量 := 构造子
    /// 侧值"（即"老的变量 := 新的变量"，与上下文顺序一致）。
    fn unify_indices(
        mach: &mut Machine,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        head_sum: V,
        ret_sum: V,
        ctor: &str,
    ) -> Result<(), Error> {
        let (hp, rp) = match (v_xcell_of(head_sum), v_xcell_of(ret_sum)) {
            (XCell::Sum { params: p1, .. }, XCell::Sum { params: p2, .. }) => (p1, p2),
            _ => return Err(Error(format!("构造子 {} 的返回类型不是和类型", ctor))),
        };
        if hp.len() != rp.len() {
            return Err(Error(format!(
                "构造子 {} 与被匹配类型的参数数不一致",
                ctor
            )));
        }
        let decl = cxt.decl.borrow();
        for (a, b) in hp.iter().zip(rp.iter()) {
            if !mach.unify(bump, &decl, cxt.lvl, a.val, b.val) {
                return Err(Error(format!(
                    "构造子 {} 与被匹配类型不相容（分支不可达）",
                    ctor
                )));
            }
        }
        Ok(())
    }

    fn walk(
        &mut self,
        mach: &mut Machine,
        bump: &'a Bump,
        pat: &Pattern,
        head_ty: V,
        head_val: V,
        cxt: &Cxt<'a>,
    ) -> Result<Walk<'a>, Error> {
        match pat {
            Pattern::Any(span, _) => {
                let lvl = cxt.lvl;
                let a_t = mach.quote(bump, &cxt.decl.borrow(), cxt.lvl, head_ty);
                let cxt2 = mach.bind_name(bump, cxt, "_", a_t, head_ty);
                mach.pm_solvable.push(lvl);
                Ok(Walk::Matched(PatternDetail::Any(*span), cxt2))
            }
            Pattern::Con(name, subs, _) => {
                self.walk_con(mach, bump, name, subs, head_ty, head_val, cxt)
            }
        }
    }

    /// 下钻一个构造子模式。槽位纪律：**每个绑定器一个槽，先绑定后下钻**——
    /// 构造子 Pi 链上每个绑定器都在当前 `cxt.lvl` 处绑定为 fresh rigid
    /// （枚举隐式参数除外：用头部 Sum 的实参实例化，不产生槽），然后按
    /// icit 对齐用户子模式继续下钻。嵌套 Con 模式由子 walk_con 入口绑自己
    /// 的 head 槽（槽值即本字段的实例化 rigid u），编译期绑定、运行时
    /// prepend、bind_count 三方同序同数。
    #[allow(clippy::too_many_arguments)]
    fn walk_con(
        &mut self,
        mach: &mut Machine,
        bump: &'a Bump,
        name: &crate::parser_lib::Span<String>,
        subs: &[Pattern],
        head_ty: V,
        head_val: V,
        cxt: &Cxt<'a>,
    ) -> Result<Walk<'a>, Error> {
        let decls = cxt.decl.borrow();
        let head_sum = mach.force_v(bump, &decls, head_ty);
        if !(v_tag(head_sum) == 7 && matches!(v_xcell_of(head_sum), XCell::Sum { .. })) {
            // 非和类型头部：只能当变量绑定
            if !subs.is_empty() {
                return Err(Error(format!(
                    "`{}` 不是构造子，不能带子模式解构",
                    name.data
                )));
            }
            let lvl = cxt.lvl;
            let a_t = mach.quote(bump, &decls, cxt.lvl, head_ty);
            let cxt2 = mach.bind_name(bump, cxt, &name.data, a_t, head_ty);
            mach.pm_solvable.push(lvl);
            return Ok(Walk::Matched(PatternDetail::Bind(name.clone()), cxt2));
        }
        let (sum_name, sum_params, cases) = match v_xcell_of(head_sum) {
            XCell::Sum {
                name,
                params,
                cases,
            } => (*name, *params, *cases),
            _ => unreachable!(),
        };
        let is_ctor = cases.iter().any(|c| *c == name.data);
        if !is_ctor {
            // 不是该类型的构造子 → 变量绑定
            if !subs.is_empty() {
                return Err(Error(format!(
                    "`{}` 不是 {} 的构造子，不能带子模式解构",
                    name.data, sum_name
                )));
            }
            let lvl = cxt.lvl;
            let a_t = mach.quote(bump, &decls, cxt.lvl, head_ty);
            let cxt2 = mach.bind_name(bump, cxt, &name.data, a_t, head_ty);
            mach.pm_solvable.push(lvl);
            return Ok(Walk::Matched(PatternDetail::Bind(name.clone()), cxt2));
        }
        let entry = *cxt
            .decl
            .borrow()
            .get(&format!("{}.{}", sum_name, name.data))
            .ok_or_else(|| Error(format!("找不到构造子 {}.{}", sum_name, name.data)))?;
        // head 槽：Con 模式自身占一槽。运行时 eval_aux 的 Con 路径把被匹配
        // 值 prepend 进 env，三方（编译期绑定 / 运行时 prepend / bind_count）
        // 同序同数。
        let lvl = cxt.lvl;
        let head_binder = format!("_{}", name.data);
        let a_t = mach.quote(bump, &decls, cxt.lvl, head_ty);
        let mut cxt = mach.bind_name(bump, cxt, &head_binder, a_t, head_ty);
        mach.pm_solvable.push(lvl);
        let mut ty = entry.ty;
        let impl_vals: Vec<V> = sum_params
            .iter()
            .filter(|p| p.icit == Icit::Impl)
            .map(|p| p.val)
            .collect();
        let mut impl_idx = 0;
        let mut sub_queue: Vec<&Pattern> = subs.iter().collect();
        let mut details: Vec<PatternDetail> = Vec::new();
        // 构造子自身绑定器的值（写入头部精化时用）
        let mut ctor_datas: Vec<SumDataV<'a>> = Vec::new();
        let ret = loop {
            let tyf = mach.force_v(bump, &decls, ty);
            if v_tag(tyf) == 4 {
                let p = v_pi_of(tyf);
                let (bname, bicit, dom) = (p.name, p.icit, p.dom);
                if impl_idx < impl_vals.len() {
                    // 枚举隐式参数：不产生模式槽
                    let u = impl_vals[impl_idx];
                    impl_idx += 1;
                    let env = env_ext(bump, p.env, u);
                    ty = mach.eval(bump, &decls, env, p.body);
                    continue;
                }
                // 用户子模式按 icit 对齐：隐式绑定器可以缺省（自动通配），
                // 显式绑定器必须提供；子模式必须与绑定器顺序一致
                let sub: Option<&Pattern> = match bicit {
                    Icit::Impl => {
                        let matches_impl = sub_queue
                            .first()
                            .map(|p2| p2.get_icit() == Icit::Impl)
                            .unwrap_or(false);
                        if matches_impl {
                            Some(sub_queue.remove(0))
                        } else {
                            None
                        }
                    }
                    Icit::Expl => match sub_queue.first() {
                        Some(p2) if p2.get_icit() == Icit::Expl => Some(sub_queue.remove(0)),
                        _ => {
                            return Err(Error(format!(
                                "构造子 {} 缺少字段 {} 的模式",
                                name.data, bname
                            )))
                        }
                    },
                };
                // 绑定器的"值"：一律 fresh rigid（模式变量，可被特化方程解出）
                let u = v_lvl(cxt.lvl);
                let (detail, new_cxt) = match sub {
                    None => {
                        let lvl2 = cxt.lvl;
                        let bname2 = format!("_{bname}");
                        let d_t = mach.quote(bump, &decls, cxt.lvl, dom);
                        let c2 = mach.bind_name(bump, &cxt, &bname2, d_t, dom);
                        mach.pm_solvable.push(lvl2);
                        (PatternDetail::Any(empty_span(())), c2)
                    }
                    Some(Pattern::Any(span, _)) => {
                        let lvl2 = cxt.lvl;
                        let d_t = mach.quote(bump, &decls, cxt.lvl, dom);
                        let c2 = mach.bind_name(bump, &cxt, "_", d_t, dom);
                        mach.pm_solvable.push(lvl2);
                        (PatternDetail::Any(*span), c2)
                    }
                    Some(Pattern::Con(cn, csubs, _)) => {
                        let domf = mach.force_v(bump, &decls, dom);
                        let is_ctor2 = v_tag(domf) == 7
                            && match v_xcell_of(domf) {
                                XCell::Sum { cases: c2s, .. } => c2s.iter().any(|c| *c == cn.data),
                                _ => false,
                            };
                        if is_ctor2 {
                            // 解构：子 walk_con 入口绑自己的 head 槽
                            // （槽值即本字段的实例化 rigid u）
                            match self.walk_con(mach, bump, cn, csubs, dom, u, &cxt)? {
                                Walk::Matched(d, c) => (d, c),
                                Walk::Unreachable => return Ok(Walk::Unreachable),
                            }
                        } else {
                            if !csubs.is_empty() {
                                return Err(Error(format!(
                                    "`{}` 不是构造子，不能带子模式解构",
                                    cn.data
                                )));
                            }
                            let lvl2 = cxt.lvl;
                            let d_t = mach.quote(bump, &decls, cxt.lvl, dom);
                            let c2 = mach.bind_name(bump, &cxt, &cn.data, d_t, dom);
                            mach.pm_solvable.push(lvl2);
                            (PatternDetail::Bind(cn.clone()), c2)
                        }
                    }
                };
                cxt = new_cxt;
                details.push(detail);
                ctor_datas.push(SumDataV {
                    name: bump.alloc_str(bname),
                    val: u,
                    icit: bicit,
                });
                let env = env_ext(bump, p.env, u);
                ty = mach.eval(bump, &decls, env, p.body);
            } else {
                break tyf;
            }
        };
        if !sub_queue.is_empty() {
            return Err(Error(format!(
                "构造子 {} 的模式多了 {} 个子模式",
                name.data,
                sub_queue.len()
            )));
        }
        // 特化方程：头部索引 ≐ 构造子返回索引。失败 = 分支不可达。
        let ret_sum = mach.force_v(bump, &decls, ret);
        if !(v_tag(ret_sum) == 7 && matches!(v_xcell_of(ret_sum), XCell::Sum { .. })) {
            return Err(Error(format!(
                "构造子 {} 的返回类型不是和类型",
                name.data
            )));
        }
        if Self::unify_indices(mach, bump, &cxt, head_sum, ret_sum, &name.data).is_err() {
            return Ok(Walk::Unreachable);
        }
        // 头部精化（无条件）：被匹配变量本身写入事实表。`V a`、`add a zero`
        // 这类依赖被匹配变量的类型，要等 a := zero / a := succ t 之后才能
        // 归约——force 在读点展开这些事实。只对"本子句里尚未精化的变量"
        // 做（force 已展开过的不会再以 bare Rigid 出现）。
        let head_val_f = mach.force_v(bump, &decls, head_val);
        if v_tag(head_val_f) == 0 {
            let x = v_lvl_of(head_val_f);
            if x < cxt.lvl
                && pm_solvable_contains(&mach.pm_solvable, x)
                && mach.pm_def(x).is_none()
            {
                let ctor_val = v_xcell(bump.alloc(XCell::SumCase {
                    typ: head_sum,
                    case_name: bump.alloc_str(&name.data),
                    datas: bump.alloc_slice_fill_iter(ctor_datas),
                }));
                // 环守卫失败（typ 的索引提及 x 自身等病态情形）时跳过精化，
                // 不阻断分支检查
                mach.pm_solve(x, ctor_val);
            }
        }
        Ok(Walk::Matched(PatternDetail::Con(name.clone(), details), cxt))
    }
}

// quote/rename 卡住 match 的分支体时用的 decl 表：所有全局值换成指向自身
// 的中性 `Decl`，防止递归定义在求值分支体时被重展开。enum 类型本体的值
// （`Sum`）保持原样——构造子值的 `typ` 槽需要真实的 Sum 值。（参考版
// `simpl_decl` 同款；快版直接克隆表替换 val——与参考版逐条目换值同构，
// 无需给内核加"中性全局"开关。）
fn simpl_decl(bump: &Bump, decls: &FxHashMap<String, DeclEntryF>) -> FxHashMap<String, DeclEntryF> {
    decls
        .iter()
        .map(|(k, e)| {
            let val = if v_tag(e.val) == 7 && matches!(v_xcell_of(e.val), XCell::Sum { .. }) {
                e.val
            } else {
                v_xcell(bump.alloc(XCell::Decl(bump.alloc_str(k))))
            };
            (k.clone(), DeclEntryF { ty: e.ty, val })
        })
        .collect()
}

// builtin 注册（每轮 prime；参考版 `Cxt::new` + `add_builtin` 逐条对应）
// --------------------------------------------------------------------------------

/// `(String ->)^n ret` —— L07 builtin 的参数类型全为 String。
fn str_pi<'a>(bump: &'a Bump, params: &[&str], ret: &'a Tm<'a>) -> &'a Tm<'a> {
    let mut t = ret;
    for name in params.iter().rev() {
        t = bump.alloc(Tm::Pi(
            bump.alloc_str(name),
            Icit::Expl,
            bump.alloc(Tm::LiteralType),
            t,
        ));
    }
    t
}

/// `(name : dom) -> cod`。
fn tm_pi<'a>(bump: &'a Bump, name: &str, dom: &'a Tm<'a>, cod: &'a Tm<'a>) -> &'a Tm<'a> {
    bump.alloc(Tm::Pi(bump.alloc_str(name), Icit::Expl, dom, cod))
}

/// `string_to_global_type Var(ix)`（de Bruijn 引用前序参数）。
fn st2g_app<'a>(bump: &'a Bump, ix: u32) -> &'a Tm<'a> {
    bump.alloc(Tm::App(
        bump.alloc(Tm::Decl(bump.alloc_str("string_to_global_type"))),
        bump.alloc(Tm::Var(ix)),
        Icit::Expl,
    ))
}

impl Machine {
    /// 每轮注册（参考版 `Cxt::new(&infer)`）：String 类型进 decl 表；全组
    /// builtin 登记（类型经 eval 成 Π 链值；**值 = λ 参数链 → `Tm::Prim`
    /// 体**——应用满元数后由 force 的 [`prim_reduce`] 归约，L07 的触发
    /// 语义；L06 是应用时触发）。**注册顺序与参考版一致**——
    /// string_to_global_type 必须先于引用它的 global 族（其类型闭包体在
    /// check 期才查表，但防御性保持顺序）。与 L06 不同：builtin 名**不进
    /// env**（源码名经 decl 表解析，参考版 Raw::Var 同序）。
    fn prime_round<'a>(&mut self, bump: &'a Bump) -> Cxt<'a> {
        let cxt = decl_insert(
            &Cxt::empty(),
            "String",
            DeclEntryF {
                ty: v_u(),
                val: v_lit_ty(),
            },
        );
        let lit_ty: &'a Tm<'a> = bump.alloc(Tm::LiteralType);
        let u_t: &'a Tm<'a> = bump.alloc(Tm::U);
        let builtins: Vec<(&str, &'a Tm<'a>)> = vec![
            ("string_concat", str_pi(bump, &["x", "y"], lit_ty)),
            ("str_eq", str_pi(bump, &["x", "y"], lit_ty)),
            ("str_indent2", str_pi(bump, &["x"], lit_ty)),
            (
                "report_check_issue",
                str_pi(bump, &["code", "module", "signal", "message"], u_t),
            ),
            ("string_to_global_type", str_pi(bump, &["x"], u_t)),
            (
                "create_global",
                tm_pi(
                    bump,
                    "x",
                    lit_ty,
                    tm_pi(bump, "y", st2g_app(bump, 0), u_t),
                ),
            ),
            (
                "change_mutable",
                tm_pi(
                    bump,
                    "x",
                    lit_ty,
                    tm_pi(
                        bump,
                        "f",
                        tm_pi(bump, "_", st2g_app(bump, 0), st2g_app(bump, 1)),
                        u_t,
                    ),
                ),
            ),
            (
                "get_global",
                tm_pi(bump, "x", lit_ty, st2g_app(bump, 0)),
            ),
            (
                "get_global_default",
                tm_pi(
                    bump,
                    "x",
                    lit_ty,
                    tm_pi(bump, "z", st2g_app(bump, 0), st2g_app(bump, 1)),
                ),
            ),
            (
                "change_mutable_default",
                tm_pi(
                    bump,
                    "x",
                    lit_ty,
                    tm_pi(
                        bump,
                        "f",
                        tm_pi(bump, "_", st2g_app(bump, 0), st2g_app(bump, 1)),
                        tm_pi(bump, "z", st2g_app(bump, 1), u_t),
                    ),
                ),
            ),
            ("file_read_all_text", str_pi(bump, &["path"], lit_ty)),
            ("file_write_all_text", str_pi(bump, &["path", "content"], u_t)),
            ("file_append_all_text", str_pi(bump, &["path", "content"], u_t)),
            ("file_exists", str_pi(bump, &["path"], lit_ty)),
            ("file_delete", str_pi(bump, &["path"], u_t)),
        ];
        let mut cxt = cxt;
        for (name, ty) in builtins {
            let va = self.eval(bump, &cxt.decl.borrow(), EMPTY_ENV, ty);
            // 值 = λ 参数链 → Prim(name)；参数名从类型的 Π 链取（与域同序）
            let mut names: Vec<&str> = Vec::new();
            let mut cur = ty;
            while let Tm::Pi(n, _, _, body) = cur {
                names.push(n);
                cur = body;
            }
            let mut val: &'a Tm<'a> = bump.alloc(Tm::Prim(bump.alloc_str(name)));
            for p in names.iter().rev() {
                val = bump.alloc(Tm::Lam(bump.alloc_str(p), Icit::Expl, val));
            }
            let head = self.eval(bump, &cxt.decl.borrow(), EMPTY_ENV, val);
            cxt = decl_insert(&cxt, name, DeclEntryF { ty: va, val: head });
        }
        cxt
    }

    /// 参考版 `bench_check` 的主循环（无输出变体）：返回 (是否通过，最终
    /// 上下文，最后一个 def 的名)。
    fn elab_all<'a>(
        &mut self,
        bump: &'a Bump,
        ast: &[Decl],
    ) -> (Result<(), Error>, Cxt<'a>, Option<&'a str>) {
        let mut cxt = self.prime_round(bump);
        let mut last = None;
        for d in ast {
            match self.infer_decl(bump, &cxt, d) {
                Ok((out, nc)) => {
                    if let DeclOut::Def { name } = out {
                        last = Some(name);
                    }
                    cxt = nc;
                }
                Err(e) => return (Err(e), cxt, last),
            }
        }
        (Ok(()), cxt, last)
    }
}

// export 与对外入口
// --------------------------------------------------------------------------------

/// 把 bump 结果项转回参考版的 `Box` 树（迭代任务栈；icit/掩码随任务
/// 携带），复用参考版的 pretty。L07 新变体的 span 全零（内容即输出）。
fn export(t: &Tm<'_>) -> CTm {
    use crate::list::List as CList;
    enum J<'a> {
        Do(&'a Tm<'a>),
        Lam2(&'a str, Icit),
        Pi2(&'a str, Icit),
        Let2(&'a str),
        App2(Icit),
        AppPrun2(CList<Option<Icit>>),
        Obj2(&'a str),
        Sum2 {
            name: &'a str,
            params: &'a [SumParamT<'a>],
            cases: &'a [&'a str],
        },
        SumCase2 {
            case_name: &'a str,
            datas: &'a [SumDataT<'a>],
        },
    }
    fn name(x: &str) -> crate::parser_lib::Span<String> {
        empty_span(x.to_owned())
    }
    let mut tasks: Vec<J<'_>> = vec![J::Do(t)];
    let mut done: Vec<CTm> = Vec::new();
    while let Some(j) = tasks.pop() {
        match j {
            J::Do(Tm::Var(i)) => done.push(CTm::Var(Ix(*i))),
            J::Do(Tm::Lam(x, i, b)) => {
                tasks.push(J::Lam2(x, *i));
                tasks.push(J::Do(b));
            }
            J::Do(Tm::App(f, a, i)) => {
                tasks.push(J::App2(*i));
                tasks.push(J::Do(a));
                tasks.push(J::Do(f));
            }
            J::Do(Tm::AppPruning(h, pr)) => {
                // bds 持久链表（头 = 最内层）→ 参考版 List<Option<Icit>>（同序）
                let mut vec: Vec<Option<Icit>> = Vec::new();
                let mut cur = *pr;
                while let Some(b) = cur {
                    vec.push(b.slot);
                    cur = b.next;
                }
                let mut list: CList<Option<Icit>> = CList::new();
                for s in vec.into_iter().rev() {
                    list = list.prepend(s);
                }
                tasks.push(J::AppPrun2(list));
                tasks.push(J::Do(h));
            }
            J::Do(Tm::U) => done.push(CTm::U),
            J::Do(Tm::Pi(x, i, a, b)) => {
                tasks.push(J::Pi2(x, *i));
                tasks.push(J::Do(b));
                tasks.push(J::Do(a));
            }
            J::Do(Tm::Let(x, a, t, u)) => {
                tasks.push(J::Let2(x));
                tasks.push(J::Do(u));
                tasks.push(J::Do(t));
                tasks.push(J::Do(a));
            }
            J::Do(Tm::Meta(m)) => done.push(CTm::Meta(MetaVar(*m))),
            J::Do(Tm::LiteralType) => done.push(CTm::LiteralType),
            J::Do(Tm::LiteralIntro(s)) => done.push(CTm::LiteralIntro(name(s))),
            J::Do(Tm::Decl(s)) => done.push(CTm::Decl(smol_str::SmolStr::new(s))),
            J::Do(Tm::Prim(s)) => done.push(CTm::Prim(smol_str::SmolStr::new(s))),
            J::Do(Tm::Obj(h, n)) => {
                tasks.push(J::Obj2(n));
                tasks.push(J::Do(h));
            }
            J::Do(Tm::Sum(nm, params, cases)) => {
                tasks.push(J::Sum2 { name: nm, params, cases });
                for p in params.iter().rev() {
                    tasks.push(J::Do(p.ty));
                    tasks.push(J::Do(p.val));
                }
            }
            J::Do(Tm::SumCase {
                typ,
                case_name,
                datas,
            }) => {
                tasks.push(J::SumCase2 { case_name, datas });
                for d in datas.iter().rev() {
                    tasks.push(J::Do(d.val));
                }
                tasks.push(J::Do(typ));
            }
            J::Do(Tm::Match(s, cases)) => {
                // 分支体逐个内联导出（递归深度 = match 嵌套深度，体本身的
                // 导出仍走任务栈）；模式直接克隆（PatternDetail 是参考版
                // 类型，两版共用）
                let s2 = export(s);
                let mut cs: Vec<(PatternDetail, CTm)> = Vec::with_capacity(cases.len());
                for (p, b) in cases.iter() {
                    cs.push((p.clone(), export(b)));
                }
                done.push(CTm::Match(Box::new(s2), cs));
            }
            J::Lam2(x, i) => {
                let b = done.pop().expect("export 栈：Lam 缺体");
                done.push(CTm::Lam(name(x), i, Box::new(b)));
            }
            J::Pi2(x, i) => {
                let cod = done.pop().expect("export 栈：Pi 缺余定义域");
                let dom = done.pop().expect("export 栈：Pi 缺定义域");
                done.push(CTm::Pi(name(x), i, Box::new(dom), Box::new(cod)));
            }
            J::Let2(x) => {
                let u = done.pop().expect("export 栈：Let 缺体");
                let t = done.pop().expect("export 栈：Let 缺值");
                let a = done.pop().expect("export 栈：Let 缺类型");
                done.push(CTm::Let(name(x), Box::new(a), Box::new(t), Box::new(u)));
            }
            J::App2(i) => {
                let a = done.pop().expect("export 栈：App 缺实参");
                let f = done.pop().expect("export 栈：App 缺函数");
                done.push(CTm::App(Box::new(f), Box::new(a), i));
            }
            J::AppPrun2(pr) => {
                let h = done.pop().expect("export 栈：AppPruning 缺头");
                done.push(CTm::AppPruning(Box::new(h), pr));
            }
            J::Obj2(n) => {
                let h = done.pop().expect("export 栈：Obj 缺接收者");
                done.push(CTm::Obj(Box::new(h), name(n)));
            }
            J::Sum2 { name: nm, params, cases } => {
                let mut ps: Vec<(crate::parser_lib::Span<String>, CTm, CTm, Icit)> =
                    Vec::with_capacity(params.len());
                for p in params.iter().rev() {
                    let ty = done.pop().expect("export 栈：Sum 缺参数类型");
                    let val = done.pop().expect("export 栈：Sum 缺参数值");
                    ps.push((name(p.name), val, ty, p.icit));
                }
                ps.reverse();
                let cs: Vec<crate::parser_lib::Span<String>> =
                    cases.iter().map(|c| name(c)).collect();
                done.push(CTm::Sum(name(nm), ps, cs));
            }
            J::SumCase2 { case_name, datas } => {
                let mut ds: Vec<(crate::parser_lib::Span<String>, CTm, Icit)> =
                    Vec::with_capacity(datas.len());
                for d in datas.iter().rev() {
                    let val = done.pop().expect("export 栈：SumCase 缺字段");
                    ds.push((name(d.name), val, d.icit));
                }
                ds.reverse();
                let typ = done.pop().expect("export 栈：SumCase 缺 typ");
                done.push(CTm::SumCase {
                    typ: Box::new(typ),
                    case_name: name(case_name),
                    datas: ds,
                });
            }
        }
    }
    done.pop().expect("export 必须恰有一个根")
}

/// 参考版项的节点数（与 mod.rs `tm_size_ref` 同口径）。
fn tm_size(t: &Tm<'_>) -> u64 {
    let mut stack: Vec<&Tm<'_>> = vec![t];
    let mut n = 0u64;
    while let Some(x) = stack.pop() {
        n += 1;
        match x {
            Tm::Var(_) | Tm::U | Tm::Meta(_) | Tm::LiteralType | Tm::LiteralIntro(_)
            | Tm::Decl(_) | Tm::Prim(_) => {}
            Tm::Obj(h, _) => stack.push(h),
            Tm::Lam(_, _, b) => stack.push(b),
            Tm::App(f, a, _) => {
                stack.push(f);
                stack.push(a);
            }
            Tm::AppPruning(h, pr) => {
                stack.push(h);
                let mut cur = *pr;
                while let Some(b) = cur {
                    n += 1;
                    cur = b.next;
                }
            }
            Tm::Pi(_, _, a, b) => {
                stack.push(a);
                stack.push(b);
            }
            Tm::Let(_, a, t, u) => {
                stack.push(a);
                stack.push(t);
                stack.push(u);
            }
            Tm::Sum(_, params, _) => {
                for p in params.iter() {
                    stack.push(p.val);
                    stack.push(p.ty);
                }
            }
            Tm::SumCase { typ, datas, .. } => {
                stack.push(typ);
                for d in datas.iter() {
                    stack.push(d.val);
                }
            }
            Tm::Match(s, cases) => {
                stack.push(s);
                for (p, b) in cases.iter() {
                    n += p.bind_count() as u64;
                    stack.push(b);
                }
            }
        }
    }
    n
}

/// A/B 实验开关（Raw::Var 名字解析消融）：置 `L06_NO_NAME_MAP=1` 回落为
/// 沿 `types` 链的线性找名（`=0` 不关闭）。
static NO_NAME_MAP: std::sync::LazyLock<std::sync::atomic::AtomicBool> =
    std::sync::LazyLock::new(|| {
        std::sync::atomic::AtomicBool::new(std::env::var("L06_NO_NAME_MAP").is_ok_and(|v| v != "0"))
    });

/// 稳态类型检查器（同 L03-L06：owns 反复 `reset` 的 `Bump` 与跨调用复用
/// 的 [`Machine`]）。
pub(crate) struct Tycker {
    bump: Bump,
    machine: Machine,
}

impl Tycker {
    pub(crate) fn new() -> Self {
        Tycker {
            bump: Bump::with_capacity(1 << 20),
            machine: Machine::new(),
        }
    }

    /// 参考版 `run` 的等价物：preprocess + parse 由调用方完成（与参考版
    /// 共用 parser），本方法做轮重置 + builtin 重注册 + 逐 decl 推断，
    /// println 的 nf 经 pretty 输出（quote 走记忆化口径——与无记忆化
    /// 输出逐字节一致，L03-L06 已证；L07 新值形态不进 memo 表，口径与
    /// 参考版的全量 quote 一致）。
    pub(crate) fn run_decls(&mut self, ast: &[Decl]) -> Result<String, Error> {
        self.bump.reset();
        self.machine.clear_round();
        let bump = &self.bump;
        let mut cxt = self.machine.prime_round(bump);
        let mut ret = String::new();
        for d in ast {
            let (out, nc) = self.machine.infer_decl(bump, &cxt, d)?;
            cxt = nc;
            if let DeclOut::Println(t) = out {
                let decls = cxt.decl.borrow();
                // nf 入口充值 fuel（参考版 `Infer::nf` 同款）
                self.machine.fuel.set(UNIFY_FUEL);
                let v = self.machine.eval(bump, &decls, cxt.env, t);
                let q = self.machine.quote_memo(bump, &decls, cxt.lvl, v);
                let names = types_names_list(cxt.types);
                ret += &pretty_tm(0, names, &export(q));
                ret += "\n";
            }
        }
        Ok(ret)
    }

    /// 参考版 `run` 的全流程等价物（含 preprocess/parse）。
    pub(crate) fn run_input(&mut self, input: &str, path_id: u32) -> Result<String, Error> {
        let ast = super::parser::parser(&super::preprocess(input), path_id).map_err(Error)?;
        self.run_decls(&ast)
    }

    /// 基准口径（bench 用）：仅 elaborate。
    pub(crate) fn bench_check(&mut self, ast: &[Decl]) -> bool {
        self.bump.reset();
        self.machine.clear_round();
        let bump = &self.bump;
        self.machine.elab_all(bump, ast).0.is_ok()
    }

    /// 基准口径：check + nf（最后一个 def 在 decl 表登记的值空层级引读，
    /// 与参考版 `bench_check_nf` 同口径——按名查表、quote 无记忆化），
    /// 返回结果树节点数。
    pub(crate) fn bench_check_nf(&mut self, ast: &[Decl]) -> u64 {
        self.bench_nf_impl(ast, false)
    }

    /// [`Tycker::bench_check_nf`] 的 quote 记忆化口径。
    pub(crate) fn bench_check_nf_memo(&mut self, ast: &[Decl]) -> u64 {
        self.bench_nf_impl(ast, true)
    }

    fn bench_nf_impl(&mut self, ast: &[Decl], use_memo: bool) -> u64 {
        self.bump.reset();
        self.machine.clear_round();
        let bump = &self.bump;
        let (r, cxt, last) = self.machine.elab_all(bump, ast);
        if r.is_err() {
            return 0;
        }
        let Some(name) = last else {
            return 0;
        };
        let Some(entry) = cxt.decl.borrow().get(name).copied() else {
            return 0;
        };
        let q = if use_memo {
            self.machine.quote_memo(bump, &cxt.decl.borrow(), 0, entry.val)
        } else {
            self.machine.quote(bump, &cxt.decl.borrow(), 0, entry.val)
        };
        tm_size(q)
    }
}

/// 一次性口径入口（与参考版 `run` 同签名同 Ok 输出）。
pub(crate) fn run_fast(input: &str, path_id: u32) -> Result<String, Error> {
    let mut tycker = Tycker::new();
    tycker.run_input(input, path_id)
}

/// 测试/基准辅助：共用参考版 parser（fast 是 L08_product_type 的子模块，可见
/// 私有 parser；产出的 `Decl` 同时喂参考版与快版的 bench 口径）。
pub(crate) fn parse(input: &str, path_id: u32) -> Result<Vec<Decl>, String> {
    super::parser::parser(&super::preprocess(input), path_id)
}

/// 解析产出的 decl AST 类型别名（测试/基准用；Decl 本身的 use 是私有的）。
pub(crate) type SourceDecl = Decl;

// 基准负载生成器（L06 全家桶的 L07 语法版 + sum-type 特色负载）
// --------------------------------------------------------------------------------

/// church 2^(k+1)：k 次 ×2 翻倍（`add p p`）的 def 链，末位 def 为 `p_k`
/// （L07 顶层是 decl 序列：**无尾表达式行、def 无分号**；nf 节点数与
/// L06 同为 2n + 4）。
pub(crate) fn church_src(k: u32) -> String {
    let mut s = String::from(
        "def Nat : U = (N : U) -> (N -> N) -> N -> N\n\
         def add : Nat -> Nat -> Nat = a => b => N => s => z => a N s (b N s z)\n\
         def p0 : Nat = N => s => z => s (s z)\n",
    );
    for i in 1..=k {
        s += &format!("def p{i} : Nat = add p{} p{}\n", i - 1, i - 1);
    }
    s
}

/// strchain 2^(k+1)（**L06 特色负载**）：每层 `string_concat s_{i-1} "x"`
/// ——decl 表增长 + 每层一次 builtin prim 触发（force 时字面量拼接），
/// 末值是长度 n 的字面量（nf 节点数 = 1）。
pub(crate) fn strchain_src(k: u32) -> String {
    let n = 1u64 << (k + 1);
    let mut s = String::from("def s0 : String = \"x\"\n");
    for i in 1..n {
        s += &format!("def s{i} : String = string_concat s{} \"x\"\n", i - 1);
    }
    s
}

/// globals 2^(k+1)（L06 特色：可变全局 + 重入 prim）：每层
/// `change_mutable "k" (s => string_concat s "x")`——mutable_map 读写 +
/// 函数实参的 β 应用 + 重入 prim 触发；末值 = U（nf 节点数 = 1）。
pub(crate) fn globals_src(k: u32) -> String {
    let n = 1u64 << (k + 1);
    let mut s = String::from("def g0 : U = create_global \"k\" \"x\"\n");
    for i in 1..n {
        s += &format!("def g{i} : U = change_mutable \"k\" (s => string_concat s \"x\")\n");
    }
    s
}

/// match 2^(k+1)（**L07 特色负载**）：每层一个**自递归**的依赖 match def
/// ——decl 表占位/覆盖 + 编译期特化合一 + 运行时首匹配 + 卡住 match 在
/// check 期（期望类型）与 quote 期（分支体简化表）的协同。
pub(crate) fn match_src(k: u32) -> String {
    let mut s = String::from("enum Nat {\n    zero\n    succ(x: Nat)\n}\n");
    for i in 0..=k {
        s += &format!(
            "def f_{i}(x : Nat) : Nat =\n    match x {{\n        case zero => zero\n        case succ(n) => succ (f_{i} n)\n    }}\n"
        );
    }
    s += &format!(
        "def two : Nat = succ (succ zero)\nprintln (f_{k} two)\n"
    );
    s
}

/// enum 负载（**L07 特色**）：多 enum + 依赖索引（Vec 风格 GADT）+ 投影
/// + 索引等式（Eq）+ 递归 length——覆盖 Sum/SumCase 值的 unify / quote /
/// rename 全链路。
pub(crate) fn enum_src() -> String {
    String::from(
        r#"enum Nat {
    zero
    succ(x: Nat)
}

enum Bool {
    true
    false
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

enum Eq[A](x: A, y: A) {
    refl[a: A] -> Eq[A] a a
}

def two = succ (succ zero)

def t = cons zero (cons two nil)

println t.len

def ok : Eq two two = refl

def length[T, l: Nat](x: Vec[T] l): Nat =
    match x {
        case nil => zero
        case cons(_, xs) => succ (length xs)
    }

println (length t)

def add(x: Nat, y: Nat): Nat =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }

def rep[n: Nat](x: Vec[Nat] n): Nat =
    match x {
        case nil => zero
        case cons(h, xs) => add h (rep xs)
    }

println (rep (cons two (cons two nil)))
"#,
    )
}

/// struct 负载（**L08 特色**）：固定深度的嵌套 Box（4 层：类型级 `.mk`
/// 剥链 + 左结合投影链 + 一个浅嵌套值）+ 规模按 2^(k+1) 的**浅值投影
/// def 链**（`def q{i} : Nat = get_x (new P(q{i-1}, zero))`——每层一次
/// 构造子 β + 类型级投影 + 合一）。末值 = `zero`（nf 节点数 = 2：
/// SumCase + typ 的 Sum 两个节点）。
///
/// 设计注记：**不**用深嵌套值链（`b_i` 含 `b_{i-1}`）作主负载——参考版
/// 的 decl 表 `Rc` 写时复制 + `Val` 深拷贝语义下，深度 i 的值树在插入
/// 第 n 个 def 时被整体克隆，复杂度 O(n³)（k=700 即分钟级）；孪生版的
/// 平铺表无此问题，但双 oracle 同负载对比失去意义。嵌套深度固定为 4，
/// 规模轴走浅值。
pub(crate) fn struct_src(k: u32) -> String {
    let n = 1u64 << (k + 1);
    let mut s = String::from(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\n\
         struct Box0 {\n    v: Nat\n}\n\n\
         struct Box1 {\n    v: Nat\n    inner: Box0\n}\n\n\
         struct Box2 {\n    v: Nat\n    inner: Box1\n}\n\n\
         struct Box3 {\n    v: Nat\n    inner: Box2\n}\n\n\
         def get_v2(p: Box2): Nat = p.inner.v\n\n\
         def seed : Nat = get_v2(new Box2(zero, new Box1(succ zero, new Box0(succ (succ zero)))))\n\n\
         struct P {\n    x: Nat\n    y: Nat\n}\n\n\
         def get_x(p: P): Nat = p.x\n\n\
         def q0 : Nat = get_x(new P(zero, seed))\n",
    );
    for i in 1..n {
        s += &format!("def q{i} : Nat = get_x(new P(q{}, zero))\n", i - 1);
    }
    s += &format!("println q{}\n", n - 1);
    s
}
