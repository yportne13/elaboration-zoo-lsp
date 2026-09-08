//! L11 核心机（eval / quote / unify / rename / solve / prune / check /
//! infer / check_universe / 模式编译 / trait 求解）的极致性能版：L10
//! 冠军配方（`bump_spine_iter`）向宏层的移植。继承 L05-L10 的全部机制
//! （见 L06/L08/L10 版模块注释与 readme）：bump arena、打包值 [`V`]、
//! 扁平中性 + spine 栈、复合环境、迭代内核（eval 双栈 / quote 任务栈 /
//! unify 工作表 / rename 任务栈）、quote 记忆化、O(1) 名字解析、
//! `Tycker` 稳态复用。
//!
//! **L11 自己的增量与差异**（参考版 = `super` 的分文件实现，语义以其为
//! 准）——L11 参考版是 L13 引擎的早期形态（Arc 持久化 + decl 表贯穿），
//! 与 L10 的 global 大下标世界有系统性不同，孪生版逐项对齐：
//!
//! - **全局 = decl 表（名字键）+ `Tm::Decl`/`Val::Decl`**：没有
//!   `Infer.global` 表与 1919810 哨兵。顶层 def/enum/构造子/内建全部登记
//!   在 `Cxt.decl: HashMap<String, (Span, Tm, Val, Ty, VTy)>`（快版 =
//!   `Rc<Decls>` 写时复制，方法与参考版逐 cxt 克隆语义一致）；项层引用是
//!   `Tm::Decl(name)`（bump str）。eval 的 Decl 臂查表取登记值，未登记
//!   → 卡 `Val::Decl(name, [])`（递归自引用 = fake_bind 插桩的存根）。
//!   v_app 对 Decl 头压 spine；quote/rename 原样产出 `Tm::Decl`。
//! - **`decl: &Decls` 参数贯穿**：eval/force/v_app/quote/unify/rename/
//!   invert/prune/solve/lams/eval_aux/Compiler 全部带 decl（参考版同款）。
//!   卡住 Match 的 quote/rename/unify 分支体在 **declb**（全表条目换成
//!   `Decl(name)` 存根的重建表）下重求值——参考版 declb 逐字同构，取代
//!   L10 的中性 global 视图。
//! - **builtin 是 5 个带类型的 `Tm::Prim(typ, pid)`**：`string_concat` /
//!   `string_to_global_type` / `create_global` / `change_mutable` /
//!   `get_global`，注册在 Cxt::new 的 decl 表里（λ 链体是无名的
//!   `Tm::Prim` 节点）。快版用 `PrimId` 枚举替代参考版 `Rc<dyn Fn>`
//!   （bump 内不能携带闭包），语义逐句移植 cxt.rs 的 5 个实现：
//!   string_concat 拼接两槽字面量（非字面量 → 卡 `Val::Prim`，带 typ）；
//!   string_to_global_type 按名字查 decl 表（未登记 → 卡 Decl）；后三者
//!   读写 `mutable_map`（每轮清空，参考版 per-Infer 同款）。卡住 Prim 的
//!   unify：与携带的 typ 合一（参考版两臂），**不再是** L10 的
//!   `(LiteralType, Prim) => Ok(())` 宽放。
//! - **卡住 match 无 pending、force 展开 Flex + Obj**：v_app 对 Match panic
//!   （不可能吸收实参）；参考版 force 只有 Flex + Obj 两臂——meta 解开后
//!   不会重选 match、不展开 Decl。卡住投影 `Val::Obj` 只在 eval 的 Tm::Obj
//!   臂产生：接收者 force 后非 Sum/SumCase 一律卡成 Obj（Flex、卡住 match、
//!   卡住投影、字面量都在其内）。**L09 才是**仅 Rigid 卡、其余 panic。
//! - **模式特化不走 pm_defs**：参考版走 `check_pm`/`unify_pm` +
//!   `Cxt::update_cxt`/`refresh`——把精化等式**直接改写进环境**（目标槽
//!   替换 + 全槽在"更新后 env"下重求值重锚定），src_names 按层级取类型
//!   （BiMap 的 map2 持久），快版镜像为 `lvl_types` 表 + 双轨迹撤销。
//!   模式编译器（Compiler）逐句移植参考版 pattern_match.rs：决策树、
//!   PatConstructor、filter_accessible_constrs 的 temp-infer 克隆探测
//!   （快版 = metas 快照换入换出）、checked_ret 备忘。
//! - **unify 无燃料、无 pm 臂、无 (Obj,Obj)/宽松臂**：臂序 = U/Pi/Rigid/
//!   Decl/Decl 同名/Flex/Flex/Lam/η/Flex 求解/LiteralType/Prim 带类型/
//!   Sum/SumCase/Match/Obj；flex_flex 单方向尝试无快照回滚；SumCase/
//!   SumCase **比 typ+datas**（L07+ 只比 datas）；Match/Match 分支体在
//!   **declb 存根表**下重求值（参考版同款）。
//! - **fake_bind = decl 表插桩 + redefine 检查**：递归 def 检查前先
//!   `decl.insert(name, Decl 存根)`，撞名（含内建）即 `redefine {name}`；
//!   检查后 `decl()` 静默覆盖为真值。src_names 只收局部 binder，顶层
//!   名字一律走 decl 表回落。
//! - **重定义静默覆盖**（参考版 `cxt.decl` 的检查被注释）；构造子只以
//!   **裸名**登记（无 `Enum.case` 别名；struct 的 case 名本身是
//!   `Name.mk`）。
//!
//! 与参考版共用 parser / pretty / preprocess，**Ok 输出逐字节一致**（互检
//! 测试 + `tests/l11_fast_parity.rs`）。已知偏差（仅错误消息内容，不影响
//! 判定与 Ok 输出）：快版错误里内嵌的 Debug-Val/Tm 的名字 Span 全零
//! （参考版携带源码偏移），套件比对前按 `start_offset/end_offset/path_id`
//! 归一化。

use bumpalo::Bump;
use smol_str::SmolStr;
use rustc_hash::{FxHashMap, FxHashSet};
use std::cell::RefCell;
use std::rc::Rc;

use super::parser::syntax::{Decl, Either, Icit, Pattern, Raw};
use crate::parser_lib::ToSpan;
use super::pretty::pretty_tm;
use super::{empty_span, Error, Ix, MetaVar, PatternDetail, Tm as CTm};
use std::collections::HashMap;

use super::typeclass::{Assertion, Instance, Synth, Typ};

/// 内建函数标识（参考版 `PrimFunc` 闭包；bump 内以枚举替代）。
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum PrimId {
    /// `string_concat`：λ 链体，求值时读 env 前两槽拼接。
    StringConcat,
    /// `string_to_global_type`：字符串 → decl 表动态引用。
    StringToGlobalType,
    /// `create_global`：写 mutable_map。
    CreateGlobal,
    /// `change_mutable`：读改写 mutable_map（v_app 应用到旧值）。
    ChangeMutable,
    /// `get_global`：读 mutable_map（缺名 panic——参考版 unwrap 同款）。
    GetGlobal,
}

// syntax（bump 内的项表示）
// --------------------------------------------------------------------------------

/// bump 内分配的核心项。名字只服务 pretty（`Var` 无名，索引寻址）。
pub(crate) enum Tm<'a> {
    Var(u32),
    /// 全局声明的名字引用（参考版 `Tm::Decl(Span<String>)`；名字是 bump
    /// 内的 str，pretty 直接打印）。
    Decl(&'a str),
    Lam(&'a str, Icit, &'a Tm<'a>),
    App(&'a Tm<'a>, &'a Tm<'a>, Icit),
    /// 把头按掩码应用到求值环境：`Some(icit)` 槽位以该 icit 应用实参，
    /// `None` 槽位跳过。
    AppPruning(&'a Tm<'a>, Option<&'a PrCons<'a>>),
    U(u32),
    Pi(&'a str, Icit, &'a Tm<'a>, &'a Tm<'a>),
    Let(&'a str, &'a Tm<'a>, &'a Tm<'a>, &'a Tm<'a>),
    Meta(u32),
    /// String 字面量的类型（`String`）。
    LiteralType,
    /// 字符串字面量（内容即值）。
    LiteralIntro(&'a str),
    /// builtin 体标记：带声明返回类型（值层 `Val::Prim(typ, _)` 的同构）
    /// 与函数标识。求值时按 `PrimId` 分派（拼接 / decl 查表 / mutable_map
    /// 读写），reduce 不成功则卡 `XCell::Prim { typ, pid }`。
    Prim(V, PrimId),
    /// `x.field` 投影（参考版 `Tm::Obj`；字段名只服务 pretty/查表）。
    Obj(&'a Tm<'a>, &'a str),
    /// enum 类型本体（enum 声明 λ 链的体）。params = (参数名, 值项, 类型项,
    /// icit)，声明处值项即参数自身；实例化后值槽携带当前实参。
    /// `is_trait`：trait 脱糖的 enum（fresh_meta 走实例合成）。
    Sum(&'a str, &'a [SumParamT<'a>], &'a [&'a str], bool),
    /// 构造子值：typ 求值后必须是其所属的（已实例化的）`Sum`。
    SumCase {
        typ: &'a Tm<'a>,
        case_name: &'a str,
        datas: &'a [SumDataT<'a>],
        is_trait: bool,
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
/// `2=Spine(idx<<3|2)`、`3=U(lvl<<3|3)`（宇宙层级进打包字）、`4=Pi(ptr|4)`、
/// `5=Meta(m<<3|5)`（未解 meta 立即数）、`6=LiteralType`（立即数）、
/// `7=XCell(ptr|7)`（字面量 / Prim / 卡住投影 / Sum / SumCase / Match）。
/// icit 不进打包字——由 Clo/Pi 单元与 spine 槽携带（打包字是 quote/unify
/// 记忆化的键，icit 随值结构唯一确定）。
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
pub(crate) fn v_u(lvl: u32) -> V {
    V(((lvl as u64) << 3) | 3)
}
#[inline]
pub(crate) fn v_pi<'a>(p: &'a PiCell<'a>) -> V {
    V((p as *const _ as u64) | 4)
}
#[inline]
pub(crate) fn v_meta(m: u32) -> V {
    V(((m as u64) << 3) | 5)
}
/// `LiteralType` 立即数。
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
/// tag 3 的宇宙层级。
#[inline]
pub(crate) fn v_u_of(v: V) -> u32 {
    (v.0 >> 3) as u32
}
/// tag 7 单元解引用（bump 内分配，本轮内有效）。
#[inline]
pub(crate) fn v_xcell_of<'a>(v: V) -> &'a XCell<'a> {
    unsafe { &*((v.0 & !7) as *const XCell) }
}

/// `Val::Sum` 的参数槽（值层，bump 内）。
#[derive(Clone)]
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

/// tag 7 的载体：字面量值、builtin 体标记、卡住声明引用、卡住投影、和
/// 类型本体、构造子值、卡住 match。判等按单元指针（同内容不同次求值各造
/// 单元——与参考版每次构造新值同构）；**位相等捷径对 tag 7 关闭**（见模块
/// 注释）。
pub(crate) enum XCell<'a> {
    Lit(&'a str),
    /// 卡住的声明引用（参考版 `Val::Decl(name, sp)` 的裸头）：decl 表
    /// 未登记 / 递归自引用的存根。带实参的卡住声明 = spine 链（头 = 本
    /// 单元），v_app 对 Decl 头压 spine。
    Decl { name: &'a str },
    /// builtin 体标记（带声明返回类型；v_app 对它 panic，故永无 Prim 头
    /// 的链）。
    Prim { typ: V, pid: PrimId },
    /// 卡住投影：被投影者 + 字段名。带实参的卡住投影 = spine 链（头 =
    /// 本单元），与参考版 `Val::Obj(v, name, sp)` 同构。
    Obj { val: V, name: &'a str },
    /// 和类型本体：名 + 参数槽（名/实参/实参类型/icit）+ 构造子名表 +
    /// is_trait（trait 脱糖的 enum）。
    Sum {
        name: &'a str,
        params: &'a [SumParamV<'a>],
        cases: &'a [&'a str],
        is_trait: bool,
    },
    /// 构造子值：typ 求值后是其所属的已实例化 `Sum`。
    SumCase {
        typ: V,
        case_name: &'a str,
        datas: &'a [SumDataV<'a>],
        is_trait: bool,
    },
    /// 卡住 match：scrutinee（创建时已 force）+ 捕获 env + 编译分支。
    /// **无 pending**——参考版 v_app 对 Match panic，卡住 match 永不吸收
    /// 实参。
    Match {
        scrutinee: V,
        env: Env<'a>,
        cases: &'a [(PatternDetail, &'a Tm<'a>)],
    },
}

/// decl 表条目（参考版 decl 行 `(Span, Tm, Val, Ty, VTy)` 的快版：Span 不
/// 进表（快版错误消息全零 Span）；`ty` 类型项在快版无读取点，省略）。
#[derive(Clone, Copy)]
pub(crate) struct DeclEntry<'a> {
    /// 登记项（参考版行的 .1；除 declb 重建口径外无读取点）。
    pub(crate) tm: &'a Tm<'a>,
    /// 登记值（参考版行的 .2；eval 的 `Tm::Decl` 臂与 string_to_global_type
    /// 直接取）。
    pub(crate) val: V,
    /// 类型值（参考版行的 .4；infer_expr 的 Var→decl 回落取它当类型）。
    pub(crate) vty: V,
}

/// 全局声明表（名字键；写时复制——[`Cxt::decls`] 是 `Rc<Decls>`，插入经
/// `Rc::make_mut`，与参考版逐 cxt clone 的语义一致）。
pub(crate) type Decls<'a> = FxHashMap<SmolStr, DeclEntry<'a>>;

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

/// 环境总槽数（链深 + 平坦区）。
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

/// 环境全部槽按 [`env_nth`] 的下标序单趟拷进 `out`：链段直走 +
/// 平坦区倒序读。`(0..env_len).map(env_nth)` 对链段每次从头重走，是
/// O(d²)；本函数一趟 O(d)（同 L07/L08 的 struct_eq / val_mentions_lvl 口径）。
#[inline]
pub(crate) fn env_collect(defs: &[V], env: Env<'_>, out: &mut Vec<V>) {
    let mut nb = env.binds;
    while let Some(e) = nb {
        out.push(e.val);
        nb = e.next;
    }
    for k in 0..env.flat_len {
        out.push(defs[(env.flat_base + env.flat_len - 1 - k) as usize]);
    }
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

/// 链头种类（`Entry.hk`）：push 时随函数侧传播，O(1) 判定链头是 Flex（force
/// 的唯一展开臂）/ 卡住投影 Obj（unify 的位相等捷径对它关闭）还是其它（Rigid / Decl
/// ——force 直接原样返回）。
const HK_OTHER: u8 = 0;
const HK_FLEX: u8 = 1;
const HK_OBJ: u8 = 2;

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
    /// 中性应用 `f a`（icit i）压栈，返回句柄值。`hk` 随函数侧传播：裸单元
    /// 直查种类，既有链延伸保持原种类（顶端槽已记下头种类）。
    #[inline]
    fn push(&mut self, f: V, a: V, icit: Icit) -> V {
        let idx = self.stack.len();
        let hk = match v_tag(f) {
            5 => HK_FLEX,
            7 => match v_xcell_of(f) {
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
        self.stack.push(Entry { f, a, icit, len, base, hk });
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
                if self.stack[h].hk != HK_FLEX {
                    return None;
                }
                let hd = self.spine_head(h);
                self.collect_args(h, out);
                Some(v_meta_of(hd))
            }
            _ => None,
        }
    }
}

/// 值是否 Flex（裸未解 meta 立即数或 meta 头的链——链查顶端槽的 `hk`，
/// O(1)，无需沿链走底）。
#[inline]
fn is_flex(spine: &Spine, v: V) -> bool {
    match v_tag(v) {
        5 => true,
        2 => spine.stack[v_spine_of(v)].hk == HK_FLEX,
        _ => false,
    }
}

// metacontext
// --------------------------------------------------------------------------------

/// metacontext 条目（与参考版同构）：**类型一律保留**（pruning 检查与
/// `lams` 都要读），解是 bump 内的打包值。Clone 供 temp-infer 探测的
/// 快照换入换出。
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

/// 从实参值取字面量内容（非字面量 → None）。返回值的 `'a` 与入参无
/// link——健全性依赖全局不变式：所有 `V` 的 XCell 都指向**当前轮的
/// bump**或 `'static` 钉串，跨轮 `bump.reset()` 前一切句柄已消亡。
#[inline]
fn lit_of<'a>(v: V) -> Option<&'a str> {
    match v_tag(v) {
        7 => match v_xcell_of(v) {
            XCell::Lit(s) => Some(s),
            _ => None,
        },
        _ => None,
    }
}

/// `v.field` 的值级投影：Sum 取索引参数的值；SumCase 先查 typ 的参数（索引）
/// 再查构造子字段。其余返回 None。（参考版 eval 的 Tm::Obj 臂自带
/// unwrap-panic 语义，调用方处理；本函数只在命中时给出值。）
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

/// 独立应用（eval_iter 之外的 v_app：force 的解值展开等）。λ → β；其余
/// 形态逐项对齐参考版 v_app：Rigid/Flex（裸或链）、卡住声明 Decl 与卡住
/// 投影 Obj → spine 压栈；字面量 / Prim / U / Π / LiteralType / Sum /
/// SumCase / 卡住 match → panic（"impossible apply"，参考版同款——两版
/// 同时不可达 / 同时 panic，判定一致）。
#[allow(clippy::too_many_arguments)]
fn vapp1<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decl: &Decls<'a>,
    mutable: &RefCell<FxHashMap<SmolStr, V>>,
    f: V,
    a: V,
    i: Icit,
) -> V {
    if v_tag(f) == 1 {
        let c = v_clo_of(f);
        let env = env_ext(bump, c.env, a);
        eval_iter(bump, spine, work, vals, icits, defs, metas, decl, mutable, env, c.body)
    } else if v_tag(f) == 7 {
        match v_xcell_of(f) {
            XCell::Obj { .. } | XCell::Decl { .. } => spine.push(f, a, i),
            _ => panic!("impossible apply"),
        }
    } else if v_tag(f) == 3 || v_tag(f) == 4 || v_tag(f) == 6 {
        panic!("impossible apply")
    } else {
        spine.push(f, a, i)
    }
}

// force（迭代；L11 参考版只有 Flex + Obj 两臂）
// --------------------------------------------------------------------------------

/// **force**：把值更新到 metacontext 的当前状态。参考版 `Infer::force`
/// 只有 Flex 臂（已解 → 展开应用；未解原样）与 Obj 臂（递归进内层重建）——
/// 无 pm 精化读点展开、无 Decl unfold（求值期替换 + 卡住存根，递归自然
/// 停在 `Val::Decl`）、无 Match 重选、无投影归约。无燃料（meta 解由
/// occurs check 保证无环，参考版同款裸递归）。
fn force<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decl: &Decls<'a>,
    mutable: &RefCell<FxHashMap<SmolStr, V>>,
    v0: V,
) -> V {
    let mut v = v0;
    let mut work: Vec<W<'a>> = Vec::new();
    let mut vals: Vec<V> = Vec::new();
    let mut icits: Vec<Icit> = Vec::new();
    let mut args: Vec<(V, Icit)> = Vec::new();
    loop {
        match v_tag(v) {
            5 => match &metas[v_meta_of(v) as usize] {
                MetaEntry::Solved(sol, _) => v = *sol,
                _ => return v,
            },
            2 => {
                let h = v_spine_of(v);
                if spine.stack[h].hk != HK_FLEX {
                    // Rigid / Obj / Decl 头的链：卡住（参考版 force 无对应臂）。
                    // O(1) 读顶端槽种类，省去非 flex 链的整趟走底
                    return v;
                }
                let hd = spine.spine_head(h);
                // flex 链：解应用到全部实参（应用序 = 收集序的逆序）；
                // 每步都可能 β（参考版 vAppSp 逐步 vApp 同款）
                match &metas[v_meta_of(hd) as usize] {
                    MetaEntry::Unsolved(_) => return v,
                    MetaEntry::Solved(sol, _) => {
                        args.clear();
                        spine.collect_args(h, &mut args);
                        let mut t = *sol;
                        for &(a, i) in args.iter().rev() {
                            t = vapp1(
                                bump, spine, &mut work, &mut vals, &mut icits, defs, metas, decl, mutable, t, a, i,
                            );
                        }
                        v = t;
                    }
                }
            }
            7 => match v_xcell_of(v) {
                // force 递归进卡住投影的内层并**重建** Obj（参考版 force
                // 的 Obj 臂：`Val::Obj(self.force(x), a, b)`，重建后即返回）。
                // 不能把新 Obj 赋回 v 继续循环：内层已是 force 的不动点，
                // 下一轮又落进本臂重建出同形值，死循环
                //（binder 下的嵌套投影 `l.a.x` 即触发）。
                XCell::Obj { val, name } => {
                    let v2 = force(bump, spine, defs, metas, decl, mutable, *val);
                    return v_xcell(bump.alloc(XCell::Obj { val: v2, name }));
                }
                _ => return v,
            },
            _ => return v,
        }
    }
}

// 运行时分支选择（值层首匹配，无合一；L09 参考版 Compiler::eval_aux 同款）
// --------------------------------------------------------------------------------

/// 按模式首匹配。参考版语义逐句对齐：
/// - 入口 force(head)；force 后非 SumCase → 任何 Con 模式都按"不在类型构造
///   子表里"的变量模式命中（`$unknown$` + 空表）。
/// - force 后是 SumCase：typ 必须 force 成 Sum（**否则 panic**——参考版
///   `panic!("by now only can match a sum type")`）；Con 模式名不在 Sum 的
///   cases 里 → 按变量模式命中（prepend head）；名 == case_name → datas 与
///   子模式 zip（**zip 截断**）逐个递归（每步单臂表，env 累积——**head 本身
///   不 prepend**，参考版 Con 臂从 cxt 起步）；同名异构造子 → 试下一分支。
fn eval_aux<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decl: &Decls<'a>,
    mutable: &RefCell<FxHashMap<SmolStr, V>>,
    head: V,
    env: Env<'a>,
    cases: &'a [(PatternDetail, &'a Tm<'a>)],
) -> Option<(&'a Tm<'a>, Env<'a>)> {
    let head = force(bump, spine, defs, metas, decl, mutable, head);
    let (case_name, datas, ctor_names): (&str, &[SumDataV<'a>], &[&str]) = if v_tag(head) == 7 {
        match v_xcell_of(head) {
            XCell::SumCase { typ, case_name, datas, .. } => {
                let cases_list = match v_xcell_of(*typ) {
                    XCell::Sum { cases, .. } => *cases,
                    // 参考 panic：typ 不是 Sum（declb 存根表下的重求值可达）
                    _ => panic!("by now only can match a sum type"),
                };
                (case_name, *datas, cases_list)
            }
            _ => ("$unknown$", &[], &[]),
        }
    } else {
        ("$unknown$", &[], &[])
    };
    for (pat, body) in cases.iter() {
        if let Some(r) = eval_aux_case(
            bump, spine, defs, metas, decl, mutable, head, case_name, datas, ctor_names, env, pat,
            *body,
        ) {
            return Some(r);
        }
    }
    None
}

/// 单 (模式, 分支体) 的匹配（`eval_aux` 的内层；返回 None = 试下一分支）。
/// 子模式的下钻走**完整 eval_aux**（对子值重新派生 case 信息——参考版
/// 递归同款，`[(pat.clone(), body)]` 单臂表也照克隆）。
#[allow(clippy::too_many_arguments)]
fn eval_aux_case<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decl: &Decls<'a>,
    mutable: &RefCell<FxHashMap<SmolStr, V>>,
    head: V,
    case_name: &str,
    datas: &[SumDataV<'a>],
    ctor_names: &[&str],
    env: Env<'a>,
    pat: &PatternDetail,
    body: &'a Tm<'a>,
) -> Option<(&'a Tm<'a>, Env<'a>)> {
    match pat {
        PatternDetail::Any(_) | PatternDetail::Bind(_) => {
            Some((body, env_ext(bump, env, head)))
        }
        PatternDetail::Con(name, subs) => {
            let in_type = ctor_names.iter().any(|c| *c == name.data);
            if !in_type {
                // 不是该类型的构造子名 → 变量模式（保守兼容；参考版首臂）
                Some((body, env_ext(bump, env, head)))
            } else if case_name == name.data {
                // datas 与子模式按序 zip（zip 截断；参考版 try_fold 同款：
                // 每步单臂完整 eval_aux，body 原样传递，env 累积——head 不
                // prepend）
                let mut cur_body = body;
                let mut cur_env = env;
                for (d, sub) in datas.iter().zip(subs.iter()) {
                    let arms1: &'a [(PatternDetail, &'a Tm<'a>)] =
                        bump.alloc([(sub.clone(), cur_body)]);
                    match eval_aux(
                        bump, spine, defs, metas, decl, mutable, d.val, cur_env, arms1,
                    ) {
                        Some((b, e)) => {
                            cur_body = b;
                            cur_env = e;
                        }
                        None => return None, // 子模式失配：试下一分支
                    }
                }
                Some((cur_body, cur_env))
            } else {
                None // 同类型不同构造子 → 试下一分支
            }
        }
    }
}

// eval（双栈迭代 + 右链快速路径 + AppPruning 实参应用 + L09 变体）
// --------------------------------------------------------------------------------

/// eval 的 work 栈条目。
enum W<'a> {
    Tm(&'a Tm<'a>, Env<'a>),
    /// 应用（icit 来自 `Tm::App`）：vals 顶两个（先函数后实参）。
    Apply(Icit),
    /// vals 顶上是实参；函数值已知是闭包，直接 β（icit 无关）。
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
    /// vals 顶是 `vAppPruning` 的当前值；本步把 `arg` 以 `icit` 应用上去。
    AppPrunOne(V, Icit),
    /// vals 顶是投影接收者的值（先 force）：Sum/SumCase 命中给投影值
    /// （**miss panic**，参考版 unwrap 同款）；其余形态一律卡成 Obj
    ///（参考版 `_` 臂——L09 才是仅 Rigid 卡、其余 panic）。
    ObjSel(&'a str),
    /// vals 顶自底向上是 (v0,t0,...,v_{n-1},t_{n-1})（求值序）：装配 Sum。
    SumAsm {
        name: &'a str,
        params: &'a [SumParamT<'a>],
        cases: &'a [&'a str],
        is_trait: bool,
    },
    /// vals 顶自底向上是 (typ, d0..d_{nd-1})：装配 SumCase。
    SumCaseAsm {
        case_name: &'a str,
        datas: &'a [SumDataT<'a>],
        is_trait: bool,
    },
    /// vals 顶是 scrutinee 的值：force 后是 SumCase → eval_aux 选分支
    /// （**None 即 panic**，参考版 unwrap 同款）；否则卡成 Match（无
    /// pending）。
    MatchSel {
        cases: &'a [(PatternDetail, &'a Tm<'a>)],
        env: Env<'a>,
    },
}

/// 双栈迭代 eval（L06 版 + L11 变体：Decl 表查名、带类型的 Prim 五路
/// 分派、投影的 panic 语义、match 的编译期选择与卡住停等）。
#[allow(clippy::too_many_arguments)]
fn eval_iter<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decl: &Decls<'a>,
    mutable: &RefCell<FxHashMap<SmolStr, V>>,
    env0: Env<'a>,
    tm0: &'a Tm<'a>,
) -> V {
    work.clear();
    vals.clear();
    icits.clear();
    work.push(W::Tm(tm0, env0));
    while let Some(w) = work.pop() {
        match w {
            W::Tm(Tm::Var(i), env) => {
                vals.push(env_nth(defs, env, *i));
            }
            // 全局声明：decl 表查名（登记值 = 检查过的体求值）；未登记 →
            // 卡 `Decl(name, 空 spine)`（参考版 `unwrap_or(Val::Decl(...))`
            // 同款——递归自引用 / string_to_global_type 逃逸的形态）。
            W::Tm(Tm::Decl(x), env) => {
                let _ = env;
                match decl.get(*x) {
                    Some(e) => vals.push(e.val),
                    None => vals.push(v_xcell(bump.alloc(XCell::Decl { name: x }))),
                }
            }
            W::Tm(Tm::Lam(name, icit, body), env) => {
                let c = bump.alloc(CloCell {
                    name,
                    icit: *icit,
                    env,
                    body,
                });
                vals.push(v_clo(c));
            }
            W::Tm(Tm::U(l), _) => vals.push(v_u(*l)),
            W::Tm(Tm::LiteralType, _) => vals.push(v_lit_ty()),
            W::Tm(Tm::LiteralIntro(s), _) => vals.push(v_xcell(bump.alloc(XCell::Lit(s)))),
            // builtin 体（带声明返回类型 + 函数标识；参考版 cxt.rs 5 个
            // PrimFunc 的逐句移植）：reduce 不成功 → 卡 `XCell::Prim { typ,
            // pid }`（v_app 对它 panic，永无 Prim 头的链）。env 槽数不足时
            // env_nth 越界 panic（参考版 unwrap 同款崩溃）。
            W::Tm(Tm::Prim(typ, pid), env) => match pid {
                // string_concat：env 前两槽全为字面量 → 拼接；否则卡住。
                PrimId::StringConcat => {
                    let b = env_nth(defs, env, 0);
                    let a = env_nth(defs, env, 1);
                    match (lit_of(a), lit_of(b)) {
                        (Some(a), Some(b)) => {
                            let len = a.len() + b.len();
                            let ptr = bump
                                .alloc_layout(std::alloc::Layout::from_size_align(len, 1).unwrap())
                                .as_ptr();
                            // SAFETY: a/b 都是 &str（合法 UTF-8）；两段完整
                            // 序列按字节拼接仍是合法 UTF-8，不会引入跨边界
                            // 截断的码点
                            let s = unsafe {
                                std::ptr::copy_nonoverlapping(a.as_ptr(), ptr, a.len());
                                std::ptr::copy_nonoverlapping(b.as_ptr(), ptr.add(a.len()), b.len());
                                std::str::from_utf8_unchecked(std::slice::from_raw_parts(ptr, len))
                            };
                            vals.push(v_xcell(bump.alloc(XCell::Lit(s))));
                        }
                        _ => vals.push(v_xcell(bump.alloc(XCell::Prim { typ: *typ, pid: *pid }))),
                    }
                }
                // string_to_global_type：首槽字面量 → decl 表查名（命中给
                // 登记值，未登记卡 `Decl(name)`——参考版 eval(Tm::Decl)
                // 同款逃逸）；非字面量卡住。
                PrimId::StringToGlobalType => {
                    match lit_of(env_nth(defs, env, 0)) {
                        Some(name) => match decl.get(name) {
                            Some(e) => vals.push(e.val),
                            None => vals.push(v_xcell(bump.alloc(XCell::Decl { name }))),
                        },
                        None => vals.push(v_xcell(bump.alloc(XCell::Prim { typ: *typ, pid: *pid }))),
                    }
                }
                // create_global：首槽字面量名字 + 次槽值 → mutable_map 写入
                //（参考版 RwLock write 同款；同线程重入自锁域不在这条路径）。
                PrimId::CreateGlobal => match lit_of(env_nth(defs, env, 1)) {
                    Some(name) => {
                        let v0 = env_nth(defs, env, 0);
                        mutable.borrow_mut().insert(SmolStr::new(name), v0);
                        vals.push(v_u(0));
                    }
                    None => vals.push(v_xcell(bump.alloc(XCell::Prim { typ: *typ, pid: *pid }))),
                },
                // change_mutable：首槽字面量名字，次槽函数应用到旧值再写回
                //（参考版 get_mut + v_app 同款；v_app 在持锁区间外执行——
                // 参考版持写锁期间 v_app 重入自锁，快版以短借用规避，行为
                // 仅在嵌套 builtin 的病理程序上可观察差异）。
                PrimId::ChangeMutable => match lit_of(env_nth(defs, env, 1)) {
                    Some(name) => {
                        let f = env_nth(defs, env, 0);
                        let old = mutable.borrow().get(name).copied();
                        if let Some(x) = old {
                            // 内层 β 用**独立草稿栈**——eval_iter 入口会清空
                            // work/vals/icits，复用外层栈会销毁外层 eval 的
                            // 待续状态（change 之后的下一条求值即被吞掉）
                            let mut w2: Vec<W<'a>> = Vec::new();
                            let mut v2: Vec<V> = Vec::new();
                            let mut i2: Vec<Icit> = Vec::new();
                            let nx = vapp1(
                                bump, spine, &mut w2, &mut v2, &mut i2, defs, metas, decl,
                                mutable, f, x, Icit::Expl,
                            );
                            mutable.borrow_mut().insert(SmolStr::new(name), nx);
                        }
                        vals.push(v_u(0));
                    }
                    None => vals.push(v_xcell(bump.alloc(XCell::Prim { typ: *typ, pid: *pid }))),
                },
                // get_global：首槽字面量名字 → mutable_map 读取（缺名 panic
                //——参考版 `unwrap()` 同款崩溃）。
                PrimId::GetGlobal => {
                    let name = lit_of(env_nth(defs, env, 0))
                        .expect("get_global: 名字非字面量");
                    let v = mutable.borrow().get(name).copied().unwrap();
                    vals.push(v);
                }
            },
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
            // 投影：求值接收者后 force（参考版 eval 的 Tm::Obj 臂同）。
            // Sum/SumCase 命中给投影值（miss panic，参考版 unwrap 同款）；
            // 其余形态一律卡成 Obj（参考版 `_` 臂）。
            W::Tm(Tm::Obj(h, name), env) => {
                work.push(W::ObjSel(name));
                work.push(W::Tm(h, env));
            }
            // enum 本体：逐参数求值（值 + 类型）后装配
            W::Tm(Tm::Sum(name, params, cases, is_trait), env) => {
                work.push(W::SumAsm { name, params, cases, is_trait: *is_trait });
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
                    is_trait,
                },
                env,
            ) => {
                work.push(W::SumCaseAsm { case_name, datas, is_trait: *is_trait });
                for d in datas.iter().rev() {
                    work.push(W::Tm(d.val, env));
                }
                work.push(W::Tm(typ, env));
            }
            // match：求值 scrutinee → force → 选分支 / 卡住（参考版 eval 的
            // Tm::Match 臂：SumCase + eval_aux 命中给分支体（**None 即
            // panic**）；其它 neutral 卡 Match，无 pending）
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
                        bump, spine, work, vals, icits, defs, metas, decl, mutable, vf, va, i,
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
                        bump, spine, work, vals, icits, defs, metas, decl, mutable, vf, v, i,
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
                        bump, spine, work, vals, icits, defs, metas, decl, mutable, v, arg, i,
                    );
                    vals.push(r);
                }
            }
            W::ObjSel(name) => {
                let v = vals.pop().expect("eval 栈：ObjSel 缺接收者");
                // L10：接收者先 force（参考版 eval 的 Obj 臂同款）
                let v = force(bump, spine, defs, metas, decl, mutable, v);
                match v_tag(v) {
                    7 => match v_xcell_of(v) {
                        XCell::Sum { params, .. } => {
                            match params.iter().find(|p| p.name == name) {
                                Some(p) => vals.push(p.val),
                                // 参考 unwrap：字段必在
                                None => panic!("impossible"),
                            }
                        }
                        XCell::SumCase { typ, datas, .. } => {
                            // typ 必须是 Sum（否则 panic "impossible"）；
                            // 索引参数优先，字段在后
                            let sparams = match v_xcell_of(*typ) {
                                XCell::Sum { params, .. } => *params,
                                _ => panic!("impossible"),
                            };
                            match sparams
                                .iter()
                                .find(|p| p.name == name)
                                .map(|p| p.val)
                                .or_else(|| datas.iter().find(|d| d.name == name).map(|d| d.val))
                            {
                                Some(p) => vals.push(p),
                                None => panic!("impossible"),
                            }
                        }
                        // L10：其余形态（Flex / 卡住 match / 卡住投影 /
                        // 字面量…）卡成 Obj（参考版 `_` 臂同款）
                        _ => vals.push(v_xcell(bump.alloc(XCell::Obj { val: v, name }))),
                    },
                    // 裸 Rigid / Rigid 链 / Flex / 卡住 match / 字面量……
                    // 一律卡成 Obj（参考版 eval 的 Tm::Obj `_` 臂）
                    _ => vals.push(v_xcell(bump.alloc(XCell::Obj { val: v, name }))),
                }
            }
            W::SumAsm { name, params, cases, is_trait } => {
                // vals 槽序 = v0, t0, v1, t1, ...（先压者在底）→ pop 序是
                // t_{n-1}, v_{n-1}, ...：按 params 逆序逐槽收进 ps，再整体
                // 反转回自然序——单缓冲，省掉 items 中转 + 二次下标拷贝
                let mut ps: Vec<SumParamV<'_>> = Vec::with_capacity(params.len());
                for p in params.iter().rev() {
                    let ty = vals.pop().expect("eval 栈：SumAsm 缺参数");
                    let val = vals.pop().expect("eval 栈：SumAsm 缺参数");
                    ps.push(SumParamV {
                        name: p.name,
                        val,
                        ty,
                        icit: p.icit,
                    });
                }
                ps.reverse();
                vals.push(v_xcell(bump.alloc(XCell::Sum {
                    name,
                    params: bump.alloc_slice_fill_iter(ps),
                    cases,
                    is_trait,
                })));
            }
            W::SumCaseAsm { case_name, datas, is_trait } => {
                // datas 字段在 vals 栈顶（typ 先压在底）：逆序 pop 落槽后
                // 反转，typ 最后 pop
                let mut ds: Vec<SumDataV<'_>> = Vec::with_capacity(datas.len());
                for d in datas.iter().rev() {
                    let val = vals.pop().expect("eval 栈：SumCaseAsm 缺字段");
                    ds.push(SumDataV {
                        name: d.name,
                        val,
                        icit: d.icit,
                    });
                }
                ds.reverse();
                let typ = vals.pop().expect("eval 栈：SumCaseAsm 缺 typ");
                vals.push(v_xcell(bump.alloc(XCell::SumCase {
                    typ,
                    case_name,
                    datas: bump.alloc_slice_fill_iter(ds),
                    is_trait,
                })));
            }
            W::MatchSel { cases, env } => {
                let sv = vals.pop().expect("eval 栈：MatchSel 缺 scrutinee");
                let s2 = force(bump, spine, defs, metas, decl, mutable, sv);
                if v_tag(s2) == 7 && matches!(v_xcell_of(s2), XCell::SumCase { .. }) {
                    match eval_aux(bump, spine, defs, metas, decl, mutable, s2, env, cases) {
                        Some((body_tm, env2)) => {
                            // 分支选中：体在本 eval 循环里尾推
                            work.push(W::Tm(body_tm, env2));
                        }
                        // L10：无臂命中 → 卡住 Match（参考版 None => Match）
                        None => vals.push(v_xcell(bump.alloc(XCell::Match {
                            scrutinee: s2,
                            env,
                            cases,
                        }))),
                    }
                } else {
                    vals.push(v_xcell(bump.alloc(XCell::Match {
                        scrutinee: s2,
                        env,
                        cases,
                    })));
                }
            }
        }
    }
    vals.pop().expect("eval 必须恰有一个根值")
}

// quote（任务栈迭代 + 流式右链；L09 变体）
// --------------------------------------------------------------------------------

/// quote 任务。`ChainRun` 的「断点续跑」语义见 L01/L04/L05/L06；quote 不产
/// `AppPruning`（项层洞形态，值层不存在）。L09 增量：`Obj1` / `SumAsm` /
/// `SumCaseAsm` 装配任务；`Match` 直接内联处理（分支体在"捕获 env + fresh
/// rigid 槽"下用**中性 global 视图**重求值再以真实表 quote——参考版
/// quote 的 Match 臂：avoid_recursive 克隆只作用于 eval，quote 用 self）。
enum QJob<'a> {
    /// 引一个值（先 force）。
    Q(V, u32),
    /// done 栈顶是体，包一层 Lam（名字与 icit 随闭包携带）。
    Lam1(&'a str, Icit),
    /// done 栈顶两个（先 cod 后 dom），合一个 Pi（icit 在 PiCell 里）。
    Pi1(&'a PiCell<'a>),
    /// 先 eval（引出闭包/余定义域的体）再引。
    EvalQ(&'a Tm<'a>, Env<'a>, u32),
    /// done 栈顶两个（先 f 后 a），合一个 App（icit 随任务携带）。
    App1(Icit),
    /// 记忆化屏障：done 栈顶是刚完成的 `Q(key, level)` 结果，入表后放回。
    MemoStore(u64, u32),
    /// 流式右链：next..=end 逐层 App 自底向上；f 与 f0 同一变量 / 同一未解
    /// meta 时用共享节点，否则挂起（Q 引 f）后续跑。
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
        is_trait: bool,
    },
    /// done 栈顶自底向上是 (typ, d0..)：装配 Tm::SumCase（元数据取值层槽）。
    SumCaseAsm {
        case_name: &'a str,
        datas: &'a [SumDataV<'a>],
        is_trait: bool,
    },
}

/// (值打包字, quote level) → 已引结果子树。icit 不进键：它随 `V` 指向的
/// 单元/槽位携带，同一打包字在同一 level 的 quote 产出（含 icit）唯一。
/// tag 7 的变体（Match/Sum/…）不进表：它们的引读依赖中性 global 视图与
/// meta 状态（参考版无 quote 记忆化，保守起见对新增值形态保持无记忆化
/// 口径）。
type QuoteMemo<'a> = FxHashMap<(u64, u32), &'a Tm<'a>>;

/// 任务栈 quote（L06 版 + LiteralType/LiteralIntro/Prim/Obj/Sum/SumCase/
/// Match 臂；L09：tag 0 的大下标直通、tag 3 带层级）。
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
    decl: &Decls<'a>,
    mutable: &RefCell<FxHashMap<SmolStr, V>>,
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
                // 先 force（metacontext 在 quote 期间冻结，同键同结果）
                let v = force(bump, spine, defs, metas, decl, mutable, v0);
                match v_tag(v) {
                    0 => {
                        let l = v_lvl_of(v);
                        done.push(bump.alloc(Tm::Var(level - l - 1)));
                    }
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
                    3 => done.push(bump.alloc(Tm::U(v_u_of(v)))),
                    // 字面量类型与字面量值（叶子，无 memo 收益）
                    6 => done.push(bump.alloc(Tm::LiteralType)),
                    7 => match v_xcell_of(v) {
                        XCell::Lit(s) => done.push(bump.alloc(Tm::LiteralIntro(s))),
                        // 卡住声明引用：原样产出 `Tm::Decl`（参考版 quote
                        // 的 Decl 臂；spine 在 tag 2 头分派处走 ChainRun）
                        XCell::Decl { name } => done.push(bump.alloc(Tm::Decl(name))),
                        XCell::Prim { typ, pid } => {
                            done.push(bump.alloc(Tm::Prim(*typ, *pid)))
                        }
                        XCell::Obj { val, name } => {
                            tasks.push(QJob::Obj1(name));
                            tasks.push(QJob::Q(*val, level));
                        }
                        XCell::Sum {
                            name,
                            params,
                            cases,
                            is_trait,
                        } => {
                            let is_trait = *is_trait;
                            tasks.push(QJob::SumAsm {
                                name,
                                params,
                                cases,
                                is_trait,
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
                            is_trait,
                        } => {
                            tasks.push(QJob::SumCaseAsm { case_name, datas, is_trait: *is_trait });
                            for d in datas.iter().rev() {
                                tasks.push(QJob::Q(d.val, level));
                            }
                            tasks.push(QJob::Q(*typ, level));
                        }
                        XCell::Match {
                            scrutinee,
                            env: menv,
                            cases,
                        } => {
                            // 分支体在"捕获 env + fresh rigid 槽"下用
                            // **declb 存根表**重新求值（每条目换成
                            // `Decl(name)` 卡住值——递归引用停在存根，参考
                            // 版 declb 同款），再以**真实表** quote（参考版
                            // quote 的 Match 臂分工逐字对应）。
                            let declb: Rc<Decls<'a>> = Rc::new(
                                decl.iter()
                                    .map(|(k, e)| {
                                        let name = bump.alloc_str(k.as_str());
                                        (
                                            k.clone(),
                                            DeclEntry {
                                                tm: bump.alloc(Tm::Decl(name)),
                                                val: v_xcell(bump.alloc(XCell::Decl { name })),
                                                vty: e.vty,
                                            },
                                        )
                                    })
                                    .collect(),
                            );
                            let mut qc: Vec<(PatternDetail, &'a Tm<'a>)> =
                                Vec::with_capacity(cases.len());
                            for (p, b) in cases.iter() {
                                let count = p.bind_count();
                                let mut env2 = *menv;
                                for i in 0..count {
                                    env2 = env_ext(bump, env2, v_lvl(level + i));
                                }
                                let tv = eval_iter(
                                    bump, spine, work, vals, icits, defs, metas, &declb, mutable,
                                    env2, b,
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
                                    mutable,
                                    level + count,
                                    tv,
                                    None,
                                );
                                qc.push(((*p).clone(), q));
                            }
                            let cs: &'a [(PatternDetail, &'a Tm<'a>)] =
                                bump.alloc_slice_fill_iter(qc);
                            // scrutinee 用真实表（调用方的 level 下正确）
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
                                decl,
                                mutable,
                                level,
                                *scrutinee,
                                None,
                            );
                            done.push(bump.alloc(Tm::Match(sq, cs)));
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
                        // spine 链（Rigid / Flex / Obj 头）
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
                                0 => {
                                    let l = v_lvl_of(f0);
                                    Some(&*bump.alloc(Tm::Var(level - l - 1)) as &Tm<'a>)
                                }
                                // flex 链头：未解 meta 立即数（已解的在
                                // force 里早已展开），共享单一 ?m 节点
                                5 => Some(&*bump.alloc(Tm::Meta(v_meta_of(f0))) as &Tm<'a>),
                                // Obj 头的链（内层值要按 level 引读）挂起走 Q
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
                    bump, spine, work, vals, icits, defs, metas, decl, mutable, env, body,
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
                is_trait,
            } => {
                // done 槽序 = v0, t0, v1, t1, ...（先压者在底）→ 按 params
                // 逆序逐槽收进 ps 再反转，省掉 items 中转 + 二次下标拷贝
                let mut ps: Vec<SumParamT<'_>> = Vec::with_capacity(params.len());
                for p in params.iter().rev() {
                    let ty = done.pop().expect("quote 栈：Sum 缺参数");
                    let val = done.pop().expect("quote 栈：Sum 缺参数");
                    ps.push(SumParamT {
                        name: p.name,
                        val,
                        ty,
                        icit: p.icit,
                    });
                }
                ps.reverse();
                done.push(bump.alloc(Tm::Sum(
                    name,
                    bump.alloc_slice_fill_iter(ps),
                    cases,
                    is_trait,
                )));
            }
            QJob::SumCaseAsm { case_name, datas, is_trait } => {
                // datas 字段在 done 栈顶（typ 先压在底）：逆序 pop 落槽后
                // 反转，typ 最后 pop
                let mut ds: Vec<SumDataT<'_>> = Vec::with_capacity(datas.len());
                for d in datas.iter().rev() {
                    let val = done.pop().expect("quote 栈：SumCase 缺字段");
                    ds.push(SumDataT {
                        name: d.name,
                        val,
                        icit: d.icit,
                    });
                }
                ds.reverse();
                let typ = done.pop().expect("quote 栈：SumCase 缺 typ");
                done.push(bump.alloc(Tm::SumCase {
                    typ,
                    case_name,
                    datas: bump.alloc_slice_fill_iter(ds),
                    is_trait,
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

// unify（工作表迭代；L09 参考版臂序，无燃料、无 pm 臂、无 (Obj,Obj) 臂）
// --------------------------------------------------------------------------------

/// A/B 实验开关（unify 工作表的判等记忆化消融）：置 `L06_NO_CONV_MEMO=1`
/// 关闭（`=0` 不关闭）。
static NO_CONV_MEMO: std::sync::LazyLock<std::sync::atomic::AtomicBool> =
    std::sync::LazyLock::new(|| {
        std::sync::atomic::AtomicBool::new(std::env::var("L06_NO_CONV_MEMO").is_ok_and(|v| v != "0"))
    });

/// unify 的跨调用草稿。
#[derive(Default)]
struct ConvScratch {
    memo: FxHashSet<(u64, u64)>,
    scratch1: Vec<(V, Icit)>,
    scratch2: Vec<(V, Icit)>,
}

/// unify 工作表条目：待比较子对、Π 余定义域的惰性比较屏障、判等记忆化
/// 屏障、或卡住 match 的惰性展开屏障（declb 存根表下重求值后压
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
    /// 下用 **declb 存根表**重求值，再压 `l + count` 层的体对。
    MatchBranch {
        b1: &'a Tm<'a>,
        e1: Env<'a>,
        b2: &'a Tm<'a>,
        e2: Env<'a>,
        declb: Rc<Decls<'a>>,
        l: u32,
        count: u32,
    },
    /// Match/Match 的结构展开屏障（scrutinee 对比完后到达）：cases 长度
    /// 检查、分支对展开（参考版 scrutinee unify 之后的余下步骤，副作用
    /// 时序与参考版一致）。
    MatchStruct {
        e1: Env<'a>,
        e2: Env<'a>,
        c1: &'a [(PatternDetail, &'a Tm<'a>)],
        c2: &'a [(PatternDetail, &'a Tm<'a>)],
        declb: Rc<Decls<'a>>,
        l: u32,
    },
    /// 分支 pattern 相等检查（参考版逐分支在分支体之前）。
    MatchPattern(&'a PatternDetail, &'a PatternDetail),
}

/// 从 decl 表构建 declb 存根表（每条目换成 `Decl(name)` 卡住值——递归
/// 引用停在存根；参考版 declb 逐字同构）。
fn declb_of<'a>(bump: &'a Bump, decl: &Decls<'a>) -> Rc<Decls<'a>> {
    Rc::new(
        decl.iter()
            .map(|(k, e)| {
                let name = bump.alloc_str(k.as_str());
                (
                    k.clone(),
                    DeclEntry {
                        tm: bump.alloc(Tm::Decl(name)),
                        val: v_xcell(bump.alloc(XCell::Decl { name })),
                        vty: e.vty,
                    },
                )
            })
            .collect(),
    )
}

/// 链（或裸单元）是否卡住投影 Obj 头——unify 的位相等捷径对它关闭
/// （参考版无 `(Obj, Obj)` 臂，同单元也须走 `_` → Err）。
#[inline]
fn is_objheaded(spine: &Spine, v: V) -> bool {
    match v_tag(v) {
        7 => matches!(v_xcell_of(v), XCell::Obj { .. }),
        2 => spine.stack[v_spine_of(v)].hk == HK_OBJ,
        _ => false,
    }
}

/// `?m args ≡ ?m args'`（同头 flex）：上游 `intersect`。逐槽（内→外）
/// 都取到裸变量则产出掩码（槽位相等 → 其 icit、不等 → None）；有 None 即
/// 剪枝（`pruneMeta`），全相等即成立。长度不等直接失败。任一对含非变量
/// → 回落 `unify_sp` 逐实参比较。
#[allow(clippy::too_many_arguments)]
fn intersect_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    decl: &Decls<'a>,
    mutable: &RefCell<FxHashMap<SmolStr, V>>,
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
        let f1 = force(bump, spine, defs, metas, decl, mutable, args1[k].0);
        let f2 = force(bump, spine, defs, metas, decl, mutable, args2[k].0);
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
            return prune_meta_bump(bump, spine, work, vals, icits, defs, metas, decl, mutable, &pr, m)
                .is_some();
        }
        return true; // 两 spine 逐槽相等
    }
    // unify_sp 回落：前缀对压栈（内先压 → 弹出外先，对齐 unify_sp 的递归序）。
    // tag 7 不跳过：参考版对字面量实参照走 unify（恒败）——位相等的同单元
    // 也须分派（见 unify 的 tag 7 守卫）。
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
/// 失败则用另一侧求解（rhs 是整条 flex 值）。**L09 参考版无快照回滚、
/// 无第二方向**——单次尝试，失败即 Err（部分 meta 写入保留，参考版同款）。
#[allow(clippy::too_many_arguments)]
fn flex_flex_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    decl: &Decls<'a>,
    mutable: &RefCell<FxHashMap<SmolStr, V>>,
    ren: &mut RenBuf,
    gamma: u32,
    m1: u32,
    args1: &[(V, Icit)],
    v1: V,
    m2: u32,
    args2: &[(V, Icit)],
    v2: V,
) -> bool {
    // 方向选择与参考版一致：`sp.len() < sp_prime.len()` → (m', sp') 先；
    // 相等/更长 → (m, sp) 先。调用点约定（L08 同款）：v1 = u（m1 侧的
    // rhs），v2 = t（m2 侧的 rhs）。
    let (fa, aa, va, fb, ab, vb) = if args1.len() < args2.len() {
        (m2, args2, v2, m1, args1, v1)
    } else {
        (m1, args1, v1, m2, args2, v2)
    };
    match invert_bump(bump, spine, defs, metas, decl, mutable, ren, aa) {
        Some(mask) => solve_with_pren_bump(
            bump, spine, work, vals, icits, defs, metas, decl, mutable, ren, fa, aa.len() as u32, gamma,
            mask, va,
        ),
        None => solve_bump(
            bump, spine, work, vals, icits, defs, metas, decl, mutable, ren, gamma, fb, ab, vb,
        ),
    }
}

/// 同头链（unify_sp）的实参 lockstep 比较：长度失配即败；实参 icit 不比
/// （类型已定，上游同款）。位相等的实参对免比（tag 7 与 Obj 头链除外——
/// 字面量恒败、卡住投影走 `_` → Err）。
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
        // Obj 头的链（tag 2 头 = Obj 单元）同样不免——参考版无 (Obj, Obj)
        // 臂，交回完整分派后走 `_` → Err。
        let skip1 = a1.0 == a2.0 && v_tag(a1) != 7 && !is_objheaded(spine, a1);
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

/// 裸 Rigid（tag 0）或 Rigid 头的链的层级；非此形态返回 None。
#[inline]
fn rigid_lvl(spine: &Spine, v: V) -> Option<u32> {
    match v_tag(v) {
        0 => Some(v_lvl_of(v)),
        2 => {
            let h = v_spine_of(v);
            if spine.stack[h].hk != HK_OTHER {
                return None; // flex / Obj / Decl 头：必非 Rigid，免走底
            }
            let hd = spine.spine_head(h);
            if v_tag(hd) == 0 {
                Some(v_lvl_of(hd))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// unification：结构比较 + meta 求解（含 intersect / flex-flex / 剪枝），
/// 工作表迭代。臂序与参考版 `Infer::unify` 逐项对应（顺序敏感）：
/// U → Π（icit 相等）→ Rigid/Rigid 同级 → 同头 flex = intersect → 异头
/// flex-flex（单方向）→ λ/η → flex 求解 → LiteralType/宽松臂 → Sum/Sum →
/// SumCase/SumCase（typ+datas）→ Match/Match（scrutinee + 中性分支体重
/// 求值）→ 失配。**位相等捷径对 tag 7 与 Obj 头链关闭**：参考版对字面量
/// 无自反臂（同字面量也 Err）、卡住投影走 `_` → Err；捷径放行会误 Accept。
/// 无燃料（参考版无 fuel）；无 pm 臂（L09 的模式特化在 elaboration 侧的
/// unify_pm/update_cxt 完成）。
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
    decl: &Decls<'a>,
    mutable: &RefCell<FxHashMap<SmolStr, V>>,
    ren: &mut RenBuf,
    conv: &mut ConvScratch,
    l0: u32,
    t0: V,
    u0: V,
    cxt: &Cxt<'a>,
    mach_ptr: *mut Machine,
    trait_err: &mut Option<String>,
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
                    eval_iter(bump, spine, work, vals, icits, defs, metas, decl, mutable, env, b1)
                };
                let vu = {
                    let env = env_ext(bump, e2, v_lvl(l));
                    eval_iter(bump, spine, work, vals, icits, defs, metas, decl, mutable, env, b2)
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
                // bind_count，lvl 从 l 起）"下用 declb 存根表重求值，再在
                // l+count 层比较（参考版 unify 的 Match/Match 全路径同款）
                let mut env1 = e1;
                let mut env2 = e2;
                for i in 0..count {
                    env1 = env_ext(bump, env1, v_lvl(l + i));
                    env2 = env_ext(bump, env2, v_lvl(l + i));
                }
                let v1 = eval_iter(
                    bump, spine, work, vals, icits, defs, metas, &declb, mutable, env1, b1,
                );
                let v2 = eval_iter(
                    bump, spine, work, vals, icits, defs, metas, &declb, mutable, env2, b2,
                );
                stack.push(UItem::Pair(l + count, v1, v2));
                continue;
            }
            UItem::MatchStruct {
                e1,
                e2,
                c1,
                c2,
                declb,
                l,
            } => {
                // scrutinee 已比完（参考版 unify 的 Match/Match 臂 scrutinee
                // 递归之后）：cases 长度检查 → 逐分支（pattern → 分支体）。
                // LIFO 按执行序的逆序压：分支（体 → pattern，反序）
                if c1.len() != c2.len() {
                    return false;
                }
                for (i, ((p1, b1), (_, b2))) in c1.iter().zip(c2.iter()).enumerate().rev() {
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
            UItem::Pair(l, t, u) => (l, t, u),
        };
        // 位相等：同一值。tag 7 与 Obj 头链例外（见函数注释——参考版对
        // 字面量无自反性、卡住投影走 `_` → Err）
        if t.0 == u.0 && v_tag(t) != 7 && !is_objheaded(spine, t) {
            continue;
        }
        if memo_on && memo.contains(&(t.0, u.0)) {
            continue; // 本轮已判等过的子对（命中连 force 都省——成功单调）
        }
        let t = force(bump, spine, defs, metas, decl, mutable, t);
        let u = force(bump, spine, defs, metas, decl, mutable, u);
        if t.0 == u.0 && v_tag(t) != 7 && !is_objheaded(spine, t) {
            continue; // force 展开后同值（同一解的两处引用）
        }

        // —— 宇宙（参考臂 1）：层级相等才成立（无累积）——
        if v_tag(t) == 3 && v_tag(u) == 3 {
            if v_u_of(t) == v_u_of(u) {
                continue;
            }
            return false;
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
        // —— Rigid/Rigid（参考臂 3）：同级比实参 spine（裸×裸自反成立），
        // 异级落到后续臂（λ/η 等仍可命中，最终 `_` 失配）——
        if v_tag(t) == 0 && v_tag(u) == 0 {
            if v_lvl_of(t) == v_lvl_of(u) {
                continue; // 双裸单元：unify_sp([][]) 自反成立
            }
        }
        // —— 中性链 vs 中性链（参考臂 3/4/5 的链形态全在此分派）——
        if v_tag(t) == 2 && v_tag(u) == 2 {
            let h1 = v_spine_of(t);
            let h2 = v_spine_of(u);
            let hd1 = spine.spine_head(h1);
            let hd2 = spine.spine_head(h2);
            let f1 = v_tag(hd1) == 5;
            let f2 = v_tag(hd2) == 5;
            if f1 && f2 {
                // 双 flex：同头 intersect、异头 flex_flex（参考臂 4/5）
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
                        bump, spine, work, vals, icits, defs, metas, decl, mutable, stack, l, m1, &a1,
                        &a2,
                    )
                } else {
                    flex_flex_bump(
                        bump, spine, work, vals, icits, defs, metas, decl, mutable, ren, l, m1, &a1, u,
                        m2, &a2, t,
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
            // —— Decl 头链的同名判定（参考臂 3.5 的链形态）：头都是卡住
            // 声明 → 同名 unlockstep 比实参、异名失配；其余组合落同头/异头
            // 分派 ——
            if v_tag(hd1) == 7 && v_tag(hd2) == 7 {
                if let (
                    XCell::Decl { name: n1 },
                    XCell::Decl { name: n2 },
                ) = (v_xcell_of(hd1), v_xcell_of(hd2))
                {
                    if n1 == n2 {
                        if memo_on {
                            stack.push(UItem::Store((t.0, u.0)));
                        }
                        if !unify_sp_lockstep(spine, stack, l, h1, h2) {
                            return false;
                        }
                        continue;
                    }
                    return false;
                }
            }
            // 同头判定：位相等（同变量 / 同 meta / 同卡住投影单元）
            if hd1.0 == hd2.0 {
                if !is_objheaded(spine, hd1) {
                    // 同头刚性/卡住投影以外的头：逐实参比较（lockstep，长度
                    // 失配即败）；Obj 头交回 `_`（参考版无 (Obj,Obj) 臂）
                    if memo_on {
                        stack.push(UItem::Store((t.0, u.0)));
                    }
                    if !unify_sp_lockstep(spine, stack, l, h1, h2) {
                        return false;
                    }
                    continue;
                }
                return false; // 同单元 Obj 链：参考版 `_` → Err
            }
            // 异头：一侧 flex 头（f1/f2 已排除双 flex）→ 该侧 solve（参考
            // 臂 9/10 的链形态）；双刚性异级 / Obj 头组合 → 失配。
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
                bump, spine, work, vals, icits, defs, metas, decl, mutable, ren, l, mv, &args, rhs,
            );
            if solved {
                let tr = unsafe { (&mut *mach_ptr).solve_multi_trait_ref(bump, cxt, mv) };
                if let Err(e) = tr {
                    *trait_err = Some(e);
                    conv.scratch1 = args;
                    return false;
                }
            }
            conv.scratch1 = args;
            if solved {
                if memo_on {
                    memo.insert((t.0, u.0));
                }
                continue;
            }
            return false;
        }
        // —— 裸 Rigid vs 链（同级）：参考臂 3 的 unify_sp——裸侧空 spine
        // 与链长失配即败；异级落后续臂 ——
        if v_tag(t) == 0 && v_tag(u) == 2 {
            if rigid_lvl(spine, u) == Some(v_lvl_of(t)) {
                return false; // 空 spine vs 非空链：长度失配
            }
        }
        if v_tag(t) == 2 && v_tag(u) == 0 {
            if rigid_lvl(spine, t) == Some(v_lvl_of(u)) {
                return false;
            }
        }
        // —— λ / η（参考臂 6/7/8；在 flex 求解之前：Flex vs λ 走 η）——
        if v_tag(t) == 1 && v_tag(u) == 1 {
            let c1 = v_clo_of(t);
            let c2 = v_clo_of(u);
            let vt = {
                let env = env_ext(bump, c1.env, v_lvl(l));
                eval_iter(bump, spine, work, vals, icits, defs, metas, decl, mutable, env, c1.body)
            };
            let vu = {
                let env = env_ext(bump, c2.env, v_lvl(l));
                eval_iter(bump, spine, work, vals, icits, defs, metas, decl, mutable, env, c2.body)
            };
            if memo_on {
                stack.push(UItem::Store((t.0, u.0)));
            }
            stack.push(UItem::Pair(l + 1, vt, vu));
            continue;
        }
        // η：中性一侧按 λ 一侧的 icit 应用（卡住投影的应用压链；卡住
        // match / 字面量等形态的应用 panic——参考版 v_app 同款）
        if v_tag(u) == 1 {
            let c = v_clo_of(u);
            let vu = {
                let env = env_ext(bump, c.env, v_lvl(l));
                eval_iter(bump, spine, work, vals, icits, defs, metas, decl, mutable, env, c.body)
            };
            let vt = vapp1(
                bump, spine, work, vals, icits, defs, metas, decl, mutable, t, v_lvl(l), c.icit,
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
                eval_iter(bump, spine, work, vals, icits, defs, metas, decl, mutable, env, c.body)
            };
            let vu = vapp1(
                bump, spine, work, vals, icits, defs, metas, decl, mutable, u, v_lvl(l), c.icit,
            );
            if memo_on {
                stack.push(UItem::Store((t.0, u.0)));
            }
            stack.push(UItem::Pair(l + 1, vt, vu));
            continue;
        }
        // —— flex 求解（参考臂 4/5/9/10 的裸形态）——
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
                            bump, spine, work, vals, icits, defs, metas, decl, mutable, stack, l, m1,
                            &a1, &a2,
                        )
                    } else {
                        flex_flex_bump(
                            bump, spine, work, vals, icits, defs, metas, decl, mutable, ren, l, m1, &a1,
                            u, m2, &a2, t,
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
                        bump, spine, work, vals, icits, defs, metas, decl, mutable, ren, l, m, &a1, u,
                    );
                    if ok {
                        // 参考 solve 臂：解后跑 trait 合成（失败 → Err）
                        let tr = unsafe { (&mut *mach_ptr).solve_multi_trait_ref(bump, cxt, m) };
                        if let Err(e) = tr {
                            *trait_err = Some(e);
                            conv.scratch1 = a1;
                            conv.scratch2 = a2;
                            return false;
                        }
                    }
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
                        bump, spine, work, vals, icits, defs, metas, decl, mutable, ren, l, m, &a2, t,
                    );
                    if ok {
                        let tr = unsafe { (&mut *mach_ptr).solve_multi_trait_ref(bump, cxt, m) };
                        if let Err(e) = tr {
                            *trait_err = Some(e);
                            conv.scratch1 = a1;
                            conv.scratch2 = a2;
                            return false;
                        }
                    }
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
                    // 非 flex：落到字面量 / Sum / SumCase / Match 臂
                }
            }
        }
        // —— (LiteralType, LiteralType)（参考臂 11）——
        if v_tag(t) == 6 && v_tag(u) == 6 {
            continue;
        }
        // —— Prim 带类型臂（参考臂 12/12.5）：`(_, Prim(b, _)) → unify(t, b)`
        // 与 `(Prim(a, _), _) → unify(a, u)`（参考版逐字——先检次位再检
        // 首位；双 Prim 经两臂传导到 typ-vs-typ）——
        if v_tag(u) == 7 {
            if let XCell::Prim { typ, .. } = v_xcell_of(u) {
                stack.push(UItem::Pair(l, t, *typ));
                continue;
            }
        }
        if v_tag(t) == 7 {
            if let XCell::Prim { typ, .. } = v_xcell_of(t) {
                stack.push(UItem::Pair(l, *typ, u));
                continue;
            }
        }
        // —— Sum/Sum（参考臂 13）：同名即逐参数（含索引）值合一；zip 语义
        // （参数数不等取 min——参考版同款）；异名失配 ——
        if v_tag(t) == 7 && v_tag(u) == 7 {
            let (xt, xu) = (v_xcell_of(t), v_xcell_of(u));
            // —— Decl/Decl 同名（参考臂 3.5）：裸头同名比 spine（空 spine
            // 即成立）；异名失配（参考版 `_` 落点同款）——
            if let (XCell::Decl { name: n1 }, XCell::Decl { name: n2 }) = (xt, xu) {
                if n1 == n2 {
                    continue;
                }
                return false;
            }
            if let (
                XCell::Sum {
                    name: n1,
                    params: p1,
                    ..
                },
                XCell::Sum {
                    name: n2,
                    params: p2,
                    ..
                },
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
            // —— SumCase/SumCase（参考臂 14）：同构造子才比；**typ 与 datas
            // 都比**（typ 先、datas 后——L09 参考版与 L07+ 的 datas-only 不
            // 同）——
            if let (
                XCell::SumCase {
                    typ: ty1,
                    case_name: c1,
                    datas: d1,
                    ..
                },
                XCell::SumCase {
                    typ: ty2,
                    case_name: c2,
                    datas: d2,
                    ..
                },
            ) = (xt, xu)
            {
                if c1 == c2 {
                    // pop 序 = typ, d0, d1, ...（参考版执行序）
                    for (a, b) in d1.iter().zip(d2.iter()).rev() {
                        stack.push(UItem::Pair(l, a.val, b.val));
                    }
                    stack.push(UItem::Pair(l, *ty1, *ty2));
                    continue;
                }
                return false; // 异 case：参考版无后续可命中臂 → Err
            }
            // —— Match/Match（参考臂 15）：scrutinee 最先合一（真实副作用
            // 时序），cases 长度与 pattern 检查及其后分支体的中性重求值由
            // MatchStruct 屏障执行 ——
            if let (
                XCell::Match {
                    scrutinee: s1,
                    env: e1,
                    cases: c1,
                },
                XCell::Match {
                    scrutinee: s2,
                    env: e2,
                    cases: c2,
                },
            ) = (xt, xu)
            {
                stack.push(UItem::MatchStruct {
                    e1: *e1,
                    e2: *e2,
                    c1,
                    c2,
                    declb: declb_of(bump, decl),
                    l,
                });
                stack.push(UItem::Pair(l, *s1, *s2));
                continue;
            }
        }
        // —— (Obj, Obj) 合同臂（L10 新增）：字段名同 ⇒ 比接收者 + spine
        // 实参（参考版 unify 的 Obj/Obj 臂同款）——
        if is_objheaded(spine, t) && is_objheaded(spine, u) {
            let (hc1, hc2) = (
                if v_tag(t) == 7 { t } else { spine.spine_head(v_spine_of(t)) },
                if v_tag(u) == 7 { u } else { spine.spine_head(v_spine_of(u)) },
            );
            let (o1, n1, o2, n2) = match (v_xcell_of(hc1), v_xcell_of(hc2)) {
                (
                    XCell::Obj { val: a1, name: m1 },
                    XCell::Obj { val: a2, name: m2 },
                ) => (*a1, *m1, *a2, *m2),
                _ => return false,
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
                _ => return false,
            }
            continue;
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
    /// 只克隆到本代有效高水位（stamp==epoch 的最高槽）：容量只增不减，
    /// 整表克隆会背上历史最高 level 的死重；水位之上的条目本代无效，
    /// `get` 视同缺项，语义不变。
    fn clone_valid(&self) -> RenBuf {
        // 自尾回看取高水位：本代最后写入的槽通常就在尾部，几步即命中
        let end = self
            .stamp
            .iter()
            .rposition(|&g| g == self.epoch)
            .map_or(0, |i| i + 1);
        RenBuf {
            val: self.val[..end].to_vec(),
            stamp: self.stamp[..end].to_vec(),
            epoch: self.epoch,
        }
    }
}

/// 上游 `invert`：实参（应用序）逐个 force 成**裸刚性变量**。非线性
/// （重复变量）移出 renaming、记 `NONE_MARK`，产出把重复变量的全部出现
/// 记为 `None` 的掩码（**与 args 逆序 = 应用序**：最外层实参的槽在前；
/// 消费端 [`prune_ty_bump`] rev 迭代配对 Π 层）；线性时返回空 vec。非变量
/// 实参（字面量 / 带链变量 / Match）即失败（`None`）。
/// **L09 参考版无 gamma 上界检查**——全局层级（越过哨兵）同样进映射
/// （忠实移植，含其后果）。
#[allow(clippy::too_many_arguments)]
fn invert_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decl: &Decls<'a>,
    mutable: &RefCell<FxHashMap<SmolStr, V>>,
    ren: &mut RenBuf,
    args: &[(V, Icit)], // 内先序（spine 收集器的输出）
) -> Option<Vec<Option<Icit>>> {
    let _ = bump;
    ren.reset(); // 换代：本反演的映射从空开始
    let mut lvs: Vec<u32> = Vec::with_capacity(args.len());
    let mut nonlinear = false;
    for &(a, _) in args.iter().rev() {
        // 应用序（外先）
        let f = force(bump, spine, defs, metas, decl, mutable, a);
        if v_tag(f) != 0 {
            return None;
        }
        let x = v_lvl_of(f);
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
    decl: &Decls<'a>,
    mutable: &RefCell<FxHashMap<SmolStr, V>>,
    ren: &mut RenBuf,
    m: u32,
    dom: u32,
    gamma: u32,
    mask: Vec<Option<Icit>>, // invert 的非线性掩码（空 vec = 线性）
    rhs: V,
) -> bool {
    let mty = match &metas[m as usize] {
        MetaEntry::Unsolved(a) => *a,
        _ => unreachable!(), // 只对未解 meta 求解
    };
    // 非线性 spine：检查非线性的变量槽位可以从 meta 类型里剪掉
    if !mask.is_empty()
        && prune_ty_bump(bump, spine, work, vals, icits, defs, metas, decl, mutable, &mask, mty)
            .is_none()
    {
        return false;
    }
    let Some(tm) = rename_iter(
        bump, spine, work, vals, icits, defs, ren, metas, decl, mutable, Some(m), dom, gamma, rhs,
    ) else {
        return false;
    };
    let lam_tm = lams_from_ty(
        bump, spine, work, vals, icits, defs, metas, decl, mutable, dom, mty, tm,
    );
    let sol = eval_iter(
        bump, spine, work, vals, icits, defs, metas, decl, mutable, EMPTY_ENV, lam_tm,
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
    decl: &Decls<'a>,
    mutable: &RefCell<FxHashMap<SmolStr, V>>,
    ren: &mut RenBuf,
    gamma: u32,
    m: u32,
    args: &[(V, Icit)],
    rhs: V,
) -> bool {
    let _ = gamma;
    match invert_bump(bump, spine, defs, metas, decl, mutable, ren, args) {
        Some(mask) => solve_with_pren_bump(
            bump, spine, work, vals, icits, defs, metas, decl, mutable, ren, m, args.len() as u32,
            gamma, mask, rhs,
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

/// partial renaming 的迭代版（L06 版 + L09 增量：tag 0 的大下标直通、
/// tag 3 带层级、无 Decl 头、Prim 无名；Match 的分支体在"捕获 env + fresh
/// rigid 槽"下用**中性 global 视图**重求值，再在**独立克隆的 renaming**
/// （lift 过 count 次）下 rename——参考版按分支 clone 整个 HashMap，这里
/// 逐代克隆 RenBuf）。
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
    decl: &Decls<'a>,
    mutable: &RefCell<FxHashMap<SmolStr, V>>,
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
                let v = force(bump, spine, defs, metas, decl, mutable, v);
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
                        // scope check（x 不在 spine 映射里；非线性哨兵也算缺项）。
                        // 全局层级没有逃逸通道——ren miss 即 Err（参考版
                        // rename 的 Rigid 臂同款）。
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
                                    bump, spine, work, vals, icits, defs, ren, metas, decl, mutable,
                                    occ, dom, cod, m, h,
                                )?;
                                done.push(t);
                            }
                            // 卡住投影/卡住声明头的链：rename 内层再以 Tm::Obj / Tm::Decl 为头
                            // 节点折叠实参（参考版 rename 的 Obj/Decl 臂同款）
                            7 => {
                                let head_tm: &'a Tm<'a> = bump.alloc(match v_xcell_of(hd) {
                                    XCell::Obj { val, name } => {
                                        let inner = rename_iter(
                                            bump, spine, work, vals, icits, defs, ren, metas, decl, mutable, occ, dom, cod, *val,
                                        )?;
                                        Tm::Obj(inner, name)
                                    }
                                    XCell::Decl { name } => Tm::Decl(name),
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
                                bump, spine, work, vals, icits, defs, metas, decl, mutable, env, c.body,
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
                                bump, spine, work, vals, icits, defs, metas, decl, mutable, env, cell.body,
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
                    3 => done.push(bump.alloc(Tm::U(v_u_of(v)))),
                    // 字面量类型与裸单元（Lit / Prim 空链）直出
                    6 => done.push(bump.alloc(Tm::LiteralType)),
                    7 => match v_xcell_of(v) {
                        XCell::Lit(s) => done.push(bump.alloc(Tm::LiteralIntro(s))),
                        // 卡住声明引用：原样产出 `Tm::Decl`（参考版 quote
                        // 的 Decl 臂；spine 在 tag 2 头分派处走 ChainRun）
                        XCell::Decl { name } => done.push(bump.alloc(Tm::Decl(name))),
                        XCell::Prim { typ, pid } => {
                            done.push(bump.alloc(Tm::Prim(*typ, *pid)))
                        }
                        XCell::Obj { val, name } => {
                            // 卡住投影：rename 内层 → 包 Tm::Obj（空实参；
                            // 带实参的链在 tag 2 臂处理）
                            let inner = rename_iter(
                                bump, spine, work, vals, icits, defs, ren, metas, decl, mutable,
                                occ, dom, cod, *val,
                            )?;
                            done.push(bump.alloc(Tm::Obj(inner, name)));
                        }
                        XCell::Sum {
                            name,
                            params,
                            cases,
                            is_trait,
                        } => {
                            let mut ps: Vec<SumParamT<'_>> = Vec::with_capacity(params.len());
                            for p in params.iter() {
                                let pv = rename_iter(
                                    bump, spine, work, vals, icits, defs, ren, metas, decl, mutable,
                                    occ, dom, cod, p.val,
                                )?;
                                let pt = rename_iter(
                                    bump, spine, work, vals, icits, defs, ren, metas, decl, mutable,
                                    occ, dom, cod, p.ty,
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
                                *is_trait,
                            )));
                        }
                        XCell::SumCase {
                            typ,
                            case_name,
                            datas,
                            is_trait,
                        } => {
                            let tt = rename_iter(
                                bump, spine, work, vals, icits, defs, ren, metas, decl, mutable,
                                occ, dom, cod, *typ,
                            )?;
                            let mut ds: Vec<SumDataT<'_>> = Vec::with_capacity(datas.len());
                            for d in datas.iter() {
                                let dv = rename_iter(
                                    bump, spine, work, vals, icits, defs, ren, metas, decl, mutable,
                                    occ, dom, cod, d.val,
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
                                is_trait: *is_trait,
                            }));
                        }
                        XCell::Match {
                            scrutinee,
                            env: menv,
                            cases,
                        } => {
                            // 分支体是裸 Tm：先在"捕获 env + fresh rigid 槽"
                            // 下用 **declb 存根表**重新求值（防重展开），再在
                            // lift 过的独立 renaming 下用**真实表** rename
                            // （参考版 rename 的 Match 臂同款分工）
                            let declb = declb_of(bump, decl);
                            let val_tm = rename_iter(
                                bump, spine, work, vals, icits, defs, ren, metas, decl, mutable,
                                occ, dom, cod, *scrutinee,
                            )?;
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
                                    bump, spine, work, vals, icits, defs, metas, &declb, mutable,
                                    env2, tm,
                                );
                                let bt = rename_iter(
                                    bump, spine, work, vals, icits, defs, &mut ren2, metas, decl, mutable, occ, d2, c2, bv,
                                )?;
                                nc.push(((*pat).clone(), bt));
                            }
                            let cs: &'a [(PatternDetail, &'a Tm<'a>)] =
                                bump.alloc_slice_fill_iter(nc);
                            done.push(bump.alloc(Tm::Match(val_tm, cs)));
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
/// 实参——含字面量/Obj/构造子值——嵌套 rename，与参考版 prune_vflex_go 的
/// 非 Rigid 臂一致；实参探测用全量 force）。
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
    decl: &Decls<'a>,
    mutable: &RefCell<FxHashMap<SmolStr, V>>,
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
        let f = force(bump, spine, defs, metas, decl, mutable, a);
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
                bump, spine, work, vals, icits, defs, ren, metas, decl, mutable, occ, dom, cod, f,
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
        prune_meta_bump(bump, spine, work, vals, icits, defs, metas, decl, mutable, &mask, m)?
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
    decl: &Decls<'a>,
    mutable: &RefCell<FxHashMap<SmolStr, V>>,
    mask: &[Option<Icit>], // 内先序
    m: u32,
) -> Option<u32> {
    let mty = match &metas[m as usize] {
        MetaEntry::Unsolved(a) => *a,
        _ => unreachable!(), // 只对未解 meta 剪枝
    };
    let pruned_tm = prune_ty_bump(
        bump, spine, work, vals, icits, defs, metas, decl, mutable, mask, mty,
    )?;
    let prunedty = eval_iter(
        bump, spine, work, vals, icits, defs, metas, decl, mutable, EMPTY_ENV, pruned_tm,
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
        bump, spine, work, vals, icits, defs, metas, decl, mutable, mask.len() as u32, mty, ap,
    );
    let sol = eval_iter(
        bump, spine, work, vals, icits, defs, metas, decl, mutable, EMPTY_ENV, lam_tm,
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
    decl: &Decls<'a>,
    mutable: &RefCell<FxHashMap<SmolStr, V>>,
    mask_inner_first: &[Option<Icit>],
    mty: V,
) -> Option<&'a Tm<'a>> {
    let mut ren2 = RenBuf::default();
    ren2.reset(); // epoch 从 1 起（新槽 stamp 0 无效）
    let mut dom: u32 = 0;
    let mut cod: u32 = 0;
    let mut layers: Vec<(&'a str, Icit, &'a Tm<'a>)> = Vec::new();
    let mut cur = force(bump, spine, defs, metas, decl, mutable, mty);
    for entry in mask_inner_first.iter().rev() {
        // 外→内
        if v_tag(cur) != 4 {
            return None; // 上游 impossible：掩码与类型层不匹配
        }
        let p = v_pi_of(cur);
        let (name, icit, pdom, env, body) = (p.name, p.icit, p.dom, p.env, p.body);
        if entry.is_some() {
            let dtm = rename_iter(
                bump, spine, work, vals, icits, defs, &mut ren2, metas, decl, mutable, None, dom,
                cod, pdom,
            )?;
            // lift：binder 进映射
            ren2.set(cod as usize, dom);
            layers.push((name, icit, dtm));
            dom += 1;
        }
        let next = eval_iter(
            bump, spine, work, vals, icits, defs, metas, decl, mutable,
            env_ext(bump, env, v_lvl(cod)),
            body,
        );
        cod += 1;
        cur = force(bump, spine, defs, metas, decl, mutable, next);
    }
    let mut t = rename_iter(
        bump, spine, work, vals, icits, defs, &mut ren2, metas, decl, mutable, None, dom, cod,
        cur,
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
    decl: &Decls<'a>,
    mutable: &RefCell<FxHashMap<SmolStr, V>>,
    l: u32,
    ty: V,
    body: &'a Tm<'a>,
) -> &'a Tm<'a> {
    let mut names: Vec<(&'a str, Icit)> = Vec::with_capacity(l as usize);
    let mut cur = force(bump, spine, defs, metas, decl, mutable, ty);
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
            bump, spine, work, vals, icits, defs, metas, decl, mutable,
            env_ext(bump, env, v_lvl(lp)),
            body_tm,
        );
        cur = force(bump, spine, defs, metas, decl, mutable, next);
    }
    let mut t = body;
    for (name, icit) in names.iter().rev() {
        t = bump.alloc(Tm::Lam(name, *icit, t));
    }
    t
}

// Machine（稳态复用）与 elaboration
// --------------------------------------------------------------------------------

/// 名字表快照（参考版 BiMap 的 map1/map2 同构；**随 Cxt 克隆**——
/// bind/define/fake_bind 克隆整表插入，与参考版 `src_names.clone()` 的
/// 逐上下文隔离语义逐字对应，无需撤销轨迹）。
#[derive(Clone, Default)]
struct Names {
    /// 名字 → 层级（map1：只收源码 binder 与 fake_bind；inserted binder
    /// 与参考版 `new_binder` 一样不入）。
    by_name: FxHashMap<SmolStr, u32>,
    /// 层级 → 类型值（map2：按层级持久，refresh 的 get_by_key2_mut 目标；
    /// 名字查类型经此中转，refresh 更新即生效）。
    by_lvl: FxHashMap<u32, V>,
}

/// 稳态复用机（L06/L08 版 + L09 增量：global 表）。L09 没有 decl 表 /
/// 可变全局 / 燃料池 / pm 事实表——全局 def 走 [`Machine::decl`]（下标
/// = global_idx，项层以 `GLOBAL_BASE` 偏移的大下标引用）；名字状态在
/// [`Cxt`] 的 `names` 快照里（参考版 BiMap 同构）。
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
    /// 可变全局表（create_global/change_mutable/get_global 的
    /// `mutable_map`；每轮清空——参考版 per-Infer 同款）。值
    /// 是 bump 句柄，跨轮前一切句柄已消亡。
    mutable: RefCell<FxHashMap<SmolStr, V>>,
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
    /// 能在两次调用之间被求解，跨调用保留条目会拿到过期中性项。
    quote_memo: QuoteMemo<'static>,
    /// trait 合成状态（每轮清空——参考版每次调用新建 Infer 的三表）。
    tstate: TraitState,
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
            mutable: RefCell::new(FxHashMap::default()),
            eval_work: Vec::new(),
            quote_tasks: Vec::new(),
            quote_done: Vec::new(),
            quote_work: Vec::new(),
            unify_work: Vec::new(),
            unify_stack: Vec::new(),
            quote_memo: FxHashMap::default(),
            tstate: TraitState::default(),
        }
    }

    /// 每轮 reset：metacontext + 名字表/类型表/轨迹 + 环境区域 + 可变全局
    /// 表全部清空。spine 栈同轮清空（保容量）——tag-2 句柄只被当轮 bump 值 /
    /// metas / defs 持有，轮边界后无任何旧句柄可达。decl 表随 Cxt 快照
    /// 消亡（参考版每次调用新建 Cxt 同款）。
    fn clear_round(&mut self) {
        self.metas.clear();
        self.defs.clear();
        self.mutable.borrow_mut().clear();
        self.spine.stack.clear();
        self.tstate = TraitState::default();
    }

    // Extend Cxt（源码 binder / inserted binder / define / fake_bind）
    // --------------------------------------------------------------------------------

    /// Extend Cxt with a bound variable（源码 binder）。
    fn bind_name<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        x: &str,
        a_t: &'a Tm<'a>,
        ty: V,
    ) -> Cxt<'a> {
        let mut names = (*cxt.names).clone();
        names.by_name.insert(SmolStr::new(x), cxt.lvl);
        names.by_lvl.insert(cxt.lvl, ty);
        let env = env_ext(bump, cxt.env, v_lvl(cxt.lvl));
        Cxt {
            env,
            update_from: cxt.update_from,
            names: Rc::new(names),
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
            decls: cxt.decls.clone(),
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
        let env = env_ext(bump, cxt.env, v_lvl(cxt.lvl));
        Cxt {
            env,
            update_from: cxt.update_from,
            names: cxt.names.clone(),
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
            decls: cxt.decls.clone(),
        }
    }

    /// Extend Cxt with a definition（pruning 记 `None`、telescope 记 Define
    /// 槽）。
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
        let mut names = (*cxt.names).clone();
        names.by_name.insert(SmolStr::new(x), cxt.lvl);
        names.by_lvl.insert(cxt.lvl, ty);
        let env = env_ext_defs(bump, &mut self.defs, cxt.env, val);
        Cxt {
            env,
            update_from: cxt.update_from,
            names: Rc::new(names),
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
            decls: cxt.decls.clone(),
        }
    }

    /// fake_bind（参考版 `Cxt::fake_bind`）：递归 def 的占位——decl 表插入
    /// `Decl(name)` 存根条目（tm/val 都是名字自引用），**撞名（含内建）
    /// 即 `redefine {name}`**；env/lvl/locals/pruning/names 一概不动。
    fn fake_bind<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        x: &str,
        a_t: &'a Tm<'a>,
        ty: V,
    ) -> Result<Cxt<'a>, Error> {
        let mut decls = cxt.decls.clone();
        let name = bump.alloc_str(x);
        let stub = bump.alloc(Tm::Decl(name));
        let prev = Rc::make_mut(&mut decls).insert(
            SmolStr::new(x),
            DeclEntry {
                tm: stub,
                val: v_xcell(bump.alloc(XCell::Decl { name })),
                vty: ty,
            },
        );
        if prev.is_some() {
            return Err(Error(empty_span(format!("redefine {}", x))));
        }
        let _ = a_t;
        Ok(Cxt {
            env: cxt.env,
            update_from: cxt.update_from,
            names: cxt.names.clone(),
            types: cxt.types,
            locals: cxt.locals,
            pruning: cxt.pruning,
            binds: cxt.binds,
            lvl: cxt.lvl,
            decls,
        })
    }

    /// 声明登记（参考版 `Cxt::decl`）：**静默覆盖**（参考版 redefine 检查
    /// 被注释）——fake_bind 之后以真值覆盖存根。
    fn decl_reg<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        x: &str,
        t_tm: &'a Tm<'a>,
        vt: V,
        typ_tm: &'a Tm<'a>,
        vtyp: V,
    ) -> Cxt<'a> {
        let _ = bump;
        let _ = typ_tm;
        let mut decls = cxt.decls.clone();
        Rc::make_mut(&mut decls).insert(
            SmolStr::new(x),
            DeclEntry {
                tm: t_tm,
                val: vt,
                vty: vtyp,
            },
        );
        Cxt {
            env: cxt.env,
            update_from: cxt.update_from,
            names: cxt.names.clone(),
            types: cxt.types,
            locals: cxt.locals,
            pruning: cxt.pruning,
            binds: cxt.binds,
            lvl: cxt.lvl,
            decls,
        }
    }

    /// 挂新洞（上游 `freshMeta`）：物化闭类型、追加未解条目，产出
    /// `AppPruning ?m (cxt.pruning)`。快捷（L05 三级 + tag 6）：
    /// **`binds == 0`** 时常值类型（U / 裸未解 meta / LiteralType，tag
    /// 3/5/6）闭类型恒等；`quote` 无自由变量则跳过 Let 链直接空环境求值；
    /// 否则全构造（与参考版同形）。
    fn fresh_meta<'a>(&mut self, bump: &'a Bump, cxt: &Cxt<'a>, a: V) -> &'a Tm<'a> {
        // L10：trait 类型先试实例合成（成功 → 直接给实例项）；
        // trait Sum → 裸 Meta（无 AppPruning 掩码）
        if let Ok(Some((tm, _))) = self.solve_trait_ref(bump, cxt, a) {
            return tm;
        }
        let is_trait_sum = v_tag(a) == 7
            && match v_xcell_of(a) {
                XCell::Sum { is_trait, .. } => *is_trait,
                _ => false,
            };
        if is_trait_sum {
            let m = self.metas.len() as u32;
            self.metas.push(MetaEntry::Unsolved(a));
            return bump.alloc(Tm::Meta(m));
        }
        let mty = if cxt.binds == 0 && matches!(v_tag(a), 3 | 5 | 6) {
            a
        } else {
            let q = self.quote(bump, cxt, cxt.lvl, a);
            if cxt.binds == 0 && !has_free_var(q) {
                self.eval(bump, cxt, EMPTY_ENV, q)
            } else {
                let closed = self.close_tm(bump, cxt.locals, q);
                self.eval(bump, cxt, EMPTY_ENV, closed)
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
    fn eval_fresh(&mut self, bump: &Bump, cxt: &Cxt<'_>, env: Env<'_>, m: &Tm<'_>) -> V {
        if let Tm::AppPruning(head, pr) = m {
            // 头必须是裸 Meta 才有短路意义
            if let Tm::Meta(mm) = head {
                if pr.map_or(true, |p| p.slot.is_none() && p.after_run.is_none()) {
                    return v_meta(*mm);
                }
            }
        }
        self.eval(bump, cxt, env, m)
    }

    // 内核包装（Machine 字段借出）
    // --------------------------------------------------------------------------------

    // 'static → 'a 的两步指针转换是刻意的一生期重写（SAFETY 见方法体），
    // clippy 在其类型显示里塌缩生命周期参数会误报 unnecessary_cast
    #[allow(clippy::unnecessary_cast)]
    fn eval<'a>(&mut self, bump: &'a Bump, cxt: &Cxt<'a>, env: Env<'a>, tm: &'a Tm<'a>) -> V {
        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            mutable,
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
            bump, spine, work, vals, icits, defs, metas, &*cxt.decls, mutable, env, tm,
        )
    }

    // 'static → 'a 的两步指针转换是刻意的一生期重写（SAFETY 见方法体），
    // clippy 在其类型显示里塌缩生命周期参数会误报 unnecessary_cast
    #[allow(clippy::unnecessary_cast)]
    fn quote<'a>(&mut self, bump: &'a Bump, cxt: &Cxt<'a>, level: u32, v: V) -> &'a Tm<'a> {
        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            mutable,
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
            &*cxt.decls,
            mutable,
            level,
            v,
            None,
        )
    }

    /// quote 的记忆化口径（表容量跨调用复用、内容每次调用 clear，绝不跨
    /// reset 持有条目——meta 求解会让旧条目过期）。
    // 'static → 'a 的两步指针转换是刻意的一生期重写（SAFETY 见方法体），
    // clippy 在其类型显示里塌缩生命周期参数会误报 unnecessary_cast
    #[allow(clippy::unnecessary_cast)]
    fn quote_memo<'a>(&mut self, bump: &'a Bump, cxt: &Cxt<'a>, level: u32, v: V) -> &'a Tm<'a> {
        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            mutable,
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
            &*cxt.decls,
            mutable,
            level,
            v,
            Some(&mut *memo),
        )
    }

    // 'static → 'a 的两步指针转换是刻意的一生期重写（SAFETY 见方法体），
    // clippy 在其类型显示里塌缩生命周期参数会误报 unnecessary_cast
    #[allow(clippy::unnecessary_cast)]
    fn unify<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        l: u32,
        t: V,
        u: V,
        trait_err: &mut Option<String>,
    ) -> bool {
        // 先取裸指针再解构字段（避免 &mut self 与字段借用的叠加）
        let mach_ptr: *mut Machine = self;
        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            mutable,
            ren,
            conv,
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
        // 重入句柄 mach_ptr 在解构前取得：unify 的 flex 求解点要回调
        // trait 求解（参考版 solve 臂的 solve_multi_trait）——字段已按
        // 不相交集合借出，重入经裸指针走 Machine 方法（仅触碰同分配的
        // 堆内容，无移动）
        unify_iter(
            bump, spine, work, stack, vals, icits, defs, metas, &*cxt.decls, mutable, ren, conv,
            l, t, u, cxt, mach_ptr, trait_err,
        )
    }

    /// 参考 `Infer::solve_multi_trait`：从 meta m 起扫描所有未解 meta，
    /// 类型是 trait 的逐个跑实例合成（合成成功 → meta := 实例值）。
    fn solve_multi_trait_ref<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        m: u32,
    ) -> Result<(), String> {
        let prepare: Vec<(u32, V)> = self
            .metas
            .get(m as usize..)
            .unwrap_or(&[])
            .iter()
            .enumerate()
            .flat_map(|(i, x)| match x {
                MetaEntry::Unsolved(v) => Some((i as u32, *v)),
                _ => None,
            })
            .collect();
        for (idx, x) in prepare {
            let solved = self.solve_trait_ref(bump, cxt, x)?;
            if let Some((_, val)) = solved {
                self.metas[(idx + m) as usize] = MetaEntry::Solved(val, x);
            }
        }
        Ok(())
    }

    /// 参考 `Infer::solve_trait`：x 是 trait Sum → 查实例表合成；命中给
    /// (实例项, 实例值)，失败给 Err 文案，非 trait 给 None。
    fn solve_trait_ref<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        x: V,
    ) -> Result<Option<(&'a Tm<'a>, V)>, String> {
        let is_trait_sum = v_tag(x) == 7
            && match v_xcell_of(x) {
                XCell::Sum { is_trait, .. } => *is_trait,
                _ => false,
            };
        if !is_trait_sum {
            return Ok(None);
        }
        let (name, params) = match v_xcell_of(x) {
            XCell::Sum { name, params, .. } => (*name, *params),
            _ => unreachable!(),
        };
        let out_param = match self.tstate.out_param.get(name) {
            Some(o) => o.clone(),
            None => return Ok(None),
        };
        // 参考版 solve_trait（L11 unification.rs 471-482）：实参逐个
        // force 再 to_typ，**任一个 to_typ 失败（未解 meta 等）即提前
        // Ok(None)**——确定性短路，不是 filter 跳过（跳过会把缺参的
        // Assertion 送进 synth，误报 "solve trait failed"）。
        let args: Vec<Typ> = {
            let Machine {
                spine,
                defs,
                metas,
                mutable,
                ..
            } = self;
            let collected: Option<Vec<Typ>> = params
                .iter()
                .zip(out_param.iter())
                .filter(|(_, o)| !**o)
                .map(|(p, _)| {
                    let f = force(bump, spine, defs, metas, &*cxt.decls, mutable, p.val);
                    val_to_typ(spine, defs, f)
                })
                .collect();
            match collected {
                Some(a) => a,
                None => return Ok(None),
            }
        };
        self.tstate.solver.clean();
        let answer = self.tstate.solver.synth(Assertion {
            name: name.to_string(),
            arguments: args.clone(),
        });
        if let Some(a) = answer {
            // infer_expr(Var 实例名) + insert
            let raw = Raw::Var(crate::parser_lib::Span {
                data: a.data,
                start_offset: a.start_offset,
                end_offset: a.end_offset,
                path_id: a.path_id,
            });
            let infered =
                self.infer_expr(bump, cxt, &raw).map_err(|e| e.0.data)?;
            let (tm, _) =
                self.insert(bump, cxt, infered.0, infered.1).map_err(|e| e.0.data)?;
            let val = self.eval(bump, cxt, cxt.env, tm);
            if v_tag(val) == 7 {
                if let XCell::SumCase { typ, .. } = v_xcell_of(val) {
                    let mut te = None;
                    let _ = self.unify(bump, cxt, cxt.lvl, *typ, x, &mut te);
                }
            }
            Ok(Some((tm, val)))
        } else {
            // 参考版文案：`{}[{:?}]` + 类实例表逐行（Debug 序列化）
            let args_dbg = format!("{:?}", args);
            Err(format!(
                "solve trait failed: {}[{}]
{}",
                name,
                args_dbg,
                self.tstate
                    .solver
                    .class_instances
                    .get(name)
                    .unwrap_or(&vec![])
                    .iter()
                    .map(|x| format!("{:?}", x))
                    .reduce(|a, b| a + "
" + &b)
                    .unwrap_or_default(),
            ))
        }
    }

    /// 错误消息（参考版 `unify_catch`：pretty + 上下文名字表；快版导出项
    /// 的 Span 全零，消息内容与参考版同构）。
    fn unify_catch<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: V,
        t_prime: V,
    ) -> Result<(), Error> {
        let mut trait_err: Option<String> = None;
        let ok = self.unify(bump, cxt, cxt.lvl, t, t_prime, &mut trait_err);
        if ok {
            Ok(())
} else {
            if let Some(e) = trait_err {
                return Err(Error(empty_span(e)));
            }
            let tq = export(self.quote(bump, cxt, cxt.lvl, t));
            let uq = export(self.quote(bump, cxt, cxt.lvl, t_prime));
            let names = types_names_list(cxt.types);
            Err(Error(empty_span(format!(
                "can't unify\n  expected: {}\n      find: {}",
                pretty_tm(0, names.clone(), &tq),
                pretty_tm(0, names, &uq),
            ))))
        }
    }

    /// force 的方法包装（Machine 内 elaboration 侧的散装调用点用；解值
    /// 应用可能 β——分配一律落本轮 bump）。
    fn force_v(&mut self, bump: &Bump, cxt: &Cxt<'_>, v: V) -> V {
        let Machine {
            spine,
            defs,
            metas,
            mutable,
            ..
        } = self;
        force(bump, spine, defs, metas, &*cxt.decls, mutable, v)
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
        let va = self.force_v(bump, cxt, va);
        if v_tag(va) == 4 && v_pi_of(va).icit == Icit::Impl {
            let p = v_pi_of(va);
            let m = self.fresh_meta(bump, cxt, p.dom);
            let mv = self.eval_fresh(bump, cxt, cxt.env, m);
            let b = {
                let env = env_ext(bump, p.env, mv);
                self.eval(bump, cxt, env, p.body)
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
        let mut t = t;
        loop {
            let forced = self.force_v(bump, cxt, va);
            va = forced;
            if v_tag(va) == 4 && v_pi_of(va).icit == Icit::Impl {
                let p = v_pi_of(va);
                if p.name == name {
                    return Ok((t, va));
                }
                let m = self.fresh_meta(bump, cxt, p.dom);
                let mv = self.eval_fresh(bump, cxt, cxt.env, m);
                let b = {
                    let env = env_ext(bump, p.env, mv);
                    self.eval(bump, cxt, env, p.body)
                };
                t = bump.alloc(Tm::App(t, m, Icit::Impl));
                va = b;
            } else {
                return Err(Error(empty_span(format!("no named implicit arg {}", name))));
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
        // force 期望类型后分派（已解 meta 可能展开成 Pi）
        let a = self.force_v(bump, cxt, a);
        if let Raw::Lam(x, larg, tbody) = t {
            if v_tag(a) == 4 {
                let p = v_pi_of(a);
                // 参考版首臂的守卫：命名隐式对准同名隐式 Π；显式对显式
                let matched = match larg {
                    Either::Name(n) => n.data == p.name && p.icit == Icit::Impl,
                    &Either::Icit(j) => j == p.icit,
                };
                if matched {
                    // 命中：按 λ 的 binder 名绑定（源码名，入名字表）
                    let name: &'a str = bump.alloc_str(&x.data);
                    let body_a = {
                        let env = env_ext(bump, p.env, v_lvl(cxt.lvl));
                        self.eval(bump, cxt, env, p.body)
                    };
                    let a_t = self.quote(bump, cxt, cxt.lvl, p.dom);
                    let cxt2 = self.bind_name(bump, cxt, &x.data, a_t, p.dom);
                    let body = self.check(bump, &cxt2, tbody, body_a)?;
                    Ok(bump.alloc(Tm::Lam(name, p.icit, body)))
                } else if p.icit == Icit::Impl {
                    // 检查到隐式 Π：补 inserted binder（Pi 侧名字，源码
                    // 不可见），整个项对余定义域重检
                    let name: &'a str = bump.alloc_str(p.name);
                    let body_a = {
                        let env = env_ext(bump, p.env, v_lvl(cxt.lvl));
                        self.eval(bump, cxt, env, p.body)
                    };
                    let a_t = self.quote(bump, cxt, cxt.lvl, p.dom);
                    let cxt2 = self.new_binder(bump, cxt, p.name, a_t, p.dom);
                    let body = self.check(bump, &cxt2, t, body_a)?;
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
                self.eval(bump, cxt, env, p.body)
            };
            let a_t = self.quote(bump, cxt, cxt.lvl, p.dom);
            let cxt2 = self.new_binder(bump, cxt, p.name, a_t, p.dom);
            let body = self.check(bump, &cxt2, t, body_a)?;
            Ok(bump.alloc(Tm::Lam(name, Icit::Impl, body)))
        } else if let Raw::Let(x, a_ty, t2, u2) = t {
            let (a_tm, _) = self.check_universe(bump, cxt, a_ty)?;
            let va = self.eval(bump, cxt, cxt.env, a_tm);
            let t_tm = self.check(bump, cxt, t2, va)?;
            let vt = self.eval(bump, &cxt, cxt.env, t_tm);
            let name: &'a str = bump.alloc_str(&x.data);
            let cxt2 = self.define_name(bump, cxt, &x.data, a_tm, t_tm, vt, va);
            let u_tm = self.check(bump, &cxt2, u2, a)?;
            Ok(bump.alloc(Tm::Let(name, a_tm, t_tm, u_tm)))
        } else if let Raw::Hole(_) = t {
            // hole：以 fresh meta 填充（类型 = 期望类型）
            Ok(self.fresh_meta(bump, cxt, a))
        } else if let Raw::Match(expr, clauses) = t {
            // match：编译（特化合一在编译期完成）+ 逐分支检查
            let expr_span = expr.to_span();
            let (tm, typ) = self.infer_expr(bump, cxt, expr)?;
            let target = self.eval(bump, cxt, cxt.env, tm);
            let mut compiler = Compiler::new(a);
            compiler.compile(self, bump, typ, clauses, cxt, target)?;
            if !compiler.warnings.is_empty() {
                return Err(Error(expr_span.map(|_| format!("{:?}", compiler.warnings))));
            }
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

    // 类型注解的 universe 检查（参考版 elaboration.rs `check_universe` 完整
    // 移植：可解 meta——两分支都把 meta 解成 `U(0)` 形态并返回层级 0）
    // --------------------------------------------------------------------------------

    fn check_universe<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: &Raw,
    ) -> Result<(&'a Tm<'a>, u32), Error> {
        let t_span = t.to_span();
        let x = self.infer_expr(bump, cxt, t)?;
        let (t_inferred, inferred_type) = self.insert(bump, cxt, x.0, x.1)?;
        // U：层级直出（参考版 match 的 U 臂，不 force）
        if v_tag(inferred_type) == 3 {
            return Ok((t_inferred, v_u_of(inferred_type)));
        }
        // Flex：反演 spine，可解则把 meta 解成 `U(0)` 形态（参考版不 force
        // 直接 match——已解 flex 会触发参考版的 unreachable!，快版同款）
        let mut args: Vec<(V, Icit)> = Vec::new();
        if let Some(m) = self.spine.flex_of(inferred_type, &mut args) {
            let mty = match &self.metas[m as usize] {
                MetaEntry::Unsolved(a) => *a,
                _ => unreachable!(),
            };
            let inv = {
                let Machine {
                    spine,
                    defs,
                    metas, mutable,
                    ren,
                    ..
                } = self;
                invert_bump(bump, spine, defs, metas, &*cxt.decls, mutable, ren, &args)
            };
            let Some(mask) = inv else {
                return Err(Error(t_span.map(|_| "invert failed".to_owned())));
            };
            // 非线性：剪枝可行性检查（结果弃置——参考版只用作把关）
            if !mask.is_empty() {
                let ok = {
                    let Machine {
                        spine,
                        vals,
                        icits,
                        defs,
                        metas, mutable,
                        eval_work,
                        ..
                    } = self;
                    let work: &mut Vec<W<'a>> = unsafe {
                        &mut *(eval_work as *mut Vec<W<'static>> as *mut Vec<W<'a>>)
                    };
                    work.clear();
                    prune_ty_bump(
                        bump, spine, work, vals, icits, defs, metas, &*cxt.decls, mutable, &mask, mty,
                    )
                };
                if ok.is_none() {
                    return Err(Error(t_span.map(|_| "prune failed".to_owned())));
                }
            }
            if args.is_empty() {
                // pren.dom == 0：meta 类型 force 后是 U 即解 `U(0)`
                let f = self.force_v(bump, cxt, mty);
                if v_tag(f) == 3 {
                    self.metas[m as usize] = MetaEntry::Solved(v_u(0), mty);
                    return Ok((t_inferred, 0));
                }
                let f2 = self.force_v(bump, cxt, mty);
                let msg = format!("meta type {} is not a universe", debug_val(&self.spine, &self.defs, f2));
                return Err(Error(t_span.map(|_| msg.clone())));
            }
            // rename 出 `U(0)` 的解（occ = m），λ 包裹后空环境求值写表
            let rhs = {
                let Machine {
                    spine,
                    vals,
                    icits,
                    defs,
                    metas, mutable,
                    ren,
                    unify_work,
                    ..
                } = self;
                let work: &mut Vec<W<'a>> = unsafe {
                    &mut *(unify_work as *mut Vec<W<'static>> as *mut Vec<W<'a>>)
                };
                work.clear();
                rename_iter(
                    bump, spine, work, vals, icits, defs, ren, metas, &*cxt.decls, mutable,
                    Some(m), args.len() as u32, cxt.lvl, v_u(0),
                )
            };
            let Some(rhs) = rhs else {
                return Err(Error(
                    t_span.map(|_| "when check universe, try to rename failed".to_string()),
                ));
            };
            let lam_tm = {
                let Machine {
                    spine,
                    vals,
                    icits,
                    defs,
                    metas, mutable,
                    eval_work,
                    ..
                } = self;
                let work: &mut Vec<W<'a>> = unsafe {
                    &mut *(eval_work as *mut Vec<W<'static>> as *mut Vec<W<'a>>)
                };
                work.clear();
                lams_from_ty(bump, spine, work, vals, icits, defs, metas, &*cxt.decls, mutable, args.len() as u32, mty, rhs)
            };
            let solution = self.eval(bump, cxt, EMPTY_ENV, lam_tm);
            self.metas[m as usize] = MetaEntry::Solved(solution, mty);
            return Ok((t_inferred, 0));
        }
        Err(Error(t_span.map(|_| {
            format!(
                "expected universe, got {}",
                debug_val(&self.spine, &self.defs, inferred_type)
            )
        })))
    }
}

// Elaboration 上下文
// --------------------------------------------------------------------------------

/// scope 里的一项：名字 + 类型值 + 来源（源码 binder / inserted binder）。
struct TCons<'a> {
    name: &'a str,
    ty: V,
    source: bool,
    next: Option<&'a TCons<'a>>,
}

/// Elaboration 上下文（绑定量在 bump 里）。方法一律借用 `&Cxt`（扩展上下
/// 文返回**新的** Cxt 值；名字/类型的可变状态在 [`Machine`] 的
/// name_map/lvl_types，随 `mark` 轨迹撤销）。
struct Cxt<'a> {
    env: Env<'a>,
    /// 已精化的最低层级（L10 `update_from`：refresh 只走增量区间）。
    update_from: Option<usize>,
    /// 名字快照（参考版 `src_names: BiMap` 同构；随扩展克隆——隔离语义
    /// 与参考版逐字对应）。
    names: Rc<Names>,
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
    /// 全局声明表（参考版 `Cxt.decl: HashMap` 同构；写时复制——
    /// fake_bind 的撞名检查与 decl 登记都经 `Rc::make_mut`）。
    decls: Rc<Decls<'a>>,
}

impl<'a> Cxt<'a> {
    fn empty() -> Self {
        Cxt {
            env: EMPTY_ENV,
            update_from: None,
            names: Rc::new(Names::default()),
            types: None,
            locals: None,
            pruning: None,
            binds: 0,
            lvl: 0,
            decls: Rc::new(Decls::default()),
        }
    }
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
            Tm::Decl(_) => {}
            Tm::Lam(_, _, b) => stack.push((b, d + 1)),
            Tm::App(f, a, _) => {
                stack.push((f, d));
                stack.push((a, d));
            }
            Tm::AppPruning(h, _) => stack.push((h, d)),
            Tm::U(_) | Tm::Meta(_) | Tm::LiteralType | Tm::LiteralIntro(_)
            | Tm::Prim(_, _) => {}
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
            Tm::Sum(_, params, ..) => {
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

impl Machine {
    // check_pm / unify_pm / update_cxt / refresh（参考版 elaboration.rs +
    // cxt.rs 的模式特化机制——精化等式直接改写进环境）
    // --------------------------------------------------------------------------------

    /// `unify_pm`：模式特化的合一（参考版 elaboration.rs 同款臂序）：
    /// 双裸 Rigid 同级自反；单侧裸 Rigid → `update_cxt`（精化写进环境）；
    /// 同名 SumCase 逐 datas、同名 Sum 逐参数（均**只比值槽**）递归；
    /// 其余落 `unify_catch`（全文案合一错误）。
    fn unify_pm<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: V,
        t_prime: V,
        t_span: &crate::parser_lib::Span<()>,
    ) -> Result<Cxt<'a>, Error> {
        let f1 = self.force_v(bump, cxt, t);
        let f2 = self.force_v(bump, cxt, t_prime);
        // (Rigid(x1, []), Rigid(x2, [])) if x1 == x2 → 同变量也走精化
        // （L10：update_cxt(x1, t_prime, update_prune=false)）
        if v_tag(f1) == 0 && v_tag(f2) == 0 && v_lvl_of(f1) == v_lvl_of(f2) {
            return self.update_cxt_impl(bump, cxt, v_lvl_of(f1), f2, false);
        }
        // (Rigid(x, []), v) → 精化 x := v（update_prune=true）
        if v_tag(f1) == 0 {
            return self.update_cxt_impl(bump, cxt, v_lvl_of(f1), f2, true);
        }
        // (v, Rigid(x, [])) → 精化 x := v
        if v_tag(f2) == 0 {
            return self.update_cxt_impl(bump, cxt, v_lvl_of(f2), f1, true);
        }
        // 同名 SumCase：逐 datas（值槽）
        if v_tag(f1) == 7 && v_tag(f2) == 7 {
            if let (
                XCell::SumCase {
                    case_name: n1,
                    datas: d1,
                    ..
                },
                XCell::SumCase {
                    case_name: n2,
                    datas: d2,
                    ..
                },
            ) = (v_xcell_of(f1), v_xcell_of(f2))
            {
                if n1 == n2 {
                    let mut cxt = clone_cxt(cxt);
                    for (x, y) in d1.iter().zip(d2.iter()) {
                        cxt = self.unify_pm(bump, &cxt, x.val, y.val, t_span)?;
                    }
                    return Ok(cxt);
                }
                return Err(Error(t_span.map(|_| "".to_string())));
            }
            // 同名 Sum：逐参数（值槽）
            if let (
                XCell::Sum {
                    name: n1,
                    params: d1,
                    ..
                },
                XCell::Sum {
                    name: n2,
                    params: d2,
                    ..
                },
            ) = (v_xcell_of(f1), v_xcell_of(f2))
            {
                if n1 == n2 {
                    let mut cxt = clone_cxt(cxt);
                    for (x, y) in d1.iter().zip(d2.iter()) {
                        cxt = self.unify_pm(bump, &cxt, x.val, y.val, t_span)?;
                    }
                    return Ok(cxt);
                }
                return Err(Error(t_span.map(|_| "".to_string())));
            }
        }
        self.unify_catch(bump, cxt, f1, f2).map(|_| clone_cxt(cxt))
    }

    /// `check_pm`：infer + insert + `unify_pm`。
    fn check_pm<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: &Raw,
        a: V,
    ) -> Result<(&'a Tm<'a>, Cxt<'a>), Error> {
        let t_span = t.to_span();
        let x = self.infer_expr(bump, cxt, t)?;
        let (t_inferred, inferred_type) = self.insert(bump, cxt, x.0, x.1)?;
        let new_cxt = self.unify_pm(bump, cxt, a, inferred_type, &t_span)?;
        Ok((t_inferred, new_cxt))
    }

    /// `check_pm_final`：`check_pm` 之后把原始值与精化后的期望再对一次
    /// （`.unwrap_or(new_cxt)`——失败容忍，参考版同款）。
    fn check_pm_final<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: &Raw,
        a: V,
        ori: V,
    ) -> Result<(&'a Tm<'a>, Cxt<'a>), Error> {
        let t_span = t.to_span();
        let x = self.infer_expr(bump, cxt, t)?;
        let (t_inferred, inferred_type) = self.insert(bump, cxt, x.0, x.1)?;
        let new_cxt = self.unify_pm(bump, cxt, a, inferred_type, &t_span)?;
        let ori_v = self.eval(bump, cxt, new_cxt.env, t_inferred);
        // ori 精化**要传下去**（参考版 `let new_cxt = ...unwrap_or(new_cxt)`
        // ——被匹配变量本身的值写进环境，期望类型重锚定后才能选中分支）
        let refined = self.unify_pm(bump, &new_cxt, ori, ori_v, &t_span);
        let new_cxt = refined.unwrap_or(new_cxt);
        Ok((t_inferred, new_cxt))
    }

    fn update_cxt<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        x: u32,
        v: V,
    ) -> Result<Cxt<'a>, Error> {
        self.update_cxt_impl(bump, cxt, x, v, true)
    }

    /// `Cxt::update_cxt` 的 L10 版本体：Flex 不动；`update_from` 记录已
    /// 精化的最低层级（单调取小）；`update_prune=false` 时 pruning 保持；
    /// refresh 只走 `lvl - update_from` 的增量区间（walk 参数），src_names
    /// 按层级同步（L10 `if let Some`——无条目静默跳过）。
    fn update_cxt_impl<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        x: u32,
        v: V,
        update_prune: bool,
    ) -> Result<Cxt<'a>, Error> {
        if is_flex(&self.spine, v) {
            return Ok(clone_cxt(cxt));
        }
        let update_from = match cxt.update_from {
            Some(u) if u < x as usize => u,
            _ => x as usize,
        };
        // lvl2ix(lvl, x)：x 恒为局部层级（顶层声明不进环境——参考版
        // update_cxt 同款）
        let x_prime: usize = (cxt.lvl - x - 1) as usize;
        let n = env_len(cxt.env) as usize;
        let mut slots2: Vec<V> = Vec::with_capacity(n);
        env_collect(&self.defs, cxt.env, &mut slots2);
        if x_prime < n {
            slots2[x_prime] = v;
        }
        let mut names = (*cxt.names).clone();
        let walk = cxt.lvl as usize - update_from;
        let refreshed = self.refresh(bump, cxt, &slots2, &mut names, walk);
        // pruning：update_prune 时目标槽改 None（define 槽）并前缀重建；
        // 否则保持原 pruning（参考版 update_prune=false 同款）
        let mut pr_slots: Vec<Option<Icit>> = Vec::with_capacity(n);
        {
            let mut cur = cxt.pruning;
            while let Some(b) = cur {
                pr_slots.push(b.slot);
                cur = b.next;
            }
        }
        if update_prune && x_prime < pr_slots.len() {
            pr_slots[x_prime] = None;
        }
        let pruning: Option<&'a PrCons<'a>> = if update_prune {
            let mut pr: Option<&'a PrCons<'a>> = None;
            for slot in pr_slots.into_iter().rev() {
                pr = Some(bump.alloc(PrCons::new(slot, pr)));
            }
            pr
        } else {
            cxt.pruning
        };
        // 环境：纯链重建（refresh 后的槽序，头 = 最内层）
        let mut env: Option<&'a EnvCons<'a>> = None;
        for val in refreshed.into_iter().rev() {
            env = Some(bump.alloc(EnvCons { val, next: env }));
        }
        Ok(Cxt {
            env: Env {
                flat_base: 0,
                flat_len: 0,
                binds: env,
            },
            update_from: Some(update_from),
            names: Rc::new(names),
            types: cxt.types,
            locals: cxt.locals,
            pruning,
            binds: cxt.binds,
            lvl: cxt.lvl,
            decls: cxt.decls.clone(),
        })
    }

    /// `Cxt::refresh`（参考版递归的迭代化）：从最内层槽向外逐槽把旧值在
    /// 「目标槽已替换 + 更外槽已刷新」的环境下重锚定（quote 旧 env 长度 →
    /// eval 新 env），`names.by_lvl` 同槽更新（**调用方传入的克隆快照**，
    /// 与参考版 `new_src_names` 的 clone-then-mutate 同款）。参考版
    /// `get_by_key2_mut(...).unwrap()`：无条目的层级（inserted binder）
    /// panic——同款保留。
    #[allow(clippy::too_many_arguments)]
    fn refresh<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        slots2: &[V],
        names: &mut Names,
        walk: usize,
    ) -> Vec<V> {
        let n = env_len(cxt.env) as usize;
        let old: Vec<V> = {
            let mut v = Vec::with_capacity(n);
            env_collect(&self.defs, cxt.env, &mut v);
            v
        };
        let mut refreshed: Vec<Option<V>> = vec![None; n];
        // L10 walk：只刷新最后 `walk` 个槽（参考版 walk 参数——其余槽
        // 原样直通）；walk 区间外的槽先填原值（内层引用直接可见）
        let walk_n = walk.min(n);
        for d in walk_n..n {
            refreshed[d] = Some(old[d]);
        }
        for d in (0..walk_n).rev() {
            // env_tt：头 d+1 个取 slots2（含目标替换），其余取已刷新槽
            let mut env_tt: Vec<V> = Vec::with_capacity(n);
            env_tt.extend_from_slice(&slots2[..d + 1]);
            for i in d + 1..n {
                env_tt.push(refreshed[i].expect("refresh: 内层槽未刷新"));
            }
            let env_tt_chain = chain_env(bump, &env_tt);
            // 槽值重锚定
            let q = self.quote(bump, cxt, n as u32, old[d]);
            let rv = self.eval(bump, cxt, env_tt_chain, q);
            refreshed[d] = Some(rv);
            // src_names 按层级同步（Lvl(env_t.len()) = n-1-d）；L10：
            // 无条目静默跳过（if let Some 同款）
            let lvl = (n - 1 - d) as u32;
            if let Some(old_ty) = names.by_lvl.get(&lvl) {
                let old_ty = *old_ty;
                let qt = self.quote(bump, cxt, n as u32, old_ty);
                let rty = self.eval(bump, cxt, env_tt_chain, qt);
                names.by_lvl.insert(lvl, rty);
            }
        }
        refreshed.into_iter().map(|x| x.expect("refresh: 槽未刷新")).collect()
    }

    // L10：trait 方法包装（参考版 elaboration.rs `trait_wrap` 逐句移植）
    // --------------------------------------------------------------------------------

    /// 字段未命中时在 trait 表里找同名方法：能合成出实例 → 生成
    /// `let $method = λ...; $method x` 的包装项；否则报 "has no object"。
    fn trait_wrap<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: crate::parser_lib::Span<String>,
        a: V,
        x: &Raw,
        tm: &'a Tm<'a>,
    ) -> Result<(&'a Tm<'a>, V), Error> {
        if std::env::var("L11_LOOPCAP").is_ok() {
            eprintln!("TRACE trait_wrap field={} recv={:?}", t.data, debug_tm(tm));
        }
        // has_no_object 不做成闭包（避免 &self 捕获与 infer_expr 的 &mut
        // 冲突）——两个错误点直接调用 [`Self::mk_no_object_err`]
        let Some(typ) = val_to_typ(&self.spine, &self.defs, a) else {
            return Err(self.mk_no_object_err(bump, cxt, &t, a, tm));
        };
        // 方法名命中的 trait：合成 `Any × len(out_param)` 参数的 Assertion
        // （首参 = 接收者类型）——能解出实例才包装
        let defs: Vec<(
            String,
            Vec<(crate::parser_lib::Span<String>, Raw, Icit)>,
            Vec<bool>,
            (crate::parser_lib::Span<String>, Vec<(crate::parser_lib::Span<String>, Raw, Icit)>, Raw),
        )> = self
            .tstate
            .definition
            .iter()
            .flat_map(|(trait_name, (trait_params, out_param, methods))| {
                methods.iter().find(|x| x.0.data == t.data).map(|x| {
                    (trait_name.clone(), trait_params.clone(), out_param.clone(), x.clone())
                })
            })
            .filter(|(trait_name, _, out_param, _)| {
                let len = out_param.iter().filter(|x| !**x).count();
                if len == 0 {
                    return false;
                }
                let mut args = vec![Typ::Any; len];
                args[0] = typ.clone();
                self.tstate.solver.clean();
                // 参考版：断言名用 **trait 名**（类表按 trait 名注册；用方法
                // 名会让 new_subgoal 的 unwrap panic）
                self.tstate
                    .solver
                    .synth(Assertion {
                        name: trait_name.clone(),
                        arguments: args,
                    })
                    .is_some()
            })
            .collect();
        // 参考版取第一个能推断成功的包装（traits.first().and_then(infer.ok)）
        let mut result: Option<Result<(&'a Tm<'a>, V), Error>> = None;
        for (trait_name, trait_params, _out_param, (methods_name, methods_params, ret_type)) in defs {
            let mut params = trait_params.clone();
            params.push((
                methods_name.clone().map(|_| "$this".to_owned()),
                Raw::Var(methods_name.clone().map(|_| "Self".to_owned())),
                Icit::Expl,
            ));
            params.push((
                methods_name.clone().map(|_| "$$".to_owned()),
                trait_params
                    .iter()
                    .map(|x| x.0.clone())
                    .fold(
                        Raw::Var(methods_name.clone().map(|_| trait_name.clone())),
                        |ret, x| Raw::App(Box::new(ret), Box::new(Raw::Var(x)), Either::Icit(Icit::Impl)),
                    ),
                Icit::Impl,
            ));
            params.extend(methods_params.iter().cloned());
            let body = std::iter::once((
                Raw::Var(methods_name.clone().map(|_| "$this".to_owned())),
                Icit::Expl,
            ))
            .chain(methods_params.iter().map(|x| (Raw::Var(x.0.clone()), x.2)))
            .fold(
                Raw::Obj(
                    Box::new(Raw::Var(methods_name.clone().map(|_| "$$".to_owned()))),
                    Some(methods_name.clone()),
                ),
                |ret, (x, icit)| Raw::App(Box::new(ret), Box::new(x), Either::Icit(icit)),
            );
            let decl = Raw::Let(
                methods_name.clone().map(|x| format!("${x}")),
                Box::new(params.iter().rev().fold(ret_type.clone(), |a, b| {
                    Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a))
                })),
                Box::new(params.iter().rev().fold(body, |a, b| {
                    Raw::Lam(b.0.clone(), Either::Icit(b.2), Box::new(a))
                })),
                Box::new(Raw::App(
                    Box::new(Raw::Var(methods_name.clone().map(|x| format!("${x}")))),
                    Box::new(x.clone()),
                    Either::Icit(Icit::Expl),
                )),
            );
            let r = self.infer_expr(bump, cxt, &decl);
            if r.is_ok() {
                result = Some(r);
                break;
            }
        }
        match result {
            Some(r) => r,
            None => Err(self.mk_no_object_err(bump, cxt, &t, a, tm)),
        }
    }

    /// Obj/trait 包装失败的消息（参考版 trait_wrap 的 Err：接收者 pretty +
    /// 期望类型的 **nf** pretty——`\`{}\`: {} has no object \`{}\``）。
    fn mk_no_object_err(
        &mut self,
        bump: &Bump,
        cxt: &Cxt<'_>,
        t: &crate::parser_lib::Span<String>,
        a: V,
        tm: &Tm<'_>,
    ) -> Error {
        if std::env::var("L11_LOOPCAP").is_ok() {
            eprintln!("TRACE no_object field={}", t.data);
        }
        // 参考版：`self.nf(&cxt.decl, &cxt.env, &self.quote(&cxt.decl,
        // cxt.lvl, &a))`——quote 后再 eval 再 quote（nf = quote(eval)）
        let q1 = self.quote(bump, cxt, cxt.lvl, a);
        let v = self.eval(bump, cxt, cxt.env, q1);
        let q2 = self.quote(bump, cxt, cxt.lvl, v);
        let names = types_names_list(cxt.types);
        Error(t.clone().map(|t| {
            format!(
                "`{}`: {} has no object `{}`",
                pretty_tm(0, names.clone(), &export(tm)),
                pretty_tm(0, names.clone(), &export(q2)),
                t,
            )
        }))
    }

    // 主 infer / infer_expr（与参考版 elaboration.rs 逐臂对应）
    // --------------------------------------------------------------------------------

    fn infer_expr<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: &Raw,
    ) -> Result<(&'a Tm<'a>, V), Error> {
        match t {
            // 变量：局部名字（name_map + lvl_types）优先；miss → decl 表
            // 回落（顶层 def/enum/构造子/内建——Tm::Decl 引用 + 登记类型，
            // 参考版 Raw::Var 臂同款，两者皆 miss 即 not in scope）
            Raw::Var(x) => {
                if let Some(&blvl) = cxt.names.by_name.get(x.data.as_str()) {
                    let ty = *cxt.names.by_lvl.get(&blvl).expect("by_lvl 缺层级");
                    let ix = cxt.lvl - blvl - 1;
                    return Ok((bump.alloc(Tm::Var(ix)), ty));
                }
                if let Some(e) = cxt.decls.get(x.data.as_str()) {
                    let name = bump.alloc_str(x.data.as_str());
                    return Ok((bump.alloc(Tm::Decl(name)), e.vty));
                }
                Err(Error(x.clone().map(|x| format!("error name not in scope: {}", x))))
            }

            Raw::Obj(x, t) => {
                // 字段名可缺省（中缀运算符前缀 / 空 `.foo` 补全场景）；参考版
                // Obj 臂入口 unwrap_or(empty_span("")) 同款
                let t = t.clone().unwrap_or(empty_span("".to_owned()));
                // `Point.mk` 限定构造子引用：改写成 Var("Point.mk")（src_names
                // 里 struct 的 case 名）——参考版 Obj 臂的 mk 特例同款
                if t.data == "mk" {
                    if let Raw::Var(sum_name) = x.as_ref() {
                        return self.infer_expr(
                            bump,
                            cxt,
                            &Raw::Var(sum_name.clone().map(|n| format!("{n}.mk"))),
                        );
                    }
                }
                let (tm, a) = self.infer_expr(bump, cxt, x)?;
                let a_f = self.force_v(bump, cxt, a);
                if v_tag(a_f) == 7 {
                    if let XCell::Sum { params, cases, .. } = v_xcell_of(a_f) {
                        // struct：单 case 且名字带 `.mk` → 剥 mk 的构造子
                        // 类型链取字段类型（**U(0) 占位怪癖保留**——参考版
                        // TODO 注释原样：显式 binder 以 U(0) 实例化）
                        let mut c: Option<Vec<(&str, V)>> = None;
                        if cases.len() == 1 && cases[0].contains(".mk") {
                            let case = cases[0];
                            if let Ok((_, case_typ)) =
                                self.infer_expr(bump, cxt, &Raw::Var(empty_span(case.to_string())))
                            {
                                let mut ret: Vec<(&str, V)> = vec![];
                                let mut typ = case_typ;
                                let mut param: Vec<&SumParamV<'_>> =
                                    params.iter().collect();
                                param.reverse();
                                loop {
                                    let typ_f = self.force_v(bump, cxt, typ);
                                    if v_tag(typ_f) == 4 {
                                        let p = v_pi_of(typ_f);
                                        if p.icit == Icit::Expl {
                                            ret.push((p.name, p.dom));
                                            typ = {
                                                let env = env_ext(bump, p.env, v_u(0));
                                                self.eval(bump, cxt, env, p.body)
                                            };
                                        } else {
                                            let val = param
                                                .pop()
                                                .map(|x| x.val)
                                                .unwrap_or_else(v_u0);
                                            ret.push((p.name, p.dom));
                                            typ = {
                                                let env = env_ext(bump, p.env, val);
                                                self.eval(bump, cxt, env, p.body)
                                            };
                                        }
                                    } else {
                                        break;
                                    }
                                }
                                c = Some(ret);
                            }
                        }
                        let field = c
                            .and_then(|params| {
                                params
                                    .into_iter()
                                    .find(|(fields_name, _)| *fields_name == t.data.as_str())
                                    .map(|(_, ty)| ty)
                            })
                            .or_else(|| {
                                params
                                    .iter()
                                    .find(|p| p.name == t.data.as_str())
                                    .map(|p| p.ty)
                            });
                        if let Some(ty) = field {
                            return Ok((
                                bump.alloc(Tm::Obj(tm, bump.alloc_str(&t.data))),
                                ty,
                            ));
                        }
                        // L10：Sum 接收者字段未命中 → trait 方法包装
                        //（参考版把 **force 后**的类型传给 trait_wrap）
                        return self.trait_wrap(bump, cxt, t.clone(), a_f, x, tm);
                    }
                    if let XCell::SumCase { datas, .. } = v_xcell_of(a_f) {
                        // 接收者类型是构造子值：字段类型在 datas 里
                        let field = datas
                            .iter()
                            .find(|d| d.name == t.data.as_str())
                            .map(|d| d.val);
                        if let Some(ty) = field {
                            return Ok((
                                bump.alloc(Tm::Obj(tm, bump.alloc_str(&t.data))),
                                ty,
                            ));
                        }
                        // L10：SumCase 接收者字段未命中 → trait 方法包装
                        return self.trait_wrap(bump, cxt, t.clone(), a_f, x, tm);
                    }
                }
                // L10：其余接收者形态 → trait 方法包装（失败给原文案）
                self.trait_wrap(bump, cxt, t.clone(), a, x, tm)
            }

            // λ 推断：域用 fresh meta，值域闭包封口
            Raw::Lam(x, Either::Icit(i), tbody) => {
                let name: &'a str = bump.alloc_str(&x.data);
                let new_meta = self.fresh_meta(bump, cxt, v_u(0));
                let a = self.eval_fresh(bump, cxt, cxt.env, new_meta);
                let a_t = self.quote(bump, cxt, cxt.lvl, a);
                let cxt2 = self.bind_name(bump, cxt, &x.data, a_t, a);
                let infered = self.infer_expr(bump, &cxt2, tbody);
                let (t_inferred0, b0) = infered?;
                let (t_inferred, b) = self.insert(bump, &cxt2, t_inferred0, b0)?;
                // closeVal：quote 在 lvl+1——给即将到来的 binder 留第 0 槽
                let body = self.quote(bump, cxt, cxt.lvl + 1, b);
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
                Err(Error(x.clone().map(|_| "infer named lambda".to_owned())))
            }

            // 应用
            Raw::App(t, u, arg) => {
                // 实参分派：命名 → insertUntilName 后按 Impl 应用；
                // 位置 Impl → 直接应用；位置 Expl → 先 insert_t
                let t_span = t.to_span();
                let (i, t, tty) = match arg {
                    Either::Name(name) => {
                        let infered = self.infer_expr(bump, cxt, t)?;
                        let (t, tty) = self.insert_until_name(bump, cxt, &name.data, infered.0, infered.1)?;
                        (Icit::Impl, t, tty)
                    }
                    Either::Icit(Icit::Impl) => {
                        let (t, tty) = self.infer_expr(bump, cxt, t)?;
                        (Icit::Impl, t, tty)
                    }
                    Either::Icit(Icit::Expl) => {
                        let infered = self.infer_expr(bump, cxt, t)?;
                        let (t, tty) = self.insert_t(bump, cxt, infered.0, infered.1)?;
                        (Icit::Expl, t, tty)
                    }
                };
                let tty = self.force_v(bump, cxt, tty);
                let (a, bcell) = if v_tag(tty) == 4 {
                    let p = v_pi_of(tty);
                    if p.icit != i {
                        return Err(Error(t_span.map(|_| {
                            format!("icit mismatch {:?} {:?}", i, p.icit)
                        })));
                    }
                    (p.dom, p)
                } else {
                    // 非 Π 头：合成 Π（定义域 + 余定义域挂洞）与之合一。
                    // 参考版把合成 Π 放在 unify_catch 的首位——忠实复刻，
                    // 只影响报错文案方向。合成 binder（"x"）按参考版
                    // cxt.bind 走全量 bind（env/telescope/pruning 扩展），
                    // 但名字不入表外泄（临时 cxt 只喂 fresh_meta）。
                    let new_meta = self.fresh_meta(bump, cxt, v_u(0));
                    let a = self.eval_fresh(bump, cxt, cxt.env, new_meta);
                    let a_t = self.quote(bump, cxt, cxt.lvl, a);
                    let cxt2 = self.bind_name(bump, cxt, "x", a_t, a);
                    let cod_meta = self.fresh_meta(bump, &cxt2, v_u(0));
                    let cell = bump.alloc(PiCell {
                        name: "x",
                        icit: i,
                        dom: a,
                        env: cxt.env,
                        body: cod_meta,
                    });
                    self.unify_catch(bump, cxt, v_pi(cell), tty)?;
                    (a, &*cell)
                };
                let u_checked = self.check(bump, cxt, u, a)?;
                let arg_v = self.eval(bump, cxt, cxt.env, u_checked);
                // t u : B[x |-> u]
                let ty = {
                    let env = env_ext(bump, bcell.env, arg_v);
                    self.eval(bump, cxt, env, bcell.body)
                };
                Ok((bump.alloc(Tm::App(t, u_checked, i)), ty))
            }

            // Infer universe type
            Raw::U(x) => Ok((bump.alloc(Tm::U(*x)), v_u(x + 1))),

            // Infer dependent function types
            Raw::Pi(x, i, a, b) => {
                let mut universe = 0u32;
                let (a_checked, lvl) = self.check_universe(bump, cxt, a)?;
                universe = universe.max(lvl);
                let a_eval = self.eval(bump, &cxt, cxt.env, a_checked);
                let name: &'a str = bump.alloc_str(&x.data);
                let a_t = self.quote(bump, &cxt, cxt.lvl, a_eval);
                let cxt2 = self.bind_name(bump, cxt, &x.data, a_t, a_eval);
                let checked = self.check_universe(bump, &cxt2, b);
                let (b_checked, lvl) = checked?;
                universe = universe.max(lvl);
                Ok((
                    bump.alloc(Tm::Pi(name, *i, a_checked, b_checked)),
                    v_u(universe),
                ))
            }

            // Infer let bindings
            Raw::Let(x, a_ty, t2, u2) => {
                let (a_checked, _) = self.check_universe(bump, cxt, a_ty)?;
                let va = self.eval(bump, &cxt, cxt.env, a_checked);
                let t_checked = self.check(bump, cxt, t2, va)?;
                let vt = self.eval(bump, cxt, cxt.env, t_checked);
                let name: &'a str = bump.alloc_str(&x.data);
                let cxt2 = self.define_name(bump, cxt, &x.data, a_checked, t_checked, vt, va);
                let inferred = self.infer_expr(bump, &cxt2, u2);
                let (u_inferred, b) = inferred?;
                Ok((
                    bump.alloc(Tm::Let(name, a_checked, t_checked, u_inferred)),
                    b,
                ))
            }

            // Infer holes
            Raw::Hole(_) => {
                let new_meta = self.fresh_meta(bump, cxt, v_u(0));
                let a = self.eval_fresh(bump, cxt, cxt.env, new_meta);
                let t = self.fresh_meta(bump, cxt, a);
                Ok((t, a))
            }

            Raw::LiteralIntro(literal) => Ok((
                bump.alloc(Tm::LiteralIntro(bump.alloc_str(&literal.data))),
                v_lit_ty(),
            )),

            // match 只能在检查模式下使用（期望类型决定分支体怎么查）
            Raw::Match(_, _) => Err(Error(
                t_span_of(t).map(|_| "try to infer match".to_owned()),
            )),

            // enum 本体（Decl::Enum 注册期构造）：逐参数推断值 + 引读类型
            Raw::Sum(name, params, cases, universe, is_trait) => {
                let mut ps: Vec<SumParamT<'_>> = Vec::with_capacity(params.len());
                for (n, i, raw) in params {
                    let (value_checked, value_ty) = self.infer_expr(bump, cxt, raw)?;
                    let ty = self.quote(bump, cxt, cxt.lvl, value_ty);
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
                        *is_trait,
                    )),
                    v_u(*universe),
                ))
            }

            // 构造子值（Decl::Enum 注册期构造）：typ 只推断不检查
            Raw::SumCase {
                typ,
                case_name,
                datas,
                is_trait,
            } => {
                let (typ_checked, _) = self.infer_expr(bump, cxt, typ)?;
                let typ_val = self.eval(bump, cxt, cxt.env, typ_checked);
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
                        is_trait: *is_trait,
                    }),
                    typ_val,
                ))
            }
        }
    }

    // decl 层的推断（参考版 `Infer::infer(Decl)`）：def 折叠参数后
    // check_universe 类型、fake_bind 占位、检查体、global 表覆盖真值；
    // Println 推断体；enum 先扫宇宙层级再注册类型本体 + 逐构造子（裸名）。
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
                let (typ_tm, _) = self.check_universe(bump, cxt, &typ)?;
                let vtyp = self.eval(bump, &cxt, cxt.env, typ_tm);
                // 递归：fake_bind 先把名字登记成 `Decl(name)` 存根（撞名即
                // redefine 报错），检查体，再用真值覆盖（decl_reg 静默写）。
                let fake = self.fake_bind(bump, cxt, &name.data, typ_tm, vtyp)?;
                let t_tm = self.check(bump, &fake, &bod, vtyp)?;
                // 参考版 Def 臂：检查后 solve_multi_trait(0).unwrap()（求解
                // 失败即 panic——参考版 unwrap 同款崩溃）
                self.solve_multi_trait_ref(bump, &fake, 0).unwrap();
                // 参考版 Def 臂：no_metas 检查（未解 meta 带类型类定型消息）
                if let Some(meta_ty) = no_metas(bump, self, &fake, t_tm) {
                    return Err(err_unsolved_meta(bump, self, &fake, t_tm, meta_ty));
                }
                // 登记值在**含存根的 fake 表**下求值（自引用停在国内；
                // 参考版 eval(&fake_cxt.decl, ...) 同款）
                let vt = self.eval(bump, &fake, fake.env, t_tm);
                let out = self.decl_reg(bump, cxt, &name.data, t_tm, vt, typ_tm, vtyp);
                Ok((DeclOut::Def { name: bump.alloc_str(&name.data) }, out))
            }
            Decl::Println(t) => {
                let (tm, _) = self.infer_expr(bump, cxt, t)?;
                Ok((DeclOut::Println(tm), clone_cxt(cxt)))
            }
            Decl::Enum {
                is_trait,
                name,
                params,
                cases,
            } => {
                // 宇宙层级扫描（副作用照参考版：infer_expr/check_universe
                // 的 meta 分配全保留，结果只取层级）
                let mut universe_lvl = 0u32;
                for p in params.iter() {
                    if let Ok((Tm::U(lvl), _)) = self.infer_expr(bump, cxt, &p.1) {
                        universe_lvl = universe_lvl.max(*lvl);
                    }
                }
                for case in cases.iter() {
                    for c in case.1.iter() {
                        if let Ok((_, lvl)) = self.check_universe(bump, cxt, &c.1) {
                            universe_lvl = universe_lvl.max(lvl);
                        }
                    }
                }
                // enum 类型本体：λ params → Sum(name, [(p, Var p, ?, icit)], cases)
                let new_params: Vec<(crate::parser_lib::Span<String>, Icit, Raw)> = params
                    .iter()
                    .map(|x| (x.0.clone(), x.2, Raw::Var(x.0.clone())))
                    .collect();
                // 构造子缺省返回类型：Name 逐个应用到隐式参数
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
                let sum = Raw::Sum(
                    name.clone(),
                    new_params,
                    cases_spanned,
                    universe_lvl,
                    *is_trait,
                );
                let typ = params
                    .iter()
                    .rev()
                    .fold(Raw::U(universe_lvl), |a, b| {
                        Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a))
                    });
                let bod = params.iter().rev().fold(sum, |a, b| {
                    Raw::Lam(b.0.clone(), Either::Icit(b.2), Box::new(a))
                });
                let (typ_tm, _) = self.check_universe(bump, cxt, &typ)?;
                let vtyp = self.eval(bump, &cxt, cxt.env, typ_tm);
                let fake = self.fake_bind(bump, cxt, &name.data, typ_tm, vtyp)?;
                let t_tm = self.check(bump, &fake, &bod, vtyp)?;
                // 登记值在含存根的 fake 表下求值（参考版 eval(&cxt.decl,
                // &fake_cxt.env, ...)——注意用**原 cxt 的 decl**：Enum 臂
                // 与 Def 臂不同，参考版在此用 `cxt.decl`
                let vt = self.eval(bump, cxt, fake.env, t_tm);
                let mut cxt = self.decl_reg(bump, cxt, &name.data, t_tm, vt, typ_tm, vtyp);
                // 逐构造子注册：体 = λ(隐式参数, 字段) → SumCase{typ: ret, datas: 字段自身}；
                // **裸名登记**（L11 无 Enum.case 别名）
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
                        is_trait: *is_trait,
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
                    let (typ_tm, _) = self.check_universe(bump, &cxt, ctor_ty)?;
                    let vtyp = self.eval(bump, &cxt, cxt.env, typ_tm);
                    let t_tm = self.check(bump, &cxt, &bod, vtyp)?;
                    let vt = self.eval(bump, &cxt, cxt.env, t_tm);
                    cxt = self.decl_reg(bump, &cxt, &ctor_name.data, t_tm, vt, typ_tm, vtyp);
                }
                Ok((DeclOut::Enum, cxt))
            }
            // trait 声明：solver 注册新类；Self + params 组成 enum 参数
            //（out_param 参数的类型是 `outParam(...)` 应用）；方法表记入
            // trait_definition；本体脱糖成单构造子（`{Name}.mk`）的 trait
            // enum（is_trait=true）
            Decl::TraitDecl { name, params, methods } => {
                self.tstate.solver.new_trait(name.data.clone());
                let mut param = vec![(name.clone().map(|_| "Self".to_owned()), Raw::Hole(empty_span(())), Icit::Impl)];
                param.append(&mut params.clone());
                let out_param = param.iter().map(|x| match &x.1 {
                        Raw::App(t, ..) if matches!(t.as_ref(), Raw::Var(d) if d.data == "outParam") => true,
                        _ => false,
                    }).collect::<Vec<_>>();
                self.tstate.definition.insert(name.data.clone(), (param.clone(), out_param.clone(), methods.clone()));
                self.tstate.out_param.insert(name.data.clone(), out_param);
                let mut cxt = clone_cxt(cxt);
                let new_cases = vec![(
                    name.clone().map(|x| format!("{x}.mk")),
                    methods
                        .iter()
                        .map(|x| (
                            x.0.clone(),
                            std::iter::once((x.0.clone().map(|_| "this".to_owned()), Raw::Var(x.0.clone().map(|_| "Self".to_owned())), Icit::Expl))
                                .chain(x.1.iter().cloned())
                                .rev()
                                .fold(x.2.clone(), |a, b| {
                                    Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a))
                                }),
                            Icit::Expl,
                        ))
                        .collect(),
                    None,
                )];
                let (_, c) = self.infer_decl(bump, &cxt, &Decl::Enum {
                    is_trait: true,
                    name: name.clone(),
                    params: param,
                    cases: new_cases,
                })?;
                cxt = c;
                Ok((DeclOut::Trait, cxt))
            }
            // 实例声明：need_create 时先合成 trait 声明；实例类型经
            // to_typ 收集（out_param 槽剔除）；登记 Instance 后把方法
            // 包成 `λ this. body` 的 def（名 = "{:?}{:?}" 的 typ_name）
            Decl::ImplDecl { name, params, trait_name, trait_params, methods, need_create } => {
                let mut cxt = clone_cxt(cxt);
                if *need_create {
                    let new_methods = methods
                        .iter()
                        .filter_map(|x| match x {
                            Decl::Def { name, params, ret_type, body: _ } => {
                                Some((name.clone(), params.clone(), ret_type.clone()))
                            },
                            _ => None,
                        })
                        .collect::<Vec<_>>();
                    let (_, new_cxt) = self.infer_decl(bump, &cxt, &Decl::TraitDecl {
                        name: trait_name.clone(),
                        params: params.clone(),
                        methods: new_methods,
                    })?;
                    cxt = new_cxt;
                }
                for (x, a, _) in params.iter() {
                    let (a_checked, _) = self.check_universe(bump, &cxt, a)?;
                    let a_eval = self.eval(bump, &cxt, cxt.env, a_checked);
                    let a_t = self.quote(bump, &cxt, cxt.lvl, a_eval);
                    cxt = self.bind_name(bump, &cxt, &x.data, a_t, a_eval);
                }
                let name_raw = (*name).clone();
                let typ = self.check_universe(bump, &cxt, &name_raw)?.0;
                let typ_val = self.eval(bump, &cxt, cxt.env, typ);
                let typ = val_to_typ(&self.spine, &self.defs, typ_val)
                    .ok_or_else(|| Error(name.to_span().map(|_| "Not a type".to_string())))?;
                let mut trait_param = vec![typ.clone()];
                for a in trait_params.iter() {
                    let (a_checked, _) = self.check_universe(bump, &cxt, a)?;
                    let a_eval = self.eval(bump, &cxt, cxt.env, a_checked);
                    match val_to_typ(&self.spine, &self.defs, a_eval) {
                        Some(x) => trait_param.push(x),
                        None => return Err(Error(trait_name.clone().map(|_| "Not a type".to_string()))),
                    };
                }
                let out_param = self.tstate.out_param.get(&trait_name.data)
                    .ok_or(Error(trait_name.clone().map(|n| format!("trait `{}` not declared", n))))?;
                let trait_param: Vec<Typ> = trait_param.into_iter()
                    .zip(out_param.iter())
                    .filter(|(_, o)| !**o)
                    .map(|(x, _)| x)
                    .collect();
                let typ_name = format!("{:?}{:?}", trait_name.data, trait_param);
                let inst = Instance {
                    assertion: Assertion { name: trait_name.data.clone(), arguments: trait_param },
                    dependencies: crate::list::List::new(),
                    lvl: trait_name.clone().to_span().map(|_| typ_name.clone()),
                };
                self.tstate.solver.impl_trait_for(trait_name.data.clone(), inst);
                let mut ret = std::iter::once((*name).clone())
                    .chain(trait_params.iter().cloned())
                    .fold(Raw::Var(trait_name.clone().map(|x| format!("{x}.mk"))), |ret, x| {
                        Raw::App(Box::new(ret), Box::new(x), Either::Icit(Icit::Impl))
                    });
                for decl in methods {
                    if let Decl::Def { name: def_name, params, ret_type: _, body } = decl {
                        ret = Raw::App(
                            Box::new(ret),
                            Box::new(Raw::Lam(
                                def_name.clone().map(|_| "this".to_owned()),
                                Either::Icit(Icit::Expl),
                                Box::new(params.iter().rev()
                                    .fold(body.clone(), |ret, x| Raw::Lam(x.0.clone(), Either::Icit(x.2), Box::new(ret)))
                                )
                            )),
                            Either::Icit(Icit::Expl),
                        );
                    }
                }
                let trait_name_raw = Raw::Var(trait_name.clone());
                let ret_type = trait_params.iter().cloned()
                    .fold(Raw::App(
                        Box::new(trait_name_raw),
                        Box::new((*name).clone()),
                        Either::Icit(Icit::Impl)
                    ), |a, b| Raw::App(Box::new(a), Box::new(b), Either::Icit(Icit::Impl)));
                let def_name = trait_name.clone().to_span().map(|_| typ_name.clone());
                let (_, c) = self.infer_decl(bump, &cxt, &Decl::Def {
                    name: def_name,
                    params: params.clone(),
                    ret_type,
                    body: ret,
                })?;
                cxt = c;
                Ok((DeclOut::TraitImpl, cxt))
            }
        }
    }
}

/// `Raw::Match` 推断错误用的 span（to_span 的借用版）。
fn t_span_of(t: &Raw) -> crate::parser_lib::Span<()> {
    t.to_span()
}

/// `Val::U(0)` 占位（参考版 struct 字段剥链的 `unwrap_or(Val::U(0))`）。
fn v_u0() -> V {
    v_u(0)
}

/// Cxt 的浅克隆（env/引用 Copy，names 是 Rc 克隆——快照共享）。
fn clone_cxt<'a>(cxt: &Cxt<'a>) -> Cxt<'a> {
    Cxt {
        env: cxt.env,
        update_from: cxt.update_from,
        names: cxt.names.clone(),
        types: cxt.types,
        locals: cxt.locals,
        pruning: cxt.pruning,
        binds: cxt.binds,
        lvl: cxt.lvl,
            decls: cxt.decls.clone(),
    }
}

/// trait 定义 / 合成状态（参考版 `Infer` 的 trait_solver / trait_definition /
/// trait_out_param 三表同构；Clone 供 temp-infer 快照换入换出）。
#[derive(Clone, Default)]
pub(crate) struct TraitState {
    /// Prolog 式实例求解器。
    solver: Synth,
    /// trait 名 → (参数表（含 Self）, out_param 掩码, 方法表)。
    definition:
        HashMap<String, (Vec<(crate::parser_lib::Span<String>, Raw, Icit)>, Vec<bool>, Vec<(crate::parser_lib::Span<String>, Vec<(crate::parser_lib::Span<String>, Raw, Icit)>, Raw)>)>,
    /// trait 名 → 参数 out_param 掩码。
    out_param: HashMap<String, Vec<bool>>,
}

/// 参考 `Val::to_typ` 的快版（快版 Val → trait 求解器的 Typ）。
/// 字面量 / Prim 分支参考版是 `todo!()`——同款不可达即崩。
pub(crate) fn val_to_typ(spine: &Spine, defs: &[V], v: V) -> Option<Typ> {
    match v_tag(v) {
        5 => None, // Flex
        0 => {
            let _ = (spine, defs);
            Some(Typ::Var(v_lvl_of(v)))
        }
        2 => {
            // Rigid/Flex/Obj 头的链 → None（参考版 Rigid(_, _) 非空 spine → None）
            let _ = (spine, defs);
            None
        }
        3 => Some(Typ::Val(crate::parser_lib::Span {
            data: format!("Type {}", v_u_of(v)),
            start_offset: 0,
            end_offset: 0,
            path_id: 0,
        })),
        7 => match v_xcell_of(v) {
            XCell::Sum {
                name,
                params,
                is_trait,
                ..
            } => {
                let _ = is_trait;
                Some(if params.is_empty() {
                    Typ::Val(crate::parser_lib::Span {
                        data: name.to_string(),
                        start_offset: 0,
                        end_offset: 0,
                        path_id: 0,
                    })
                } else {
                    let args: Vec<Typ> = params
                        .iter()
                        .filter_map(|p| val_to_typ(spine, defs, p.val))
                        .collect();
                    Typ::Construct(
                        crate::parser_lib::Span {
                            data: name.to_string(),
                            start_offset: 0,
                            end_offset: 0,
                            path_id: 0,
                        },
                        args,
                    )
                })
            }
            _ => None,
        },
        _ => None,
    }
}

/// 把 Option 臂表原地展平为 Some 臂的 Vec（参考版 `into_iter().flatten()`）。
fn remaining_flatten<'a>(remaining: &mut Vec<Option<Arm<'a>>>) -> Vec<Arm<'a>> {
    std::mem::take(remaining).into_iter().flatten().collect()
}

/// 槽位向量 → 纯链环境（头 = 最内层）。
fn chain_env<'a>(bump: &'a Bump, slots: &[V]) -> Env<'a> {
    let mut env: Option<&'a EnvCons<'a>> = None;
    for val in slots.iter().rev() {
        env = Some(bump.alloc(EnvCons { val: *val, next: env }));
    }
    Env {
        flat_base: 0,
        flat_len: 0,
        binds: env,
    }
}

/// decl 层推断的产出：Def 带名（bench 的 nf 口径按名定位），Println 带
/// elaborated 体（run 的 nf 输出用）。
enum DeclOut<'a> {
    Def { name: &'a str },
    Println(&'a Tm<'a>),
    Enum,
    Trait,
    TraitImpl,
}

// 模式匹配编译（参考版 pattern_match.rs 的逐句移植）
// --------------------------------------------------------------------------------

type Var = i32;

#[derive(Debug, Clone)]
pub(crate) enum Warning {
    Unreachable(Raw),
    Unmatched(Pattern),
}

#[derive(Debug, Clone)]
struct PatConstructor {
    data: Vec<(usize, Vec<PatternDetail>)>,
}

impl PatConstructor {
    fn new() -> Self {
        PatConstructor { data: vec![(2, vec![])] }
    }

    fn clean(mut self) -> Self {
        while let Some(true) = self.data.last().map(|(num, x)| x.len() == *num) {
            let (_, t) = self.data.pop().unwrap();
            self.data
                .last_mut()
                .map(|x| {
                    x.1.last_mut()
                        .map(|x| match x {
                            PatternDetail::Con(_, x) => {*x = t;},
                            _ => {},
                        })
                });
        }
        self
    }

    fn push(self, detail: PatternDetail) -> Self {
        let mut ret = self.clean();
        ret.data.last_mut().map(|(_, x)| x.push(detail));
        ret
    }

    fn new_level(mut self, index: usize) -> Self {
        self.data.push((index, vec![]));
        self
    }
}

#[derive(Debug, Clone)]
struct MatchArm {
    pats: Vec<Pattern>,
    body: (Raw, usize),
}

#[derive(Debug, Clone)]
enum MatchContext {
    Outermost,
    InCons {
        parent: Rc<MatchContext>,
        constr: crate::parser_lib::Span<String>,
        icit: Icit,
        before: Vec<Pattern>,
        after: Vec<Pattern>,
    },
}

/// compile_aux 的臂记录（参考版元组的具名版）：heads = 构造子下钻的新增
/// 槽（初始臂为空），is_impl = 隐式槽合成的通配臂标记。
struct Arm<'a> {
    arm: MatchArm,
    idx: usize,
    cxt: Cxt<'a>,
    heads: Vec<(Var, V, crate::parser_lib::Span<String>, Icit)>,
    raw: Raw,
    target_typ: V,
    ori: V,
    patcon: PatConstructor,
    is_impl: bool,
}

pub(crate) struct Compiler<'a> {
    warnings: Vec<Warning>,
    reachable: FxHashMap<usize, ()>,
    checked_ret: FxHashSet<Raw>,
    pub(crate) pats: Vec<(PatternDetail, &'a Tm<'a>)>,
    seed: i32,
    ret_type: V,
}

impl<'a> Compiler<'a> {
    fn new(ret_type: V) -> Self {
        Compiler {
            warnings: Vec::new(),
            reachable: FxHashMap::default(),
            checked_ret: FxHashSet::default(),
            pats: Vec::new(),
            seed: 0,
            ret_type,
        }
    }

    fn fresh(&mut self) -> i32 {
        self.seed += 1;
        self.seed
    }

    fn fill_context(ctx: &MatchContext, pat: &Pattern) -> Pattern {
        match ctx {
            MatchContext::Outermost => pat.clone(),
            MatchContext::InCons {
                parent,
                constr,
                icit,
                before,
                after,
            } => {
                let mut new_before = before.clone();
                new_before.reverse();
                new_before.push(pat.clone());
                new_before.extend(after.clone());
                Self::fill_context(parent, &Pattern::Con(constr.clone(), new_before, *icit))
            }
        }
    }

    fn next_hole(ctx: &MatchContext, pat: &Pattern) -> MatchContext {
        match ctx {
            MatchContext::Outermost => MatchContext::Outermost,
            MatchContext::InCons {
                parent,
                constr,
                icit,
                before,
                after,
            } => match after[..] {
                [] => Self::next_hole(parent, &Pattern::Con(constr.clone(), before.clone(), *icit)),
                _ => MatchContext::InCons {
                    parent: parent.clone(),
                    constr: constr.clone(),
                    icit: *icit,
                    before: vec![pat.clone()],
                    after: after[1..].to_vec(),
                },
            },
        }
    }

    /// 构造子可达性过滤（参考版 `filter_accessible_constrs`）：构造子类型
    /// 链逐层推断（**真实 infer**——meta 分配保留），可访问性判定在
    /// **metas 快照换入换出**的 temp-infer 里跑 check_pm（参考版克隆
    /// `temp_infer` 的对应物）。错误路径统一撤销名字轨迹（temp cxt 的
    /// 绑定全部丢弃——参考版克隆丢弃同款）。
    fn filter_accessible_constrs(
        &mut self,
        mach: &mut Machine,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        typ: V, // 被匹配项的具体类型，如 `Vec (Succ n)` 的 Val
        all_constrs: &[crate::parser_lib::Span<String>],
    ) -> Result<Vec<crate::parser_lib::Span<String>>, Error> {
        self.filter_accessible_constrs_inner(mach, bump, cxt, typ, all_constrs)
    }

    fn filter_accessible_constrs_inner(
        &mut self,
        mach: &mut Machine,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        typ: V,
        all_constrs: &[crate::parser_lib::Span<String>],
    ) -> Result<Vec<crate::parser_lib::Span<String>>, Error> {
        let mut accessible = Vec::new();

        let forced_type = mach.force_v(bump, cxt, typ);
        if !(v_tag(forced_type) == 7 && matches!(v_xcell_of(forced_type), XCell::Sum { .. })) {
            // 非和类型：所有构造子按"可达"处理（参考版同款退路）
            for constr_def in all_constrs {
                accessible.push(constr_def.clone());
            }
            return Ok(accessible);
        }

        for constr_name in all_constrs {
            // 1. 为构造子自身实参造 fresh meta（类型经逐层推断取得；推断在
            //    **真实 infer** 上——meta 分配保留，参考版同款）
            let mut to_check = Raw::Var(constr_name.clone());
            let mut cur_cxt = clone_cxt(cxt);
            loop {
                let (_, typ2) = mach.infer_expr(bump, &cur_cxt, &to_check)?;
                if v_tag(typ2) == 4 {
                    let p = v_pi_of(typ2);
                    // Only explicit args matter for the structure
                    to_check = Raw::App(
                        Box::new(to_check),
                        Box::new(Raw::Hole(empty_span(()))),
                        Either::Icit(p.icit),
                    );
                    let q = mach.quote(bump, &cur_cxt, cur_cxt.lvl, p.dom);
                    let name = p.name.to_string();
                    cur_cxt = mach.bind_name(bump, &cur_cxt, &name, q, p.dom);
                } else {
                    break;
                }
            }

            // 2. 可访问性判定在 metas 快照里跑（temp infer；快照换入换出 +
            //    名字轨迹回滚）
            let temp_metas = mach.metas.clone();
            let saved = std::mem::replace(&mut mach.metas, temp_metas);
            let r = mach.check_pm(bump, &cur_cxt, &to_check, forced_type);
            mach.metas = saved;
            if std::env::var("L09_TRACE").is_ok() {
                eprintln!("FILTER {} {}", constr_name.data, if r.is_ok() {"ok"} else {"err"});
            }
            if r.is_ok() {
                // 构造子可访问
                accessible.push(constr_name.clone());
            }
        }

        Ok(accessible)
    }

    fn compile(
        &mut self,
        mach: &mut Machine,
        bump: &'a Bump,
        typ: V,
        arms: &[(Pattern, Raw)],
        cxt: &Cxt<'a>,
        target_val: V,
    ) -> Result<(), Error> {
        self.warnings = Vec::new();
        self.reachable = FxHashMap::default();
        let initial: Vec<Arm<'a>> = arms
            .iter()
            .enumerate()
            .map(|(idx, (pat, body))| Arm {
                arm: MatchArm {
                    pats: vec![pat.clone()],
                    body: (body.clone(), idx),
                },
                idx,
                cxt: clone_cxt(cxt),
                heads: vec![],
                raw: pat.to_raw(),
                target_typ: typ,
                ori: target_val,
                patcon: PatConstructor::new(),
                is_impl: false,
            })
            .collect();
        self.compile_aux(
            mach,
            bump,
            &[(0, typ, empty_span(String::new()), Icit::Expl)],
            &initial,
            &MatchContext::Outermost,
        )?;

        // 检查是否有不可达分支
        let unreachable = arms
            .iter()
            .enumerate()
            .filter_map(|(idx, (_, body))| {
                if !self.reachable.contains_key(&idx) {
                    Some(Warning::Unreachable(body.clone()))
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();
        // 参考版 `unreachable.into_iter().chain(self.warnings)`——不可达
        // 警告在前
        let mut all = unreachable;
        all.extend(self.warnings.clone());
        self.warnings = all;
        Ok(())
    }

    /// 臂边界统一撤销名字轨迹（compile_aux 内部经 bind_name 压入的绑定
    /// 不经 unwind 退出——参考版 src_names 随 Cxt 克隆天然隔离，快版轨迹
    /// 需手动回滚）。
    fn compile_aux(
        &mut self,
        mach: &mut Machine,
        bump: &'a Bump,
        heads: &[(Var, V, crate::parser_lib::Span<String>, Icit)],
        arms: &[Arm<'a>],
        context: &MatchContext,
    ) -> Result<bool, Error> {
        self.compile_aux_inner(mach, bump, heads, arms, context)
    }

    fn compile_aux_inner(
        &mut self,
        mach: &mut Machine,
        bump: &'a Bump,
        heads: &[(Var, V, crate::parser_lib::Span<String>, Icit)],
        arms: &[Arm<'a>],
        context: &MatchContext,
    ) -> Result<bool, Error> {
        if std::env::var("L09_TRACE").is_ok() {
            eprintln!(
                "CAUX heads={} arms={} pats0={:?}",
                heads.len(),
                arms.len(),
                arms.iter().map(|a| format!("{:?}", a.arm.pats)).collect::<Vec<_>>()
            );
        }
        match heads {
            [] => match arms {
                // L10 leaf 守卫：臂耗尽 或 首模式是**虚**通配（Span<bool>
                // data=false——ctor 走查自动生成的槽，不再绑定/检查）
                [arm, ..]
                    if arm.arm.pats.is_empty()
                        || arm
                            .arm
                            .pats
                            .get(0)
                            .map(|x| matches!(x, Pattern::Any(sp, _) if !sp.data))
                            == Some(true) =>
                {
                    // check_pm 失败 → Ok(false)（参考版同款：整个构造子
                    // 分支回退 false）
                    let (_, cxt) = match mach.check_pm_final(
                        bump, &arm.cxt, &arm.raw, arm.target_typ, arm.ori,
                    ) {
                        Ok(x) => x,
                        Err(_) => return Ok(false),
                    };
                    if std::env::var("L09_TRACE").is_ok() {
                        eprintln!("CAUX REACH idx={}", arm.idx);
                    }
                    self.reachable.insert(arm.idx, ());
                    if self.checked_ret.contains(&arm.raw) {
                        return Ok(true);
                    }
                    // 期望类型重锚到臂上下文：quote → eval（flex 免锚）
                    let ret_type = {
                        let t = mach.force_v(bump, &cxt, self.ret_type);
                        if is_flex(&mach.spine, t) {
                            t
                        } else {
                            let tm = mach.quote(bump, &cxt, cxt.lvl, t);
                            mach.eval(bump, &cxt, cxt.env, tm)
                        }
                    };
                    let ret = mach.check(bump, &cxt, &arm.arm.body.0, ret_type)?;
                    self.checked_ret.insert(arm.raw.clone());
                    let patcon = arm.patcon.clone().clean();
                    self.pats.push((patcon.data[0].1[0].clone(), ret));
                    Ok(true)
                }
                // L10：还有非虚模式但无法推进 → "invalid pattern" 定向错误
                [arm, ..] => {
                    let msg = match &arm.arm.pats[0] {
                        Pattern::Any(span, _) => span.map(|_| "invalid pattern".to_owned()),
                        Pattern::Con(span, _, _) => {
                            span.clone().map(|x| format!("invalid pattern {}", x))
                        }
                    };
                    Err(Error(msg))
                }
                [] => Ok(false),
            },
            [(var, typ, head_name, icit), heads_rest @ ..] => {
                let not_necessary = arms
                    .iter()
                    .all(|arm| matches!(arm.arm.pats[..], [Pattern::Any(_, i)] if i == *icit));

                if not_necessary {
                    let new_context =
                        Self::next_hole(context, &Pattern::Any(empty_span(true), *icit));
                    let mut new_arms: Vec<Arm<'a>> = Vec::with_capacity(arms.len());
                    for arm in arms {
                        // L10：首模式是虚通配（data=false）的臂**不绑定**、
                        // patcon 原样（参考版同款）
                        let fake_first = matches!(
                            arm.arm.pats.first(),
                            Some(Pattern::Any(sp, _)) if !sp.data
                        );
                        let cxt2 = if fake_first {
                            clone_cxt(&arm.cxt)
                        } else {
                            let q = mach.quote(bump, &arm.cxt, arm.cxt.lvl, *typ);
                            let name = head_name.clone().map(|x| format!("_{}", x));
                            let cname = name.data.clone();
                            mach.bind_name(bump, &arm.cxt, &cname, q, *typ)
                        };
                        let patcon2 = if fake_first {
                            arm.patcon.clone()
                        } else {
                            arm.patcon
                                .clone()
                                .clean()
                                .push(PatternDetail::Any(empty_span(())))
                        };
                        new_arms.push(Arm {
                            arm: MatchArm {
                                pats: arm.arm.pats.get(1..).map(|x| x.to_vec()).unwrap_or(vec![]),
                                body: arm.arm.body.clone(),
                            },
                            idx: arm.idx,
                            cxt: cxt2,
                            heads: vec![],
                            raw: arm.raw.clone(),
                            target_typ: arm.target_typ,
                            ori: arm.ori,
                            patcon: patcon2,
                            is_impl: false,
                        });
                    }
                    return self.compile_aux(mach, bump, heads_rest, &new_arms, &new_context);
                }
                let (param, constrs) = {
                    let f = mach.force_v(bump, &arms[0].cxt, *typ);
                    if v_tag(f) == 7 {
                        if let XCell::Sum { params, cases, .. } = v_xcell_of(f) {
                            let cs: Vec<crate::parser_lib::Span<String>> = cases
                                .iter()
                                .map(|c| empty_span(c.to_string()))
                                .collect();
                            (params.to_vec(), cs)
                        } else {
                            (vec![], vec![empty_span("$any$".to_owned())])
                        }
                    } else {
                        (vec![], vec![empty_span("$any$".to_owned())])
                    }
                };

                let constrs_name: std::collections::BTreeSet<String> = constrs
                    .iter()
                    .map(|x| x.data.clone())
                    .collect();

                let mut any_valid = false;
                for constr in constrs.iter() {
                    // remaining_arms：每臂一个 Option（None = 该臂不参与本
                    // 构造子分支——参考版 filter_map 的 Some(None)/None 同型）
                    let mut remaining: Vec<Option<Arm<'a>>> = Vec::new();
                    for arm in arms {
                        let mut new_heads: Vec<(Var, V, crate::parser_lib::Span<String>, Icit)> =
                            vec![];
                        if constr.data != "$any$" {
                            let matched = 'armblk: {
                                let accessible_constrs = match self.filter_accessible_constrs(
                                    mach,
                                    bump,
                                    &arm.cxt,
                                    *typ,
                                    &constrs,
                                ) {
                                    Ok(a) => a,
                                    Err(e) => {
                                        if std::env::var("L09_TRACE").is_ok() {
                                            eprintln!("FILTER_ERR {}", e.0.data);
                                        }
                                        break 'armblk None; // .ok()?：本臂移除
                                    }
                                };
                                if !accessible_constrs.iter().any(|x| x == constr) {
                                    break 'armblk Some(None); // 不可达：Some(None) 保留
                                }

                                let infered =
                                    mach.infer_expr(bump, &arm.cxt, &Raw::Var(constr.clone()));
                                let (_, mut cty) = match infered {
                                    Ok(x) => x,
                                    Err(_) => break 'armblk None, // .ok()?：本臂丢弃
                                };
                                let mut param_impl: Vec<SumParamV<'_>> = param
                                    .iter()
                                    .filter(|x| x.icit == Icit::Impl)
                                    .cloned()
                                    .collect();
                                param_impl.reverse();
                                while v_tag(cty) == 4 {
                                    let p = v_pi_of(cty);
                                    if !param_impl.is_empty() {
                                        let val =
                                            param_impl.pop().map(|x| x.val).unwrap_or_else(v_u0);
                                        cty = {
                                            let env = env_ext(bump, p.env, val);
                                            mach.eval(bump, &arm.cxt, env, p.body)
                                        };
                                    } else {
                                        new_heads.push((
                                            self.fresh(),
                                            p.dom,
                                            empty_span(p.name.to_string()),
                                            p.icit,
                                        ));
                                        cty = {
                                            let env = env_ext(
                                                bump,
                                                p.env,
                                                v_lvl(arm.cxt.lvl + new_heads.len() as u32 - 1),
                                            );
                                            mach.eval(bump, &arm.cxt, env, p.body)
                                        };
                                    }
                                }
                                Some(Some(()))
                            };
                            // matched: None = 本臂从 vec 移除；Some(None) =
                                // 不可达保留；Some(Some(())) = 继续模式分派
                                match matched {
                                    None => continue,
                                    Some(None) => {
                                        remaining.push(None);
                                        continue;
                                    }
                                    Some(Some(())) => {}
                                }
                        }
                        let new_heads_len = new_heads.len();
                        let matched: Option<Arm<'a>> = match &arm.arm.pats[..] {
                            [Pattern::Any(x, i), ..] if i == icit => {
                                let name = head_name.clone().map(|x| format!("_{}", x));
                                let cname = name.data.clone();
                                let (cxt2, patcon2) = if !x.data {
                                    (clone_cxt(&arm.cxt), arm.patcon.clone())
                                } else {
                                    let q = mach.quote(bump, &arm.cxt, arm.cxt.lvl, *typ);
                                    (
                                        mach.bind_name(bump, &arm.cxt, &cname, q, *typ),
                                        arm.patcon
                                            .clone()
                                            .clean()
                                            .push(PatternDetail::Any(x.to_span())),
                                    )
                                };
                                Some(Arm {
                                    arm: MatchArm {
                                        pats: [
                                            new_heads
                                                .iter()
                                                .map(|n| {
                                                    Pattern::Any(
                                                        x.to_span().map(|_| false),
                                                        n.3,
                                                    )
                                                })
                                                .collect::<Vec<_>>(),
                                            arm.arm.pats[1..].to_vec(),
                                        ]
                                        .concat(),
                                        body: arm.arm.body.clone(),
                                    },
                                    idx: arm.idx,
                                    cxt: cxt2,
                                    heads: new_heads.clone(),
                                    raw: arm.raw.clone(),
                                    target_typ: arm.target_typ,
                                    ori: arm.ori,
                                    patcon: patcon2,
                                    is_impl: false,
                                })
                            }
                            [Pattern::Con(constr_, _item_pats, i), ..]
                                if i == icit
                                    && (constr.data == "$any$"
                                        || !constrs_name.contains(&constr_.data)) =>
                            {
                                let q = mach.quote(bump, &arm.cxt, arm.cxt.lvl, *typ);
                                Some(Arm {
                                    arm: MatchArm {
                                        pats: [
                                            new_heads
                                                .iter()
                                                .map(|n| {
                                                    Pattern::Any(
                                                        constr_.to_span().map(|_| false),
                                                        n.3,
                                                    )
                                                })
                                                .collect::<Vec<_>>(),
                                            arm.arm.pats[1..].to_vec(),
                                        ]
                                        .concat(),
                                        body: arm.arm.body.clone(),
                                    },
                                    idx: arm.idx,
                                    cxt: mach.bind_name(bump, &arm.cxt, &constr_.data, q, *typ),
                                    heads: new_heads.clone(),
                                    raw: arm.raw.clone(),
                                    target_typ: arm.target_typ,
                                    ori: arm.ori,
                                    patcon: arm
                                        .patcon
                                        .clone()
                                        .clean()
                                        .push(PatternDetail::Bind(constr_.clone())),
                                    is_impl: false,
                                })
                            }
                            [Pattern::Con(constr_, item_pats, i), ..]
                                if i == icit && constr_ == constr =>
                            {
                                let mut pats = item_pats.iter().cloned().collect::<Vec<_>>();
                                pats.extend(arm.arm.pats[1..].iter().cloned());
                                Some(Arm {
                                    arm: MatchArm {
                                        pats,
                                        body: arm.arm.body.clone(),
                                    },
                                    idx: arm.idx,
                                    cxt: clone_cxt(&arm.cxt),
                                    heads: new_heads.clone(),
                                    raw: arm.raw.clone(),
                                    target_typ: arm.target_typ,
                                    ori: arm.ori,
                                    patcon: arm
                                        .patcon
                                        .clone()
                                        .clean()
                                        .push(PatternDetail::Con(constr_.clone(), vec![]))
                                        .new_level(new_heads_len),
                                    is_impl: false,
                                })
                            }
                            _ => {
                                if *icit == Icit::Impl {
                                    let q = mach.quote(bump, &arm.cxt, arm.cxt.lvl, *typ);
                                    let name = head_name.clone().map(|x| format!("_{}", x));
                                    let cname = name.data.clone();
                                    Some(Arm {
                                        arm: MatchArm {
                                            pats: arm.arm.pats.clone(),
                                            body: arm.arm.body.clone(),
                                        },
                                        idx: arm.idx,
                                        cxt: mach.bind_name(bump, &arm.cxt, &cname, q, *typ),
                                        heads: vec![],
                                        raw: arm.raw.clone(),
                                        target_typ: arm.target_typ,
                                        ori: arm.ori,
                                        patcon: arm
                                            .patcon
                                            .clone()
                                            .clean()
                                            .push(PatternDetail::Any(empty_span(()))),
                                        is_impl: true,
                                    })
                                } else {
                                    None
                                }
                            }
                        };
                        // 模式失配（None）→ 本臂从 vec 移除（不 push）；
                        // 匹配 → Some(臂) 保留
                        if let Some(a) = matched {
                            remaining.push(Some(a));
                        }
                    }

                    // vec 为空 → Unmatched 警告；否则递归本构造子分支（含
                    // 全 None 的退化分支——零臂递归天然 Ok(false)，参考版
                    // `.any()` 聚合语义：一臂成功即整体成功，不因空分支中止）
                    if !remaining.is_empty() {
                        let heads_of_first = remaining
                            .first()
                            .and_then(|x| x.as_ref())
                            .map(|x| x.heads.clone())
                            .unwrap_or(vec![]);
                        let is_impl = remaining
                                .first()
                                .and_then(|x| x.as_ref())
                                .map(|x| x.is_impl)
                                .unwrap_or(false);
                        let context_ = if heads_of_first.is_empty() {
                            if heads_rest.is_empty() || is_impl {
                                context.clone()
                            } else {
                                Self::next_hole(
                                    context,
                                    &Pattern::Con(constr.clone(), vec![], *icit),
                                )
                            }
                        } else {
                            MatchContext::InCons {
                                parent: Rc::new(context.clone()),
                                constr: constr.clone(),
                                icit: *icit,
                                before: vec![],
                                after: vec![
                                    Pattern::Any(empty_span(true), *icit);
                                    heads_of_first.len() - 1
                                ],
                            }
                        };
                        let valid = self.compile_aux(
                            mach,
                            bump,
                            &heads_of_first
                                .iter()
                                .chain(heads_rest.iter())
                                .cloned()
                                .collect::<Vec<_>>(),
                            &remaining_flatten(&mut remaining),
                            &context_,
                        )?;
                        if valid {
                            any_valid = true;
                        }
                    } else {
                        let unmatched = Self::fill_context(
                            context,
                            &Pattern::Con(constr.clone(), vec![], *icit),
                        );
                        self.warnings.push(Warning::Unmatched(unmatched));
                    }
                }
                let _ = var; // 决策树不进项层（pats 才是产物）
                Ok(any_valid)
            }
        }
    }
}

// Debug 复刻（错误消息里内嵌的 `{:?}` 输出；名字 Span 全零——套件比对
// 前按 start_offset/end_offset/path_id 归一化）
// --------------------------------------------------------------------------------

fn dbg_span_str(s: &str) -> String {
    format!("{:?} @ {},{}", s, 0, 0)
}

fn dbg_span_unit() -> String {
    "() @ 0,0".to_string()
}

/// `{:?}` 的字符串字面量转义（Debug 的 escape_debug 语义：引号与控制
/// 字符转义，其余原样）。
fn strconv_quote(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c.is_control() => out.push_str(&format!("\\u{{{:x}}}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// 参考 `Val` 的 Debug 形态（递归；闭包体走 Tm Debug）。
fn debug_val(spine: &Spine, defs: &[V], v: V) -> String {
    let mut out = String::new();
    debug_val_go(spine, defs, v, &mut out);
    out
}

fn debug_spine(spine: &Spine, defs: &[V], h: usize, out: &mut String) {
    let mut args: Vec<(V, Icit)> = Vec::new();
    spine.collect_args(h, &mut args);
    // collect_args 产出 = 逆应用序（内层在前）；参考 Spine = List（头 =
    // 最后应用 = 内层）——Debug 序一致
    out.push('[');
    for (k, (a, i)) in args.iter().enumerate() {
        if k > 0 {
            out.push_str(", ");
        }
        out.push('(');
        debug_val_go(spine, defs, *a, out);
        out.push_str(", ");
        out.push_str(debug_icit(*i));
        out.push(')');
    }
    out.push(']');
}

fn debug_val_go(spine: &Spine, defs: &[V], v: V, out: &mut String) {
    match v_tag(v) {
        0 => {
            out.push_str(&format!("Rigid(Lvl({}), ", v_lvl_of(v)));
            out.push_str("[])");
        }
        1 => {
            let c = v_clo_of(v);
            out.push_str(&format!(
                "Lam({}, {}, Closure(.., ",
                dbg_span_str(c.name),
                debug_icit(c.icit)
            ));
            debug_tm_go(c.body, out);
            out.push_str("))");
        }
        2 => {
            let h = v_spine_of(v);
            let hd = spine.spine_head(h);
            match v_tag(hd) {
                0 => {
                    out.push_str(&format!("Rigid(Lvl({}), ", v_lvl_of(hd)));
                    debug_spine(spine, defs, h, out);
                    out.push(')');
                }
                5 => {
                    out.push_str(&format!("Flex(MetaVar({}), ", v_meta_of(hd)));
                    debug_spine(spine, defs, h, out);
                    out.push(')');
                }
                7 => match v_xcell_of(hd) {
                    XCell::Obj { val, name } => {
                        out.push_str("Obj(");
                        debug_val_go(spine, defs, *val, out);
                        out.push_str(&format!(", {}, ", dbg_span_str(name)));
                        debug_spine(spine, defs, h, out);
                        out.push(')');
                    }
                    _ => {
                        // 其余头不可达（v_app panic，进不了链）；防御输出
                        out.push_str("Neutral(...)");
                    }
                },
                _ => out.push_str("Neutral(...)"),
            }
        }
        3 => {
            out.push_str(&format!("U({})", v_u_of(v)));
        }
        4 => {
            let p = v_pi_of(v);
            out.push_str(&format!(
                "Pi({}, {}, {}, Closure(.., ",
                dbg_span_str(p.name),
                debug_icit(p.icit),
                debug_val(spine, defs, p.dom)
            ));
            debug_tm_go(p.body, out);
            out.push_str("))");
        }
        5 => {
            out.push_str(&format!("Flex(MetaVar({}), [])", v_meta_of(v)));
        }
        6 => out.push_str("LiteralType"),
        7 => match v_xcell_of(v) {
            XCell::Lit(s) => {
                out.push_str(&format!("LiteralIntro({})", dbg_span_str(s)));
            }
            XCell::Decl { name } => {
                out.push_str(&format!("Decl({})", dbg_span_str(name)));
            }
            XCell::Prim { .. } => out.push_str("Prim"),
            XCell::Obj { val, name } => {
                out.push_str(&format!(
                    "Obj({}, {}, [])",
                    debug_val(spine, defs, *val),
                    dbg_span_str(name)
                ));
            }
            XCell::Sum { name, params, cases, is_trait } => {
                out.push_str(&format!("Sum({}, [", dbg_span_str(name)));
                for (k, p) in params.iter().enumerate() {
                    if k > 0 {
                        out.push_str(", ");
                    }
                    out.push_str(&format!(
                        "({}, {}, {}, {})",
                        dbg_span_str(p.name),
                        debug_val(spine, defs, p.val),
                        debug_val(spine, defs, p.ty),
                        debug_icit(p.icit)
                    ));
                }
                out.push_str("], [");
                for (k, c) in cases.iter().enumerate() {
                    if k > 0 {
                        out.push_str(", ");
                    }
                    out.push_str(&dbg_span_str(c));
                }
                out.push_str(&format!("], {})", is_trait));
            }
            XCell::SumCase { is_trait, typ, case_name, datas } => {
                out.push_str(&format!(
                    "SumCase {{ is_trait: {}, typ: {}, case_name: {}, datas: [",
                    is_trait,
                    debug_val(spine, defs, *typ),
                    dbg_span_str(case_name)
                ));
                for (k, d) in datas.iter().enumerate() {
                    if k > 0 {
                        out.push_str(", ");
                    }
                    out.push_str(&format!(
                        "({}, {}, {})",
                        dbg_span_str(d.name),
                        debug_val(spine, defs, d.val),
                        debug_icit(d.icit)
                    ));
                }
                out.push_str("]) }");
            }
            XCell::Match { scrutinee, env, cases } => {
                out.push_str(&format!(
                    "Match({}, ",
                    debug_val(spine, defs, *scrutinee)
                ));
                // 捕获 env（List<Val> 的 debug_list）
                out.push('[');
                let n = env_len(*env);
                for i in 0..n {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    let sv = env_nth(defs, *env, i);
                    let mut tmp = String::new();
                    debug_val_go(spine, defs, sv, &mut tmp);
                    out.push_str(&tmp);
                }
                out.push_str("], [");
                for (k, (p, b)) in cases.iter().enumerate() {
                    if k > 0 {
                        out.push_str(", ");
                    }
                    out.push('(');
                    debug_pat_go(p, out);
                    out.push_str(", ");
                    debug_tm_go(b, out);
                    out.push(')');
                }
                out.push_str("])");
            }
        },
        _ => out.push_str("Val(...)"),
    }
}

fn debug_icit(i: Icit) -> &'static str {
    match i {
        Icit::Impl => "Impl",
        Icit::Expl => "Expl",
    }
}

fn debug_pat_go(p: &PatternDetail, out: &mut String) {
    match p {
        PatternDetail::Any(_) => {
            out.push_str(&format!("Any({})", dbg_span_unit()));
        }
        PatternDetail::Bind(name) => {
            out.push_str(&format!("Bind({})", dbg_span_str(&name.data)));
        }
        PatternDetail::Con(name, subs) => {
            out.push_str(&format!("Con({}, [", dbg_span_str(&name.data)));
            for (k, s) in subs.iter().enumerate() {
                if k > 0 {
                    out.push_str(", ");
                }
                debug_pat_go(s, out);
            }
            out.push_str("])");
        }
    }
}

/// 参考 `Tm` 的 Debug 形态（快版 bump 项 → 参考格式；`Var` 印成 `Ix`）。
fn debug_tm(t: &Tm<'_>) -> String {
    let mut out = String::new();
    debug_tm_go(t, &mut out);
    out
}

fn debug_tm_go(t: &Tm<'_>, out: &mut String) {
    match t {
        Tm::Var(i) => out.push_str(&format!("Var(Ix({}))", i)),
        Tm::Decl(x) => out.push_str(&format!("Decl({})", dbg_span_str(x))),
        Tm::Lam(x, i, b) => {
            out.push_str(&format!(
                "Lam({}, {}, ",
                dbg_span_str(x),
                debug_icit(*i)
            ));
            debug_tm_go(b, out);
            out.push(')');
        }
        Tm::App(f, a, i) => {
            out.push_str("App(");
            debug_tm_go(f, out);
            out.push_str(", ");
            debug_tm_go(a, out);
            out.push_str(&format!(", {})", debug_icit(*i)));
        }
        Tm::AppPruning(h, pr) => {
            out.push_str("AppPruning(");
            debug_tm_go(h, out);
            out.push_str(", ");
            // Pruning = List<Option<Icit>>（头 = 最内层）
            out.push('[');
            let mut slots: Vec<Option<Icit>> = Vec::new();
            let mut cur = *pr;
            while let Some(b) = cur {
                slots.push(b.slot);
                cur = b.next;
            }
            for (k, s) in slots.iter().enumerate() {
                if k > 0 {
                    out.push_str(", ");
                }
                match s {
                    Some(i) => out.push_str(&format!("Some({})", debug_icit(*i))),
                    None => out.push_str("None"),
                }
            }
            out.push_str("])");
        }
        Tm::U(l) => out.push_str(&format!("U({})", l)),
        Tm::Pi(x, i, a, b) => {
            out.push_str(&format!(
                "Pi({}, {}, ",
                dbg_span_str(x),
                debug_icit(*i)
            ));
            debug_tm_go(a, out);
            out.push_str(", ");
            debug_tm_go(b, out);
            out.push(')');
        }
        Tm::Let(x, a, t, u) => {
            out.push_str(&format!("Let({}, ", dbg_span_str(x)));
            debug_tm_go(a, out);
            out.push_str(", ");
            debug_tm_go(t, out);
            out.push_str(", ");
            debug_tm_go(u, out);
            out.push(')');
        }
        Tm::Meta(m) => out.push_str(&format!("Meta(MetaVar({}))", m)),
        Tm::LiteralType => out.push_str("LiteralType"),
        Tm::LiteralIntro(s) => out.push_str(&format!("LiteralIntro({})", dbg_span_str(s))),
        Tm::Prim(_, _) => out.push_str("Prim"),
        Tm::Obj(h, name) => {
            out.push_str("Obj(");
            debug_tm_go(h, out);
            out.push_str(&format!(", {})", dbg_span_str(name)));
        }
        Tm::Sum(name, params, cases, ..) => {
            out.push_str(&format!("Sum({}, [", dbg_span_str(name)));
            for (k, p) in params.iter().enumerate() {
                if k > 0 {
                    out.push_str(", ");
                }
                out.push_str(&format!(
                    "({}, ",
                    dbg_span_str(p.name)
                ));
                debug_tm_go(p.val, out);
                out.push_str(", ");
                debug_tm_go(p.ty, out);
                out.push_str(&format!(", {})", debug_icit(p.icit)));
            }
            out.push_str("], [");
            for (k, c) in cases.iter().enumerate() {
                if k > 0 {
                    out.push_str(", ");
                }
                out.push_str(&dbg_span_str(c));
            }
            out.push_str("])");
        }
        Tm::SumCase { typ, case_name, datas, .. } => {
            out.push_str(&format!(
                "SumCase {{ typ: {}, case_name: {}, datas: [",
                {
                    let mut tmp = String::new();
                    debug_tm_go(typ, &mut tmp);
                    tmp
                },
                dbg_span_str(case_name)
            ));
            for (k, d) in datas.iter().enumerate() {
                if k > 0 {
                    out.push_str(", ");
                }
                out.push_str(&format!("({}, ", dbg_span_str(d.name)));
                debug_tm_go(d.val, out);
                out.push_str(&format!(", {})", debug_icit(d.icit)));
            }
            out.push_str("]) }");
        }
        Tm::Match(s, cases) => {
            out.push_str("Match(");
            debug_tm_go(s, out);
            out.push_str(", [");
            for (k, (p, b)) in cases.iter().enumerate() {
                if k > 0 {
                    out.push_str(", ");
                }
                out.push('(');
                debug_pat_go(p, out);
                out.push_str(", ");
                debug_tm_go(b, out);
                out.push(')');
            }
            out.push_str("])");
        }
    }
}

// export 与对外入口
// --------------------------------------------------------------------------------

/// 把 bump 结果项转回参考版的 `Box` 树（迭代任务栈；icit/掩码随任务
/// 携带），复用参考版的 pretty。
fn export(t: &Tm<'_>) -> CTm {
    use std::sync::Arc as CRc;
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
            is_trait: bool,
        },
        SumCase2 {
            case_name: &'a str,
            datas: &'a [SumDataT<'a>],
            is_trait: bool,
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
            J::Do(Tm::U(l)) => done.push(CTm::U(*l)),
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
            J::Do(Tm::Decl(x)) => done.push(CTm::Decl(name(x))),
            J::Do(Tm::Prim(_, _)) => done.push(CTm::Prim(
                CRc::new(super::Val::LiteralType),
                super::PrimFunc(CRc::new(|_, _, _, _| super::Val::U(0).into())),
            )),
            J::Do(Tm::Obj(h, n)) => {
                tasks.push(J::Obj2(n));
                tasks.push(J::Do(h));
            }
            J::Do(Tm::Sum(nm, params, cases, is_trait)) => {
                let is_trait = *is_trait;
                tasks.push(J::Sum2 {
                    name: nm,
                    params,
                    cases,
                    is_trait,
                });
                for p in params.iter().rev() {
                    tasks.push(J::Do(p.ty));
                    tasks.push(J::Do(p.val));
                }
            }
            J::Do(Tm::SumCase {
                typ,
                case_name,
                datas,
                is_trait,
            }) => {
                let is_trait = *is_trait;
                tasks.push(J::SumCase2 {
                    case_name,
                    datas,
                    is_trait,
                });
                for d in datas.iter().rev() {
                    tasks.push(J::Do(d.val));
                }
                tasks.push(J::Do(typ));
            }
            J::Do(Tm::Match(s, cases)) => {
                // 分支体逐个内联导出（递归深度 = match 嵌套深度）；模式直接
                // 克隆（PatternDetail 是参考版类型，两版共用）
                let s2 = export(s);
                let mut cs: Vec<(PatternDetail, CRc<CTm>)> = Vec::with_capacity(cases.len());
                for (p, b) in cases.iter() {
                    cs.push((p.clone(), CRc::new(export(b))));
                }
                done.push(CTm::Match(CRc::new(s2), cs));
            }
            J::Lam2(x, i) => {
                let b = done.pop().expect("export 栈：Lam 缺体");
                done.push(CTm::Lam(name(x), i, CRc::new(b)));
            }
            J::Pi2(x, i) => {
                let cod = done.pop().expect("export 栈：Pi 缺余定义域");
                let dom = done.pop().expect("export 栈：Pi 缺定义域");
                done.push(CTm::Pi(name(x), i, CRc::new(dom), CRc::new(cod)));
            }
            J::Let2(x) => {
                let u = done.pop().expect("export 栈：Let 缺体");
                let t = done.pop().expect("export 栈：Let 缺值");
                let a = done.pop().expect("export 栈：Let 缺类型");
                done.push(CTm::Let(name(x), CRc::new(a), CRc::new(t), CRc::new(u)));
            }
            J::App2(i) => {
                let a = done.pop().expect("export 栈：App 缺实参");
                let f = done.pop().expect("export 栈：App 缺函数");
                done.push(CTm::App(CRc::new(f), CRc::new(a), i));
            }
            J::AppPrun2(pr) => {
                let h = done.pop().expect("export 栈：AppPruning 缺头");
                done.push(CTm::AppPruning(CRc::new(h), pr));
            }
            J::Obj2(n) => {
                let h = done.pop().expect("export 栈：Obj 缺接收者");
                done.push(CTm::Obj(CRc::new(h), name(n)));
            }
            J::Sum2 {
                name: nm,
                params,
                cases,
                is_trait,
            } => {
                let mut ps: Vec<(crate::parser_lib::Span<String>, CRc<CTm>, CRc<CTm>, Icit)> =
                    Vec::with_capacity(params.len());
                for p in params.iter().rev() {
                    let ty = CRc::new(done.pop().expect("export 栈：Sum 缺参数类型"));
                    let val = CRc::new(done.pop().expect("export 栈：Sum 缺参数值"));
                    ps.push((name(p.name), val, ty, p.icit));
                }
                ps.reverse();
                let cs: Vec<crate::parser_lib::Span<String>> =
                    cases.iter().map(|c| name(c)).collect();
                done.push(CTm::Sum(name(nm), ps, cs, is_trait));
            }
            J::SumCase2 {
                case_name,
                datas,
                is_trait,
            } => {
                let mut ds: Vec<(crate::parser_lib::Span<String>, CRc<CTm>, Icit)> =
                    Vec::with_capacity(datas.len());
                for d in datas.iter().rev() {
                    let val = CRc::new(done.pop().expect("export 栈：SumCase 缺字段"));
                    ds.push((name(d.name), val, d.icit));
                }
                ds.reverse();
                let typ = done.pop().expect("export 栈：SumCase 缺 typ");
                done.push(CTm::SumCase {
                    typ: CRc::new(typ),
                    case_name: name(case_name),
                    datas: ds,
                    is_trait,
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
            Tm::Var(_) | Tm::Decl(_) | Tm::U(_) | Tm::Meta(_) | Tm::LiteralType
            | Tm::LiteralIntro(_) | Tm::Prim(_, _) => {}
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
            Tm::Sum(_, params, ..) => {
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

// builtin 注册（每轮 prime；参考版 `Cxt::new` 逐条对应）
// --------------------------------------------------------------------------------

impl Machine {
    /// 每轮注册（参考版 `Cxt::new` 逐条对应）：String 类型 + 5 个内建
    /// （string_concat / string_to_global_type / create_global /
    /// change_mutable / get_global）。值/类型形态按参考版手工构造——
    /// string_concat 的 λ 闭包 env 里钉着 `LiteralType` 填充槽（使
    /// `Tm::Prim` 读 env 前两槽），类型闭包 env 与参考版逐槽一致；其余
    /// 内建的 λ 链闭包 env 为空（参考版 Closure(List::new(), ...) 同款）。
    fn prime_round<'a>(&mut self, bump: &'a Bump) -> Cxt<'a> {
        let empty = Cxt::empty();
        // String : U(0)，值 = LiteralType
        let cxt = self.decl_reg(
            bump, &empty, "String",
            bump.alloc(Tm::LiteralType),
            v_lit_ty(),
            bump.alloc(Tm::U(0)),
            v_u(0),
        );
        // string_concat：λ x y → Prim(LiteralType)；值 = Lam x (Closure
        // [LitType] (Lam y Prim))；类型 Π x:String. Π y:String. String
        //（参考版 cxt.rs 逐字——返回型是 Tm::Decl("String")）
        let st: &'a str = bump.alloc_str("String");
        let stgt_name: &'a str = bump.alloc_str("string_to_global_type");
        let (sc, stgt, cg, cm, gg) = (
            PrimId::StringConcat,
            PrimId::StringToGlobalType,
            PrimId::CreateGlobal,
            PrimId::ChangeMutable,
            PrimId::GetGlobal,
        );
        let filled = env_ext(bump, EMPTY_ENV, v_lit_ty());
        let sc_lam_tm: &'a Tm<'a> = bump.alloc(Tm::Lam(
            "x",
            Icit::Expl,
            bump.alloc(Tm::Lam("y", Icit::Expl, bump.alloc(Tm::Prim(v_lit_ty(), sc)))),
        ));
        let sc_val = v_clo(bump.alloc(CloCell {
            name: "x",
            icit: Icit::Expl,
            env: filled,
            body: bump.alloc(Tm::Lam("y", Icit::Expl, bump.alloc(Tm::Prim(v_lit_ty(), sc)))),
        }));
        let sc_pi_tm: &'a Tm<'a> = bump.alloc(Tm::Pi(
            "x",
            Icit::Expl,
            bump.alloc(Tm::Decl(st)),
            bump.alloc(Tm::Pi(
                "y",
                Icit::Expl,
                bump.alloc(Tm::Decl(st)),
                bump.alloc(Tm::Decl(st)),
            )),
        ));
        let sc_ty = v_pi(bump.alloc(PiCell {
            name: "x",
            icit: Icit::Expl,
            dom: v_lit_ty(),
            env: filled,
            body: bump.alloc(Tm::Pi(
                "y",
                Icit::Expl,
                bump.alloc(Tm::Decl(st)),
                bump.alloc(Tm::Decl(st)),
            )),
        }));
        let cxt = self.decl_reg(bump, &cxt, "string_concat", sc_lam_tm, sc_val, sc_pi_tm, sc_ty);
        // string_to_global_type：λ x → Prim(LiteralType)；值 = Lam x
        // (Closure [] Prim)；类型 Π x:String. U(0)
        let stgt_val = v_clo(bump.alloc(CloCell {
            name: "x",
            icit: Icit::Expl,
            env: EMPTY_ENV,
            body: bump.alloc(Tm::Prim(v_lit_ty(), stgt)),
        }));
        let cxt = self.decl_reg(
            bump, &cxt, "string_to_global_type",
            bump.alloc(Tm::Lam("x", Icit::Expl, bump.alloc(Tm::Prim(v_lit_ty(), stgt)))),
            stgt_val,
            bump.alloc(Tm::Pi("x", Icit::Expl, bump.alloc(Tm::Decl(st)), bump.alloc(Tm::U(0)))),
            v_pi(bump.alloc(PiCell {
                name: "x",
                icit: Icit::Expl,
                dom: v_lit_ty(),
                env: EMPTY_ENV,
                body: bump.alloc(Tm::U(0)),
            })),
        );
        // create_global：λ x y → Prim(U(0))；类型
        // Π x:String. Π y: string_to_global_type x. U(0)
        let cg_val = v_clo(bump.alloc(CloCell {
            name: "x",
            icit: Icit::Expl,
            env: EMPTY_ENV,
            body: bump.alloc(Tm::Lam(
                "y",
                Icit::Expl,
                bump.alloc(Tm::Prim(v_u(0), cg)),
            )),
        }));
        let cg_pi_tm: &'a Tm<'a> = bump.alloc(Tm::Pi(
            "x",
            Icit::Expl,
            bump.alloc(Tm::Decl(st)),
            bump.alloc(Tm::Pi(
                "y",
                Icit::Expl,
                bump.alloc(Tm::App(
                    bump.alloc(Tm::Decl(stgt_name)),
                    bump.alloc(Tm::Var(0)),
                    Icit::Expl,
                )),
                bump.alloc(Tm::U(0)),
            )),
        ));
        let cxt = self.decl_reg(
            bump, &cxt, "create_global",
            bump.alloc(Tm::Lam(
                "x",
                Icit::Expl,
                bump.alloc(Tm::Lam("y", Icit::Expl, bump.alloc(Tm::Prim(v_u(0), cg)))),
            )),
            cg_val,
            cg_pi_tm,
            v_pi(bump.alloc(PiCell {
                name: "x",
                icit: Icit::Expl,
                dom: v_lit_ty(),
                env: EMPTY_ENV,
                body: bump.alloc(Tm::Pi(
                    "y",
                    Icit::Expl,
                    bump.alloc(Tm::App(
                        bump.alloc(Tm::Decl(stgt_name)),
                        bump.alloc(Tm::Var(0)),
                        Icit::Expl,
                    )),
                    bump.alloc(Tm::U(0)),
                )),
            })),
        );
        // change_mutable：λ x f → Prim(U(0))；类型
        // Π x:String. Π f: Π _: stgt x. stgt (f x). U(0)（参考版逐字，
        // 含其变量索引怪癖）
        let cm_val = v_clo(bump.alloc(CloCell {
            name: "x",
            icit: Icit::Expl,
            env: EMPTY_ENV,
            body: bump.alloc(Tm::Lam(
                "f",
                Icit::Expl,
                bump.alloc(Tm::Prim(v_u(0), cm)),
            )),
        }));
        let cm_pi_tm: &'a Tm<'a> = bump.alloc(Tm::Pi(
            "x",
            Icit::Expl,
            bump.alloc(Tm::Decl(st)),
            bump.alloc(Tm::Pi(
                "f",
                Icit::Expl,
                bump.alloc(Tm::Pi(
                    "_",
                    Icit::Expl,
                    bump.alloc(Tm::App(
                        bump.alloc(Tm::Decl(stgt_name)),
                        bump.alloc(Tm::Var(0)),
                        Icit::Expl,
                    )),
                    bump.alloc(Tm::App(
                        bump.alloc(Tm::Decl(stgt_name)),
                        bump.alloc(Tm::Var(1)),
                        Icit::Expl,
                    )),
                )),
                bump.alloc(Tm::U(0)),
            )),
        ));
        let cm_cod: &'a Tm<'a> = bump.alloc(Tm::Pi(
            "f",
            Icit::Expl,
            bump.alloc(Tm::Pi(
                "_",
                Icit::Expl,
                bump.alloc(Tm::App(
                    bump.alloc(Tm::Decl(stgt_name)),
                    bump.alloc(Tm::Var(0)),
                    Icit::Expl,
                )),
                bump.alloc(Tm::App(
                    bump.alloc(Tm::Decl(stgt_name)),
                    bump.alloc(Tm::Var(1)),
                    Icit::Expl,
                )),
            )),
            bump.alloc(Tm::U(0)),
        ));
        let cxt = self.decl_reg(
            bump, &cxt, "change_mutable",
            bump.alloc(Tm::Lam(
                "x",
                Icit::Expl,
                bump.alloc(Tm::Lam("f", Icit::Expl, bump.alloc(Tm::Prim(v_u(0), cm)))),
            )),
            cm_val,
            cm_pi_tm,
            v_pi(bump.alloc(PiCell {
                name: "x",
                icit: Icit::Expl,
                dom: v_lit_ty(),
                env: EMPTY_ENV,
                body: cm_cod,
            })),
        );
        // get_global：λ x → Prim(U(0))；类型 Π x:String. stgt x
        let gg_val = v_clo(bump.alloc(CloCell {
            name: "x",
            icit: Icit::Expl,
            env: EMPTY_ENV,
            body: bump.alloc(Tm::Prim(v_u(0), gg)),
        }));
        let gg_pi_tm: &'a Tm<'a> = bump.alloc(Tm::Pi(
            "x",
            Icit::Expl,
            bump.alloc(Tm::Decl(st)),
            bump.alloc(Tm::App(
                bump.alloc(Tm::Decl(stgt_name)),
                bump.alloc(Tm::Var(0)),
                Icit::Expl,
            )),
        ));
        self.decl_reg(
            bump, &cxt, "get_global",
            bump.alloc(Tm::Lam("x", Icit::Expl, bump.alloc(Tm::Prim(v_u(0), gg)))),
            gg_val,
            gg_pi_tm,
            v_pi(bump.alloc(PiCell {
                name: "x",
                icit: Icit::Expl,
                dom: v_lit_ty(),
                env: EMPTY_ENV,
                body: bump.alloc(Tm::App(
                    bump.alloc(Tm::Decl(stgt_name)),
                    bump.alloc(Tm::Var(0)),
                    Icit::Expl,
                )),
            })),
        )
    }

    /// 参考版 `bench_check` 的主循环（无输出变体）：返回 (是否通过，最终
    /// 上下文，最后一个 def 的登记值)。L11 的顶层 def 不进 env——按名字
    /// 回 decl 表取登记值。
    fn elab_all<'a>(
        &mut self,
        bump: &'a Bump,
        ast: &[Decl],
    ) -> (Result<(), Error>, Cxt<'a>, Option<V>) {
        let mut cxt = self.prime_round(bump);
        let mut last = None;
        for d in ast {
            match self.infer_decl(bump, &cxt, d) {
                Ok((out, nc)) => {
                    cxt = nc;
                    if let DeclOut::Def { name } = out {
                        last = cxt.decls.get(name).map(|e| e.val);
                    }
                }
                Err(e) => return (Err(e), cxt, last),
            }
        }
        (Ok(()), cxt, last)
    }
}

/// 参考版 `Tm::no_metas`（L11）：项里第一个**未解** meta 的类型（已解
/// 视为无——参考版 Solved 臂同款不深入解）。未解 meta 的类型是闭类型
/// （`AppPruning` 掩码已剥）。
fn no_metas<'a>(
    bump: &'a Bump,
    m: &Machine,
    cxt: &Cxt<'a>,
    t: &'a Tm<'a>,
) -> Option<V> {
    let _ = bump;
    let _ = cxt;
    let mut stack: Vec<&Tm<'a>> = vec![t];
    while let Some(x) = stack.pop() {
        match x {
            Tm::Meta(mm) => match &m.metas[*mm as usize] {
                MetaEntry::Unsolved(ty) => return Some(*ty),
                MetaEntry::Solved(..) => {}
            },
            Tm::Var(_) | Tm::Decl(_) | Tm::U(_) | Tm::LiteralType | Tm::LiteralIntro(_)
            | Tm::Prim(_, _) => {}
            Tm::Lam(_, _, b) => stack.push(b),
            Tm::App(f, a, _) => {
                stack.push(f);
                stack.push(a);
            }
            Tm::AppPruning(h, _) => stack.push(h),
            Tm::Pi(_, _, a, b) => {
                stack.push(a);
                stack.push(b);
            }
            Tm::Let(_, a, t, u) => {
                stack.push(a);
                stack.push(t);
                stack.push(u);
            }
            Tm::Obj(h, _) => stack.push(h),
            Tm::Sum(_, params, ..) => {
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
                for (_, b) in cases.iter() {
                    stack.push(b);
                }
            }
        }
    }
    None
}

/// 参考版 Def 臂的未解 meta 报错（elaboration.rs 逐字——类型类是 trait
/// Sum 时给类型类消息，否则 `find unsolved meta with type ...`）。
fn err_unsolved_meta<'a>(
    bump: &'a Bump,
    m: &mut Machine,
    cxt: &Cxt<'a>,
    _t_tm: &'a Tm<'a>,
    meta_ty: V,
) -> Error {
    let is_trait_sum = v_tag(meta_ty) == 7
        && match v_xcell_of(meta_ty) {
            XCell::Sum { is_trait, .. } => *is_trait,
            _ => false,
        };
    if is_trait_sum {
        let (name, params) = match v_xcell_of(meta_ty) {
            XCell::Sum { name, params, .. } => (*name, *params),
            _ => unreachable!(),
        };
        let has_flex = {
            let Machine { spine, defs, metas, mutable, .. } = m;
            params.iter().any(|p| {
                matches!(
                    force(bump, spine, defs, metas, &*cxt.decls, mutable, p.val),
                    x if v_tag(x) == 5
                )
            })
        };
        // 实例名预拷出（tstate 的借用不能在 quote 闭包期间存活）
        let instances: Option<Vec<String>> = m
            .tstate
            .solver
            .class_instances
            .get(name)
            .map(|i| i.iter().map(|x| x.lvl.data.clone()).collect());
        let err_msg = if has_flex {
            format!("cannot infer typeclass `{}`: type parameter is unknown", name)
        } else if params.is_empty() {
            format!("no instance of typeclass `{}`", name)
        } else {
            // 参考版 pretty_val：quote 于 cxt.lvl，names 走 types 表
            let pretty_val = |m: &mut Machine, val: V| {
                let q = m.quote(bump, cxt, cxt.lvl, val);
                pretty_tm(0, types_names_list(cxt.types), &export(q))
            };
            let first = pretty_val(m, params[0].val);
            let rest: Vec<String> = params[1..]
                .iter()
                .map(|p| pretty_val(m, p.val))
                .collect();
            let trait_repr = if rest.is_empty() {
                name.to_string()
            } else {
                format!("{}[{}]", name, rest.join(", "))
            };
            if instances.as_ref().map_or(true, |i| i.is_empty()) {
                format!("no instance of typeclass `{}` for types `{}`", trait_repr, first)
            } else {
                let insts = instances.unwrap();
                format!(
                    "no matching instance of typeclass `{}` for types `{}`\navailable instances: {}",
                    trait_repr,
                    first,
                    insts.join(", "),
                )
            }
        };
        Error(empty_span(err_msg))
    } else {
        let q = m.quote(bump, cxt, cxt.lvl, meta_ty);
        let msg = format!(
            "find unsolved meta with type `{}`",
            pretty_tm(0, types_names_list(cxt.types), &export(q))
        );
        Error(empty_span(msg))
    }
}

/// 稳态类型检查器（同 L03-L08：owns 反复 `reset` 的 `Bump` 与跨调用复用
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
    /// 共用 parser；参考版对 parse 失败 unwrap panic、对 parse 错误只
    /// 打印后继续——快版同口径：None panic、错误静默），本方法做轮重置 +
    /// builtin 重注册 + 逐 decl 推断，println 的 nf 经 pretty 输出（quote
    /// 走记忆化口径——与无记忆化输出逐字节一致，L03-L06 已证）。
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
                // nf：eval + quote（层级 = env 槽数，参考版 `Infer::nf` 同款）
                let v = self.machine.eval(bump, &cxt, cxt.env, t);
                let lvl = env_len(cxt.env);
                let q = self.machine.quote_memo(bump, &cxt, lvl, v);
                let names = types_names_list(cxt.types);
                ret += &pretty_tm(0, names, &export(q));
                ret += "\n";
            }
        }
        Ok(ret)
    }

    /// 参考版 `run` 的全流程等价物（含 preprocess/parse）。
    pub(crate) fn run_input(&mut self, input: &str, path_id: u32) -> Result<String, Error> {
        let (ast, _parse_errs) = match super::parser::parser(&super::preprocess(input), path_id) {
            Some(x) => x,
            // 参考版 run 对 parse 失败 unwrap panic——同款
            None => panic!("parse failed"),
        };
        self.run_decls(&ast)
    }

    /// 基准口径（bench 用）：仅 elaborate。
    pub(crate) fn bench_check(&mut self, ast: &[Decl]) -> bool {
        self.bump.reset();
        self.machine.clear_round();
        let bump = &self.bump;
        self.machine.elab_all(bump, ast).0.is_ok()
    }

    /// 基准口径：check + nf（最后一个 def 的登记值空层级引读，与参考版
    /// `bench_check_nf` 同口径——quote 无记忆化），返回结果树节点数。
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
        let (r, _cxt, last) = self.machine.elab_all(bump, ast);
        if r.is_err() {
            return 0;
        }
        let Some(v) = last else {
            return 0;
        };
        let q = if use_memo {
            self.machine.quote_memo(bump, &_cxt, 0, v)
        } else {
            self.machine.quote(bump, &_cxt, 0, v)
        };
        tm_size(q)
    }
}

/// 一次性口径入口（与参考版 `run` 同签名同 Ok 输出）。
pub(crate) fn run_fast(input: &str, path_id: u32) -> Result<String, Error> {
    let mut tycker = Tycker::new();
    tycker.run_input(input, path_id)
}

/// 测试/基准辅助：共用参考版 parser（fast 是 L09_mltt 的子模块，可见
/// 私有 parser；产出的 `Decl` 同时喂参考版与快版的 bench 口径）。
pub(crate) fn parse(input: &str, path_id: u32) -> Result<Vec<Decl>, String> {
    match super::parser::parser(&super::preprocess(input), path_id) {
        Some((ast, _errs)) => Ok(ast),
        None => Err("parse failed".to_owned()),
    }
}

/// 解析产出的 decl AST 类型别名（测试/基准用；Decl 本身的 use 是私有的）。
pub(crate) type SourceDecl = Decl;

// 基准负载生成器（L09 语法子集：`Type N` 宇宙、string_concat、enum/match、
// 递归 def、struct/new）
// --------------------------------------------------------------------------------

/// church 2^(k+1)：k 次 ×2 翻倍（`add p p`）的 def 链，末位 def 为 `p_k`
/// （nf 节点数与 L06/L08 同为 2n + 4）。
pub(crate) fn church_src(k: u32) -> String {
    let mut s = String::from(
        "def Nat : Type 1 = (N : Type 0) -> (N -> N) -> N -> N\n\
         def add : Nat -> Nat -> Nat = a => b => N => s => z => a N s (b N s z)\n\
         def p0 : Nat = N => s => z => s (s z)\n",
    );
    for i in 1..=k {
        s += &format!("def p{i} : Nat = add p{} p{}\n", i - 1, i - 1);
    }
    s
}

/// 枚举 Nat 加法链 2^(k+1)：`p0 = 2`、`p{i} = add p{i-1} p{i-1}`——递归
/// match + 构造子链的深负载（L11 合法语法：函数注解是完整类型，`Type N`
/// 注解放弃——参考版对"λ 体 + Type 注解"组合判型失败）。
pub(crate) fn natadd_src(k: u32) -> String {
    let mut s = String::from(
        "enum Nat {
    zero
    succ(x: Nat)
}

         def add(x: Nat, y: Nat): Nat =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }

         def p0 : Nat = succ (succ zero)
",
    );
    for i in 1..=k {
        s += &format!("def p{i} : Nat = add p{} p{}
", i - 1, i - 1);
    }
    s
}

/// GADT 负载（test_index 同款：Vec 依赖索引 + head/length 递归）。
pub(crate) fn gadt_src() -> String {
    String::from(
        "enum Nat {
    zero
    succ(x: Nat)
}

         enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

         def two = succ (succ zero)

         def three = succ (succ (succ zero))

         def t = cons (zero, cons(two, cons(three, cons two nil)))

         println t.len

         def head[T, L: Nat](x: Vec[T] (succ L)): T =
    match x {
        case cons(x, _) => x
    }

         println (head (cons zero nil))

         def length[T, l: Nat](x: (Vec[T] l)): Nat =
    match x {
        case nil => zero
        case cons(_, xs) => succ (xs.len)
    }

         println (length t)
",
    )
}

/// strchain 2^(k+1)：每层 `string_concat s_{i-1} "x"`——每层一次 builtin
/// 触发（eval 的 env 双槽字面量拼接），末值是长度 n 的字面量（nf 节点数
/// = 1）。
pub(crate) fn strchain_src(k: u32) -> String {
    let n = 1u64 << (k + 1);
    let mut s = String::from("def s0 : String = \"x\"\n");
    for i in 1..n {
        s += &format!("def s{i} : String = string_concat s{} \"x\"\n", i - 1);
    }
    s
}

/// match 2^(k+1)：每层一个**自递归**的依赖 match def——global 占位/覆盖
/// + check_pm 精化 + 运行时首匹配 + 卡住 match 在 check 期与 quote 期
/// （分支体中性重求值）的协同。
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

/// enum 负载：多 enum + 依赖索引（Vec 风格 GADT）+ 投影 + 索引等式（Eq）
/// + 递归 length——覆盖 Sum/SumCase 值的 unify / quote / rename 全链路。
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

/// struct 负载（L09 语义子集）：两层嵌套 struct（`Line{a, b: P}`）+
/// 规模按 2^(k+1) 的**浅值投影 def 链**（每层一次构造子 β + 类型级投影
/// + 合一）。末值 = `zero`（nf 节点数 = 2：SumCase + typ 的 Sum 两个
/// 节点）。注：L09 参考版的 `.mk` 剥链带 U(0) 占位怪癖，三层嵌套 struct
/// 的构造子应用两版一致地 Err——负载避开该形态（parity 不受影响）。
pub(crate) fn struct_src(k: u32) -> String {
    let n = 1u64 << (k + 1);
    let mut s = String::from(
        "enum Nat {
    zero
    succ(x: Nat)
}

         struct P {
    x: Nat
    y: Nat
}

         struct Line {
    a: P
    b: P
}

         def get_x(p: P): Nat = p.x

         def q0 : Nat = get_x(new P(zero, zero))
",
    );
    for i in 1..n {
        s += &format!("def q{i} : Nat = get_x(new P(q{}, zero))
", i - 1);
    }
    s += &format!("println q{}
", n - 1);
    s
}
