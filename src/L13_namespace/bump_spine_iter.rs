//! L13 核心机（eval / quote / unify / rename / solve / prune / check /
//! infer / check_universe / 模式编译 / trait 求解）的极致性能版：L12
//! 冠军配方（`bump_spine_iter`）向 namespace 层的移植。继承 L05-L12 的
//! 全部机制（见 L06/L08/L10/L12 版模块注释）：bump arena、打包值 [`V`]、
//! 扁平中性 + spine 栈（含链头种类 `Entry.hk` 的 O(1) 头判定）、复合环境、
//! 迭代内核（eval 双栈 / quote 任务栈 / unify 工作表 / rename 任务栈）、
//! quote 记忆化、O(1) 名字解析、`Tycker` 稳态复用。
//!
//! **L13 自己的增量与差异**（参考版 = `super` 的分文件实现，语义以其为
//! 准）——L13 是产品层（LSP / HDL codegen 宿主），核心机相对 L12 的变化：
//!
//! - **原生 Nat**：`Val::Nat(u64)`（快版 = [`XCell::Nat`]，打包字 tag
//!   0-7 已满走 bump 单元）。`build_nat`（数字字面量）直接构造；eval 的
//!   SumCase 装配点折叠（`nat_step_value`：`succ (Nat k)` → `Nat (k+1)`）；
//!   force WHNF 叶；pattern `eval_aux` 的 `succ` 绑定 `Nat(k-1)`；quote
//!   经 `quote_nat` 展开回 SumCase 链（Nat 类型项查 `decl["Nat"]` 登记值，
//!   缺失回退 U(0)），下游（pretty/nf/unify）看到的项形状与一元链时代
//!   逐字节一致。
//! - **SumCase 按构造子 index**：`case_name` → `index: u32`（构造子在
//!   所属 Sum 的 cases 表中的下标），名字反查 `cases[index]`；
//!   `PatternDetail::Con` 首字段同步为 index（共享类型免费）。
//! - **prim 挂 decl 表**（不再有 `Tm::Prim`/`Val::Prim`）：decl 表条目
//!   7 元组（快版 [`DeclEntry`] 加 `prim: Option<PrimId>`），`Cxt::new`
//!   注册 String + 15 个内建。执行点 = force 的 Decl 臂（结果再 force）
//!   + v_app 的 Decl 臂（结果直接返回）；实参逆 spine 序收集后转正序；
//!   `None` = 卡住留 spine 上。nat 算术 prim 与 vconnT 仅 prelude 挂载，
//!   run() 口径不出现。
//! - **Call / OpCall**：Def 臂 `wrap_match_in_call` 把 λ 链体顶端的 Match
//!   包成 `Call(name, Var 链+icit, Match)`；eval 的 Call 帧"体求值结果卡
//!   Match 才包 `Val::Call`"；v_app 对 Call 头 args prepend + 体递归
//!   v_app；force 的 Call 臂做 stale nat-primop 归一 + 体/实参 force；
//!   quote 查 `symbol_table`（impl 算符方法注册）在 args 全 Expl 且 1-2
//!   个时产显示专用 `Tm::OpCall`（quote→eval 往返恒等）。
//! - **def replay**：无参 def 的 body 含全局副作用（REPLAY_GLOBAL_OPS）
//!   时登记值存 `Val::Decl` 占位不求值；eval 的 `Tm::Decl` 臂命中则清空
//!   env 重放 body（`def_needs_replay` 按名 memo + 环敏感扫描）。
//! - **namespace / package / import**：`package a.b` 设 `namespace_prefix`
//!   （后续 def/enum/trait/class 名自动加前缀）并登记可见 namespace 集；
//!   `import` 生成文件局部别名表（含 `X.mk` 点状成员别名）；Var 解析
//!   五级链：局部 → decl 精确键 → import 别名 → `prefix.name` → `.name`
//!   后缀唯一回退（歧义报错并给 import 修复建议）。inherent impl 的方法
//!   注册进 `TypeHead.method`（`x.m` 经 namespace 条目直查分派 + 算符
//!   方法登记 `symbol_table`）。
//! - **class 两阶段**：Phase A 在本机检查字段/语句（未注解字段的 fresh
//!   meta 直解为推断类型，`tm_refs_bn` 判定 bn 引用），产出参考版
//!   `PrecheckedItems`（经 `export`/`v_to_ref_val`）喂共享的
//!   `parser::expand_class_decls`；Phase B 的 `Raw::Tm` 检查臂经**指针
//!   导入表**（export/v_to_ref_val 产出的 Rc 指针 → 本机 Tm/V，见
//!   [`Machine::tm_import`]/[`Machine::val_import`]）复用 Phase A 结果——
//!   eval 副作用重放 + 空 spine Unsolved Flex 直解 / unify 复验，不重复
//!   elaboration。
//! - **unify**：Call/Call 同名 spine 快路径（无 Flex 免快照 / 有 Flex
//!   meta/trait_metas/约束三重快照回滚）、Call 三条退化臂前置、Decl 头
//!   prim 视为不透明叶 + 对侧 Flex 先走求解拦截（不烧燃料）、eta 臂
//!   `is_appliable` 守卫、Match 对 Rigid 的 eta-expansion 检查、SumCase
//!   内层硬编码 fuel 100、燃料语义（Decl 失配重 eval / Match 臂
//!   fuel-1）；solve 的 non-invertible-spine 常数解 fallback（rename 空
//!   表尝试 + `lams(min(spine, Π 链))`）。
//! - **trait**：`trait_metas` 登记表（fresh_meta 对 trait Sum 走此表，
//!   solve_multi_trait 只扫它）、`allow_flex_defaulting`（多个非 out
//!   参数仅 1 个已知时把其余 unify 到它）、head_index 兜 + 桶过滤 +
//!   GENERIC_SELF_HEAD 通配桶、非 out 参数 Flex 推迟、实例命中 SumCase
//!   unify 后重 eval；Synth 求解器与参考版共享（Val 经 `v_to_ref_val`
//!   解码进出，扩展 Nat/Call/index SumCase）。
//! - **BindingName 隐参**：let/字段检查前设 `cxt.binding_name`（bind 清、
//!   define 保留、`with_binding_name` 显式设），insert 遇 `BindingName`
//!   型隐参以 `BindingName.mk` 字面量合成。
//!
//! 与参考版共用 parser / pretty / preprocess / Synth，**Ok 输出逐字节
//! 一致**（互检测试 + `tests/l13_fast_parity.rs`）。不移植（观察面 / LSP
//! 专用）：hover/completion/inlay/retry 闭包、FUNC_PROF、force 记忆化
//! （本机 force 按值重算、无 memo，taint/prim_version 随之不需要）、
//! Tm/Val 迭代 Drop（bump 免疫）、PreludePool/defer_println（run() 口径
//! 为 false）、canonical/iddfs（只在参考版 Err 路径的重试闭包里，不
//! 影响判定与输出）。
//!
//! **已知偏差**：
//! 1. ~~multiline 枚举声明的 match 编译~~ **已修复**（曾报
//!    `STATUS_ACCESS_VIOLATION`）：真凶是原生 Nat 折叠 `nat_step_value`——
//!    `succ(字段)` 装配时对字段值**不查 tag** 就 `v_xcell_of` 解引用，字段为
//!    中性值（Rigid，打包的是层级非指针）即野指针读。现加 `v_tag == 7`
//!    守卫（中性字段保持卡住 SumCase 形状，与参考版一致）；决策树侧的
//!    裸变量 catch-all（`is_var_like`）与叶子 `patcon.to_raw()` 同步照
//!    参考版补齐。另注意：**单行枚举声明**（`enum Nat { zero succ(x: Nat) }`
//!    构造子不换行）本就不在本语言面——共用 parser 恢复性解析会吞掉第二
//!    个及之后的构造子，两版同错同报（parity 仍逐字节一致）。
//! 2. GADT 索引宇宙判定 × trait 求解交互、struct 接收者实例、单臂构造子
//!    匹配、Prim 求值时机差（L12 先例家族）在快版分叉或发散。
//! 3. 仅错误消息内容、不影响判定与 Ok 输出：快版错误里内嵌 Debug-Val/Tm
//!    的名字 Span 全零（参考版携带源码偏移），meta 编号 `?N` 双实现分配
//!    序列不同——套件比对前按 `start_offset/end_offset/path_id` 归一化。
//! 4. 观察面（LSP 接线阶段 1）：全局名使用的 hover 串取**登记处**缓存
//!    （`DeclEntry::typ_pretty`），参考版在**使用处**上下文渲染；类型含
//!    binder 且使用处名字遮蔽时 pretty fresh 后缀（`x` vs `x'`）或有显示
//!    差异。判定、诊断与 Ok 输出不受影响（观察表不参与 run 口径）。
//! 5. 观察面表形态：孪生 Enum 臂构造子体 `datas` 复用 `Raw::Var(参数名)`
//!    过 infer，产生与 binder 条目**同 span 同串的重复项**（参考版该处在
//!    值层合成、不过 infer）。`hover_entry_at` 平手取先且串相同，对 LSP
//!    行为无影响；全表互检按「无缺失 + 无异质」口径断言（见
//!    `observation_tests::hover_table_full_matches_reference_on_qualified_fixture`）。

use bumpalo::Bump;
use smol_str::SmolStr;
use rustc_hash::{FxHashMap, FxHashSet};
use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;

use super::parser::syntax::{ClassItem, Decl, Either, Icit, Pattern, Raw};
use crate::parser_lib::ToSpan;
use super::pretty::pretty_tm;
use super::{empty_span, Error, Ix, MetaVar, PatternDetail, Tm as CTm};
use std::collections::HashMap;

use super::typeclass::{Assertion, Instance, Synth};
use super::Val as CVal;
use crate::list::List as CList;
use super::MetaVar as CMetaVar;

/// 内建 prim 标识（参考版 `PrimFunc` 闭包挂在 decl 表条目的 `.5` 槽；
/// bump 内不能携带闭包，以枚举替代）。执行点：force 的 Decl 臂（结果再
/// force）与 v_app 的 Decl 臂（结果直接返回）；实参逆 spine 序收集后转
/// 正序传入；返回 `None` = 卡住（留 spine 上等再 force）。nat 算术 prim
/// 与 `vconnT` 仅在 prelude 挂载（register_nat_builtins /
/// register_vconn_builtin），run() 口径不出现，故不在枚举内。
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum PrimId {
    /// `string_concat`：两字面量槽拼接（非字面量 → 卡住）。
    StringConcat,
    /// `str_eq`：两字面量相等 → decl 表的 `true`/`false` 登记值（缺失卡
    /// Decl 存根——无 prelude 口径）。
    StrEq,
    /// `str_indent2`：每行缩进 2 空格（Verilog 多行字符串）。
    StrIndent2,
    /// `report_check_issue`：向 mutable `CheckIssues` 追加一行（行级去重），
    /// 返回 U(0)。输出串的 `[hdl][warning]` 行由此而来。
    ReportCheckIssue,
    /// `string_to_global_type`：字符串 → decl 表动态引用（eval `Tm::Decl`）。
    StringToGlobalType,
    /// `create_global`：写 mutable_map，返回 U(0)。
    CreateGlobal,
    /// `change_mutable`：读改写 mutable_map（v_app 实参到旧值），返回 U(0)。
    ChangeMutable,
    /// `get_global`：读 mutable_map（缺名 panic——参考版 unwrap 同款）。
    GetGlobal,
    /// `get_global_default`：纯读 + 缺省（不写表）。
    GetGlobalDefault,
    /// `change_mutable_default`：读改写或缺省插入，返回 U(0)。
    ChangeMutableDefault,
    FileReadAllText,
    FileWriteAllText,
    FileAppendAllText,
    FileExists,
    FileDelete,
    /// `nat_to_dec`：Nat → 十进制字符串（`count_nat_forced`）。
    NatToDec,
    /// `width_range`：Nat 宽度 → Verilog `"[N-1:0] "`（N≤1 空串）。
    WidthRange,
    /// `nat_is_ground`：Nat 是否全具体 → decl 表的 `true`/`false`。
    NatIsGround,
    /// Nat 五则算术（word-size primop，复刻 `nat.typort` 结构递归的可归约性）。
    NatAdd,
    NatMul,
    NatSub,
    NatDiv,
    NatRem,
    /// `vconnT`：Verilog 兼容具名端口连接（`child u1 (.a(x))` 宏展开产物，
    /// 仅 prelude 后挂载——签名引用 prelude 的 ModuleTree/Expr）。走子树判
    /// 端口方向并经 prelude 助手 `vconnEmit` 发射 assign（参考版 cxt.rs
    /// `vconn_builtin` 逐句）。
    VconnT,
}

/// 可变全局表 + def-replay 备忘（参考版 `Infer.mutable_map` +
/// `Infer.def_replay_memo` 的合一；两者都是 per-run 状态，随轮清空）。
struct Mutable {
    map: FxHashMap<SmolStr, V>,
    /// 无参 def 的 body 是否含全局副作用（`def_needs_replay` 按名缓存）。
    replay: FxHashMap<SmolStr, bool>,
}

impl Mutable {
    fn clear(&mut self) {
        self.map.clear();
        self.replay.clear();
    }
}

/// `REPLAY_GLOBAL_OPS`（参考版 mod.rs 同名常量）：求值 `Tm::Decl` 命中这些
/// 名字（直接或经其它 def 传递）时走重放路径。
const REPLAY_GLOBAL_OPS: &[&str] =
    &["create_global", "change_mutable", "change_mutable_default", "get_global"];

/// `def_needs_replay`：无参 def 的求值是否带全局副作用（按名 memo，环安全）。
/// builtin（prim 挂载）永不重放（登记项是自引用 `Tm::Decl(name)` 占位，
/// 真正行为经 prim 走）——参考版 `scan_def_replay` 同款。
fn def_needs_replay(mutable: &RefCell<Mutable>, decl: &Decls<'_>, name: &str) -> bool {
    if let Some(m) = mutable.borrow().replay.get(name) {
        return *m;
    }
    let mut visiting = std::collections::HashSet::new();
    let result = scan_def_replay(mutable, decl, name, &mut visiting);
    mutable.borrow_mut().replay.insert(SmolStr::new(name), result);
    result
}

fn scan_def_replay(
    mutable: &RefCell<Mutable>,
    decl: &Decls<'_>,
    name: &str,
    visiting: &mut std::collections::HashSet<SmolStr>,
) -> bool {
    if !visiting.insert(SmolStr::new(name)) {
        return false; // 环：无新信息
    }
    let result = match decl.get(name) {
        Some(e) if e.prim.is_some() => false,
        Some(e) => {
            let mut found = false;
            tm_scan_global_ops(mutable, decl, e.tm, visiting, &mut found);
            found
        }
        None => false,
    };
    visiting.remove(name);
    result
}

/// 深度优先扫闭合项里的 REPLAY_GLOBAL_OPS 调用（`Tm::Decl` 头）或对其它
/// 需重放 def 的引用（参考版 `tm_scan_global_ops` 逐句）。
fn tm_scan_global_ops(
    mutable: &RefCell<Mutable>,
    decl: &Decls<'_>,
    tm: &Tm<'_>,
    visiting: &mut std::collections::HashSet<SmolStr>,
    found: &mut bool,
) {
    if *found {
        return;
    }
    match tm {
        Tm::Decl(x) => {
            if REPLAY_GLOBAL_OPS.contains(x) {
                *found = true;
            } else if decl.get(*x).is_some() && scan_def_replay(mutable, decl, x, visiting) {
                *found = true;
            }
        }
        Tm::Obj(t, _) => tm_scan_global_ops(mutable, decl, t, visiting, found),
        Tm::Lam(_, _, b) => tm_scan_global_ops(mutable, decl, b, visiting, found),
        Tm::App(f, u, _) => {
            tm_scan_global_ops(mutable, decl, f, visiting, found);
            tm_scan_global_ops(mutable, decl, u, visiting, found);
        }
        Tm::AppPruning(t, _) => tm_scan_global_ops(mutable, decl, t, visiting, found),
        Tm::Pi(_, _, a, b) => {
            tm_scan_global_ops(mutable, decl, a, visiting, found);
            tm_scan_global_ops(mutable, decl, b, visiting, found);
        }
        Tm::Let(_, _, t, u) => {
            tm_scan_global_ops(mutable, decl, t, visiting, found);
            tm_scan_global_ops(mutable, decl, u, visiting, found);
        }
        Tm::SumCase { typ, datas, .. } => {
            tm_scan_global_ops(mutable, decl, typ, visiting, found);
            for d in datas.iter() {
                tm_scan_global_ops(mutable, decl, d.val, visiting, found);
            }
        }
        Tm::Match(t, cases) => {
            tm_scan_global_ops(mutable, decl, t, visiting, found);
            for (_, b) in cases.iter() {
                tm_scan_global_ops(mutable, decl, b, visiting, found);
            }
        }
        Tm::Call(_, args, body) => {
            for (t, _) in args.iter() {
                tm_scan_global_ops(mutable, decl, t, visiting, found);
            }
            tm_scan_global_ops(mutable, decl, body, visiting, found);
        }
        Tm::Sum(_, params, _, _) => {
            for p in params.iter() {
                tm_scan_global_ops(mutable, decl, p.val, visiting, found);
                tm_scan_global_ops(mutable, decl, p.ty, visiting, found);
            }
        }
        Tm::Var(_) | Tm::U(_) | Tm::Meta(_) | Tm::LiteralType | Tm::LiteralIntro(_) => {}
    }
}

/// 值是否为 `Nat` sum 类型本体（参考版 `is_nat_sum` 的快版对应）。
#[inline]
fn is_nat_sum_v(v: V) -> bool {
    v_tag(v) == 7
        && matches!(v_xcell_of(v), XCell::Sum { name: "Nat", is_trait: false, .. })
}

/// SumCase 装配点的原生 Nat 折叠（参考版 `nat_step_value`）：typ 已求值为
/// `v`；`zero`（index 0 空）→ 0，`succ (Nat k)`（index 1 单字段且内层是
/// Nat）→ k+1；其余 None（保持 SumCase 形状）。
fn nat_step_value(typ: V, index: u32, datas: &[SumDataV<'_>]) -> Option<u64> {
    if !is_nat_sum_v(typ) {
        return None;
    }
    match index {
        0 if datas.is_empty() => Some(0),
        // 字段值须已是 XCell（tag 7）才能按 Nat 单元读——中性字段
        // （Rigid / 卡住 SumCase / spine 头等）的构造链保持 SumCase 形状
        // （与参考版一致）；tag 检查同时是 v_xcell_of 解引用的前置守卫
        1 if datas.len() == 1 && v_tag(datas[0].val) == 7 => match v_xcell_of(datas[0].val) {
            XCell::Nat(k) => k.checked_add(1),
            _ => None,
        },
        _ => None,
    }
}

// syntax（bump 内的项表示）
// --------------------------------------------------------------------------------

/// bump 内分配的核心项。名字只服务 pretty（`Var` 无名，索引寻址）。
pub(crate) enum Tm<'a> {
    Var(u32),
    /// 全局声明的名字引用（参考版 `Tm::Decl(Span<String>)`；名字是 bump
    /// 内的 str，pretty 直接打印——namespace 限定键原样输出）。
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
    /// `x.field` 投影（参考版 `Tm::Obj`；字段名只服务 pretty/查表）。
    Obj(&'a Tm<'a>, &'a str),
    /// enum 类型本体（enum 声明 λ 链的体）。params = (参数名, 值项, 类型项,
    /// icit)，声明处值项即参数自身；实例化后值槽携带当前实参。
    /// `is_trait`：trait 脱糖的 enum（fresh_meta 走实例合成）。
    Sum(&'a str, &'a [SumParamT<'a>], &'a [&'a str], bool),
    /// 构造子值：typ 求值后必须是其所属的（已实例化的）`Sum`。case 以
    /// **index** 标识（所属 Sum 的 cases 表下标，参考版 L13 同款），名字
    /// 反查 `cases[index]`。
    SumCase {
        typ: &'a Tm<'a>,
        index: u32,
        datas: &'a [SumDataT<'a>],
        is_trait: bool,
    },
    /// 已编译的 match：分支体是检查过的项，运行时按模式首匹配。
    Match(&'a Tm<'a>, &'a [(PatternDetail, &'a Tm<'a>)]),
    /// 内联调用（参考版 `Tm::Call` / `Tm::OpCall` 的合一）：`name` 是被内联
    /// 的 def 名，args 是 λ 链参数的 `Var` 引用（带 icit，**List 序**：外层
    /// 参数在前——`wrap_match_in_call` 的构造序），body 是原 match 体。eval
    /// 的 Call 帧"body 求值结果卡 Match 才包 `Val::Call`"。参考版的显示专用
    /// `OpCall`（quote 查 `symbol_table` 产中缀/前缀节点）在快版由
    /// [`export`] 以同一规则决定——本机 Tm 不区分，求值行为本就一致。
    Call(&'a str, &'a [(&'a Tm<'a>, Icit)], &'a Tm<'a>),
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
#[derive(Clone, Copy, PartialEq, Eq)]
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
#[derive(Clone, Copy)]
pub(crate) struct SumDataV<'a> {
    name: &'a str,
    val: V,
    icit: Icit,
}

/// tag 7 的载体：字面量值、原生 Nat、卡住声明引用、卡住投影、和类型
/// 本体、构造子值、内联调用、卡住 match。判等按单元指针（同内容不同次
/// 求值各造单元——与参考版每次构造新值同构）；**位相等捷径对 tag 7
/// 关闭**（见模块注释）。
pub(crate) enum XCell<'a> {
    Lit(&'a str),
    /// 原生 Nat（参考版 `Val::Nat(u64)`，Lean/Agda 式压缩）：定义上等于
    /// `succ^n zero` 的值用单个 u64 持有。WHNF 叶（force 原样返回）；
    /// quote 经 `quote_nat` 展开回 SumCase 链。
    Nat(u64),
    /// 卡住的声明引用（参考版 `Val::Decl(name, sp)` 的裸头）：decl 表
    /// 未登记 / 递归自引用的存根 / prim 卡住（`None`）。带实参的卡住
    /// 声明 = spine 链（头 = 本单元），v_app 对 Decl 头压 spine。
    Decl { name: &'a str },
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
    /// 构造子值：typ 求值后是其所属的已实例化 `Sum`；case 以 index 标识。
    SumCase {
        typ: V,
        index: u32,
        datas: &'a [SumDataV<'a>],
        is_trait: bool,
    },
    /// 内联调用值（参考版 `Val::Call`）：name + 实参（带 icit）+ 体（卡
    /// Match）。v_app 对它 args prepend + 对 body 递归 v_app。
    Call {
        name: &'a str,
        args: &'a [(V, Icit)],
        body: V,
    },
    /// 卡住 match：scrutinee（创建时已 force）+ 捕获 env + 编译分支。
    /// 无 pending（参考版 L13 同款）；v_app 对 Match 把应用 splice 进
    /// 每个分支体（参考版 mod.rs 的 Match 臂）。
    Match {
        scrutinee: V,
        env: Env<'a>,
        cases: &'a [(PatternDetail, &'a Tm<'a>)],
    },
}

/// decl 表条目（参考版 decl 行 7 元组 `(Span, Tm, Val, Ty, VTy,
/// Option<PrimFunc>, String)` 的快版：`ty` 类型项在快版无读取点，省略；
/// Span/typ_pretty 为观察面（LSP 接线阶段 1）回填——错误消息仍用零 Span
/// 渲染，不受影响）。
#[derive(Clone)]
pub(crate) struct DeclEntry<'a> {
    /// 登记名源码 span（参考版行的 .0；观察面 hover 的 def_span 与
    /// goto-definition 读取。LSP 接线阶段 1 回填）。
    pub(crate) span: crate::parser_lib::Span<()>,
    /// 登记处渲染的类型字符串（参考版行的 .6 `typ_pretty`，同思路：
    /// [`Machine::decl_reg`] 一次 quote→export→pretty；全局名使用的
    /// hover 直接 clone，免去每使用点重复渲染。已知口径差：类型含
    /// binder 遮蔽时注册处 names 与使用处 names 的 fresh 后缀可能
    /// 不同——仅显示差异，见模块头偏差说明）。
    pub(crate) typ_pretty: Option<Rc<String>>,
    /// 登记项（参考版行的 .1；eval 的 `Tm::Decl` 臂 replay 路径取它重放）。
    pub(crate) tm: &'a Tm<'a>,
    /// 登记值（参考版行的 .2；eval 的 `Tm::Decl` 臂与 string_to_global_type
    /// 直接取）。
    pub(crate) val: V,
    /// 类型值（参考版行的 .4；infer_expr 的 Var→decl 回落取它当类型）。
    pub(crate) vty: V,
    /// prim 挂载（参考版行的 .5；force/v_app 的 Decl 臂执行、unify 的
    /// 不透明叶判定、def replay 的 builtin 排除）。
    pub(crate) prim: Option<PrimId>,
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
/// 的 meta 展开臂）/ Decl（force 的 prim 臂）/ 卡住投影 Obj（unify 的位相等
/// 捷径对它关闭）还是其它（Rigid——force 直接原样返回）。
const HK_OTHER: u8 = 0;
const HK_FLEX: u8 = 1;
const HK_DECL: u8 = 2;
const HK_OBJ: u8 = 3;

/// spine 栈槽：一次中性应用（icit 随槽携带）。`len`/`base` 支撑流式右链
/// quote；`hk` 记录链头种类（push 时随函数侧传播）。链头只可能是 Rigid /
/// Flex / Decl / 卡住投影 Obj（其余形态 v_app 即 panic，进不了链）。
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
                XCell::Decl { .. } => HK_DECL,
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

/// 值侧头种类判定（裸单元直查；链查顶端槽的 `hk` 标志，O(1)，无需沿链走底）。
#[inline]
fn head_kind(spine: &Spine, v: V) -> u8 {
    match v_tag(v) {
        5 => HK_FLEX,
        7 => match v_xcell_of(v) {
            XCell::Obj { .. } => HK_OBJ,
            XCell::Decl { .. } => HK_DECL,
            _ => HK_OTHER,
        },
        2 => spine.stack[v_spine_of(v)].hk,
        _ => HK_OTHER,
    }
}

/// 值是否 Flex（裸未解 meta 立即数或 meta 头的链）。
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

/// meta 创建时刻的上下文快照（参考版 `Arc<Cxt>` 的孪生：错误路径的
/// pretty/lvl/decls 重建 **+ 求解时用创建处上下文**）。`'static` 存放口径
/// 同工作栈（跨轮 reset 前一切句柄已消亡）。
pub(crate) struct MetaSnap<'a> {
    /// meta 创建时的层级。
    pub(crate) lvl: u32,
    /// 名字 telescope（pretty 的 names 用）。
    pub(crate) types: Option<&'a TCons<'a>>,
    /// decl 表快照（错误路径 quote/eval 用）。
    pub(crate) decls: Rc<Decls<'a>>,
    /// **完整上下文快照**（参考版 `MetaEntry::Unsolved(v, Arc<Cxt>, ..)`
    /// 的第二元）：`solve_multi_trait` 必须用 **meta 创建处**的上下文求解，
    /// 不能用调用方的——goal 里的 Rigid 层级按创建处 de Bruijn 编号，换用
    /// 浅上下文会让 rename/quote 算出越界变量（HDL prelude decl 308 的
    /// `impl Add for UInt[width]`：meta 创建于 lvl=4，被以 lvl=0 求解，
    /// 报 `Into[Nat, UInt[Variable index out of bounds]]`）。
    pub(crate) cxt: Cxt<'static>,
}

/// metacontext 条目（参考版 L13 四元同构）：**类型一律保留**（pruning 检查
/// 与 `lams` 都要读）；第二元 = 创建时刻的上下文快照（no_metas 错误路径）；
/// 第三元 = 创建时的开放类型（错误消息 pretty 与 oty 检查用）；第四元 =
/// 创建处 span（no_metas 报错定位——快版全零 span，字段保留对齐参考版
/// 形状）。解是 bump 内的打包值。Clone 供 temp-infer 探测的快照换入换出。
#[derive(Clone)]
pub(crate) enum MetaEntry {
    Solved(V, V),
    Unsolved(V, Rc<MetaSnap<'static>>, V, crate::parser_lib::Span<()>),
}

/// 取未解条目的（闭类型, 快照, 原始类型, span）。非未解 → unreachable。
#[inline]
pub(crate) fn meta_unsolved<'a>(m: &MetaEntry) -> (V, &'a MetaSnap<'a>, V, crate::parser_lib::Span<()>) {
    match m {
        MetaEntry::Unsolved(a, snap, o, sp) => {
            let snap: &'a MetaSnap<'a> = unsafe { &*(snap.as_ref() as *const MetaSnap<'static> as *const MetaSnap<'a>) };
            (*a, snap, *o, *sp)
        }
        _ => unreachable!(),
    }
}

/// `vMeta` 的打包版：已解给解值，未解给 Meta 立即数。
#[inline]
fn meta_val_of(metas: &[MetaEntry], m: u32) -> V {
    match &metas[m as usize] {
        MetaEntry::Solved(v, _) => *v,
        MetaEntry::Unsolved(..) => v_meta(m),
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

/// 独立应用（eval_iter 之外的 v_app：force 的解值展开、prim 执行等）。
/// 逐臂对齐参考版 v_app：λ → β；Flex/Rigid（裸或链）→ spine；Decl 头 →
/// prim 检查（命中执行：`Some` 直接返回、`None` 压 spine 卡住）；Obj 头 →
/// spine；Call 头 → args prepend + 对 body 递归 v_app；卡住 Match → 应用
/// splice 进每个分支体（参考版 L13 的 Match 臂：quote 实参后 `Tm::App`）；
/// 其余 panic（"impossible apply"——两版同时不可达 / 同时 panic）。
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
    mutable: &RefCell<Mutable>,
    f: V,
    a: V,
    i: Icit,
) -> V {
    if v_tag(f) == 1 {
        let c = v_clo_of(f);
        let env = env_ext(bump, c.env, a);
        eval_iter(bump, spine, work, vals, icits, defs, metas, decl, mutable, env, c.body)
    } else if v_tag(f) == 2 {
        // 链头：Decl 头先查 prim（带全部既有实参 + 新实参执行）。顶端槽的
        // `hk` 让非 Decl 链免去整趟走底——每次中性应用都省这一笔。
        let h = v_spine_of(f);
        if spine.stack[h].hk == HK_DECL {
            let hd = spine.spine_head(h);
            if let XCell::Decl { name } = v_xcell_of(hd) {
                let name = *name;
                if let Some(pid) = decl.get(name).and_then(|e| e.prim) {
                    if !prim_is_pure(pid) {
                        force_taint_bump();
                    }
                    let mut args: Vec<(V, Icit)> = Vec::new();
                    spine.collect_args(h, &mut args); // 逆应用序（最新在前）
                    args.reverse(); // 自然序（最老在前）
                    args.push((a, i));
                    if let Some(r) = prim_exec(
                        bump, spine, work, vals, icits, defs, metas, decl, mutable, pid, &args,
                    ) {
                        return r;
                    }
                }
            }
        }
        spine.push(f, a, i)
    } else if v_tag(f) == 7 {
        match v_xcell_of(f) {
            XCell::Obj { .. } => spine.push(f, a, i),
            XCell::Decl { name } => {
                // 裸 Decl 单元上应用：prim 以单实参试执行（实参不足 → None
                // → 压 spine；参考版 v_app 的 Decl 臂同款）
                let name = *name;
                if let Some(pid) = decl.get(name).and_then(|e| e.prim) {
                    if !prim_is_pure(pid) {
                        force_taint_bump();
                    }
                    let args = [(a, i)];
                    if let Some(r) = prim_exec(
                        bump, spine, work, vals, icits, defs, metas, decl, mutable, pid, &args,
                    ) {
                        return r;
                    }
                }
                spine.push(f, a, i)
            }
            XCell::Call { name, args, body } => {
                let mut new_args: Vec<(V, Icit)> = Vec::with_capacity(args.len() + 1);
                new_args.push((a, i));
                new_args.extend_from_slice(args);
                let nb = vapp1(
                    bump, spine, work, vals, icits, defs, metas, decl, mutable, *body, a, i,
                );
                v_xcell(bump.alloc(XCell::Call {
                    name,
                    args: bump.alloc_slice_copy(&new_args),
                    body: nb,
                }))
            }
            XCell::Match { scrutinee, env, cases } => {
                // splice：每个分支体追 `App(body, quote_l(u), i)`；quote 用
                // 独立任务栈（quote_iter 自清）。
                let l = env_len(*env);
                let u_tm = quote_iter(
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
                    l,
                    a,
                    None,
                );
                let new_case_vec: Vec<(PatternDetail, &'a Tm<'a>)> = cases
                    .iter()
                    .map(|(p, b)| {
                        // bump.alloc 返回 &mut，冻结成 &（collect 期望 &Tm）
                        ((*p).clone(), &*bump.alloc(Tm::App(*b, u_tm, i)))
                    })
                    .collect();
                let new_cases: &'a [(PatternDetail, &'a Tm<'a>)] =
                    bump.alloc_slice_fill_iter(new_case_vec);
                v_xcell(bump.alloc(XCell::Match {
                    scrutinee: *scrutinee,
                    env: *env,
                    cases: new_cases,
                }))
            }
            _ => panic!("impossible apply"),
        }
    } else if v_tag(f) == 3 || v_tag(f) == 4 || v_tag(f) == 6 {
        panic!("impossible apply")
    } else {
        spine.push(f, a, i)
    }
}

/// prim 执行（参考版 cxt.rs 各 `PrimFunc` 的逐句移植；实参自然序）。
/// `None` = 卡住（调用方留 spine 上等再 force）。文件 IO 原样落盘/
/// Nat prim 的共享辅助（参考版 cxt.rs 同名函数的逐句移植）。
///
/// `count_nat_forced`：Nat 值走成 u64（原生 `Nat(k)` 直取，succ 链逐层 +1，
/// 卡住尾 → 0）。`nat_concrete`：仅全具体才有值。`nat_succ_inner`：
/// `succ d` 的 d（要求已 force）。`nat_succ_shape`：装配 `succ inner`。
/// `stuck_decl`：把 prim 名 + 实参装成卡住 `Decl` 链。
fn count_nat_forced(
    bump: &Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decl: &Decls<'_>,
    mutable: &RefCell<Mutable>,
    val: V,
) -> u64 {
    let mut count = 0u64;
    let mut current = force(bump, spine, defs, metas, decl, mutable, val);
    loop {
        if v_tag(current) != 7 {
            return 0;
        }
        match v_xcell_of(current) {
            XCell::Nat(k) => return count.checked_add(*k).unwrap_or(0),
            XCell::SumCase { index: 0, .. } => return count,
            XCell::SumCase { index: 1, datas, .. } => match datas.first() {
                Some(d) => {
                    count = match count.checked_add(1) {
                        Some(c) => c,
                        None => return 0,
                    };
                    current = force(bump, spine, defs, metas, decl, mutable, d.val);
                }
                None => return 0,
            },
            _ => return 0,
        }
    }
}

/// 全具体 Nat → u64（未压缩的 `zero` 也算 0）；卡住一律 None。
fn nat_concrete(
    bump: &Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decl: &Decls<'_>,
    mutable: &RefCell<Mutable>,
    v: V,
) -> Option<u64> {
    let f = force(bump, spine, defs, metas, decl, mutable, v);
    if v_tag(f) != 7 {
        return None;
    }
    match v_xcell_of(f) {
        XCell::Nat(k) => Some(*k),
        XCell::SumCase { typ, index: 0, datas, .. } if datas.is_empty() => {
            if is_nat_sum_v(force(bump, spine, defs, metas, decl, mutable, *typ)) {
                Some(0)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// `succ d` 链的内层 d（要求 v 已 force）；其余（含原生 `Nat(k)`）→ None。
fn nat_succ_inner(v: V) -> Option<V> {
    if v_tag(v) != 7 {
        return None;
    }
    match v_xcell_of(v) {
        XCell::SumCase { typ, index: 1, datas, .. }
            if datas.len() == 1 && is_nat_sum_v(*typ) =>
        {
            Some(datas[0].val)
        }
        _ => None,
    }
}

/// 装配 `succ inner`（Nat 类型缺失 → None）。
fn nat_succ_shape<'a>(bump: &'a Bump, decl: &Decls<'a>, inner: V) -> Option<V> {
    let nat_ty = decl.get("Nat")?.val;
    let ds: &'a [SumDataV<'a>] =
        bump.alloc([SumDataV { name: "n", val: inner, icit: Icit::Expl }]);
    Some(v_xcell(bump.alloc(XCell::SumCase {
        typ: nat_ty,
        index: 1,
        datas: ds,
        is_trait: false,
    })))
}

/// 卡住应用 `name args...`（参考版 `stuck_decl`：`Val::Decl(name, spine)`）。
fn stuck_decl<'a>(bump: &'a Bump, spine: &mut Spine, name: &str, args: &[V]) -> V {
    let mut acc = v_xcell(bump.alloc(XCell::Decl { name: bump.alloc_str(name) }));
    for a in args {
        acc = spine.push(acc, *a, Icit::Expl);
    }
    acc
}

/// 崩溃（parity 套件不触达；与参考版行为一致）。
#[allow(clippy::too_many_arguments)]
fn prim_exec<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decl: &Decls<'a>,
    mutable: &RefCell<Mutable>,
    pid: PrimId,
    args: &[(V, Icit)],
) -> Option<V> {
    let arg = |i: usize| args.get(i).map(|x| x.0);
    match pid {
        PrimId::StringConcat => {
            if args.len() < 2 {
                return None;
            }
            match (lit_of(arg(0)?), lit_of(arg(1)?)) {
                (Some(a), Some(b)) => {
                    let len = a.len() + b.len();
                    let ptr = bump
                        .alloc_layout(std::alloc::Layout::from_size_align(len, 1).unwrap())
                        .as_ptr();
                    // SAFETY: a/b 都是 &str（合法 UTF-8）；两段完整序列按
                    // 字节拼接仍是合法 UTF-8
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
        PrimId::StrEq => {
            if args.len() < 2 {
                return None;
            }
            match (lit_of(arg(0)?), lit_of(arg(1)?)) {
                (Some(a), Some(b)) => {
                    let name = if a == b { "true" } else { "false" };
                    Some(decl.get(name).map(|e| e.val).unwrap_or_else(|| {
                        v_xcell(bump.alloc(XCell::Decl { name: bump.alloc_str(name) }))
                    }))
                }
                _ => None,
            }
        }
        PrimId::StrIndent2 => {
            let s = lit_of(arg(0)?)?;
            let indented = s.replace('\n', "\n  ");
            Some(v_xcell(bump.alloc(XCell::Lit(bump.alloc_str(&indented)))))
        }
        PrimId::ReportCheckIssue => {
            if args.len() < 4 {
                return None;
            }
            let get = |i: usize| lit_of(args[i].0).unwrap_or("");
            let (code, module, signal, message) = (get(0), get(1), get(2), get(3));
            if code.is_empty() || module.is_empty() {
                return Some(v_u(0));
            }
            let line = format!("{}|{}|{}|{}", code, module, signal, message);
            let mut m = mutable.borrow_mut();
            let existing = match m.map.get("CheckIssues") {
                Some(v) => lit_of(*v).unwrap_or("").to_string(),
                None => String::new(),
            };
            if !existing.split('\n').any(|l| l == line) {
                let next = if existing.is_empty() {
                    line
                } else {
                    format!("{}\n{}", existing, line)
                };
                m.map.insert(
                    SmolStr::new("CheckIssues"),
                    v_xcell(bump.alloc(XCell::Lit(bump.alloc_str(&next)))),
                );
            }
            drop(m);
            Some(v_u(0))
        }
        PrimId::StringToGlobalType => {
            let name = lit_of(arg(0)?)?;
            // eval `Tm::Decl(name)`（空 env；含 replay 路径——参考版同款）
            let tm = bump.alloc(Tm::Decl(name));
            let mut w2: Vec<W<'a>> = Vec::new();
            let mut v2: Vec<V> = Vec::new();
            let mut i2: Vec<Icit> = Vec::new();
            Some(eval_iter(
                bump, spine, &mut w2, &mut v2, &mut i2, defs, metas, decl, mutable, EMPTY_ENV, tm,
            ))
        }
        PrimId::CreateGlobal => {
            if args.len() < 2 {
                return None;
            }
            let name = lit_of(arg(0)?)?;
            mutable.borrow_mut().map.insert(SmolStr::new(name), arg(1).unwrap());
            Some(v_u(0))
        }
        PrimId::ChangeMutable => {
            if args.len() < 2 {
                return None;
            }
            let name = lit_of(arg(0)?)?;
            let f = arg(1).unwrap();
            let old = mutable.borrow().map.get(name).copied();
            if let Some(x) = old {
                // 内层 β 用独立草稿栈（eval_iter 入口清空 work/vals/icits，
                // 复用外层栈会销毁外层 eval 的待续状态）
                let mut w2: Vec<W<'a>> = Vec::new();
                let mut v2: Vec<V> = Vec::new();
                let mut i2: Vec<Icit> = Vec::new();
                let nx = vapp1(
                    bump, spine, &mut w2, &mut v2, &mut i2, defs, metas, decl, mutable, f, x,
                    Icit::Expl,
                );
                mutable.borrow_mut().map.insert(SmolStr::new(name), nx);
            }
            Some(v_u(0))
        }
        PrimId::GetGlobal => {
            let name = lit_of(arg(0)?)?;
            Some(mutable.borrow().map.get(name).copied().unwrap())
        }
        PrimId::GetGlobalDefault => {
            if args.len() < 2 {
                return None;
            }
            let name = lit_of(arg(0)?)?;
            Some(
                mutable
                    .borrow()
                    .map
                    .get(name)
                    .copied()
                    .unwrap_or_else(|| arg(1).unwrap()),
            )
        }
        PrimId::ChangeMutableDefault => {
            if args.len() < 3 {
                return None;
            }
            let name = lit_of(arg(0)?)?;
            let f = arg(1).unwrap();
            let default = arg(2).unwrap();
            let old = mutable.borrow().map.get(name).copied();
            match old {
                Some(x) => {
                    let mut w2: Vec<W<'a>> = Vec::new();
                    let mut v2: Vec<V> = Vec::new();
                    let mut i2: Vec<Icit> = Vec::new();
                    let nx = vapp1(
                        bump, spine, &mut w2, &mut v2, &mut i2, defs, metas, decl, mutable, f, x,
                        Icit::Expl,
                    );
                    mutable.borrow_mut().map.insert(SmolStr::new(name), nx);
                }
                None => {
                    mutable.borrow_mut().map.insert(SmolStr::new(name), default);
                }
            }
            Some(v_u(0))
        }
        PrimId::FileReadAllText => {
            let path = lit_of(arg(0)?)?;
            let content = std::fs::read_to_string(path)
                .unwrap_or_else(|e| panic!("file_read_all_text: failed to read '{}': {}", path, e));
            Some(v_xcell(bump.alloc(XCell::Lit(bump.alloc_str(&content)))))
        }
        PrimId::FileWriteAllText => {
            if args.len() < 2 {
                return None;
            }
            let (path, content) = (lit_of(arg(0)?)?, lit_of(arg(1)?)?);
            std::fs::write(path, content)
                .unwrap_or_else(|e| panic!("file_write_all_text: failed to write '{}': {}", path, e));
            Some(v_u(0))
        }
        PrimId::FileAppendAllText => {
            if args.len() < 2 {
                return None;
            }
            let (path, content) = (lit_of(arg(0)?)?, lit_of(arg(1)?)?);
            use std::io::Write;
            let mut file = std::fs::OpenOptions::new()
                .append(true)
                .create(true)
                .open(path)
                .unwrap_or_else(|e| panic!("file_append_all_text: failed to open '{}': {}", path, e));
            write!(file, "{}", content).unwrap_or_else(|e| {
                panic!("file_append_all_text: failed to append to '{}': {}", path, e)
            });
            Some(v_u(0))
        }
        PrimId::FileExists => {
            let path = lit_of(arg(0)?)?;
            let exists = std::path::Path::new(path).exists();
            let s = if exists { "true" } else { "false" };
            Some(v_xcell(bump.alloc(XCell::Lit(bump.alloc_str(s)))))
        }
        PrimId::FileDelete => {
            let path = lit_of(arg(0)?)?;
            std::fs::remove_file(path)
                .unwrap_or_else(|e| panic!("file_delete: failed to delete '{}': {}", path, e));
            Some(v_u(0))
        }
        // ── nat 族（参考版 cxt.rs 同名 PrimFunc 逐句）──
        PrimId::NatToDec => {
            let n = count_nat_forced(bump, spine, defs, metas, decl, mutable, arg(0)?);
            Some(v_xcell(bump.alloc(XCell::Lit(bump.alloc_str(&n.to_string())))))
        }
        PrimId::WidthRange => {
            let w = count_nat_forced(bump, spine, defs, metas, decl, mutable, arg(0)?);
            let s = if w <= 1 { String::new() } else { format!("[{}:0] ", w - 1) };
            Some(v_xcell(bump.alloc(XCell::Lit(bump.alloc_str(&s)))))
        }
        PrimId::NatIsGround => {
            let mut cur = force(bump, spine, defs, metas, decl, mutable, arg(0)?);
            let ground = loop {
                if v_tag(cur) != 7 {
                    break false;
                }
                match v_xcell_of(cur) {
                    XCell::Nat(_) => break true,
                    XCell::SumCase { index: 0, .. } => break true,
                    XCell::SumCase { index: 1, datas, .. } => match datas.first() {
                        Some(d) => cur = force(bump, spine, defs, metas, decl, mutable, d.val),
                        None => break false,
                    },
                    _ => break false,
                }
            };
            let name = if ground { "true" } else { "false" };
            Some(decl.get(name).map(|e| e.val).unwrap_or_else(|| {
                v_xcell(bump.alloc(XCell::Decl { name: bump.alloc_str(name) }))
            }))
        }
        // nat_add x y：y≡0 → x（无条件）；双具体 → u64；y≡succ⟨d⟩ →
        // succ (nat_add x d)；y=Nat(k>0) 且 x 非具体 → 展开 succ^k x。
        PrimId::NatAdd => {
            if args.len() < 2 {
                return None;
            }
            let x = args[0].0;
            let y = force(bump, spine, defs, metas, decl, mutable, args[1].0);
            if nat_concrete(bump, spine, defs, metas, decl, mutable, y) == Some(0) {
                return Some(x);
            }
            if let (Some(a), Some(b)) = (
                nat_concrete(bump, spine, defs, metas, decl, mutable, x),
                nat_concrete(bump, spine, defs, metas, decl, mutable, y),
            ) {
                return a.checked_add(b).map(|k| v_xcell(bump.alloc(XCell::Nat(k))));
            }
            if let Some(d) = nat_succ_inner(y) {
                let inner = stuck_decl(bump, spine, "nat_add", &[x, d]);
                return nat_succ_shape(bump, decl, inner);
            }
            if v_tag(y) == 7 {
                if let XCell::Nat(k) = v_xcell_of(y) {
                    let mut inner = x;
                    for _ in 0..*k {
                        inner = nat_succ_shape(bump, decl, inner)?;
                    }
                    return Some(inner);
                }
            }
            None
        }
        // nat_mul x y：y≡0 → 0；双具体 → u64；y≡succ⟨d⟩ → x + (x * d)；
        // y=Nat(k>0) → k 层 add 链。
        PrimId::NatMul => {
            if args.len() < 2 {
                return None;
            }
            let x = args[0].0;
            let y = force(bump, spine, defs, metas, decl, mutable, args[1].0);
            if nat_concrete(bump, spine, defs, metas, decl, mutable, y) == Some(0) {
                return Some(v_xcell(bump.alloc(XCell::Nat(0))));
            }
            if let (Some(a), Some(b)) = (
                nat_concrete(bump, spine, defs, metas, decl, mutable, x),
                nat_concrete(bump, spine, defs, metas, decl, mutable, y),
            ) {
                return a.checked_mul(b).map(|k| v_xcell(bump.alloc(XCell::Nat(k))));
            }
            if let Some(d) = nat_succ_inner(y) {
                let inner = stuck_decl(bump, spine, "nat_mul", &[x, d]);
                return Some(stuck_decl(bump, spine, "nat_add", &[x, inner]));
            }
            if v_tag(y) == 7 {
                if let XCell::Nat(k) = v_xcell_of(y) {
                    let mut acc = v_xcell(bump.alloc(XCell::Nat(0)));
                    for _ in 0..*k {
                        acc = stuck_decl(bump, spine, "nat_add", &[x, acc]);
                    }
                    return Some(acc);
                }
            }
            None
        }
        // nat_sub x y：x≡0 → 0；双具体 → saturating_sub；x≡succ⟨dx⟩ 时按 y
        // 分支；x 卡住 → None（**不得**返回 x）。
        PrimId::NatSub => {
            if args.len() < 2 {
                return None;
            }
            let x = force(bump, spine, defs, metas, decl, mutable, args[0].0);
            let y = force(bump, spine, defs, metas, decl, mutable, args[1].0);
            let xc = nat_concrete(bump, spine, defs, metas, decl, mutable, x);
            let yc = nat_concrete(bump, spine, defs, metas, decl, mutable, y);
            if xc == Some(0) {
                return Some(v_xcell(bump.alloc(XCell::Nat(0))));
            }
            if let (Some(a), Some(b)) = (xc, yc) {
                return Some(v_xcell(bump.alloc(XCell::Nat(a.saturating_sub(b)))));
            }
            if let Some(dx) = nat_succ_inner(x) {
                return match yc {
                    Some(0) => Some(x),
                    Some(b) => Some(stuck_decl(
                        bump,
                        spine,
                        "nat_sub",
                        &[dx, v_xcell(bump.alloc(XCell::Nat(b - 1)))],
                    )),
                    _ => nat_succ_inner(y)
                        .map(|dy| stuck_decl(bump, spine, "nat_sub", &[dx, dy])),
                };
            }
            None
        }
        // nat_div / nat_rem：仅全具体快路径；y==0 返回 x。
        PrimId::NatDiv => {
            if args.len() < 2 {
                return None;
            }
            let x = nat_concrete(bump, spine, defs, metas, decl, mutable, args[0].0);
            let y = nat_concrete(bump, spine, defs, metas, decl, mutable, args[1].0);
            match (x, y) {
                (Some(a), Some(0)) => Some(v_xcell(bump.alloc(XCell::Nat(a)))),
                (Some(a), Some(b)) => Some(v_xcell(bump.alloc(XCell::Nat(a / b)))),
                _ => None,
            }
        }
        PrimId::NatRem => {
            if args.len() < 2 {
                return None;
            }
            let x = nat_concrete(bump, spine, defs, metas, decl, mutable, args[0].0);
            let y = nat_concrete(bump, spine, defs, metas, decl, mutable, args[1].0);
            match (x, y) {
                (Some(a), Some(0)) => Some(v_xcell(bump.alloc(XCell::Nat(a)))),
                (Some(a), Some(b)) => Some(v_xcell(bump.alloc(XCell::Nat(a % b)))),
                _ => None,
            }
        }
        // vconnT（参考版 cxt.rs `vconn_builtin` 逐句）：port 必须是
        // `subSignal` 构造值；走子 ModuleTree 的 head def `expr` 列表按端口
        // 名判方向（createIn* → input）；经 prelude 助手 `vconnEmit` 发射
        // assign（结果弃）；恒返回 U(0)。
        PrimId::VconnT => {
            if args.len() < 3 {
                return None;
            }
            let noop = v_u(0);
            let child_tree = args[0].0;
            let port = args[1].0;
            let sig = args[2].0;
            // SumCase 值的构造子名：经 typ 的 Sum cases 表按 index 反查
            // （不 hardcode 枚举顺序；typ 不 force——参考版同款）。
            let ctor_name = |v: V| -> Option<&str> {
                if v_tag(v) != 7 {
                    return None;
                }
                match v_xcell_of(v) {
                    XCell::SumCase { typ, index, .. } => match v_xcell_of(*typ) {
                        XCell::Sum { cases, .. } => cases.get(*index as usize).copied(),
                        _ => None,
                    },
                    _ => None,
                }
            };
            if ctor_name(port) != Some("subSignal") {
                return Some(noop);
            }
            let pname = match v_xcell_of(port) {
                XCell::SumCase { datas, .. } => match datas.get(1) {
                    Some(d) => match v_xcell_of(d.val) {
                        XCell::Lit(s) => *s,
                        _ => return Some(noop),
                    },
                    None => return Some(noop),
                },
                _ => return Some(noop),
            };
            // 参考版 field() 只认 SumCase 的 datas（不查 Sum 参数槽）。
            let field = |v: V, name: &str| -> Option<V> {
                match v_xcell_of(v) {
                    XCell::SumCase { datas, .. } => {
                        datas.iter().find(|d| d.name == name).map(|d| d.val)
                    }
                    _ => None,
                }
            };
            let field_str = |v: V, name: &str| -> Option<&str> {
                match field(v, name) {
                    Some(x) => match v_xcell_of(x) {
                        XCell::Lit(s) => Some(*s),
                        _ => None,
                    },
                    None => None,
                }
            };
            // 子树是 ModuleTree 结构：取 `data` → head ModuleDef 的 `expr`
            // 列表，逐个扫描端口声明找 `pname`。
            let ct = force(bump, spine, defs, metas, decl, mutable, child_tree);
            let data = match field(ct, "data") {
                Some(v) => force(bump, spine, defs, metas, decl, mutable, v),
                None => return Some(noop),
            };
            let head_def = match field(data, "x") {
                Some(v) => force(bump, spine, defs, metas, decl, mutable, v),
                None => return Some(noop),
            };
            let mut is_input = false;
            let mut cur = match field(head_def, "expr") {
                Some(v) => force(bump, spine, defs, metas, decl, mutable, v),
                None => return Some(noop),
            };
            while let Some("cons") = ctor_name(cur) {
                let (x, xs) = match (field(cur, "x"), field(cur, "xs")) {
                    (Some(x), Some(xs)) => (x, xs),
                    _ => break,
                };
                let xf = force(bump, spine, defs, metas, decl, mutable, x);
                let cn = ctor_name(xf).unwrap_or_default();
                if matches!(cn, "createIn" | "createInWidth" | "createSIntInWidth")
                    && field_str(xf, "name") == Some(pname)
                {
                    is_input = true;
                    break;
                }
                cur = force(bump, spine, defs, metas, decl, mutable, xs);
            }
            let bool_name = if is_input { "Boolean.true" } else { "Boolean.false" };
            let Some(b) = decl.get(bool_name).map(|e| e.val) else {
                return Some(noop);
            };
            if let Some(emit) = decl.get("vconnEmit").map(|e| e.val) {
                // 内层 β 用独立草稿栈（同 ChangeMutable：复用外层栈会销毁
                // 外层 eval 的待续状态）；发射结果弃（副作用走 mutable）。
                let mut w2: Vec<W<'a>> = Vec::new();
                let mut v2: Vec<V> = Vec::new();
                let mut i2: Vec<Icit> = Vec::new();
                let e = vapp1(
                    bump, spine, &mut w2, &mut v2, &mut i2, defs, metas, decl, mutable, emit, b,
                    Icit::Expl,
                );
                let e = vapp1(
                    bump, spine, &mut w2, &mut v2, &mut i2, defs, metas, decl, mutable, e, port,
                    Icit::Expl,
                );
                let _ = vapp1(
                    bump, spine, &mut w2, &mut v2, &mut i2, defs, metas, decl, mutable, e, sig,
                    Icit::Expl,
                );
            }
            Some(noop)
        }
    }
}

// force 记忆化（参考版 mod.rs `FORCE_MEMO` 的 bump 版；L13 参考版靠它把
// prelude 22.4s → 6.0s，见 docs/l13-perf-review-4.md §16）。
//
// 参考版的三根正确性支柱在 bump 模型下的处置：
// 1. **keepalive**（条目持有输入 Rc 防地址复用）——bump 同代内单调分配、
//    地址不复用，跨代 `bump.reset()` 前一切句柄已消亡；只要 memo 在每轮
//    入口清空（见 `force_memo_clear` 的调用点）即可，无需持有输入。
// 2. **taint**：walk 途中 consult 了不可抽象状态（未解 meta / 有副作用
//    prim）就 bump 计数器，动过的条目不插入。
// 3. **prim-ness 版本**：force 唯一读的 decl 表状态是名字的 prim-ness
//    （Decl / prim 两条臂）；`decl_reg` 时 prim-ness 变化即 bump 版本，
//    条目记版本、不匹配即 miss。
thread_local! {
    /// key = 输入 `V` 的打包字（仅 tag 7 复合形状入表；同代内唯一）。
    static FORCE_MEMO: RefCell<FxHashMap<u64, (V, u64)>> =
        RefCell::new(FxHashMap::default());
    static FORCE_TAINT: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    static PRIM_VERSION: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// 条目上限；溢出整表清空（防 keepalive 钉住垃圾，代价是一次重走）。
const FORCE_MEMO_CAP: usize = 1 << 20;

/// 每轮入口清空 memo（bump.reset() 处调用；地址可能被下一代复用）。
fn force_memo_clear() {
    FORCE_MEMO.with(|m| m.borrow_mut().clear());
}

#[inline]
fn force_taint_bump() {
    FORCE_TAINT.with(|t| t.set(t.get() + 1));
}

/// decl 条目的 prim-ness 发生变化时调用（缓存失效）。
#[inline]
fn prim_version_bump() {
    PRIM_VERSION.with(|v| v.set(v.get() + 1));
}

/// 结果只依赖实参的 prim（可安全记忆化）；其余（mutable 全局 / 文件 IO /
/// 诊断）一律按 impure 处理。参考版 `prim_is_pure` 的 PrimId 版。
fn prim_is_pure(pid: PrimId) -> bool {
    matches!(
        pid,
        PrimId::NatAdd
            | PrimId::NatMul
            | PrimId::NatSub
            | PrimId::NatDiv
            | PrimId::NatRem
            | PrimId::NatToDec
            | PrimId::WidthRange
            | PrimId::StringConcat
            | PrimId::StrEq
            | PrimId::StrIndent2
    )
}

// force（迭代；L13 参考版 force_inner 的臂集：Flex 链 / Nat 叶 / Obj 重建
// / Call 归一 / Decl prim / SumCase typ+datas / Sum 与其余 WHNF 叶）
// --------------------------------------------------------------------------------

/// **force**：把值更新到 metacontext 的当前状态，带记忆化（参考版
/// `Infer::force` 的 memo 壳）。只有 `SumCase | Call | Obj` 三种复合形状
/// 走 memo（叶子臂是 O(1)，连哈希查找都省）。逐臂语义见 [`force_inner`]。
fn force<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decl: &Decls<'a>,
    mutable: &RefCell<Mutable>,
    v0: V,
) -> V {
    let compound = v_tag(v0) == 7
        && matches!(
            v_xcell_of(v0),
            XCell::SumCase { .. } | XCell::Call { .. } | XCell::Obj { .. }
        );
    if !compound {
        return force_inner(bump, spine, defs, metas, decl, mutable, v0);
    }
    let key = v0.0;
    let ver = PRIM_VERSION.with(|v| v.get());
    if let Some(r) = FORCE_MEMO.with(|m| {
        m.borrow()
            .get(&key)
            .filter(|(_, v)| *v == ver)
            .map(|(r, _)| *r)
    }) {
        return r;
    }
    let taint0 = FORCE_TAINT.with(|t| t.get());
    let r = force_inner(bump, spine, defs, metas, decl, mutable, v0);
    // walk 途中 consult 了未解 meta / 有副作用 prim → 不插入
    if FORCE_TAINT.with(|t| t.get()) == taint0 && PRIM_VERSION.with(|v| v.get()) == ver {
        FORCE_MEMO.with(|m| {
            let mut m = m.borrow_mut();
            if m.len() >= FORCE_MEMO_CAP {
                m.clear();
            }
            m.insert(key, (r, ver));
        });
    }
    r
}

/// force 的实际臂集（无 memo；参考版 `force_inner` 逐臂对齐）：
/// Flex（已解 → 展开应用；未解原样）、原生 Nat（WHNF 叶）、Obj（递归进内层
/// 重建）、Call（stale nat-primop 归一 / force body + 实参）、Decl（prim
/// 执行：`Some` 结果**再 force**）、SumCase（force typ + 逐 data 重建）、
/// Sum 与其余（WHNF 叶，不下钻）。
///
/// 内部的 eval_iter 调用用**本调用私有的草稿栈**：外层 eval/unify 循环的
/// work/vals 不能被清空（force 可能在它们循环体中途被调用，且经 eval_aux
/// 与本函数互递归；Decl prim 的 `Some` 结果也就地再 force）。L04-L06 的
/// force 借用调用方的栈，是因为那几章的 eval_iter 不回调 force——这个差异
/// **不是**漏同步，别往那方向改。四个 `Vec::new()` 本身不分配，只有真正
/// 下钻时才增长，早退路径零成本。
fn force_inner<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decl: &Decls<'a>,
    mutable: &RefCell<Mutable>,
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
                _ => {
                    // 裸未解 meta：taint（参考版 force 的 Flex 臂同款）
                    force_taint_bump();
                    return v;
                }
            },
            2 => {
                let h = v_spine_of(v);
                // 顶端槽的 `hk` 直接给出分派（省去非 flex/Decl 链的整趟走底）
                match spine.stack[h].hk {
                    HK_FLEX => {
                        let hd = spine.spine_head(h);
                        // flex 链：解应用到全部实参（应用序 = 收集序的逆序）；
                        // 每步都可能 β（参考版 vAppSp 逐步 vApp 同款）
                        match &metas[v_meta_of(hd) as usize] {
                            MetaEntry::Unsolved(..) => {
                                // 未解 meta：解会变（ns 探测还会快照回滚），
                                // 不可抽象 → taint（参考版同款）
                                force_taint_bump();
                                return v;
                            }
                            MetaEntry::Solved(sol, _) => {
                                args.clear();
                                spine.collect_args(h, &mut args);
                                let mut t = *sol;
                                for &(a, i) in args.iter().rev() {
                                    t = vapp1(
                                        bump, spine, &mut work, &mut vals, &mut icits, defs, metas,
                                        decl, mutable, t, a, i,
                                    );
                                }
                                v = t;
                            }
                        }
                    }
                    HK_DECL => {
                        let hd = spine.spine_head(h);
                        // Decl 头的链：prim 执行（Some 结果再 force；None
                        // 卡住返回原链——参考版 force 的 Decl 臂）
                        let name = match v_xcell_of(hd) {
                            XCell::Decl { name } => *name,
                            _ => return v,
                        };
                        match decl.get(name).and_then(|e| e.prim) {
                            Some(pid) => {
                                // 有副作用 prim：重执行可观察 → taint（参考版
                                // force 的 Decl 臂 `prim_is_pure` 同款）
                                if !prim_is_pure(pid) {
                                    force_taint_bump();
                                }
                                args.clear();
                                spine.collect_args(h, &mut args);
                                args.reverse();
                                let mut w2: Vec<W<'a>> = Vec::new();
                                let mut v2: Vec<V> = Vec::new();
                                let mut i2: Vec<Icit> = Vec::new();
                                match prim_exec(
                                    bump, spine, &mut w2, &mut v2, &mut i2, defs, metas, decl,
                                    mutable, pid, &args,
                                ) {
                                    Some(r) => {
                                        v = force(bump, spine, defs, metas, decl, mutable, r)
                                    }
                                    None => return v,
                                }
                            }
                            None => return v,
                        }
                    }
                    // Rigid / Obj 头的链：卡住
                    _ => return v,
                }
            }
            7 => match v_xcell_of(v) {
                // 原生 Nat 是 WHNF（定义上 succ^n zero 的压缩表示）
                XCell::Nat(_) => return v,
                // force 递归进卡住投影的内层并**重建** Obj（参考版 force
                // 的 Obj 臂；不变则原样返回）
                XCell::Obj { val, name } => {
                    let v2 = force(bump, spine, defs, metas, decl, mutable, *val);
                    if v2 == *val {
                        return v;
                    }
                    return v_xcell(bump.alloc(XCell::Obj { val: v2, name }));
                }
                XCell::Call { name, args, body } => {
                    // stale def-shape 归一：名字现被 prim 接管时，重放实参
                    // 走 prim 路径归一到与 prim 产物相同的形状（参考版
                    // force 的 Call 臂；nat_primop_symbol 预过滤 + decl 表
                    // 权威检查）
                    let name: &str = name;
                    if super::nat_primop_symbol(name).is_some()
                        && decl.get(name).is_some_and(|e| e.prim.is_some())
                    {
                        let mut acc = v_xcell(bump.alloc(XCell::Decl { name }));
                        for &(a, i) in args.iter() {
                            acc = vapp1(
                                bump, spine, &mut work, &mut vals, &mut icits, defs, metas, decl,
                                mutable, acc, a, i,
                            );
                        }
                        // prim 不能返回另一个 Call；Call 形态再 force 一次
                        return if v_tag(acc) == 7 && matches!(v_xcell_of(acc), XCell::Call { .. })
                        {
                            force(bump, spine, defs, metas, decl, mutable, acc)
                        } else {
                            acc
                        };
                    }
                    let bf = force(bump, spine, defs, metas, decl, mutable, *body);
                    let mut changed = bf != *body;
                    let mut new_args: Vec<(V, Icit)> = Vec::with_capacity(args.len());
                    for &(a, i) in args.iter() {
                        let af = force(bump, spine, defs, metas, decl, mutable, a);
                        if af != a {
                            changed = true;
                        }
                        new_args.push((af, i));
                    }
                    return if changed {
                        v_xcell(bump.alloc(XCell::Call {
                            name,
                            args: bump.alloc_slice_copy(&new_args),
                            body: bf,
                        }))
                    } else {
                        v
                    };
                }
                // 裸 Decl 单元：prim 以空实参试执行（各 prim 需 ≥1 实参 →
                // None 卡住；参考版 force 的 Decl 臂同款路径）
                XCell::Decl { name } => {
                    let name = *name;
                    let prim = decl.get(name).and_then(|e| e.prim);
                    match prim {
                        Some(pid) => {
                            if !prim_is_pure(pid) {
                                force_taint_bump();
                            }
                            let mut w2: Vec<W<'a>> = Vec::new();
                            let mut v2: Vec<V> = Vec::new();
                            let mut i2: Vec<Icit> = Vec::new();
                            if let Some(r) = prim_exec(
                                bump,
                                spine,
                                &mut w2,
                                &mut v2,
                                &mut i2,
                                defs,
                                metas,
                                decl,
                                mutable,
                                pid,
                                &[],
                            ) {
                                v = force(bump, spine, defs, metas, decl, mutable, r);
                            } else {
                                return v;
                            }
                        }
                        None => return v,
                    }
                }
                // SumCase：force typ + 逐 data（副作用必须跑），变化才重建
                XCell::SumCase { typ, index, datas, is_trait } => {
                    let tf = force(bump, spine, defs, metas, decl, mutable, *typ);
                    let mut changed = tf != *typ;
                    let mut new_datas: Vec<SumDataV<'a>> = Vec::with_capacity(datas.len());
                    for (i, d) in datas.iter().enumerate() {
                        let df = force(bump, spine, defs, metas, decl, mutable, d.val);
                        if changed {
                            // 首变化后回填已见未变字段（原值指针相同）
                            if new_datas.is_empty() {
                                for d0 in datas.iter().take(i) {
                                    new_datas.push(SumDataV { name: d0.name, val: d0.val, icit: d0.icit });
                                }
                            }
                            new_datas.push(SumDataV { name: d.name, val: df, icit: d.icit });
                        } else if df != d.val {
                            changed = true;
                            for d0 in datas.iter().take(i) {
                                new_datas.push(SumDataV { name: d0.name, val: d0.val, icit: d0.icit });
                            }
                            new_datas.push(SumDataV { name: d.name, val: df, icit: d.icit });
                        }
                    }
                    return if changed {
                        v_xcell(bump.alloc(XCell::SumCase {
                            typ: tf,
                            index: *index,
                            datas: bump.alloc_slice_copy(&new_datas),
                            is_trait: *is_trait,
                        }))
                    } else {
                        v
                    };
                }
                _ => return v,
            },
            _ => return v,
        }
    }
}

// 运行时分支选择（值层首匹配，无合一；L13 参考版 Compiler::eval_aux 同款：
// index 制 + 原生 Nat O(1) 分派）
// --------------------------------------------------------------------------------

/// 按模式首匹配（参考版 `Compiler::eval_aux` 逐句）：
/// - 构造子头（SumCase / 原生 Nat）**不 force 直接分派**（深链 O(n²) 规避）；
///   非构造子头先 force 再分类，仍非构造子 → index = `u32::MAX`。
/// - `Nat 0` → index 0（zero，无字段）；`Nat k>0` → index 1（succ，字段绑
///   `Nat(k-1)`——不建一元链）。
/// - 第一遍：Con 模式 index 相等 → datas 与子模式 zip（zip 截断）逐个递归
///   （每步单臂表，env 累积——head 本身不 prepend）；子模式失配 → 试下臂。
/// - 第二遍（兜底）：首个 Any/Bind 模式命中，**原始 head**（非 force 后的
///   值）prepend 进 env——参考版 `cxt.prepend(heads.clone())` 同款。
#[allow(clippy::too_many_arguments)]
fn eval_aux<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decl: &Decls<'a>,
    mutable: &RefCell<Mutable>,
    head: V,
    env: Env<'a>,
    cases: &'a [(PatternDetail, &'a Tm<'a>)],
) -> Option<(&'a Tm<'a>, Env<'a>)> {
    // 构造子头分类：Some((index, datas))；Nat(k>0) 的参数表按需 bump 构造
    fn classify<'a>(bump: &'a Bump, v: V) -> Option<(u32, &'a [SumDataV<'a>])> {
        if v_tag(v) != 7 {
            return None;
        }
        match v_xcell_of(v) {
            XCell::SumCase { index, datas, .. } => Some((*index, datas)),
            XCell::Nat(k) if *k == 0 => Some((0, &[])),
            XCell::Nat(k) => {
                let inner = v_xcell(bump.alloc(XCell::Nat(k - 1)));
                let ds: &'a [SumDataV<'a>] =
                    bump.alloc([SumDataV { name: "n", val: inner, icit: Icit::Expl }]);
                Some((1, ds))
            }
            _ => None,
        }
    }
    let (index, datas): (u32, &[SumDataV<'a>]) = match classify(bump, head) {
        Some(x) => x,
        None => {
            let h2 = force(bump, spine, defs, metas, decl, mutable, head);
            match classify(bump, h2) {
                Some((ix, ds)) => (ix, ds),
                None => (u32::MAX, &[]),
            }
        }
    };
    // 第一遍：Con(index) 相等（子模式 zip 失配 → 试下一臂）
    for (pat, body) in cases.iter() {
        if let PatternDetail::Con(constr_idx, _, subs) = pat {
            if *constr_idx == index {
                let mut cur_body = *body;
                let mut cur_env = env;
                let mut ok = true;
                for (d, sub) in datas.iter().zip(subs.iter()) {
                    let arms1: &'a [(PatternDetail, &'a Tm<'a>)] =
                        bump.alloc([(sub.clone(), cur_body)]);
                    match eval_aux(bump, spine, defs, metas, decl, mutable, d.val, cur_env, arms1)
                    {
                        Some((b, e)) => {
                            cur_body = b;
                            cur_env = e;
                        }
                        None => {
                            ok = false;
                            break;
                        }
                    }
                }
                if ok {
                    return Some((cur_body, cur_env));
                }
            }
        }
    }
    // 第二遍：首个 Any/Bind（绑定原始 head）
    for (pat, body) in cases.iter() {
        match pat {
            PatternDetail::Any(..) | PatternDetail::Bind(_) => {
                return Some((body, env_ext(bump, env, head)))
            }
            PatternDetail::Con(..) => {}
        }
    }
    None
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
    /// vals 顶是投影接收者的值：构造子头（Sum/SumCase）不 force 直接投影
    /// （miss panic，参考版 unwrap 同款；SumCase 的 typ 非 Sum 时降级卡住
    /// Obj）；其余头先 force，仍不可投影 → 卡住 Obj。
    ObjSel(&'a str),
    /// vals 顶自底向上是 (v0,t0,...,v_{n-1},t_{n-1})（求值序）：装配 Sum。
    SumAsm {
        name: &'a str,
        params: &'a [SumParamT<'a>],
        cases: &'a [&'a str],
        is_trait: bool,
    },
    /// vals 顶自底向上是 (typ, d0..d_{nd-1})：装配 SumCase（含原生 Nat 折叠
    /// ——`nat_step_value`）。
    SumCaseAsm {
        index: u32,
        datas: &'a [SumDataT<'a>],
        is_trait: bool,
    },
    /// vals 顶是 Call/OpCall 体的值：**卡 Match 才包 `Val::Call`**（实参项在
    /// 捕获 env 下求值；参考版 eval 的 Frame::Call 同款），否则原样。
    CallAsm {
        name: &'a str,
        args: &'a [(&'a Tm<'a>, Icit)],
        env: Env<'a>,
    },
    /// vals 顶是 scrutinee 的值：构造子头（SumCase/Nat）不 force 直接
    /// eval_aux 选分支；其余先 force；无臂命中 / 非构造子头 → 卡住 Match。
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
    mutable: &RefCell<Mutable>,
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
            // 全局声明：decl 表查名。**replay 路径**：无参 def 的 body 含全局
            // 副作用（`def_needs_replay`：REPLAY_GLOBAL_OPS 名单，builtin 排除）
            // 时清空 env 重放 body（参考版 eval 的 Tm::Decl 臂同款——副作用
            // 对当前 mutable 状态生效）；否则返回登记值。未登记 → 卡
            // `Decl(name, 空 spine)`（递归自引用存根 / 逃逸形态）。
            W::Tm(Tm::Decl(x), _) => match decl.get(*x) {
                Some(e) => {
                    if e.prim.is_none() && def_needs_replay(mutable, decl, x) {
                        work.push(W::Tm(e.tm, EMPTY_ENV));
                    } else {
                        vals.push(e.val);
                    }
                }
                None => vals.push(v_xcell(bump.alloc(XCell::Decl { name: x }))),
            },
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
            // Call（含参考版 OpCall 的 eval 行为——两节点 eval 完全一致）：
            // 先求体，体值卡 Match 才在 CallAsm 里求实参并包 `Val::Call`
            // （参考版 eval 的 Frame::Call）
            W::Tm(Tm::Call(name, args, body), env) => {
                work.push(W::CallAsm { name, args, env });
                work.push(W::Tm(body, env));
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
            // 投影：构造子头（Sum/SumCase）不 force 直接投影（miss panic）；
            // 其余头先 force，仍不可投影一律卡成 Obj（详见 W::ObjSel）。
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
                    index,
                    datas,
                    is_trait,
                },
                env,
            ) => {
                work.push(W::SumCaseAsm { index: *index, datas, is_trait: *is_trait });
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
                // L13：构造子头（Sum/SumCase）不 force 直接投影；其余头先
                // force（参考版 Frame::Obj）。SumCase 的 typ 非 Sum（meta/
                // rigid 头）→ 降级卡住 Obj（eval 永不崩）；其余不可投影形
                // 态同样卡住 Obj。
                let is_ctor = v_tag(v) == 7
                    && matches!(
                        v_xcell_of(v),
                        XCell::Sum { .. } | XCell::SumCase { .. }
                    );
                let a = if is_ctor { v } else { force(bump, spine, defs, metas, decl, mutable, v) };
                match v_tag(a) {
                    7 => match v_xcell_of(a) {
                        XCell::Sum { params, .. } => {
                            match params.iter().find(|p| p.name == name) {
                                Some(p) => vals.push(p.val),
                                // 参考 unwrap：字段必在
                                None => panic!("impossible"),
                            }
                        }
                        XCell::SumCase { typ, datas, .. } => {
                            match v_xcell_of(*typ) {
                                XCell::Sum { params, .. } => {
                                    match params
                                        .iter()
                                        .find(|p| p.name == name)
                                        .map(|p| p.val)
                                        .or_else(|| {
                                            datas.iter().find(|d| d.name == name).map(|d| d.val)
                                        })
                                    {
                                        Some(p) => vals.push(p),
                                        None => panic!("impossible"),
                                    }
                                }
                                // typ 非 Sum：无字段表可投影 → 卡住 Obj
                                _ => vals.push(
                                    v_xcell(bump.alloc(XCell::Obj { val: a, name })),
                                ),
                            }
                        }
                        _ => vals.push(v_xcell(bump.alloc(XCell::Obj { val: a, name }))),
                    },
                    // Rigid（裸或链）/ Flex / 卡住 match / 字面量… → 卡住 Obj
                    _ => vals.push(v_xcell(bump.alloc(XCell::Obj { val: a, name }))),
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
            W::SumCaseAsm { index, datas, is_trait } => {
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
                // 原生 Nat 折叠：全具体构造步直接建 Nat(k)（`succ (Nat k)` →
                // `Nat (k+1)`、`zero` → `Nat 0`）；部分卡住链保持 SumCase
                match nat_step_value(typ, index, &ds) {
                    Some(n) => vals.push(v_xcell(bump.alloc(XCell::Nat(n)))),
                    None => vals.push(v_xcell(bump.alloc(XCell::SumCase {
                        typ,
                        index,
                        datas: bump.alloc_slice_fill_iter(ds),
                        is_trait,
                    }))),
                }
            }
            W::CallAsm { name, args, env } => {
                let body = vals.pop().expect("eval 栈：CallAsm 缺体值");
                if v_tag(body) == 7 && matches!(v_xcell_of(body), XCell::Match { .. }) {
                    // 实参项在捕获 env 下求值（独立草稿栈——eval_iter 入口
                    // 清空 work/vals/icits）
                    let mut argv: Vec<(V, Icit)> = Vec::with_capacity(args.len());
                    let mut w2: Vec<W<'a>> = Vec::new();
                    let mut v2: Vec<V> = Vec::new();
                    let mut i2: Vec<Icit> = Vec::new();
                    for (t, i) in args.iter() {
                        let av = eval_iter(
                            bump, spine, &mut w2, &mut v2, &mut i2, defs, metas, decl, mutable,
                            env, t,
                        );
                        argv.push((av, *i));
                    }
                    vals.push(v_xcell(bump.alloc(XCell::Call {
                        name,
                        args: bump.alloc_slice_copy(&argv),
                        body,
                    })));
                } else {
                    vals.push(body);
                }
            }
            W::MatchSel { cases, env } => {
                let sv = vals.pop().expect("eval 栈：MatchSel 缺 scrutinee");
                // L13：构造子头（SumCase / Nat）不 force 直接分派（深链
                // O(n²) 规避）；其余头先 force；无臂命中 / 非构造子头 →
                // 卡住 Match（无 pending）
                let is_ctor = v_tag(sv) == 7
                    && matches!(
                        v_xcell_of(sv),
                        XCell::SumCase { .. } | XCell::Nat(_)
                    );
                let s2 = if is_ctor { sv } else { force(bump, spine, defs, metas, decl, mutable, sv) };
                let dispatched = v_tag(s2) == 7
                    && matches!(
                        v_xcell_of(s2),
                        XCell::SumCase { .. } | XCell::Nat(_)
                    );
                if dispatched {
                    match eval_aux(bump, spine, defs, metas, decl, mutable, s2, env, cases) {
                        Some((body_tm, env2)) => {
                            // 分支选中：体在本 eval 循环里尾推
                            work.push(W::Tm(body_tm, env2));
                        }
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
        index: u32,
        datas: &'a [SumDataV<'a>],
        is_trait: bool,
    },
    /// done 栈顶自底向上是 (a0..a_{n-1}, body)：装配 `Tm::Call`（icit 取值
    /// 层 args 槽，与实参项 zip）。
    CallAsm {
        name: &'a str,
        icits: &'a [Icit],
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
    mutable: &RefCell<Mutable>,
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
                        // 原生 Nat → 等价的 succ/zero SumCase 链（参考版
                        // quote_nat：Nat 类型项查 decl["Nat"] 登记值并 quote，
                        // 缺失回退 U(0)——下游看到与一元链完全相同的形状）
                        XCell::Nat(k) => {
                            let nat_ty = decl.get("Nat").map(|e| e.val).unwrap_or_else(v_u0);
                            let nat_tm = quote_iter(
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
                                nat_ty,
                                None,
                            );
                            done.push(quote_nat_chain(bump, nat_tm, *k));
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
                            index,
                            datas,
                            is_trait,
                        } => {
                            tasks.push(QJob::SumCaseAsm { index: *index, datas, is_trait: *is_trait });
                            for d in datas.iter().rev() {
                                tasks.push(QJob::Q(d.val, level));
                            }
                            tasks.push(QJob::Q(*typ, level));
                        }
                        XCell::Call { name, args, body } => {
                            // icit 与实参值成对存放；任务携带需单独的 icit 切片
                            let icits: &'a [Icit] =
                                bump.alloc_slice_fill_iter(args.iter().map(|(_, i)| *i));
                            tasks.push(QJob::CallAsm { name, icits });
                            tasks.push(QJob::Q(*body, level));
                            for &(a, _) in args.iter().rev() {
                                tasks.push(QJob::Q(a, level));
                            }
                        }
                        XCell::Match {
                            scrutinee,
                            env: menv,
                            cases,
                        } => {
                            // 分支体在"捕获 env + fresh rigid 槽"下用
                            // **simpl_decl 存根表**重新求值（每 def 条目换成
                            // `Decl(name)` 卡住值、**Sum 类型值保留**——规则见
                            // [`declb_of`]），再以**真实表** quote。
                            let declb = declb_of(bump, decl);
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
                            // 函数部分可能是「陈旧应用链」：建链后其头 meta
                            // 被解成 λ（值里的位模式不随后续求解更新）。force
                            // 单独引函数部分会停在部分应用的 λ 上，照搬 App
                            // 拼接就产出 β-redex 项（参考版整值 force 经
                            // vAppSp 一路 β，永不产出）。故函数部分 force 为
                            // 闭包时，先按 β 语义应用本槽实参、再引应用结果。
                            let fval = spine.stack[h].f;
                            let ff = force(bump, spine, defs, metas, decl, mutable, fval);
                            if v_tag(ff) == 1 {
                                let c = v_clo_of(ff);
                                let applied = {
                                    let env = env_ext(bump, c.env, ea);
                                    eval_iter(
                                        bump, spine, work, vals, icits, defs, metas, decl,
                                        mutable, env, c.body,
                                    )
                                };
                                tasks.push(QJob::Q(applied, level));
                            } else {
                                tasks.push(QJob::App1(top_icit));
                                tasks.push(QJob::Q(ea, level));
                                tasks.push(QJob::Q(fval, level));
                            }
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
            QJob::SumCaseAsm { index, datas, is_trait } => {
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
                    index,
                    datas: bump.alloc_slice_fill_iter(ds),
                    is_trait,
                }));
            }
            QJob::CallAsm { name, icits } => {
                let n = icits.len();
                // done 自底向上是 (a0, ..., a_{n-1}, body)（实参按逆序压任务，
                // 故 a0 先引、body 最后引在最顶）
                let body = done.pop().expect("quote 栈：Call 缺体");
                let mut items: Vec<&'a Tm<'a>> = Vec::with_capacity(n);
                for _ in 0..n {
                    items.push(done.pop().expect("quote 栈：Call 缺实参"));
                }
                // 逐个弹出得 a_{n-1}..a0——反转回自然序再与 icits 对齐
                // （否则 2+ 实参的卡住 Call 会实参倒序、icit 错配）
                items.reverse();
                let args: Vec<(&'a Tm<'a>, Icit)> =
                    items.into_iter().zip(icits.iter().copied()).collect();
                done.push(bump.alloc(Tm::Call(name, bump.alloc_slice_copy(&args), body)));
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
                            // 非平凡链头：挂起引 f，ChainRun 续跑。f 可能是
                            // 「陈旧应用链」（建链后头 meta 被解成 λ）：force
                            // 单独引它停在部分应用的 λ 上，恢复点照搬 App 拼
                            // 接就产出 β-redex 项（参考版整值 force 经 vAppSp
                            // 一路 β，永不产出）。故 f force 为闭包时改为引
                            // 「f 应用本槽实参」的整值，恢复点直接取该结果为
                            // 已累计项（prev:None = 弹出为初始累计，不再拼接）。
                            let ff = force(bump, spine, defs, metas, decl, mutable, fi);
                            if v_tag(ff) == 1 {
                                let arg_v = spine.stack[i].a;
                                let c = v_clo_of(ff);
                                let applied = {
                                    let env = env_ext(bump, c.env, arg_v);
                                    eval_iter(
                                        bump, spine, work, vals, icits, defs, metas, decl,
                                        mutable, env, c.body,
                                    )
                                };
                                tasks.push(QJob::ChainRun {
                                    level,
                                    next: i + 1,
                                    end,
                                    f0,
                                    idx_node,
                                    prev: None,
                                });
                                tasks.push(QJob::Q(applied, level));
                            } else {
                                tasks.push(QJob::ChainRun {
                                    level,
                                    next: i + 1,
                                    end,
                                    f0,
                                    idx_node,
                                    prev: Some(prev),
                                });
                                tasks.push(QJob::Q(fi, level));
                            }
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

/// 原生 `Nat(k)` → 等价的 succ/zero `Tm::SumCase` 链（参考版 `quote_nat`：
/// `zero` = index 0 空字段；`succ^n` = n 层 index 1 单字段 `"n"`；迭代构造
/// 防深栈）。`nat_tm` 是已 quote 的 Nat 类型项。
fn quote_nat_chain<'a>(bump: &'a Bump, nat_tm: &'a Tm<'a>, k: u64) -> &'a Tm<'a> {
    let mut inner: &Tm<'a> =
        bump.alloc(Tm::SumCase { typ: nat_tm, index: 0, datas: &[], is_trait: false });
    for _ in 0..k {
        let datas: &'a [SumDataT<'a>] =
            bump.alloc([SumDataT { name: "n", val: inner, icit: Icit::Expl }]);
        inner = bump.alloc(Tm::SumCase { typ: nat_tm, index: 1, datas, is_trait: false });
    }
    inner
}

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
    /// 待比较子对（level 与 **fuel** 随对携带；弹出时先 force 双方再分派）。
    /// L13 的燃料语义：Decl 失配重 eval / Match 归约臂 `fuel-1`、SumCase
    /// 内层硬编码 100、其余臂透传（参考版 `unify(.., fuel)` 同款）。
    Pair(u32, V, V, u32),
    /// Π 余定义域的惰性比较（排在 dom 对之下——dom 不等即失败，cod 的
    /// eval 整个省掉）。
    EvalCod2(&'a Tm<'a>, Env<'a>, &'a Tm<'a>, Env<'a>, u32, u32),
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
        fuel: u32,
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
        fuel: u32,
    },
    /// 分支 pattern 相等检查（参考版逐分支在分支体之前）。
    MatchPattern(&'a PatternDetail, &'a PatternDetail),
}

/// 从 decl 表构建 declb 存根表（**Sum 类型值保留**——否则 SumCase 的 typ
/// 变 Decl 卡 pretty，参考版 `simpl_decl` 逐字对应；prim 槽随行）。
fn declb_of<'a>(bump: &'a Bump, decl: &Decls<'a>) -> Rc<Decls<'a>> {
    Rc::new(
        decl.iter()
            .map(|(k, e)| {
                let name = bump.alloc_str(k.as_str());
                (
                    k.clone(),
                    DeclEntry {
                        span: e.span,
                        typ_pretty: e.typ_pretty.clone(),
                        tm: bump.alloc(Tm::Decl(name)),
                        val: if v_tag(e.val) == 7
                            && matches!(v_xcell_of(e.val), XCell::Sum { .. })
                        {
                            e.val
                        } else {
                            v_xcell(bump.alloc(XCell::Decl { name }))
                        },
                        vty: e.vty,
                        prim: e.prim,
                    },
                )
            })
            .collect(),
    )
}

/// `v_app` 可否安全应用到该值（参考版 `is_appliable`）：λ / Flex / Rigid /
/// Decl / Obj / Call / 卡住 Match（应用 splice）；Sum / SumCase / Nat / 字面
/// 量 / Π / U 不可——η 展开对它们会 panic，须落 `_` 失配。
#[inline]
fn is_appliable(_spine: &Spine, v: V) -> bool {
    match v_tag(v) {
        0 | 1 | 2 | 5 => true,
        7 => matches!(
            v_xcell_of(v),
            XCell::Obj { .. } | XCell::Decl { .. } | XCell::Call { .. } | XCell::Match { .. }
        ),
        _ => false,
    }
}

/// 值里是否（保守地）不含未解 meta（参考版 `val_has_no_flex`：Lam/Pi/
/// Match/Call 一律报"含 flex"——体可能嵌 `Tm::Meta`）。**不 force**（与参考
/// 版同款：解开的 meta 在值里仍是 Flex 形态直到被 force 展开）。
fn val_has_no_flex(spine: &Spine, v: V) -> bool {
    match v_tag(v) {
        5 | 1 | 4 => false,
        0 | 3 | 6 => true,
        2 => {
            let h = v_spine_of(v);
            // 逐槽读 spine（collect 免分配版）
            let mut cur = h;
            loop {
                let e = &spine.stack[cur];
                if !val_has_no_flex(spine, e.a) {
                    return false;
                }
                if v_tag(e.f) == 2 {
                    cur = v_spine_of(e.f);
                } else {
                    return val_has_no_flex(spine, e.f);
                }
            }
        }
        7 => match v_xcell_of(v) {
            XCell::Lit(_) | XCell::Nat(_) => true,
            XCell::Obj { val, .. } => val_has_no_flex(spine, *val),
            XCell::Sum { params, .. } => params
                .iter()
                .all(|p| val_has_no_flex(spine, p.val) && val_has_no_flex(spine, p.ty)),
            XCell::SumCase { typ, datas, .. } => {
                val_has_no_flex(spine, *typ)
                    && datas.iter().all(|d| val_has_no_flex(spine, d.val))
            }
            XCell::Decl { .. } => true,
            XCell::Call { .. } | XCell::Match { .. } => false,
        },
        _ => true,
    }
}

/// 值是否为 prim 挂载的 decl 应用（裸 Decl 单元或 Decl 头链；参考版
/// `is_prim_application`）：force 后仍是这种形态 → 重 eval 只是同一 prim
/// 对语义相同实参的重复执行，不可能取得进展——视为不透明叶直接失败。
fn is_prim_application<'a>(decl: &Decls<'a>, spine: &Spine, v: V) -> bool {
    let name: &str = match v_tag(v) {
        7 => match v_xcell_of(v) {
            XCell::Decl { name } => *name,
            _ => return false,
        },
        2 => {
            let h = v_spine_of(v);
            // 头也须是 Decl 单元（Rigid / Flex / Obj 头链 → false，O(1)
            // 读顶端槽种类，免整趟走底）
            if spine.stack[h].hk != HK_DECL {
                return false;
            }
            let hd = spine.spine_head(h);
            match v_xcell_of(hd) {
                XCell::Decl { name } => *name,
                _ => return false,
            }
        }
        _ => return false,
    };
    decl.get(name).is_some_and(|e| e.prim.is_some())
}

/// 链（或裸单元）是否卡住投影 Obj 头——unify 的位相等捷径对它关闭
/// （参考版无 `(Obj, Obj)` 臂，同单元也须走 `_` → Err）。
#[inline]
fn is_objheaded(spine: &Spine, v: V) -> bool {
    head_kind(spine, v) == HK_OBJ
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
    mutable: &RefCell<Mutable>,
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
    // unify_sp 回落（参考版 `intersect` 的 None 臂：fuel 硬编码 100）：前缀
    // 对压栈（内先压 → 弹出外先，对齐 unify_sp 的递归序）。tag 7 不跳过：
    // 参考版对字面量实参照走 unify（恒败）——位相等的同单元也须分派。
    for k in 0..common {
        let (a1, _) = args1[k];
        let (a2, _) = args2[k];
        if a1.0 != a2.0 || v_tag(a1) == 7 {
            stack.push(UItem::Pair(l, a1, a2, 100));
        }
    }
    true
}

/// 异头 flex-flex（上游 `flexFlex`）：**短 spine 一侧优先**反演求解；反演
/// 失败则用另一侧求解（rhs 是整条 flex 值）——solve 含 L13 的 non-invertible
/// 常数解 fallback；该分支解后跑 trait 合成（参考版 `go` 的 Err 臂逐字）。
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
    mutable: &RefCell<Mutable>,
    ren: &mut RenBuf,
    gamma: u32,
    m1: u32,
    args1: &[(V, Icit)],
    v1: V,
    m2: u32,
    args2: &[(V, Icit)],
    v2: V,
    cxt: &Cxt<'a>,
    mach_ptr: *mut Machine,
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
        Some(mask) => matches!(
            solve_with_pren_bump(
                bump, spine, work, vals, icits, defs, metas, decl, mutable, ren, fa,
                aa.len() as u32, gamma, mask, va,
            ),
            SolveRes::Ok
        ),
        None => {
            if !matches!(
                solve_bump(
                    bump, spine, work, vals, icits, defs, metas, decl, mutable, ren, gamma, fb, ab,
                    vb,
                ),
                SolveRes::Ok
            ) {
                return false;
            }
            unsafe { (&mut *mach_ptr).solve_multi_trait_ref(bump, cxt, fb, false).is_ok() }
        }
    }
}

/// 同头链（unify_sp）的实参 lockstep 比较：长度失配即败；实参 icit 不比
/// （类型已定，上游同款）。位相等的实参对免比（tag 7 与 Obj 头链除外——
/// 字面量恒败、卡住投影走 `_` → Err）。fuel 随对透传。
fn unify_sp_lockstep<'a>(
    spine: &Spine,
    stack: &mut Vec<UItem<'a>>,
    l: u32,
    h1: usize,
    h2: usize,
    fuel: u32,
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
                stack.push(UItem::Pair(l, f1, f2, fuel));
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
                    stack.push(UItem::Pair(l, f1, f2, fuel));
                }
                i1 = v_spine_of(a1);
                i2 = v_spine_of(a2);
                continue;
            }
        }
        stack.push(UItem::Pair(l, a1, a2, fuel));
        if f1.0 != f2.0 {
            stack.push(UItem::Pair(l, f1, f2, fuel));
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
                return None; // flex / Decl / Obj 头：必非 Rigid，免走底
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
/// 工作表迭代。臂序与参考版 L13 `Infer::unify` 逐项对应（顺序敏感）：
/// Call/Call 同名 spine 快路径（无 Flex 免快照 / 有 Flex 三重快照回滚）→
/// Call 三条退化臂 → U → Π（icit 相等）→ Rigid/Rigid 同级 → 中性链分派
/// （flex×flex / Decl 同名 / 同头 lockstep）→ Decl 头拦截（对侧 Flex 先走
/// solve_flex_side；prim 不透明叶；fuel 重 eval）→ λ/η（**is_appliable
/// 守卫**）→ flex 求解（**Stuck → 约束挂账**）→ LiteralType → Sum/Sum →
/// SumCase（index 相等，内层 fuel=100）→ Nat/Nat + Nat 链 → Match/Match
/// （declb 存根表下重求值）→ 单侧 Match（归约 / Rigid eta-expansion 检查）
/// → Obj/Obj → 失配。**位相等捷径对 tag 7 与 Obj 头链关闭**（参考版对字
/// 面量无自反臂）。燃料：Decl 重 eval / Match 归约 `fuel-1`、SumCase 内层
/// 100、intersect 回落 100、其余透传。
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
    mutable: &RefCell<Mutable>,
    ren: &mut RenBuf,
    conv: &mut ConvScratch,
    constraints: &mut Vec<(V, V)>,
    l0: u32,
    t0: V,
    u0: V,
    fuel0: u32,
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
    stack.push(UItem::Pair(l0, t0, u0, fuel0));
    while let Some(item) = stack.pop() {
        let (l, t, u, fuel) = match item {
            UItem::Store(key) => {
                memo.insert(key);
                continue;
            }
            UItem::EvalCod2(b1, e1, b2, e2, l, fuel) => {
                let vt = {
                    let env = env_ext(bump, e1, v_lvl(l));
                    eval_iter(bump, spine, work, vals, icits, defs, metas, decl, mutable, env, b1)
                };
                let vu = {
                    let env = env_ext(bump, e2, v_lvl(l));
                    eval_iter(bump, spine, work, vals, icits, defs, metas, decl, mutable, env, b2)
                };
                stack.push(UItem::Pair(l + 1, vt, vu, fuel));
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
                fuel,
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
                stack.push(UItem::Pair(l + count, v1, v2, fuel));
                continue;
            }
            UItem::MatchStruct {
                e1,
                e2,
                c1,
                c2,
                declb,
                l,
                fuel,
            } => {
                // scrutinee 已比完（参考版 unify 的 Match/Match 臂 scrutinee
                // 递归之后）：cases 长度检查 → 逐分支（pattern → 分支体）。
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
                        fuel,
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
            UItem::Pair(l, t, u, fuel) => (l, t, u, fuel),
        };
        // 位相等：同一值。tag 7 与 Obj 头链例外（参考版对字面量无自反性、
        // 卡住投影走 (Obj,Obj) 臂）
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

        // —— Call/Call 同名 spine 快路径（参考版前置快路径）：同名且实参
        // spine 可合一 → 相等（内联体是 name+args 的纯函数）。无 Flex 免快
        // 照；有 Flex 三重快照（meta / trait_metas / 约束）失败回滚——中途
        // 可能已解出 meta。失败落入体比较。——
        if v_tag(t) == 7
            && v_tag(u) == 7
            && matches!(v_xcell_of(t), XCell::Call { .. })
            && matches!(v_xcell_of(u), XCell::Call { .. })
        {
            let (n1, a1) = match v_xcell_of(t) {
                XCell::Call { name, args, .. } => (name, args),
                _ => unreachable!(),
            };
            let (n2, a2) = match v_xcell_of(u) {
                XCell::Call { name, args, .. } => (name, args),
                _ => unreachable!(),
            };
            if n1 == n2 {
                let has_flex = a1.iter().any(|&(a, _)| !val_has_no_flex(spine, a))
                    || a2.iter().any(|&(a, _)| !val_has_no_flex(spine, a));
                // 子 unify（实参对按参考 unify_sp 尾先比较序：自然序压、
                // 逆序弹；首个对作入口，其余留子栈）。有 Flex 时三重快照
                //（meta / trait_metas / 约束），失败回滚——中途可能已解出
                // meta。conv 用全新草稿（子调用会清 memo）。
                let ok = if !has_flex {
                    // 无 Flex：子 unify 只比较基值，不可能改求解状态——免快照
                    let mut conv_fresh = ConvScratch::default();
                    let mut sub: Vec<UItem<'a>> = Vec::new();
                    let mut terr: Option<String> = None;
                    let mut first = true;
                    let mut entry = (l, t, u);
                    for ((x, _), (y, _)) in a1.iter().zip(a2.iter()) {
                        if x.0 != y.0 || v_tag(*x) == 7 {
                            if first {
                                entry = (l, *x, *y);
                                first = false;
                            } else {
                                sub.push(UItem::Pair(l, *x, *y, fuel));
                            }
                        }
                    }
                    if first {
                        true // 全部位相等 → spine 相等
                    } else {
                        unify_iter(
                            bump, spine, work, &mut sub, vals, icits, defs, metas, decl, mutable,
                            ren, &mut conv_fresh, &mut Vec::new(), entry.0, entry.1, entry.2,
                            fuel, cxt, mach_ptr, &mut terr,
                        )
                    }
                } else {
                    let meta_snapshot = metas.clone();
                    let tm_snapshot = unsafe { (*mach_ptr).trait_metas.clone() };
                    let mc_snapshot = constraints.clone();
                    let mut conv_fresh = ConvScratch::default();
                    let mut sub: Vec<UItem<'a>> = Vec::new();
                    let mut terr: Option<String> = None;
                    let mut cons: Vec<(V, V)> = Vec::new();
                    let mut first = true;
                    let mut entry = (l, t, u);
                    for ((x, _), (y, _)) in a1.iter().zip(a2.iter()) {
                        if x.0 != y.0 || v_tag(*x) == 7 {
                            if first {
                                entry = (l, *x, *y);
                                first = false;
                            } else {
                                sub.push(UItem::Pair(l, *x, *y, fuel));
                            }
                        }
                    }
                    let ok = if first {
                        true
                    } else {
                        unify_iter(
                            bump, spine, work, &mut sub, vals, icits, defs, metas, decl, mutable,
                            ren, &mut conv_fresh, &mut cons, entry.0, entry.1, entry.2, fuel,
                            cxt, mach_ptr, &mut terr,
                        )
                    };
                    if ok {
                        constraints.extend(cons);
                    } else {
                        // 回滚（mutable 的 prim 副作用不回滚——参考版同款）
                        metas.clone_from(&meta_snapshot);
                        unsafe { (*mach_ptr).trait_metas = tm_snapshot; }
                    }
                    ok
                };
                if ok {
                    if memo_on {
                        memo.insert((t.0, u.0));
                    }
                    continue;
                }
                // 失败：落入下方体比较（退化臂）
            }
        }

        // —— Call 三条退化臂（参考臂 0.5）：同名快路径失败或异名 → 体比较
        //——
        if v_tag(t) == 7 && v_tag(u) == 7 {
            if let (XCell::Call { body: b1, .. }, XCell::Call { body: b2, .. }) =
                (v_xcell_of(t), v_xcell_of(u))
            {
                if memo_on {
                    stack.push(UItem::Store((t.0, u.0)));
                }
                stack.push(UItem::Pair(l, *b1, *b2, fuel));
                continue;
            }
        }
        if v_tag(t) == 7 {
            if let XCell::Call { body: b1, .. } = v_xcell_of(t) {
                if memo_on {
                    stack.push(UItem::Store((t.0, u.0)));
                }
                stack.push(UItem::Pair(l, *b1, u, fuel));
                continue;
            }
        }
        if v_tag(u) == 7 {
            if let XCell::Call { body: b2, .. } = v_xcell_of(u) {
                if memo_on {
                    stack.push(UItem::Store((t.0, u.0)));
                }
                stack.push(UItem::Pair(l, t, *b2, fuel));
                continue;
            }
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
                stack.push(UItem::EvalCod2(p.body, p.env, q.body, q.env, l, fuel));
                stack.push(UItem::Pair(l, p.dom, q.dom, fuel));
                continue;
            }
        }
        // —— Rigid/Rigid（参考臂 3）：同级比实参 spine（裸×裸自反成立），
        // 异级落到后续臂 ——
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
                        m2, &a2, t, cxt, mach_ptr,
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
            // —— Decl 头链的同名判定：同名 lockstep 比实参；异名**不直接
            // 失配**——落入下方 (Decl,_) 拦截的 fuel 重 eval（参考臂序）——
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
                        if !unify_sp_lockstep(spine, stack, l, h1, h2, fuel) {
                            return false;
                        }
                        continue;
                    }
                    // 异名：跳出链分派，走 Decl 拦截
                }
            } else {
                // 同头判定：位相等（同变量 / 同 meta）；Obj 头交 (Obj,Obj) 臂
                if hd1.0 == hd2.0 && !is_objheaded(spine, hd1) {
                    if memo_on {
                        stack.push(UItem::Store((t.0, u.0)));
                    }
                    if !unify_sp_lockstep(spine, stack, l, h1, h2, fuel) {
                        return false;
                    }
                    continue;
                }
                // 异头：一侧 flex 头 → 该侧 solve（参考臂 9/10 的链形态，
                // solve_flex_side 语义：Stuck 挂账约束）
                if f1 || f2 {
                    let (mv, h, rhs) = if f1 {
                        (v_meta_of(hd1), h1, u)
                    } else {
                        (v_meta_of(hd2), h2, t)
                    };
                    let mut args = std::mem::take(&mut conv.scratch1);
                    args.clear();
                    spine.collect_args(h, &mut args);
                    let ok = solve_flex_side_bump(
                        bump, spine, work, vals, icits, defs, metas, decl, mutable, ren,
                        constraints, l, mv, &args, t, u, rhs, cxt, mach_ptr, trait_err,
                    );
                    conv.scratch1 = args;
                    if ok {
                        if memo_on {
                            memo.insert((t.0, u.0));
                        }
                        continue;
                    }
                    return false;
                }
                // 双刚性异级 / Obj 头组合 → 失配（(Obj,Obj) 由末段臂处理，
                // 走不到这里——两侧都是链且头异：异头 Obj 不可能同为 Obj 臂
                // 的输入形态之外）
                return false;
            }
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
        // —— (Decl, _) / (_, Decl) 拦截（参考臂 3.6，在 η/flex 臂之前）：
        // 对侧是 Flex → 直接 solve_flex_side（None 返回的 prim 永不展开，
        // 烧燃料无意义）；prim 应用 = 不透明叶；否则 fuel>0 时 quote→eval
        // 重 eval（重读 decl 表——fake_bind 存根被真值覆盖后 force 仍卡在
        // 旧值，重 eval 才能看到真值）——
        if is_decl_val(spine, t) || is_decl_val(spine, u) {
            let (dv, ov, flip) = if is_decl_val(spine, t) { (t, u, false) } else { (u, t, true) };
            // 对侧 Flex → solve_flex_side
            let other_flex = match v_tag(ov) {
                5 => Some(v_meta_of(ov)),
                2 => {
                    let hd = spine.spine_head(v_spine_of(ov));
                    if v_tag(hd) == 5 {
                        Some(v_meta_of(hd))
                    } else {
                        None
                    }
                }
                _ => None,
            };
            if let Some(m) = other_flex {
                let mut args: Vec<(V, Icit)> = match v_tag(ov) {
                    5 => Vec::new(),
                    _ => {
                        let mut a = Vec::new();
                        spine.collect_args(v_spine_of(ov), &mut a);
                        a
                    }
                };
                let ok = solve_flex_side_bump(
                    bump, spine, work, vals, icits, defs, metas, decl, mutable, ren,
                    constraints, l, m, &args, t, u, dv, cxt, mach_ptr, trait_err,
                );
                if ok {
                    if memo_on {
                        memo.insert((t.0, u.0));
                    }
                    continue;
                }
                return false;
            }
            if is_prim_application(decl, spine, dv) {
                return false; // 不透明叶
            }
            if fuel == 0 {
                return false;
            }
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
                decl,
                mutable,
                l,
                dv,
                None,
            );
            let dv2 = eval_iter(bump, spine, work, vals, icits, defs, metas, decl, mutable, cxt.env, q);
            let _ = flip;
            if is_decl_val(spine, t) {
                stack.push(UItem::Pair(l, dv2, u, fuel - 1));
            } else {
                stack.push(UItem::Pair(l, t, dv2, fuel - 1));
            }
            continue;
        }
        // —— λ / η（参考臂 6/7/8；在 flex 求解之前：Flex vs λ 走 η）。
        // η 的应用侧须 **is_appliable**（参考版守卫——对 Sum/SumCase/Nat/
        // 字面量应用会 panic，须落 `_` 失配）——
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
            stack.push(UItem::Pair(l + 1, vt, vu, fuel));
            continue;
        }
        if v_tag(u) == 1 && is_appliable(spine, t) {
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
            stack.push(UItem::Pair(l + 1, vt, vu, fuel));
            continue;
        }
        if v_tag(t) == 1 && is_appliable(spine, u) {
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
            stack.push(UItem::Pair(l + 1, vt, vu, fuel));
            continue;
        }
        // —— flex 求解（参考臂 4/5/9/10 的裸形态；solve_flex_side 语义：
        // Stuck → 约束挂账后继续）——
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
                            u, m2, &a2, t, cxt, mach_ptr,
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
                    let ok = solve_flex_side_bump(
                        bump, spine, work, vals, icits, defs, metas, decl, mutable, ren,
                        constraints, l, m, &a1, t, u, u, cxt, mach_ptr, trait_err,
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
                    let ok = solve_flex_side_bump(
                        bump, spine, work, vals, icits, defs, metas, decl, mutable, ren,
                        constraints, l, m, &a2, t, u, t, cxt, mach_ptr, trait_err,
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
                    // 非 flex：落到字面量 / Sum / SumCase / Match 臂
                }
            }
        }
        // —— (LiteralType, LiteralType)（参考臂 11）——
        if v_tag(t) == 6 && v_tag(u) == 6 {
            continue;
        }
        // —— Sum/Sum（参考臂 13）：同名即逐参数（含索引）值合一；zip 语义
        // （参数数不等取 min——参考版同款）；异名失配 ——
        if v_tag(t) == 7 && v_tag(u) == 7 {
            let (xt, xu) = (v_xcell_of(t), v_xcell_of(u));
            // —— Decl/Decl 同名（参考臂 3.5 裸形态）：空 spine 即成立；异名
            // 已在上方拦截臂处理（走不到这里）——
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
                        stack.push(UItem::Pair(l, a.val, b.val, fuel));
                    }
                    continue;
                }
                return false; // 异名 Sum：参考版无后续可命中臂 → Err
            }
            // —— SumCase/SumCase（参考臂 14）：index 相等才比；typ 与 datas
            // 都比（内层硬编码 fuel 100——参考版同款）——
            if let (
                XCell::SumCase {
                    typ: ty1,
                    index: c1,
                    datas: d1,
                    ..
                },
                XCell::SumCase {
                    typ: ty2,
                    index: c2,
                    datas: d2,
                    ..
                },
            ) = (xt, xu)
            {
                if c1 == c2 {
                    // pop 序 = typ, d0, d1, ...（参考版执行序）
                    for (a, b) in d1.iter().zip(d2.iter()).rev() {
                        stack.push(UItem::Pair(l, a.val, b.val, 100));
                    }
                    stack.push(UItem::Pair(l, *ty1, *ty2, 100));
                    continue;
                }
                return false; // 异构造子：参考版无后续可命中臂 → Err
            }
            // —— Nat/Nat + Nat/SumCase 链（参考臂 15/15.5）：定义上相等
            // 当且仅当 k == 链长（仅 Nat sum 类型；unify_nat_chain 递归）——
            if let (XCell::Nat(k), XCell::Nat(j)) = (xt, xu) {
                if k == j {
                    continue;
                }
                return false;
            }
            if let (XCell::Nat(k), XCell::SumCase { typ, index, datas, .. }) = (xt, xu) {
                let tf = force(bump, spine, defs, metas, decl, mutable, *typ);
                if is_nat_sum_v(tf) {
                    match (*index, datas.len()) {
                        (0, 0) => {
                            if *k == 0 {
                                continue;
                            }
                            return false;
                        }
                        (1, 1) => {
                            if *k > 0 {
                                let prev = v_xcell(bump.alloc(XCell::Nat(k - 1)));
                                stack.push(UItem::Pair(l, prev, datas[0].val, fuel));
                                continue;
                            }
                            return false;
                        }
                        _ => return false,
                    }
                }
                return false;
            }
            if let (XCell::SumCase { typ, index, datas, .. }, XCell::Nat(k)) = (xt, xu) {
                let tf = force(bump, spine, defs, metas, decl, mutable, *typ);
                if is_nat_sum_v(tf) {
                    match (*index, datas.len()) {
                        (0, 0) => {
                            if *k == 0 {
                                continue;
                            }
                            return false;
                        }
                        (1, 1) => {
                            if *k > 0 {
                                let prev = v_xcell(bump.alloc(XCell::Nat(k - 1)));
                                stack.push(UItem::Pair(l, datas[0].val, prev, fuel));
                                continue;
                            }
                            return false;
                        }
                        _ => return false,
                    }
                }
                return false;
            }
            // —— Match/Match（参考臂 16）：scrutinee 最先合一（真实副作用
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
                    fuel,
                });
                stack.push(UItem::Pair(l, *s1, *s2, fuel));
                continue;
            }
        }
        // —— 单侧 Match（参考末段臂）：force scrutinee → 构造子头则 eval_aux
        // 归约（fuel-1）再比；否则 Rigid/Rigid 空 spine 的 eta-expansion
        // 检查（全分支是 Any/Bind 且体是 Var(0) 才相等——soundness 修复）——
        {
            let mcell = if v_tag(t) == 7 && matches!(v_xcell_of(t), XCell::Match { .. }) {
                Some((t, u))
            } else if v_tag(u) == 7 && matches!(v_xcell_of(u), XCell::Match { .. }) {
                Some((u, t))
            } else {
                None
            };
            if let Some((mv, other)) = mcell {
                let (s, env_m, cases) = match v_xcell_of(mv) {
                    XCell::Match { scrutinee, env, cases } => (*scrutinee, *env, cases),
                    _ => unreachable!(),
                };
                let s2 = force(bump, spine, defs, metas, decl, mutable, s);
                let is_ctor = v_tag(s2) == 7
                    && matches!(v_xcell_of(s2), XCell::SumCase { .. } | XCell::Nat(_));
                if is_ctor {
                    if let Some((tm_b, env_b)) =
                        eval_aux(bump, spine, defs, metas, decl, mutable, s2, env_m, cases)
                    {
                        let reduced =
                            eval_iter(bump, spine, work, vals, icits, defs, metas, decl, mutable, env_b, tm_b);
                        if fuel > 0 {
                            stack.push(UItem::Pair(l, reduced, other, fuel - 1));
                            continue;
                        }
                    }
                }
                // eta-expansion 检查：scrutinee 与对侧都是裸 Rigid 同级
                if v_tag(s2) == 0 && v_tag(other) == 0 && v_lvl_of(s2) == v_lvl_of(other) {
                    let is_eta = !cases.is_empty()
                        && cases.iter().all(|(pat, body)| {
                            let binds_scrutinee = matches!(
                                pat,
                                PatternDetail::Any(..) | PatternDetail::Bind(_)
                            );
                            binds_scrutinee && matches!(body, Tm::Var(0))
                        });
                    if is_eta {
                        continue;
                    }
                }
                return false;
            }
        }
        // —— (Obj, Obj) 合同臂（参考臂 17）：字段名同 ⇒ 比接收者 + spine
        // 实参 ——
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
            stack.push(UItem::Pair(l, o1, o2, fuel));
            match (v_tag(t), v_tag(u)) {
                (7, 7) => {}
                (2, 2) => {
                    if !unify_sp_lockstep(spine, stack, l, v_spine_of(t), v_spine_of(u), fuel) {
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

/// 值是否 Decl 头（裸 Decl 单元或 Decl 头链）——unify 的 (Decl,_) 拦截判据。
#[inline]
fn is_decl_val(spine: &Spine, v: V) -> bool {
    head_kind(spine, v) == HK_DECL
}

/// qualified path 拼接（参考版 `qualified_path_str`）：`a.b.c` 形的 Obj 链
/// → 全路径字符串；非 Var/Obj 形态 None。
fn qualified_path_str(x: &Raw, field: &str) -> Option<SmolStr> {
    match x {
        Raw::Var(name) => Some(SmolStr::new(format!("{}.{}", name.data, field))),
        Raw::Obj(inner, Some(seg)) => qualified_path_str(inner.as_ref(), &seg.data)
            .map(|p| SmolStr::new(format!("{p}.{field}"))),
        _ => None,
    }
}

/// 路径首段切分（参考版 `split_first_segment`）。
fn split_first_segment(path: &SmolStr) -> Option<(SmolStr, SmolStr)> {
    let s = path.as_str();
    let dot = s.find('.')?;
    Some((SmolStr::new(&s[..dot]), SmolStr::new(&s[dot + 1..])))
}

/// 值的实例匹配头键（参考版 typeclass.rs `head_key` 的快版对应）：
/// Decl 头给名字、Sum 给类型名；其余（Rigid 等）None → 通配桶。
fn head_key_v(spine: &Spine, v: V) -> Option<SmolStr> {
    match v_tag(v) {
        7 => match v_xcell_of(v) {
            XCell::Decl { name } => Some(SmolStr::new(*name)),
            XCell::Sum { name, .. } => Some(SmolStr::new(*name)),
            _ => None,
        },
        2 => {
            let h = v_spine_of(v);
            // 链头能给出头键的只有 Decl（Sum 不可应用，进不了链）；顶端槽
            // 种类非 Decl 时 O(1) 落通配桶，免整趟走底
            if spine.stack[h].hk != HK_DECL {
                return None;
            }
            let hd = spine.spine_head(h);
            match v_xcell_of(hd) {
                XCell::Decl { name } => Some(SmolStr::new(*name)),
                _ => None,
            }
        }
        _ => None,
    }
}

/// `solve_flex_side` 的快版（参考版 unification.rs:879）：solve 成功 /
/// **Stuck → 约束挂账后视为成功** / 其余失败；随后跑 trait 合成（失败 →
/// trait_err 上抛）。返回 false = unify 失败。
#[allow(clippy::too_many_arguments)]
fn solve_flex_side_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    decl: &Decls<'a>,
    mutable: &RefCell<Mutable>,
    ren: &mut RenBuf,
    constraints: &mut Vec<(V, V)>,
    l: u32,
    m: u32,
    args: &[(V, Icit)],
    t: V,
    u: V,
    rhs: V,
    cxt: &Cxt<'a>,
    mach_ptr: *mut Machine,
    trait_err: &mut Option<String>,
) -> bool {
    match solve_bump(
        bump, spine, work, vals, icits, defs, metas, decl, mutable, ren, l, m, args, rhs,
    ) {
        SolveRes::Fail => return false,
        SolveRes::Stuck => constraints.push((t, u)),
        SolveRes::Ok => {}
    }
    let tr = unsafe { (&mut *mach_ptr).solve_multi_trait_ref(bump, cxt, m, false) };
    if let Err(e) = tr {
        *trait_err = Some(e);
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
    mutable: &RefCell<Mutable>,
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

/// solve 的三态结果（参考版 `Result<(), UnifyError>` 的压扁）：`Ok` = 解
/// 写入；`Stuck` = 反演失败（spine 含未解 meta 等）且常数解 fallback 也
/// 不适用——调用方（solve_flex_side）挂账约束后视为成功；`Fail` = 硬失败
/// （occurs/scope/剪枝不可行）。
enum SolveRes {
    Ok,
    Stuck,
    Fail,
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
    mutable: &RefCell<Mutable>,
    ren: &mut RenBuf,
    m: u32,
    dom: u32,
    gamma: u32,
    mask: Vec<Option<Icit>>, // invert 的非线性掩码（空 vec = 线性）
    rhs: V,
) -> SolveRes {
    let mty = match &metas[m as usize] {
        MetaEntry::Unsolved(v, ..) => *v,
        _ => unreachable!(), // 只对未解 meta 求解
    };
    // 非线性 spine：检查非线性的变量槽位可以从 meta 类型里剪掉
    if !mask.is_empty()
        && prune_ty_bump(bump, spine, work, vals, icits, defs, metas, decl, mutable, &mask, mty)
            .is_none()
    {
        return SolveRes::Fail;
    }
    let Some(tm) = rename_iter(
        bump, spine, work, vals, icits, defs, ren, metas, decl, mutable, Some(m), dom, gamma, rhs,
    ) else {
        return SolveRes::Fail;
    };
    let lam_tm = lams_from_ty(
        bump, spine, work, vals, icits, defs, metas, decl, mutable, dom, mty, tm,
    );
    let sol = eval_iter(
        bump, spine, work, vals, icits, defs, metas, decl, mutable, EMPTY_ENV, lam_tm,
    );
    metas[m as usize] = MetaEntry::Solved(sol, mty);
    SolveRes::Ok
}

/// solve = invert + solve_with_pren；invert 失败时走 **non-invertible
/// 常数解 fallback**（参考版 L13 `solve` 的 Stuck 分支）：rhs 对空 renaming
/// 可 rename（即闭于上下文变量与 spine 作用域 meta）时，解是 meta 上下文
/// 上的常值函数——λ 层数取 `min(spine 长度, meta 类型 Π 链长)`（病态程序
/// 的 spine 可能超长，lams 对超出会 panic）。fallback 也不行 → Stuck。
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
    mutable: &RefCell<Mutable>,
    ren: &mut RenBuf,
    gamma: u32,
    m: u32,
    args: &[(V, Icit)],
    rhs: V,
) -> SolveRes {
    match invert_bump(bump, spine, defs, metas, decl, mutable, ren, args) {
        Some(mask) => solve_with_pren_bump(
            bump, spine, work, vals, icits, defs, metas, decl, mutable, ren, m, args.len() as u32,
            gamma, mask, rhs,
        ),
        None => {
            // 常数解 fallback：空 renaming rename rhs
            let Some(renamed) = rename_iter(
                bump, spine, work, vals, icits, defs, ren, metas, decl, mutable, None, 0, gamma,
                rhs,
            ) else {
                return SolveRes::Stuck;
            };
            let mty = match &metas[m as usize] {
                MetaEntry::Unsolved(v, ..) => *v,
                _ => unreachable!(),
            };
            // meta 类型的前缀 Π 链长（逐步应用到 vvar）
            let mut pi_len = 0u32;
            let mut cur = force(bump, spine, defs, metas, decl, mutable, mty);
            while v_tag(cur) == 4 {
                let cell = v_pi_of(cur);
                let env = env_ext(bump, cell.env, v_lvl(pi_len));
                cur = eval_iter(bump, spine, work, vals, icits, defs, metas, decl, mutable, env, cell.body);
                pi_len += 1;
            }
            let dom = (args.len() as u32).min(pi_len);
            let lam_tm = lams_from_ty(
                bump, spine, work, vals, icits, defs, metas, decl, mutable, dom, mty, renamed,
            );
            let sol = eval_iter(
                bump, spine, work, vals, icits, defs, metas, decl, mutable, EMPTY_ENV, lam_tm,
            );
            metas[m as usize] = MetaEntry::Solved(sol, mty);
            SolveRes::Ok
        }
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
    mutable: &RefCell<Mutable>,
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
                        XCell::Nat(k) => {
                            // 原生 Nat：闭 Nat 无变量可 rename；按 quote_nat
                            // 同构展开（Nat 类型项查 decl["Nat"] 登记值并
                            // quote，缺失回退 U(0)——参考版 rename 的 Nat 臂）
                            let nat_ty =
                                decl.get("Nat").map(|e| e.val).unwrap_or_else(v_u0);
                            let nat_tm = quote_iter(
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
                                dom,
                                nat_ty,
                                None,
                            );
                            done.push(quote_nat_chain(bump, nat_tm, *k));
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
                            index,
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
                                index: *index,
                                datas: bump.alloc_slice_fill_iter(ds),
                                is_trait: *is_trait,
                            }));
                        }
                        XCell::Call { name, args, body } => {
                            // 内联调用：实参逐个 rename（icit 随行）+ 体 rename
                            //（参考版 rename 的 Call 臂）
                            let mut argv: Vec<(&'a Tm<'a>, Icit)> =
                                Vec::with_capacity(args.len());
                            for &(a, i) in args.iter() {
                                let at = rename_iter(
                                    bump, spine, work, vals, icits, defs, ren, metas, decl,
                                    mutable, occ, dom, cod, a,
                                )?;
                                argv.push((at, i));
                            }
                            let bt = rename_iter(
                                bump, spine, work, vals, icits, defs, ren, metas, decl, mutable,
                                occ, dom, cod, *body,
                            )?;
                            done.push(bump.alloc(Tm::Call(
                                name,
                                bump.alloc_slice_copy(&argv),
                                bt,
                            )));
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
    mutable: &RefCell<Mutable>,
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
    mutable: &RefCell<Mutable>,
    mask: &[Option<Icit>], // 内先序
    m: u32,
) -> Option<u32> {
    let (mty, origin) = match &metas[m as usize] {
        MetaEntry::Unsolved(v, _, o, _) => (*v, *o),
        _ => unreachable!(), // 只对未解 meta 剪枝
    };
    let pruned_tm = prune_ty_bump(
        bump, spine, work, vals, icits, defs, metas, decl, mutable, mask, mty,
    )?;
    let prunedty = eval_iter(
        bump, spine, work, vals, icits, defs, metas, decl, mutable, EMPTY_ENV, pruned_tm,
    );
    let mp = metas.len() as u32;
    // 参考版：new_meta(prunedty, 空 Cxt（只塞 decl）, origin_ty)
    let snap: Rc<MetaSnap<'static>> = unsafe {
        std::mem::transmute(Rc::new(MetaSnap {
            lvl: 0,
            types: None,
            decls: Rc::new(decl.clone()),
            cxt: std::mem::transmute::<Cxt<'_>, Cxt<'static>>(Cxt::empty()),
        }))
    };
    metas.push(MetaEntry::Unsolved(prunedty, snap, origin, empty_span(())));
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
    mutable: &RefCell<Mutable>,
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
    mutable: &RefCell<Mutable>,
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
    /// 层级 →（类型值, binder 名源码 span）（map2：按层级持久，refresh 的
    /// get_by_key2_mut 目标；名字查类型经此中转，refresh 更新即生效。
    /// span 为观察面 def_span（局部 hover/goto，合成 binder 记零 span）；
    /// 并入元组而非平行表——Names 随 bind 链 COW 克隆，三表克隆实测 +5% 。
    by_lvl: FxHashMap<u32, (V, crate::parser_lib::Span<()>)>,
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
    mutable: RefCell<Mutable>,
    /// 求解 Stuck 挂账（参考版 `Infer.meta_contrains`）：unify_catch
    /// 入口/出口清空；flex 求解遇 Stuck 时压入。
    constraints: Vec<(V, V)>,
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
    /// trait 型 Unsolved meta 登记表（参考版 `Infer.trait_metas`）：
    /// `fresh_meta` 对 trait Sum 走此表，`solve_multi_trait` 只扫它。
    /// （每轮清空。）
    trait_metas: Vec<u32>,
    /// 算符方法恢复表（参考版 `Infer.symbol_table`）：`(helper 名, 实参
    /// 个数) → 算符符号`，inherent impl 的算符名方法登记。export 的 Call
    /// 臂在此命中时产 `CTm::OpCall`。（每轮清空。）
    symbol_table: FxHashMap<(SmolStr, usize), SmolStr>,
    /// 文件局部 import 别名（参考版 `Infer.import_map`，挂 Infer 不挂
    /// Cxt 以免跨文件泄漏）：alias → decl 全键。（每轮清空。）
    import_map: FxHashMap<SmolStr, SmolStr>,
    /// trait 方法 elaboration 缓存（参考版 `Infer.trait_method_cache`；
    /// clone 时清空）：`(类型头, 方法名) → (导出项 Rc, twin Tm, twin V)`。
    /// Raw::Tm 的指针导入表随条目登记。（每轮清空。）
    trait_method_cache: FxHashMap<(SmolStr, SmolStr), (Rc<CTm>, Rc<CVal>, Rc<CTm>)>,
    /// **指针导入表**：`export` / `v_to_ref_val` 产出的参考版 Rc 指针 →
    /// 本机 Tm/V。class Phase B 的 `Raw::Tm` 检查臂与 trait 方法缓存经此
    /// 取回本机结果（export 每次产出新 Rc，指针唯一；每轮清空——本轮
    /// bump 值跨轮消亡）。
    tm_import: FxHashMap<usize, &'static Tm<'static>>,
    val_import: FxHashMap<usize, V>,
    // ── 观察面（LSP 接线阶段 1，docs/lsp-twin-wiring-2026-09.md）──
    // 与参考版 `Infer` 同名表逐字段同契约（push 期渲染成 owned String；
    // bump 域 Tm 轮末即弃）。每轮 `clear_round` 清空，`run_decls` 返回后
    // 由 LSP 读取——本轮声明的本轮快照，与 bump 生命周期严格同界。
    pub(crate) hover_table: Vec<(crate::parser_lib::Span<()>, crate::parser_lib::Span<()>, String)>,
    pub(crate) completion_table: Vec<(crate::parser_lib::Span<()>, SmolStr)>,
    pub(crate) inlay_hint_table: Vec<(u32, String)>,
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
            mutable: RefCell::new(Mutable { map: FxHashMap::default(), replay: FxHashMap::default() }),
            constraints: Vec::new(),
            eval_work: Vec::new(),
            quote_tasks: Vec::new(),
            quote_done: Vec::new(),
            quote_work: Vec::new(),
            unify_work: Vec::new(),
            unify_stack: Vec::new(),
            quote_memo: FxHashMap::default(),
            tstate: TraitState::default(),
            trait_metas: Vec::new(),
            symbol_table: FxHashMap::default(),
            import_map: FxHashMap::default(),
            trait_method_cache: FxHashMap::default(),
            tm_import: FxHashMap::default(),
            val_import: FxHashMap::default(),
            hover_table: Vec::new(),
            completion_table: Vec::new(),
            inlay_hint_table: Vec::new(),
        }
    }

    /// 每轮 reset：metacontext + 名字表/类型表/轨迹 + 环境区域 + 可变全局
    /// 表全部清空。spine 栈同轮清空（保容量）——tag-2 句柄只被当轮 bump 值 /
    /// metas / defs 持有，轮边界后无任何旧句柄可达。decl 表随 Cxt 快照
    /// 消亡（参考版每次调用新建 Cxt 同款）。L13 增量：trait_metas /
    /// symbol_table / import_map / trait 方法缓存 / 指针导入表一并清空
    ///（均为 per-run 状态——参考版 Infer::clone 的重置面 + 新建 Infer）。
    fn clear_round(&mut self) {
        self.metas.clear();
        self.defs.clear();
        self.mutable.borrow_mut().clear();
        self.constraints.clear();
        self.spine.stack.clear();
        self.tstate = TraitState::default();
        self.trait_metas.clear();
        self.symbol_table.clear();
        self.import_map.clear();
        self.trait_method_cache.clear();
        self.tm_import.clear();
        self.val_import.clear();
        self.clear_observation_tables();
    }

    /// 观察表清空（两个调用点：轮入口 `clear_round`；prelude 装载收尾——
    /// 参考版加载器对缓存态清三张表同款，用户文件查询只见用户段条目）。
    fn clear_observation_tables(&mut self) {
        self.hover_table.clear();
        self.completion_table.clear();
        self.inlay_hint_table.clear();
    }

    // ── 观察面（与参考版 `Infer::push_hover` / `hover_entry_at` 同契约）──

    /// push 期把类型渲染成 owned String 入表：走本机 println/错误消息同款
    /// `quote → export → pretty_tm` 管线（parity 已证该管线与参考版逐字节
    /// 一致）。bump 域 Tm 出表即弃，LSP 跨轮读到的只是字符串快照。
    pub(crate) fn push_hover<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t_span: crate::parser_lib::Span<()>,
        def_span: crate::parser_lib::Span<()>,
        v: V,
    ) {
        let tm = self.quote(bump, cxt, cxt.lvl, v);
        let names = types_names_list(cxt.types);
        let rendered = pretty_tm(0, names, &export(&self.symbol_table, tm));
        self.hover_table.push((t_span, def_span, rendered));
    }

    /// 全局名使用处 hover：优先复用登记处缓存串（零渲染，见
    /// [`DeclEntry::typ_pretty`]）；无缓存时现渲染兜底。
    fn push_hover_cached<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t_span: crate::parser_lib::Span<()>,
        e: &DeclEntry<'a>,
    ) {
        let rendered = match &e.typ_pretty {
            Some(s) => (**s).clone(),
            None => {
                let tm = self.quote(bump, cxt, cxt.lvl, e.vty);
                pretty_tm(0, types_names_list(cxt.types), &export(&self.symbol_table, tm))
            }
        };
        self.hover_table.push((t_span, e.span, rendered));
    }

    /// 观察面 inlay（参考版 `push_inlay_hint` 同口径）：含未解 meta 跳过，
    /// label 超 80 字符截断。
    pub(crate) fn push_inlay_hint<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        offset: u32,
        v: V,
    ) {
        let tm = self.quote(bump, cxt, cxt.lvl, v);
        if no_metas(bump, self, cxt, tm).is_some() {
            return;
        }
        let names = types_names_list(cxt.types);
        let mut label = format!(": {}", pretty_tm(0, names, &export(&self.symbol_table, tm)));
        const MAX_LEN: usize = 80;
        if label.chars().count() > MAX_LEN {
            let truncated: String = label.chars().take(MAX_LEN.saturating_sub(1)).collect();
            label = format!("{}\u{2026}", truncated);
        }
        self.inlay_hint_table.push((offset, label));
    }

    /// 参考版 `peel_pi` 对象：逐层剥 Pi（隐式/显式都剥，与参考版
    /// `Val::Pi` 全匹配同溝），封闭以 `vvar(lvl)` 填充；顺便收集参数
    /// 名拼出等价 `ret_cxt.names()`（头 = 最内层，与 types_names_list
    /// 同序）。返回 (剩余类型值, 新层级, names 追加段)。
    fn peel_pi_collect<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        vtyp: V,
    ) -> (V, u32, Vec<SmolStr>) {
        let mut t = vtyp;
        let mut lvl = cxt.lvl;
        let mut peeled: Vec<SmolStr> = Vec::new();
        loop {
            let tf = self.force_v(bump, cxt, t);
            if v_tag(tf) != 4 {
                return (t, lvl, peeled);
            }
            let p = v_pi_of(tf);
            let pname = SmolStr::new(p.name);
            let body = p.body;
            let penv = p.env;
            let val = v_lvl(lvl);
            t = {
                let env = env_ext(bump, penv, val);
                self.eval(bump, cxt, env, body)
            };
            lvl += 1;
            peeled.push(pname);
        }
    }

    /// L5：限定访问中间段 hover（参考版 `push_qualified_hover` 同款）——
    /// `mylib.Foo.mk` 在 `Foo` 上 hover 出类型、`mylib` 上 hover 出命名空
    /// 间声明（若登记）。逐段累积限定名查 decl 表，命中则 cached push。
    fn push_qualified_hover<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        x: &Raw,
    ) {
        let mut cur = x;
        loop {
            match cur {
                Raw::Obj(inner, Some(seg)) => {
                    if let Some(full) = qualified_path_str(inner.as_ref(), &seg.data) {
                        if let Some(e) = cxt.decls.get(full.as_str()) {
                            self.push_hover_cached(bump, cxt, seg.to_span(), e);
                        }
                    }
                    cur = inner.as_ref();
                }
                _ => break,
            }
        }
    }

    /// 与参考版 `Infer::hover_entry_at` 同规则：同 path 内命中 offset 的最
    /// 小 span 胜出。
    pub(crate) fn hover_entry_at(
        &self,
        path_id: u32,
        offset: usize,
    ) -> Option<&(crate::parser_lib::Span<()>, crate::parser_lib::Span<()>, String)> {
        self.hover_table
            .iter()
            .filter(|x| x.0.path_id == path_id)
            .filter(|x| x.0.contains(offset))
            .min_by_key(|x| x.0.end_offset - x.0.start_offset)
    }

    // Extend Cxt（源码 binder / inserted binder / define / fake_bind）
    // --------------------------------------------------------------------------------

    /// Extend Cxt with a bound variable（源码 binder）。
    fn bind_name<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        x: &str,
        b_span: crate::parser_lib::Span<()>,
        a_t: &'a Tm<'a>,
        ty: V,
    ) -> Cxt<'a> {
        let mut names = (*cxt.names).clone();
        names.by_name.insert(SmolStr::new(x), cxt.lvl);
        names.by_lvl.insert(cxt.lvl, (ty, b_span));
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
            namespace: cxt.namespace,
            namespace_prefix: cxt.namespace_prefix.clone(),
            namespaces: cxt.namespaces.clone(),
            // 参考版 `bind`：进入新 binder 域，绑定名清空
            binding_name: None,
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
            namespace: cxt.namespace,
            namespace_prefix: cxt.namespace_prefix.clone(),
            namespaces: cxt.namespaces.clone(),
            binding_name: None,
        }
    }

    /// Extend Cxt with a definition（pruning 记 `None`、telescope 记 Define
    /// 槽）。
    fn define_name<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        x: &str,
        b_span: crate::parser_lib::Span<()>,
        a_t: &'a Tm<'a>,
        t_t: &'a Tm<'a>,
        val: V,
        ty: V,
    ) -> Cxt<'a> {
        let mut names = (*cxt.names).clone();
        names.by_name.insert(SmolStr::new(x), cxt.lvl);
        names.by_lvl.insert(cxt.lvl, (ty, b_span));
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
            namespace: cxt.namespace,
            namespace_prefix: cxt.namespace_prefix.clone(),
            namespaces: cxt.namespaces.clone(),
            // 参考版 `define`：let 续体仍在同一绑定上下文，绑定名保留
            binding_name: cxt.binding_name.clone(),
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
                span: empty_span(()),
                typ_pretty: None,
                tm: stub,
                val: v_xcell(bump.alloc(XCell::Decl { name })),
                vty: ty,
                prim: None,
            },
        );
        if prev.is_some() {
            return Err(Error(empty_span(format!("redefine {}", x)), vec![]));
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
            namespace: cxt.namespace,
            namespace_prefix: cxt.namespace_prefix.clone(),
            namespaces: cxt.namespaces.clone(),
            binding_name: cxt.binding_name.clone(),
        })
    }

    /// 声明登记（参考版 `Cxt::decl`）：**静默覆盖**（参考版 redefine 检查
    /// 被注释）——fake_bind 之后以真值覆盖存根。prim-ness 翻转在快版无
    /// force memo，无需 PRIM_VERSION。
    fn decl_reg<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        x: &str,
        span: crate::parser_lib::Span<()>,
        t_tm: &'a Tm<'a>,
        vt: V,
        typ_tm: &'a Tm<'a>,
        vtyp: V,
        prim: Option<PrimId>,
    ) -> Cxt<'a> {
        let _ = typ_tm;
        let mut decls = cxt.decls.clone();
        // prim-ness 变化会让 force 对同名链的结果改变（Decl 臂走不走 prim
        // 执行）→ 版本号 bump，旧 memo 条目惰性失效（参考版 Cxt::decl 同款）
        let had_prim = decls.get(x).map(|e| e.prim.is_some()).unwrap_or(false);
        // 登记处渲染类型一次（观察面：每 decl 一次 quote→export→pretty；
        // 全局名使用的 hover 直接 clone 此串，见 push_hover_cached）。
        let qt = self.quote(bump, cxt, cxt.lvl, vtyp);
        let qn = types_names_list(cxt.types);
        let typ_pretty = Some(Rc::new(pretty_tm(0, qn, &export(&self.symbol_table, qt))));
        Rc::make_mut(&mut decls).insert(
            SmolStr::new(x),
            DeclEntry {
                span,
                typ_pretty,
                tm: t_tm,
                val: vt,
                vty: vtyp,
                prim,
            },
        );
        if had_prim != prim.is_some() {
            prim_version_bump();
        }
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
            namespace: cxt.namespace,
            namespace_prefix: cxt.namespace_prefix.clone(),
            namespaces: cxt.namespaces.clone(),
            binding_name: cxt.binding_name.clone(),
        }
    }

    /// 追加未解条目（参考版 `new_meta(a, cxt, origin_typ)`）：上下文快照
    /// 存 lvl + names telescope + decls（'static 存放口径，两步入 'a）。
    fn new_meta<'a>(&mut self, bump: &'a Bump, cxt: &Cxt<'a>, a: V, origin_typ: V) -> u32 {
        let _ = bump;
        let snap: Rc<MetaSnap<'static>> = unsafe {
            std::mem::transmute(Rc::new(MetaSnap {
                lvl: cxt.lvl,
                types: cxt.types,
                decls: cxt.decls.clone(),
                // 完整上下文快照（参考版 Arc<Cxt> 第二元）：solve_multi_trait
                // 用它求解，而不是调用方的 cxt。
                cxt: std::mem::transmute::<Cxt<'a>, Cxt<'static>>(clone_cxt(cxt)),
            }))
        };
        self.metas.push(MetaEntry::Unsolved(a, snap, origin_typ, empty_span(())));
        self.metas.len() as u32 - 1
    }

    /// 挂新洞（上游 `freshMeta`）：物化闭类型、追加未解条目，产出
    /// `AppPruning ?m (cxt.pruning)`。快捷（L05 三级 + tag 6）：
    /// **`binds == 0`** 时常值类型（U / 裸未解 meta / LiteralType，tag
    /// 3/5/6）闭类型恒等；`quote` 无自由变量则跳过 Let 链直接空环境求值；
    /// 否则全构造（与参考版同形）。L13：trait Sum 的 meta 进 `trait_metas`
    /// 登记表（solve_multi_trait 只扫它）。
    ///
    /// **L05-L08 的 bind-prefix 快路径（`bind_prefix_of_telescope` + define
    /// 槽由 `cxt.env` 快照供给）在 L09 起刻意不移植**：那条路径要求
    /// "telescope 里 define 槽的项 ≡ env 快照里的值"。L05-L08 的模式特化走
    /// pm_defs（只追加等式，快照恒成立）；L09 起改走参考版
    /// `Cxt::update_cxt`——精化就地改写 env 槽再 refresh 重锚定，而
    /// `locals` 照参考版保持陈旧（参考版 cxt.rs 里
    /// `locals: self.locals.clone()` 的 TODO），全 close 正是靠这份陈旧项
    /// 与参考版逐值同轨。改读快照会拿到精化后的值：孪生的契约是与参考版
    /// Ok 输出逐字节一致，不是比参考版更正确。
    fn fresh_meta<'a>(&mut self, bump: &'a Bump, cxt: &Cxt<'a>, a: V) -> &'a Tm<'a> {
        // L10：trait 类型先试实例合成（成功 → 直接给实例项）；
        // trait Sum → 裸 Meta（无 AppPruning 掩码）
        if let Ok(Some((tm, _))) = self.solve_trait_ref(bump, cxt, a, false) {
            return tm;
        }
        let is_trait_sum = v_tag(a) == 7
            && match v_xcell_of(a) {
                XCell::Sum { is_trait, .. } => *is_trait,
                _ => false,
            };
        if is_trait_sum {
            let m = self.new_meta(bump, cxt, a, a);
            self.trait_metas.push(m);
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
        let m = self.new_meta(bump, cxt, mty, a);
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
        fuel: u32,
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
                        constraints,
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
            constraints, l, t, u, fuel, cxt, mach_ptr, trait_err,
        )
    }

    /// 参考 `Infer::solve_multi_trait`（L13）：只扫 `trait_metas` 登记表
    /// （fresh_meta 对 trait Sum 走此表），清理指向截断 meta 的条目；从 m
    /// 起逐个跑实例合成（合成成功 → meta := 实例值）。
    fn solve_multi_trait_ref<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        m: u32,
        allow_flex_defaulting: bool,
    ) -> Result<(), String> {
        self.trait_metas
            .retain(|mv| (*mv as usize) < self.metas.len());
        for mv in self.trait_metas.clone() {
            if mv < m {
                continue;
            }
            let idx = mv as usize;
            if idx >= self.metas.len() {
                continue;
            }
            let x = match &self.metas[idx] {
                MetaEntry::Unsolved(v, ..) => *v,
                _ => continue,
            };
            // 用 **meta 创建处**的上下文求解（参考版 `meta_cxt`）：goal 里的
            // Rigid 层级按创建处 de Bruijn 编号，用调用方的浅上下文会让
            // rename/quote 算出越界变量。
            let meta_cxt: &Cxt<'a> = match &self.metas[idx] {
                MetaEntry::Unsolved(_, s, ..) => unsafe {
                    &*(&s.cxt as *const Cxt<'static> as *const Cxt<'a>)
                },
                _ => continue,
            };
            let typ = self
                .solve_trait_ref(bump, meta_cxt, x, allow_flex_defaulting)
                .map_err(|e| e)?;
            if let Some((_, val)) = typ {
                self.metas[idx] = MetaEntry::Solved(val, x);
            }
        }
        Ok(())
    }

    /// 参考 `Infer::solve_trait`（L13 unification.rs:600 逐句）：trait Sum →
    /// flex defaulting（多个非 out 参数仅 1 个已知时把其余 unify 到它）→
    /// Phase 1 轻量过滤实例（head_index 桶 + val_match；非 out 参数 Flex /
    /// 多候选且 out 参数 Flex → 推迟 `Ok(None)`）→ Phase 2 逐候选
    /// infer+insert+eval（SumCase 时 unify 把关 + **重 eval**——闭包捕获已解
    /// meta），失败截断 metas 换下一个；全败给含实例表的 Err 文案。
    fn solve_trait_ref<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        x: V,
        allow_flex_defaulting: bool,
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
        // 非 out 参数下标（flex defaulting 与多次收集共用）
        let non_out_idx: Vec<usize> = params
            .iter()
            .zip(out_param.iter())
            .enumerate()
            .filter(|(_, (_, o))| !**o)
            .map(|(i, _)| i)
            .collect();
        // flex defaulting：多个非 out 参数仅 1 个已知 → 把其余 unify 到它
        let mut non_out_params: Vec<V> = {
            let pv: Vec<V> = non_out_idx.iter().map(|&i| params[i].val).collect();
            self.force_list(bump, &cxt.decls, &pv)
        };
        if allow_flex_defaulting
            && non_out_params.iter().any(|v| is_flex(&self.spine, *v))
        {
            let known: Vec<V> = non_out_params
                .iter()
                .copied()
                .filter(|v| !is_flex(&self.spine, *v))
                .collect();
            if known.len() == 1 && non_out_params.len() > 1 {
                let known_type = known[0];
                let mut ok = true;
                for v in non_out_params.iter() {
                    if is_flex(&self.spine, *v) {
                        let mut terr = None;
                        if !self.unify(bump, cxt, cxt.lvl, *v, known_type, 100, &mut terr) {
                            ok = false;
                            break;
                        }
                    }
                }
                if ok {
                    let pv: Vec<V> = non_out_idx.iter().map(|&i| params[i].val).collect();
                    non_out_params = self.force_list(bump, &cxt.decls, &pv);
                    if non_out_params.iter().any(|v| is_flex(&self.spine, *v)) {
                        return Ok(None);
                    }
                } else {
                    return Ok(None);
                }
            } else {
                return Ok(None);
            }
        }
        // 全参数（含 outParam）force，供实例匹配
        let all_params: Vec<V> =
            self.force_list(bump, &cxt.decls, &params.iter().map(|p| p.val).collect::<Vec<_>>());
        // —— Phase 1：轻量过滤（head_index 桶优先 + val_match 确认）——
        let matching_lvls: Vec<crate::parser_lib::Span<SmolStr>> = {
            let instances = match self.tstate.solver.class_instances.get(&SmolStr::new(name)) {
                Some(insts) => insts,
                None => return Ok(None),
            };
            let filter = |inst: &Instance| -> Option<crate::parser_lib::Span<SmolStr>> {
                if inst.assertion.name != name {
                    return None;
                }
                if inst.assertion.arguments.len() != all_params.len() {
                    return None;
                }
                let mut subst = std::collections::HashMap::new();
                let mut ok = true;
                for (i, (g_arg, i_arg)) in
                    all_params.iter().zip(inst.assertion.arguments.iter()).enumerate()
                {
                    let is_out = out_param.get(i).copied().unwrap_or(false);
                    if is_out && is_flex(&self.spine, *g_arg) {
                        continue;
                    }
                    let g_ref = v_to_ref_val(&self.spine, &self.defs, *g_arg);
                    if !Synth::val_match(g_ref.as_ref(), i_arg, &mut subst) {
                        ok = false;
                        break;
                    }
                }
                if ok {
                    Some(inst.lvl.clone())
                } else {
                    None
                }
            };
            // 首个非 out 参数的已知头 → 具体桶 + 通配桶；否则全扫
            let self_head: Option<SmolStr> = (|| {
                for (i, arg) in all_params.iter().enumerate() {
                    if !out_param.get(i).copied().unwrap_or(false) {
                        return head_key_v(&self.spine, *arg);
                    }
                }
                None
            })();
            match self_head {
                Some(head) => {
                    let mut idxs: Vec<usize> = Vec::new();
                    if let Some(indices) = self
                        .tstate
                        .solver
                        .head_index
                        .get(&(SmolStr::new(name), head.clone()))
                    {
                        idxs.extend(indices.iter().copied());
                    }
                    if let Some(indices) = self.tstate.solver.head_index.get(&(
                        SmolStr::new(name),
                        SmolStr::new(super::typeclass::GENERIC_SELF_HEAD),
                    )) {
                        idxs.extend(indices.iter().copied());
                    }
                    if idxs.is_empty() {
                        instances.iter().filter_map(filter).collect()
                    } else {
                        idxs.iter().filter_map(|&i| filter(&instances[i])).collect()
                    }
                }
                None => instances.iter().filter_map(filter).collect(),
            }
        };
        let candidate_count = matching_lvls.len();
        if candidate_count == 0 {
            return Ok(None); // 无实例：交给后续（solve_multi_trait / 报错路径）
        }
        // 非 out 参数仍 Flex → 推迟（val_match(Flex, _) 恒真会选错实例）。
        // 注意 `is_flex` 同时覆盖裸 meta 与 meta 头链（`?m x`）——goal 的
        // 参数形态常是后者；只测 `v_tag == 5` 会漏判，让 flex goal 进入
        // 实例匹配（val_match 对每个实例恒真）后按登记序选中错误实例。
        let forced_params: Vec<V> = self.force_list(
            bump,
            &cxt.decls,
            &params.iter().map(|p| p.val).collect::<Vec<_>>(),
        );
        let has_flex_non_out = non_out_idx
            .iter()
            .any(|&i| is_flex(&self.spine, forced_params[i]));
        if has_flex_non_out {
            return Ok(None);
        }
        // 多候选且 out 参数 Flex → 推迟（等上下文约束 out 参数）
        let out_idx: Vec<usize> = params
            .iter()
            .zip(out_param.iter())
            .enumerate()
            .filter(|(_, (_, o))| **o)
            .map(|(i, _)| i)
            .collect();
        let has_flex_out = out_idx
            .iter()
            .any(|&i| is_flex(&self.spine, forced_params[i]));
        if has_flex_out && candidate_count > 1 {
            return Ok(None);
        }
        // —— Phase 2：逐候选 elaborate ——
        let mut last_err = String::new();
        for lvl in &matching_lvls {
            let meta_before = self.metas.len();
            let result = (|| -> Result<(&'a Tm<'a>, V), String> {
                let raw = Raw::Var(lvl.clone());
                let infered = self.infer_expr(bump, cxt, &raw).map_err(|e| e.0.data)?;
                let (tm, _) = self
                    .insert(bump, cxt, infered.0, infered.1)
                    .map_err(|e| e.0.data)?;
                let mut val = self.eval(bump, cxt, cxt.env, tm);
                if v_tag(val) == 7 {
                    if let XCell::SumCase { typ, .. } = v_xcell_of(val) {
                        self.unify_catch(bump, cxt, *typ, x).map_err(|e| e.0.data)?;
                        // 重 eval：首次 eval 在实例隐参（fresh meta）求解前
                        // 跑，闭包捕获冻结的未解 meta 环境——宽度参数会永远
                        // 悬空（typeclass instance Nat param bug）。以已解
                        // meta 重求使闭包捕获合一后的值。
                        val = self.eval(bump, cxt, cxt.env, tm);
                    }
                }
                Ok((tm, val))
            })();
            match result {
                Ok((tm, val)) => return Ok(Some((tm, val))),
                Err(e) => {
                    self.metas.truncate(meta_before);
                    last_err = e;
                }
            }
        }
        // 全部候选失败
        let params_dbg = all_params
            .iter()
            .map(|v| {
                let r = v_to_ref_val(&self.spine, &self.defs, *v);
                format!("{:?}", r)
            })
            .collect::<Vec<_>>()
            .join(", ");
        Err(format!(
            "solve trait failed: {}[{}]\n  last error: {}\n  instances:\n{}",
            name,
            params_dbg,
            last_err,
            matching_lvls
                .iter()
                .map(|x| format!("{:?}", x.data))
                .reduce(|a, b| a + "\n" + &b)
                .unwrap_or_default(),
        ))
    }

    /// 错误消息（参考版 `unify_catch`：pretty + 上下文名字表；快版导出项
    /// 的 Span 全零，消息内容与参考版同构）。入口/出口清空约束挂账；非空
    /// 即"can't unify for unsolved meta"（参考版同款两段文案）。
    fn unify_catch<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: V,
        t_prime: V,
    ) -> Result<(), Error> {
        let mut trait_err: Option<String> = None;
        self.constraints.clear();
        let ok = self.unify(bump, cxt, cxt.lvl, t, t_prime, 100, &mut trait_err);
        if ok && !self.constraints.is_empty() {
            let tq0 = self.quote(bump, cxt, cxt.lvl, t);
            let uq0 = self.quote(bump, cxt, cxt.lvl, t_prime);
            let tq = export(&self.symbol_table, tq0);
            let uq = export(&self.symbol_table, uq0);
            let names = types_names_list(cxt.types);
            self.constraints.clear();
            return Err(Error(
                empty_span(format!(
                    "can't unify for unsolved meta\n  expected: {}\n      find: {}",
                    pretty_tm(0, names.clone(), &tq),
                    pretty_tm(0, names, &uq),
                )),
                vec![],
            ));
        }
        self.constraints.clear();
        if ok {
            Ok(())
        } else {
            if let Some(e) = trait_err {
                return Err(Error(empty_span(e), vec![]));
            }
            let tq0 = self.quote(bump, cxt, cxt.lvl, t);
            let uq0 = self.quote(bump, cxt, cxt.lvl, t_prime);
            let tq = export(&self.symbol_table, tq0);
            let uq = export(&self.symbol_table, uq0);
            let names = types_names_list(cxt.types);
            Err(Error(
                empty_span(format!(
                    "can't unify\n  expected: {}\n      find: {}",
                    pretty_tm(0, names.clone(), &tq),
                    pretty_tm(0, names, &uq),
                )),
                vec![],
            ))
        }
    }

    /// 参数表逐个 force（solve_trait_ref 的多次收集点共用）。
    fn force_list<'a>(&mut self, bump: &'a Bump, decl: &Decls<'a>, vals: &[V]) -> Vec<V> {
        let Machine {
            spine,
            defs,
            metas,
            mutable,
            ..
        } = self;
        vals.iter().map(|&v| force(bump, spine, defs, metas, decl, mutable, v)).collect()
    }

    /// 指针导入表取回本机 Tm（export 登记的 Rc 指针 → 本轮 bump 项）。
    /// miss = 内部错误（Phase A / trait 方法缓存必须先登记）。
    fn tm_import_lookup<'a>(&self, rc: &Rc<CTm>) -> &'a Tm<'a> {
        let key = Rc::as_ptr(rc) as usize;
        match self.tm_import.get(&key) {
            Some(t) => unsafe { &*(*t as *const Tm<'static> as *const Tm<'a>) },
            None => panic!("tm_import miss: prechecked term not registered"),
        }
    }

    /// 指针导入表取回本机 V（v_to_ref_val 登记的 Rc 指针 → 本机值）。
    fn val_import_lookup(&self, rc: &Rc<CVal>) -> V {
        let key = Rc::as_ptr(rc) as usize;
        *self
            .val_import
            .get(&key)
            .expect("val_import miss: prechecked type not registered")
    }

    /// 值是否是 `BindingName` 类型（参考版 `is_binding_name_type`：Sum 名
    /// 相等，或卡住的**空 spine** Decl 同名——链形态不算，参考版同款）。
    fn is_binding_name_type(&mut self, bump: &Bump, cxt: &Cxt<'_>, a: V) -> bool {
        let a_f = self.force_v(bump, cxt, a);
        match v_tag(a_f) {
            7 => match v_xcell_of(a_f) {
                XCell::Sum { name: "BindingName", .. } => true,
                XCell::Decl { name } => *name == "BindingName",
                _ => false,
            },
            _ => false,
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
        } = self;        force(bump, spine, defs, metas, &*cxt.decls, mutable, v)
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
            // BindingName 特例（参考版 insert_go 207-232）：隐式参数类型是
            // BindingName 时，以当前绑定名自动合成实参（`BindingName.mk
            // "名字"`）
            if self.is_binding_name_type(bump, cxt, p.dom) {
                let name_str =
                    cxt.binding_name.clone().unwrap_or_else(|| SmolStr::new(""));
                let mk_key = if cxt.decls.contains_key("BindingName.mk") {
                    "BindingName.mk".to_string()
                } else {
                    cxt.decls
                        .keys()
                        .find(|k| k.ends_with(".BindingName.mk"))
                        .cloned()
                        .unwrap_or_else(|| SmolStr::new("BindingName.mk"))
                        .to_string()
                };
                let bn_tm = bump.alloc(Tm::App(
                    bump.alloc(Tm::Decl(bump.alloc_str(&mk_key))),
                    bump.alloc(Tm::LiteralIntro(bump.alloc_str(&name_str))),
                    Icit::Expl,
                ));
                let bn_val = self.eval(bump, cxt, cxt.env, bn_tm);
                let b = {
                    let env = env_ext(bump, p.env, bn_val);
                    self.eval(bump, cxt, env, p.body)
                };
                let t2 = bump.alloc(Tm::App(t, bn_tm, Icit::Impl));
                return self.insert_go(bump, cxt, t2, b);
            }
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
                return Err(Error(empty_span(format!("no named implicit arg {}", name)), vec![]));
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
        // 预检查值（class Phase-B / trait 方法缓存复用——参考版 check 的
        // Raw::Tm 臂 649-666）：eval 驱动副作用（模块树全局）与良构性；
        // 未注解字段（期望是 fresh meta）**直解** meta := Phase-A 类型（整
        // unify 的 flex_flex 会重建闭包链产生幻影解，参考版注释）；注解
        // 复验走 unify_catch。内层值不重复 elaboration——经指针导入表取回。
        if let Raw::Tm(rc_tm, rc_ty) = t {
            let tm: &'a Tm<'a> = self.tm_import_lookup(rc_tm);
            let ty = self.val_import_lookup(rc_ty);
            {
                let _ = self.eval(bump, cxt, cxt.env, tm);
            }
            match v_tag(a) {
                5 => {
                    let m = v_meta_of(a);
                    // 空 spine 未解 meta：直解（meta 类型保留在第二元）
                    let mty = match &self.metas[m as usize] {
                        MetaEntry::Unsolved(v, ..) => *v,
                        _ => unreachable!(),
                    };
                    self.metas[m as usize] = MetaEntry::Solved(ty, mty);
                }
                _ => {
                    self.unify_catch(bump, cxt, a, ty)?;
                }
            }
            return Ok(tm);
        }
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
                    // 观察面：显式 lambda binder 定义处 hover（参考版 742 同点位）
                    self.push_hover(bump, cxt, x.to_span(), x.to_span(), p.dom);
                    let cxt2 = self.bind_name(bump, cxt, &x.data, x.to_span(), a_t, p.dom);
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
            // Raw::Tm 注解：指针导入表直取（参考版同款）
            let (a_tm, va) = if let Raw::Tm(rc_tm, rc_ty) = a_ty.as_ref() {
                let tm: &'a Tm<'a> = self.tm_import_lookup(rc_tm);
                let v = self.val_import_lookup(rc_ty);
                (tm, v)
            } else {
                let (a_tm, _) = self.check_universe(bump, cxt, a_ty)?;
                let va = self.eval(bump, cxt, cxt.env, a_tm);
                (a_tm, va)
            };
            // 绑定名（隐式 BindingName 参数合成）
            let cxt_named = cxt.with_binding_name(x.data.clone());
            let t_tm = self.check(bump, &cxt_named, t2, va)?;
            let vt = self.eval(bump, &cxt, cxt.env, t_tm);
            let name: &'a str = bump.alloc_str(&x.data);
            let cxt2 = self.define_name(bump, cxt, &x.data, x.to_span(), a_tm, t_tm, vt, va);
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
                // 参考版同款：warnings 以 Display 逐条 join("; ") 作错误文案
                //（原为 Debug 形式，与参考版文案分叉）
                let msg = compiler
                    .warnings
                    .iter()
                    .map(|w| w.to_string())
                    .collect::<Vec<_>>()
                    .join("; ");
                return Err(Error(expr_span.map(|_| msg.clone()), vec![]));
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
                MetaEntry::Unsolved(v, _, _, _) => *v,
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
                return Err(Error(t_span.map(|_| "invert failed".to_owned()), vec![]));
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
                    return Err(Error(t_span.map(|_| "prune failed".to_owned()), vec![]));
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
                return Err(Error(t_span.map(|_| msg.clone()), vec![]));
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
                    vec![],
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
        Err(Error(
            t_span.map(|_| {
                format!(
                    "expected universe, got {}",
                    debug_val(&self.spine, &self.defs, inferred_type)
                )
            }),
            vec![],
        ))
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

/// namespace 条目链（参考版 `Cxt.namespace: List<(Rc<Val>, HashSet<SmolStr>,
/// SmolStr)>` 的 bump 持久链；方法名集以切片线性查——条目少）。
pub(crate) struct NsCons<'a> {
    /// 类型值（`trait_wrap` 的接收者类型探测）。
    val: V,
    /// 实例方法名集。
    methods: &'a [SmolStr],
    /// TypeHead 字符串（`TypeHead.method` 的注册前缀）。
    type_name: &'a str,
    next: Option<&'a NsCons<'a>>,
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
    /// inherent impl 登记的类型→实例方法集（参考版 `Cxt.namespace`）。
    namespace: Option<&'a NsCons<'a>>,
    /// `package a.b` 后对 def/enum/trait/class 名生效的前缀。
    namespace_prefix: Option<SmolStr>,
    /// 可见 namespace 集（后缀 fallback 的准入判定；写时复制）。
    namespaces: Rc<FxHashSet<SmolStr>>,
    /// 当前 let/字段绑定的名字（`BindingName` 隐参合成用）。bind 清、
    /// define 保留、`with_binding_name` 显式设。
    binding_name: Option<SmolStr>,
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
            namespace: None,
            namespace_prefix: None,
            namespaces: Rc::new(FxHashSet::default()),
            binding_name: None,
        }
    }

    /// `with_binding_name`：let RHS / class 字段检查前设绑定名（参考版
    /// cxt.rs 同名方法；binding_name 只影响隐式 `BindingName` 参数合成）。
    fn with_binding_name(&self, name: SmolStr) -> Self {
        Cxt {
            namespace: self.namespace,
            namespace_prefix: self.namespace_prefix.clone(),
            namespaces: self.namespaces.clone(),
            binding_name: Some(name),
            env: self.env,
            update_from: self.update_from,
            names: self.names.clone(),
            types: self.types,
            locals: self.locals,
            pruning: self.pruning,
            binds: self.binds,
            lvl: self.lvl,
            decls: self.decls.clone(),
        }
    }
}

/// prelude 短名别名 auto-import（参考版 `load_prelude_state_impl` 尾部
/// 逐句）：全局 decl 表里带 `.` 的键给短名别名（`Nat.zero` → `zero`），
/// **ns 方法键排除**（`TypeHead.method` 只经 `x.m` 分派可达、绝不裸名，
/// 不得遮构造子别名）；短名冲突按全键排序 `or_insert` first-wins（结果
/// 与 HashMap 迭代序无关的确定性）。
fn insert_prelude_aliases<'a>(mut cxt: Cxt<'a>) -> Cxt<'a> {
    let mut ns_method_keys: FxHashSet<SmolStr> = FxHashSet::default();
    let mut cur = cxt.namespace;
    while let Some(ns) = cur {
        for m in ns.methods {
            ns_method_keys.insert(SmolStr::new(format!("{}.{}", ns.type_name, m)));
        }
        cur = ns.next;
    }
    let mut aliases: Vec<(SmolStr, SmolStr, DeclEntry<'a>)> = cxt
        .decls
        .iter()
        .filter(|(k, _)| k.contains('.') && !ns_method_keys.contains(*k))
        .map(|(k, v)| {
            let short = SmolStr::new(k.split('.').last().unwrap());
            (short, k.clone(), v.clone())
        })
        .collect();
    aliases.sort_by(|a, b| a.1.cmp(&b.1));
    let map = Rc::make_mut(&mut cxt.decls);
    for (short, _full_key, v) in aliases {
        map.entry(short).or_insert(v);
    }
    cxt
}

fn tuple_n_arity(name: &str) -> Option<usize> {
    let digits = name.strip_prefix("Tuple")?;
    if digits.is_empty() || !digits.chars().all(|c| c.is_ascii_digit()) {
        return None;
    }
    digits.parse().ok()
}

/// 判定函数位是否为组合子字面构造 `TupleN.mk e0 … en`
/// （参考版 is_tuple_mk_head 逐句对应，服务元素 hover）。
fn is_tuple_mk_head(head: &Raw) -> bool {
    let mut cur = head;
    loop {
        match cur {
            Raw::App(f, _, _) => cur = f.as_ref(),
            _ => break,
        }
    }
    match cur {
        Raw::Var(n) => n
            .data
            .strip_suffix(".mk")
            .and_then(tuple_n_arity)
            .is_some(),
        Raw::Obj(base, Some(m)) if m.data == "mk" => {
            let mut cur = base.as_ref();
            loop {
                match cur {
                    Raw::App(f, _, _) => cur = f.as_ref(),
                    _ => break,
                }
            }
            matches!(cur, Raw::Var(n) if tuple_n_arity(&n.data).is_some())
        }
        _ => false,
    }
}

/// types 链 → 参考版 pretty 的名字 List（头 = 最内层；List::prepend 从尾
/// 起构回，序不变）。
fn types_names_list(tys: Option<&TCons<'_>>) -> crate::list::List<SmolStr> {
    let mut ns: Vec<SmolStr> = Vec::new();
    let mut cur = tys;
    while let Some(tc) = cur {
        ns.push(SmolStr::new(tc.name));
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
            Tm::U(_) | Tm::Meta(_) | Tm::LiteralType | Tm::LiteralIntro(_) => {}
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
            Tm::Call(_, args, body) => {
                for (a, _) in args.iter() {
                    stack.push((a, d));
                }
                stack.push((body, d));
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
                    index: i1,
                    datas: d1,
                    ..
                },
                XCell::SumCase {
                    index: i2,
                    datas: d2,
                    ..
                },
            ) = (v_xcell_of(f1), v_xcell_of(f2))
            {
                if i1 == i2 {
                    let mut cxt = clone_cxt(cxt);
                    for (x, y) in d1.iter().zip(d2.iter()) {
                        cxt = self.unify_pm(bump, &cxt, x.val, y.val, t_span)?;
                    }
                    return Ok(cxt);
                }
                return Err(Error(t_span.map(|_| "".to_string()), vec![]));
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
                return Err(Error(t_span.map(|_| "".to_string()), vec![]));
            }
        }
        self.unify_catch(bump, cxt, f1, f2).map(|_| clone_cxt(cxt))
    }

    /// 「纯探测」统一执行器：进入前快照 `metas` 与 `trait_metas`，跑完闭包后
    /// **无条件**换回（无论闭包返回 Ok/Err），把探测期分配的 fresh meta 与对
    /// 已有 meta/trait meta 的求解一律回滚，杜绝污染外泄到真实机。可达性探测等
    /// 投机性 check 都走此入口，避免各处手写快照漏掉错误路径（AV 根因）。
    ///
    /// 注意：必须**整表 clone**，不能只按 meta 上界截断——探测期的 unify 可能
    /// 解掉**已有**的 meta，而这些解又引用闭包内新建的 meta，截断会让那些解
    /// 悬空（后续查找越界 panic）；参考版 pattern_match.rs 同款理由。
    fn run_pure_probe<R>(&mut self, f: impl FnOnce(&mut Machine) -> R) -> R {
        let metas = self.metas.clone();
        let trait_metas = self.trait_metas.clone();
        let r = f(self);
        self.metas = metas;
        self.trait_metas = trait_metas;
        r
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
            namespace: cxt.namespace,
            namespace_prefix: cxt.namespace_prefix.clone(),
            namespaces: cxt.namespaces.clone(),
            binding_name: cxt.binding_name.clone(),
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
            if let Some((old_ty, sp)) = names.by_lvl.get(&lvl) {
                let old_ty = *old_ty;
                let sp = *sp;
                let qt = self.quote(bump, cxt, n as u32, old_ty);
                let rty = self.eval(bump, cxt, env_tt_chain, qt);
                names.by_lvl.insert(lvl, (rty, sp));
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
        t: crate::parser_lib::Span<SmolStr>,
        a: V,
        x: &Raw,
        tm: &'a Tm<'a>,
    ) -> Result<(&'a Tm<'a>, V), Error> {
        let t_span = t.to_span();
        // typ_raw = eval(quote(a))（参考版同款二次正规化）
        let typ_raw = {
            let q = self.quote(bump, cxt, cxt.lvl, a);
            self.eval(bump, cxt, cxt.env, q)
        };
        let typ_raw_head = head_key_v(&self.spine, typ_raw);
        let typ_raw_ref = v_to_ref_val(&self.spine, &self.defs, typ_raw);

        // —— namespace 条目查表（参考版 2742-2846）——
        // 匹配方法名的条目逐个探测（metas/trait_metas 快照回滚——探测可能
        // 解出引用临时 meta 的解，truncate 会留悬空）。
        let mut ns_result: Vec<(V, SmolStr)> = Vec::new();
        {
            let mut cur = cxt.namespace;
            while let Some(ns) = cur {
                if ns.methods.iter().any(|m| *m == t.data) {
                    // 预过滤 1：条目 trait 对该 Self 无实例 → 跳过
                    let mut skip = false;
                    if let Some(head) = &typ_raw_head {
                        if v_tag(ns.val) == 4 {
                            let p = v_pi_of(ns.val);
                            if p.icit == Icit::Impl {
                                let dom_f = self.force_v(bump, cxt, p.dom);
                                if v_tag(dom_f) == 7 {
                                    if let XCell::Sum { name: tn, is_trait: true, .. } =
                                        v_xcell_of(dom_f)
                                    {
                                        if !self
                                            .tstate
                                            .solver
                                            .can_satisfy(&SmolStr::new(tn), &typ_raw_ref)
                                        {
                                            skip = true;
                                        }
                                    }
                                }
                            }
                        }
                        let _ = head;
                    }
                    if !skip {
                        // 预过滤 2：条目首个显式参数（接收者）类型头须与接收者
                        // 类型头一致（Flex/generic 头放行）。隐式 Π 用
                        // Rigid(u32::MAX) 闭——不造 meta（参考版同款）。
                        if let Some(head) = &typ_raw_head {
                            let mut self_ty = ns.val;
                            let mut guard = 0;
                            while v_tag(self_ty) == 4 && v_pi_of(self_ty).icit == Icit::Impl {
                                let p = v_pi_of(self_ty);
                                self_ty = {
                                    let env = env_ext(bump, p.env, v_lvl(u32::MAX));
                                    self.eval(bump, cxt, env, p.body)
                                };
                                guard += 1;
                                if guard > 64 {
                                    break;
                                }
                            }
                            if v_tag(self_ty) == 4 && v_pi_of(self_ty).icit == Icit::Expl {
                                let dom_f = self.force_v(bump, cxt, v_pi_of(self_ty).dom);
                                if let Some(param_head) = head_key_v(&self.spine, dom_f) {
                                    if param_head != *head {
                                        skip = true;
                                    }
                                }
                            }
                        }
                    }
                    if !skip {
                        let meta_snapshot = self.metas.clone();
                        let tm_snapshot = self.trait_metas.clone();
                        // 探测：剥隐式 Π（fresh meta 实参化）后与接收者类型合一
                        let mut check_typ = ns.val;
                        let mut guard = 0;
                        while v_tag(check_typ) == 4 && v_pi_of(check_typ).icit == Icit::Impl {
                            let p = v_pi_of(check_typ);
                            let mv = {
                                let m = self.fresh_meta(bump, cxt, p.dom);
                                self.eval_fresh(bump, cxt, cxt.env, m)
                            };
                            check_typ = {
                                let env = env_ext(bump, p.env, mv);
                                self.eval(bump, cxt, env, p.body)
                            };
                            guard += 1;
                            if guard > 64 {
                                break;
                            }
                        }
                        if self.unify_catch(bump, cxt, check_typ, typ_raw).is_ok() {
                            ns_result.push((ns.val, SmolStr::new(ns.type_name)));
                        }
                        self.metas = meta_snapshot;
                        self.trait_metas = tm_snapshot;
                    }
                }
                cur = ns.next;
            }
        }
        if ns_result.len() > 1 {
            let names: Vec<SmolStr> = ns_result
                .iter()
                .filter_map(|(v, _)| {
                    if v_tag(*v) == 4 {
                        let p = v_pi_of(*v);
                        if p.icit == Icit::Impl {
                            let dom_f = self.force_v(bump, cxt, p.dom);
                            if v_tag(dom_f) == 7 {
                                if let XCell::Sum { name: tn, is_trait: true, .. } =
                                    v_xcell_of(dom_f)
                                {
                                    return Some(SmolStr::new(tn));
                                }
                            }
                        }
                    }
                    None
                })
                .collect();
            return Err(Error(
                t.clone().map(|m| format!(
                    "ambiguous method `{}`: found in traits {}",
                    m,
                    names.iter().map(|n| format!("`{}`", n)).collect::<Vec<_>>().join(", "),
                )),
                vec![],
            ));
        }
        if let Some((_, type_name)) = ns_result.into_iter().next() {
            // 命中：`TypeHead.method` 限定键分派（与 inherent impl 注册的键
            // 一致；裸名 fallback 排除 namespace 方法键，模式 `mux` 仍只解
            // 构造子）
            let qname = SmolStr::new(format!("{}.{}", type_name, t.data));
            let qname2 = qname.clone();
            let call = Raw::App(
                Box::new(Raw::Var(t_span.map(move |_| qname2.clone()))),
                Box::new(x.clone()),
                Either::Icit(Icit::Expl),
            );
            match self.infer_expr(bump, cxt, &call) {
                Ok(r) => {
                    // 观察面（ref 2817）：ns 方法命中 → 方法名 token hover。
                    // 参考版 def_span 取 ns 条目登记 span；此处从 decl 表取
                    // 限定键登记项的 span（同一登记来源）。
                    let ds = cxt
                        .decls
                        .get(qname.as_str())
                        .map(|e| e.span)
                        .unwrap_or(t_span);
                    self.push_hover(bump, cxt, t_span, ds, r.1);
                    return Ok(r);
                }
                // 参考版此处是 `?`——失败直接传播，不收 completion（补全只在
                // trait 定义查表未命中的 else 支）。
                Err(e) => return Err(e),
            }
        }

        // —— trait 定义查表（参考版 2847-2988）——
        let mut traits: Vec<(
            SmolStr,
            Raw,
            crate::parser_lib::Span<SmolStr>, // trait 方法声明名 span（hover def）
            usize, // argc（显式参数数——同名算符消歧）
        )> = self
            .tstate
            .definition
            .iter()
            .flat_map(|(trait_name, (trait_params, _out, _st, methods))| {
                methods
                    .iter()
                    .find(|m| m.0.data == t.data)
                    .map(|m| (trait_name.clone(), trait_params.clone(), m))
            })
            .filter(|(tn, _, _)| {
                self.tstate.solver.clean();
                self.tstate.solver.can_satisfy(tn, &typ_raw_ref)
            })
            .map(|(trait_name, trait_params, (methods_name, methods_params, ret_type, _default))| {
                let argc = methods_params.iter().filter(|p| p.2 == Icit::Expl).count();
                let call_span = t.clone();
                // **$$ 先于 $this**：insert_go 先填 Self 与 trait 实例再到位
                // $this（Self 仍 Flex 时 solve_trait 推迟 $$，$this 合一后
                // solve_multi_trait 再解——参考版注释）
                let mut params = trait_params.clone();
                params.push((
                    call_span.clone().map(|_| SmolStr::new("$$")),
                    trait_params
                        .iter()
                        .map(|x| x.0.clone())
                        .fold(
                            Raw::Var(call_span.clone().map(|_| trait_name.clone())),
                            |ret, x| {
                                Raw::App(
                                    Box::new(ret),
                                    Box::new(Raw::Var(x)),
                                    Either::Icit(Icit::Impl),
                                )
                            },
                        ),
                    Icit::Impl,
                ));
                params.push((
                    call_span.clone().map(|_| SmolStr::new("$this")),
                    Raw::Var(call_span.clone().map(|_| SmolStr::new("Self"))),
                    Icit::Expl,
                ));
                params.extend(methods_params.iter().cloned());
                let body = std::iter::once((
                    Raw::Var(call_span.clone().map(|_| SmolStr::new("$this"))),
                    Icit::Expl,
                ))
                .chain(methods_params.iter().map(|x| (Raw::Var(x.0.clone()), x.2)))
                .fold(
                    Raw::Obj(
                        Box::new(Raw::Var(call_span.clone().map(|_| SmolStr::new("$$")))),
                        Some(call_span.clone()),
                    ),
                    |ret, (x, icit)| {
                        Raw::App(Box::new(ret), Box::new(x), Either::Icit(icit))
                    },
                );
                let decl = Raw::Let(
                    call_span.clone().map(|x| SmolStr::new(format!("${x}"))),
                    Box::new(params.iter().rev().fold(ret_type.clone(), |a, b| {
                        Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a))
                    })),
                    Box::new(params.iter().rev().fold(body, |a, b| {
                        Raw::Lam(b.0.clone(), Either::Icit(b.2), Box::new(a))
                    })),
                    Box::new(Raw::App(
                        Box::new(Raw::Var(
                            call_span.clone().map(|x| SmolStr::new(format!("${x}"))),
                        )),
                        Box::new(x.clone()),
                        Either::Icit(Icit::Expl),
                    )),
                );
                (trait_name, decl, methods_name.clone(), argc)
            })
            .collect();
        if traits.len() > 1 {
            // 同名算符按显参个数消歧（中缀 `a - b` 恒有 ≥1 实参——Neg.- 0 参
            // vs Sub.- 1 参）；仍歧义才报错
            let nonzero: Vec<(SmolStr, Raw, crate::parser_lib::Span<SmolStr>, usize)> =
                traits.iter().filter(|(_, _, _, argc)| *argc > 0).cloned().collect();
            if nonzero.len() == 1 && nonzero.len() < traits.len() {
                traits = nonzero;
            } else {
                let trait_names: Vec<&SmolStr> = traits.iter().map(|(n, _, _, _)| n).collect();
                return Err(Error(
                    t.clone().map(|m| format!(
                        "ambiguous method `{}`: found in traits {}",
                        m,
                        trait_names
                            .iter()
                            .map(|n| format!("`{}`", n))
                            .collect::<Vec<_>>()
                            .join(", "),
                    )),
                    vec![],
                ));
            }
        }
        if let Some((_, decl, def_span, _)) = traits.first() {
            // trait 方法 elaboration 缓存：同算符在结构相等的接收者类型上
            // 再次 elaborate 时，经 Raw::Tm 注解复用已查 Π 链与方法体 λ
            //（跳过 check_universe 与体重查）。缓存仅在**全无 meta** 时写入
            //（引用 per-call meta 的项在后续调用里下标过期）。
            let cache_key =
                val_cache_key_t(&self.spine, a, 0).map(|k| (t.data.clone(), k));
            let result = match &cache_key {
                Some(key) => match self.trait_method_cache.get(key) {
                    Some((rc_a, rc_va, rc_t)) => {
                        // 登记指针导入表后走 Raw::Tm 注解复用
                        let new_decl = if let Raw::Let(n, _, _, u) = decl {
                            Raw::Let(
                                n.clone(),
                                Box::new(Raw::Tm(rc_a.clone(), rc_va.clone())),
                                Box::new(Raw::Tm(rc_t.clone(), rc_va.clone())),
                                u.clone(),
                            )
                        } else {
                            decl.clone()
                        };
                        self.infer_expr(bump, cxt, &new_decl)?
                    }
                    None => {
                        let result = self.infer_expr(bump, cxt, decl)?;
                        if let Tm::Let(_, a_checked, t_checked, _) = result.0 {
                            let clean = no_metas(bump, self, cxt, a_checked).is_none()
                                && no_metas(bump, self, cxt, t_checked).is_none();
                            if clean {
                                let va = self.eval(bump, cxt, cxt.env, a_checked);
                                let rc_a = export(&self.symbol_table, a_checked);
                                let rc_t = export(&self.symbol_table, t_checked);
                                let rc_va = v_to_ref_val(&self.spine, &self.defs, va);
                                // 登记指针导入表
                                self.tm_import.insert(
                                    Rc::as_ptr(&rc_a) as usize,
                                    unsafe {
                                        std::mem::transmute::<&Tm<'a>, &'static Tm<'static>>(
                                            a_checked,
                                        )
                                    },
                                );
                                self.tm_import.insert(
                                    Rc::as_ptr(&rc_t) as usize,
                                    unsafe {
                                        std::mem::transmute::<&Tm<'a>, &'static Tm<'static>>(
                                            t_checked,
                                        )
                                    },
                                );
                                self.val_import
                                    .insert(Rc::as_ptr(&rc_va) as usize, va);
                                self.trait_method_cache
                                    .insert(key.clone(), (rc_a, rc_va, rc_t));
                            }
                        }
                        result
                    }
                },
                None => self.infer_expr(bump, cxt, decl)?,
            };
            // 观察面（ref 2955）：trait 方法调用解析成功 → 方法名 token 的
            // hover，def = trait 方法声明名 span，值 = 实例化后的调用类型。
            self.push_hover(bump, cxt, t_span, def_span.to_span(), result.1);
            Ok(result)
        } else {
            // 观察面（ref 2964-2970）：方法未解析 = 补全现场，键 = 接收者
            // span；收集可满足 trait 的方法名（失败路径才收集，同参考版）。
            {
                let rcv = x.to_span();
                let mut tn: Vec<SmolStr> = Vec::new();
                for (tname, (_p, _o, _st, ms)) in self.tstate.definition.iter() {
                    self.tstate.solver.clean();
                    if self.tstate.solver.can_satisfy(tname, &typ_raw_ref) {
                        for m in ms.iter() {
                            tn.push(m.0.data.clone());
                        }
                    }
                }
                for name in tn {
                    self.completion_table.push((rcv, name));
                }
            }
            // 未解析：no object 错误（LSP 补全收集不移植）
            Err(self.mk_no_object_err(bump, cxt, &t, a, tm))
        }
    }


    fn mk_no_object_err(
        &mut self,
        bump: &Bump,
        cxt: &Cxt<'_>,
        t: &crate::parser_lib::Span<SmolStr>,
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
                pretty_tm(0, names.clone(), &export(&self.symbol_table, tm)),
                pretty_tm(0, names.clone(), &export(&self.symbol_table, q2)),
                t,
            )
        }), vec![])
    }

    // 主 infer / infer_expr（与参考版 elaboration.rs 逐臂对应）
    // --------------------------------------------------------------------------------

    fn infer_expr<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: &Raw,
    ) -> Result<(&'a Tm<'a>, V), Error> {
        // 整个 Raw 节点的 span（参考版 infer_expr 的 t_span 形参；Ob臂
        // qualified 三试的 hover 键跟它对齐，其余站点用各自 token span）
        let raw_span = t.to_span();
        match t {
            // 变量：五级解析链（参考版 Raw::Var 臂逐句）——局部名字 → decl
            // 精确键 → import 别名 → namespace 前缀 → `.name` 后缀唯一回退
            //（歧义报错；排除 namespace 方法键、要求首段可见）
            Raw::Var(x) => {
                if let Some(&blvl) = cxt.names.by_name.get(x.data.as_str()) {
                    let (ty, def_span) = *cxt.names.by_lvl.get(&blvl).expect("by_lvl 缺层级");
                    // 观察面：局部变量使用处现场渲染（与参考版使用处同溝）；
                    // def_span = binder 源码 span（Names.by_lvl 元组携带，合成 binder 为零）。
                    self.push_hover(bump, cxt, x.to_span(), def_span, ty);
                    let ix = cxt.lvl - blvl - 1;
                    return Ok((bump.alloc(Tm::Var(ix)), ty));
                }
                if let Some(e) = cxt.decls.get(x.data.as_str()) {
                    self.push_hover_cached(bump, cxt, x.to_span(), e);
                    let name = bump.alloc_str(x.data.as_str());
                    return Ok((bump.alloc(Tm::Decl(name)), e.vty));
                }
                // import 别名（`import mylib.add` 让裸 `add` → 全键）
                if let Some(full) = self.import_map.get(x.data.as_str()).cloned() {
                    if let Some(e) = cxt.decls.get(full.as_str()) {
                        self.push_hover_cached(bump, cxt, x.to_span(), e);
                        let name = bump.alloc_str(full.as_str());
                        return Ok((bump.alloc(Tm::Decl(name)), e.vty));
                    }
                }
                // namespace 前缀（`package mylib` 内的裸名）
                if let Some(prefix) = &cxt.namespace_prefix {
                    let qualified = format!("{}.{}", prefix, x.data);
                    if let Some(e) = cxt.decls.get(qualified.as_str()) {
                        self.push_hover_cached(bump, cxt, x.to_span(), e);
                        let name = bump.alloc_str(&qualified);
                        return Ok((bump.alloc(Tm::Decl(name)), e.vty));
                    }
                }
                // `.name` 后缀回退：唯一命中解析；多义报错（HashMap 迭代序
                // 不定，任意取一会静默解析错构造子）。namespace 方法键
                //（`TypeHead.method`）排除——实例方法只经 `x.m` 分派。
                let fallback = format!(".{}", x.data);
                let ns_method_keys: std::collections::HashSet<SmolStr> = {
                    let mut s = std::collections::HashSet::new();
                    let mut cur = cxt.namespace;
                    while let Some(ns) = cur {
                        for m in ns.methods.iter() {
                            s.insert(SmolStr::new(format!("{}.{}", ns.type_name, m)));
                        }
                        cur = ns.next;
                    }
                    s
                };
                let matches: Vec<(SmolStr, V, crate::parser_lib::Span<()>)> = cxt
                    .decls
                    .iter()
                    .filter(|(k, _)| k.ends_with(&fallback) && k.len() > fallback.len())
                    .filter(|(k, _)| {
                        // 候选首段必须是 decl 键或本文件可见的 namespace
                        match k.rfind('.') {
                            Some(dot) => {
                                let head = &k[..dot];
                                let first = head.split('.').next().unwrap_or(head);
                                cxt.decls.contains_key(first)
                                    || cxt.namespaces.contains(first)
                            }
                            None => false,
                        }
                    })
                    .filter(|(k, _)| !ns_method_keys.contains(*k))
                    .map(|(k, e)| (k.clone(), e.vty, e.span))
                    .collect();
                if matches.len() == 1 {
                    let (full_key, vty, dspan) = &matches[0];
                    // 观察面（ref 2242）：唯一回退命中也登记 hover（cached 渲染）
                    let rendered = match cxt.decls.get(full_key.as_str()).and_then(|e| e.typ_pretty.clone()) {
                        Some(sp) => (*sp).clone(),
                        None => {
                            let tm = self.quote(bump, cxt, cxt.lvl, *vty);
                            pretty_tm(0, types_names_list(cxt.types), &export(&self.symbol_table, tm))
                        }
                    };
                    self.hover_table.push((x.to_span(), *dspan, rendered));
                    let name = bump.alloc_str(full_key.as_str());
                    return Ok((bump.alloc(Tm::Decl(name)), *vty));
                } else if matches.len() > 1 {
                    let names = matches
                        .iter()
                        .map(|(k, _, _)| k.as_str())
                        .collect::<Vec<_>>()
                        .join(", ");
                    return Err(Error(
                        x.clone().map(|x| {
                            format!("ambiguous name `{}`: could refer to {}", x, names)
                        }),
                        vec![],
                    ));
                }
                Err(Error(x.clone().map(|x| format!("error name not in scope: {}", x)), vec![]))
            }

            // 预检查项无 Raw 结构可推（`check` 在此之前拦截——参考版同款）
            Raw::Tm(_, _) => Err(Error(
                empty_span("internal: cannot infer a pre-checked term".to_string()),
                vec![],
            )),

            // 原生 Nat 字面量（参考版 Raw::Nat 臂）：类型取 decl["Nat"] 登记值
            //（缺失回退 U(0)），值直接建 Nat(k)，quote 回链成 Tm
            Raw::Nat(n) => {
                let nat_type = cxt.decls.get("Nat").map(|e| e.val).unwrap_or_else(v_u0);
                let nat_val = v_xcell(bump.alloc(XCell::Nat(n.data)));
                let nat_tm = self.quote(bump, cxt, cxt.lvl, nat_val);
                Ok((nat_tm, nat_type))
            }

            Raw::Obj(x, t) => {
                // 字段名可缺省（中缀运算符前缀 / 空 `.foo` 补全场景）；参考版
                // Obj 臂兣口 unwrap_or(empty_span("")) 同款
                let t = t.clone().unwrap_or(empty_span(SmolStr::new("")));
                // 观察面：限定访问中间段 hover（ref 2313 同点，无条件调用）
                self.push_qualified_hover(bump, cxt, x);
                if t.data == "mk" {
                    if let Raw::Var(sum_name) = x.as_ref() {
                        return self.infer_expr(
                            bump,
                            cxt,
                            &Raw::Var(sum_name.clone().map(|n| SmolStr::new(format!("{n}.mk")))),
                        );
                    }
                }
                // asMaster/asSlave 链式诊断（参考版同款文案）
                if t.data == "asMaster" || t.data == "asSlave" {
                    if let Raw::Obj(_, Some(prev)) = x.as_ref() {
                        if prev.data == "asMaster" || prev.data == "asSlave" {
                            return Err(Error(
                                t.clone().map(|_| format!(
                                    "`{}` on an already-directed bundle: `asMaster`/`asSlave` rebuild the bundle's ports, so chaining them (`...{}.{}`) would declare every port twice (input + output of the same name) — call them on a fresh `TypeName.create` result instead",
                                    t.data, prev.data, t.data
                                )),
                                vec![],
                            ));
                        }
                    }
                }
                // qualified path 三试（参考版 2307-2343）：全路径 → import 头段
                // 重写 → namespace 前缀
                if !t.data.is_empty() {
                    if let Some(qual) = qualified_path_str(x.as_ref(), &t.data) {
                        if let Some(e) = cxt.decls.get(qual.as_str()) {
                            self.push_hover_cached(bump, cxt, raw_span, e);
                            let name = bump.alloc_str(qual.as_str());
                            return Ok((bump.alloc(Tm::Decl(name)), e.vty));
                        }
                        if let Some((head, rest)) = split_first_segment(&qual) {
                            if let Some(full_head) = self.import_map.get(head.as_str()) {
                                let resolved = format!("{}.{}", full_head, rest);
                                if let Some(e) = cxt.decls.get(resolved.as_str()) {
                                    self.push_hover_cached(bump, cxt, raw_span, e);
                                    let name = bump.alloc_str(&resolved);
                                    return Ok((bump.alloc(Tm::Decl(name)), e.vty));
                                }
                            }
                        }
                        if let Some(prefix) = &cxt.namespace_prefix {
                            let prefixed = format!("{}.{}", prefix, qual);
                            if let Some(e) = cxt.decls.get(prefixed.as_str()) {
                                self.push_hover_cached(bump, cxt, raw_span, e);
                                let name = bump.alloc_str(&prefixed);
                                return Ok((bump.alloc(Tm::Decl(name)), e.vty));
                            }
                        }
                    }
                }
                let (mut tm, mut a) = self.infer_expr(bump, cxt, x)?;
                let mut a_f = self.force_v(bump, cxt, a);
                // 接收者隐式 BindingName 参数展开（参考版 2352-2371）：
                // `Test.create.tree` 等限定访问在构造子带隐式 bn 时也能走
                let _ = &mut tm;
                while v_tag(a_f) == 4 {
                    let p = v_pi_of(a_f);
                    if p.icit != Icit::Impl || !self.is_binding_name_type(bump, cxt, p.dom) {
                        break;
                    }
                    let name_str = cxt
                        .binding_name
                        .clone()
                        .unwrap_or_else(|| SmolStr::new(""));
                    let mk_key = if cxt.decls.contains_key("BindingName.mk") {
                        "BindingName.mk".to_string()
                    } else {
                        cxt.decls
                            .keys()
                            .find(|k| k.ends_with(".BindingName.mk"))
                            .cloned()
                            .unwrap_or_else(|| SmolStr::new("BindingName.mk"))
                            .to_string()
                    };
                    let bn_tm = bump.alloc(Tm::App(
                        bump.alloc(Tm::Decl(bump.alloc_str(&mk_key))),
                        bump.alloc(Tm::LiteralIntro(bump.alloc_str(&name_str))),
                        Icit::Expl,
                    ));
                    let bn_val = self.eval(bump, cxt, cxt.env, bn_tm);
                    tm = bump.alloc(Tm::App(tm, bn_tm, Icit::Impl));
                    let cod = {
                        let env = env_ext(bump, p.env, bn_val);
                        self.eval(bump, cxt, env, p.body)
                    };
                    a_f = self.force_v(bump, cxt, cod);
                }
                a = a_f;
                if v_tag(a) == 7 {
                    if let XCell::Sum { params, cases, .. } = v_xcell_of(a) {
                        // struct：单 case 且名字带 `.mk` → 剥 mk 的构造子类型
                        // 链取字段类型。实例化口径照参考版（elaboration.rs
                        // 2380-2398）：**显式** binder 以接收者自身
                        // （`Obj(接收者)`）实例化——这样 `this.data` 的类型是
                        // `Vec[ModuleDef](this.num)` 而非占位值，下游
                        // `cons m this.data` 的隐式 len 才能解到 `this.num`；
                        // **隐式** binder 用 struct 的实际参数值，缺失回退
                        // 接收者。曾误用 `U(0)` 占位两处：依赖索引字段的投影
                        // 类型全部退化成 `Vec[..](U(0))`（HDL prelude 的
                        // `impl $trait_name$ModuleTree` 处 can't unify）。
                        let receiver = self.eval(bump, cxt, cxt.env, tm);
                        let mut c: Option<Vec<(&str, V)>> = None;
                        if cases.len() == 1 && cases[0].contains(".mk") {
                            let case = cases[0];
                            if let Ok((_, case_typ)) =
                                self.infer_expr(bump, cxt, &Raw::Var(empty_span(SmolStr::new(case))))
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
                                        let this_obj =
                                            v_xcell(bump.alloc(XCell::Obj {
                                                val: receiver,
                                                name: bump.alloc_str(p.name),
                                            }));
                                        let val = if p.icit == Icit::Expl {
                                            this_obj
                                        } else {
                                            param.pop().map(|x| x.val).unwrap_or(this_obj)
                                        };
                                        ret.push((p.name, p.dom));
                                        typ = {
                                            let env = env_ext(bump, p.env, val);
                                            self.eval(bump, cxt, env, p.body)
                                        };
                                    } else {
                                        break;
                                    }
                                }
                                c = Some(ret);
                            }
                        }
                        // 观察面：type-ahead completion 关键集（ref 2431/2446——
                        // 命中与未命中都推，键 = 接收者 span，owned 零渲染）。
                        {
                            let rcv = x.to_span();
                            self.completion_table.extend(
                                c.iter()
                                    .flatten()
                                    .map(|(n, _)| (rcv, SmolStr::new(*n)))
                                    .chain(params.iter().map(|pp| (rcv, SmolStr::new(pp.name)))),
                            );
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
                            // 观察面：字段访问 hover（ref 2422；def_span 降级为字段
                            // token 自身——双值不持字段 binder span，待评估）
                            self.push_hover(bump, cxt, t.to_span(), t.to_span(), ty);
                            return Ok((
                                bump.alloc(Tm::Obj(tm, bump.alloc_str(&t.data))),
                                ty,
                            ));
                        }
                        // L10：Sum 接收者字段未命中 → trait 方法包装
                        //（参考版把 **force 后**的类型传给 trait_wrap）
                        return self.trait_wrap(bump, cxt, t.clone(), a, x, tm);
                    }
                    if let XCell::SumCase { datas, .. } = v_xcell_of(a) {
                        // 接收者类型是构造子值：字段类型在 datas 里
                        let field = datas
                            .iter()
                            .find(|d| d.name == t.data.as_str())
                            .map(|d| d.val);
                        {
                            // 观察面：构造子值字段名 completion（ref 2466 口径）
                            let rcv = x.to_span();
                            self.completion_table
                                .extend(datas.iter().map(|d| (rcv, SmolStr::new(d.name))));
                        }
                        if let Some(ty) = field {
                            // 观察面：构造子字段访问 hover（ref 2455，同样降级 def_span）
                            self.push_hover(bump, cxt, t.to_span(), t.to_span(), ty);
                            return Ok((
                                bump.alloc(Tm::Obj(tm, bump.alloc_str(&t.data))),
                                ty,
                            ));
                        }
                        // L10：SumCase 接收者字段未命中 → trait 方法包装
                        return self.trait_wrap(bump, cxt, t.clone(), a, x, tm);
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
                let cxt2 = self.bind_name(bump, cxt, &x.data, x.to_span(), a_t, a);
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
                Err(Error(x.clone().map(|_| "infer named lambda".to_owned()), vec![]))
            }

            // 应用
            Raw::App(t, u, arg) => {
                // 实参分派：命名 → insertUntilName 后按 Impl 应用；
                // 位置 Impl → 直接应用；位置 Expl → 先 insert_t
                let t_span = t.to_span();
                let t_raw = (**t).clone();
                let tuple_head = is_tuple_mk_head(&t_raw); // 观察面：提前计算（t_raw 后续可能被移动）
                let u_raw = (**u).clone();
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
                        return Err(Error(
                            t_span.map(|_| {
                                format!("icit mismatch {:?} {:?}", i, p.icit)
                            }),
                            vec![],
                        ));
                    }
                    (p.dom, p)
                } else {
                    // Scala 式 apply（参考版）：非 Π 头先试把 `expr(arg)` 脱糖
                    // 成 `expr.apply(arg)`（icit 保持），失败截断 metas 再走
                    // 合成 Π
                    let meta_before = self.metas.len();
                    let apply_obj = Raw::Obj(
                        Box::new(t_raw),
                        Some(empty_span(SmolStr::new("apply"))),
                    );
                    let apply_call =
                        Raw::App(Box::new(apply_obj), Box::new(u_raw), Either::Icit(i));
                    if let Ok(result) = self.infer_expr(bump, cxt, &apply_call) {
                        return Ok(result);
                    }
                    self.metas.truncate(meta_before);
                    // 非 Π 头：合成 Π（定义域 + 余定义域挂洞）与之合一。
                    // 参考版把合成 Π 放在 unify_catch 的首位——忠实复刻，
                    // 只影响报错文案方向。合成 binder（"x"）按参考版
                    // cxt.bind 走全量 bind（env/telescope/pruning 扩展），
                    // 但名字不入表外泄（临时 cxt 只喂 fresh_meta）。
                    let new_meta = self.fresh_meta(bump, cxt, v_u(0));
                    let a = self.eval_fresh(bump, cxt, cxt.env, new_meta);
                    let a_t = self.quote(bump, cxt, cxt.lvl, a);
                    let cxt2 = self.bind_name(bump, cxt, "x", empty_span(()), a_t, a);
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
                // 观察面（ref 2554-2556）：组合子字面每个元素独立 hover
                // 条目（键 = 元素 span，值 = 元素类型 Pi dom）；LSP 取最窄 span。
                if tuple_head {
                    self.push_hover(bump, cxt, u.to_span(), u.to_span(), a);
                }
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
                let cxt2 = self.bind_name(bump, cxt, &x.data, x.to_span(), a_t, a_eval);
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
                // Raw::Tm 注解是缓存的已查类型（trait 方法 Π 链复用）——经
                // 指针导入表取回本机结果，不再过 check_universe（参考版同款）
                let (a_checked, va) = if let Raw::Tm(rc_tm, rc_ty) = a_ty.as_ref() {
                    let tm: &'a Tm<'a> = self.tm_import_lookup(rc_tm);
                    let v = self.val_import_lookup(rc_ty);
                    (tm, v)
                } else {
                    let (a_checked, _) = self.check_universe(bump, cxt, a_ty)?;
                    let va = self.eval(bump, &cxt, cxt.env, a_checked);
                    (a_checked, va)
                };
                // 绑定名：let RHS 检查前设置（隐式 BindingName 参数合成用）
                let cxt_named = cxt.with_binding_name(x.data.clone());
                let t_checked = self.check(bump, &cxt_named, t2, va)?;
                let vt = self.eval(bump, &cxt, cxt.env, t_checked);
                let name: &'a str = bump.alloc_str(&x.data);
                // 观察面：let 无标注 → inlay 展示推断值类型（参考版 2601，
                // 注意其传的是右值语 vt、offset 取 binder 名结束）
                if matches!(a_ty.as_ref(), Raw::Hole(_)) {
                    self.push_inlay_hint(bump, cxt, x.to_span().end_offset, vt);
                }
                // 观察面：let binder 定义处 hover（参考版 2627 同点位）
                self.push_hover(bump, cxt, x.to_span(), x.to_span(), va);
                let cxt2 = self.define_name(bump, cxt, &x.data, x.to_span(), a_checked, t_checked, vt, va);
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

            // match 可推断（参考版 L13）：scrutinee 类型挂 fresh meta，经
            // check 编译后返回
            Raw::Match(_, _) => {
                let a_meta = self.fresh_meta(bump, cxt, v_u(0));
                let a = self.eval_fresh(bump, cxt, cxt.env, a_meta);
                let tm = self.check(bump, cxt, t, a)?;
                Ok((tm, a))
            }

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

            // 构造子值（Decl::Enum 注册期构造 / 程序内 SumCase）：typ 只推
            // 断不检查；**index** 由 typ 值的 cases 表 position 查得（参考
            // 版 2687-2708）；typ 存**展开形**（求值后的类型 quote——下游
            // pretty/Nat 字面量/投影都假设展开形）
            Raw::SumCase {
                typ,
                case_name,
                datas,
                is_trait,
            } => {
                let (typ_checked, _) = self.infer_expr(bump, cxt, typ)?;
                let typ_val = self.eval(bump, cxt, cxt.env, typ_checked);
                let index = match v_tag(typ_val) {
                    7 => match v_xcell_of(typ_val) {
                        XCell::Sum { cases, .. } => cases
                            .iter()
                            .position(|c| *c == case_name.data.as_str())
                            .ok_or_else(|| {
                                Error(
                                    case_name
                                        .clone()
                                        .map(|x| format!("no such constructor `{}`", x)),
                                    vec![],
                                )
                            })? as u32,
                        _ => {
                            return Err(Error(
                                case_name.clone().map(|_| {
                                    format!(
                                        "expected a sum type, got {}",
                                        debug_val(&self.spine, &self.defs, typ_val)
                                    )
                                }),
                                vec![],
                            ));
                        }
                    },
                    _ => {
                        return Err(Error(
                            case_name.clone().map(|_| {
                                format!(
                                    "expected a sum type, got {}",
                                    debug_val(&self.spine, &self.defs, typ_val)
                                )
                            }),
                            vec![],
                        ));
                    }
                };
                let mut ds: Vec<SumDataT<'_>> = Vec::with_capacity(datas.len());
                for (n, raw, i) in datas {
                    let (tm, _) = self.infer_expr(bump, cxt, raw)?;
                    ds.push(SumDataT {
                        name: bump.alloc_str(&n.data),
                        val: tm,
                        icit: *i,
                    });
                }
                let typ_expanded = self.quote(bump, cxt, cxt.lvl, typ_val);
                Ok((
                    bump.alloc(Tm::SumCase {
                        typ: typ_expanded,
                        index,
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
        // package 前缀（参考版 infer 入口）：Def/Enum/TraitDecl/Class 的名字
        // 加 `pkg.` 前缀（方法名不加——trait_wrap 与 impl 方法匹配按写出的
        // 名字分派；Package/Import 自身不前缀）
        let d_owned;
        let d = if matches!(d, Decl::Package { .. } | Decl::Import { .. }) {
            d
        } else if let Some(prefix) = &cxt.namespace_prefix {
            d_owned = prefix_decl_name(d, prefix);
            &d_owned
        } else {
            d
        };
        self.infer_after_prefix(bump, cxt, d)
    }

    /// 已前缀的 decl 推断（class Phase B 复用，免二次前缀——参考版
    /// `infer_after_prefix`）。
    fn infer_after_prefix<'a>(
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
                let this_meta = self.metas.len() as u32;
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
                // redefine 报错），检查体，再 wrap_match_in_call 包装。
                let fake = self.fake_bind(bump, cxt, &name.data, typ_tm, vtyp)?;
                let t_checked = self.check(bump, &fake, &bod, vtyp)?;
                let t_tm = self.wrap_match_in_call(bump, name.data.as_str(), t_checked);
                // solve_multi_trait(this_meta, **true**)（参考版 Def 臂
                // elaboration.rs:972）：失败 **返回 Err** 交上层（`.map_err(
                // |e| Error(name.span, ..))?`），不是 panic——参考版没有
                // unwrap。孪生早前误写成 unwrap，会让 trait 求解失败直接崩，
                // 掩盖后续的 Nat 默认化重试与丰富错误文案路径（HDL prelude
                // decl 308 的 `impl Add for UInt[width]` 就是这样从 panic
                // 变成可诊断的 Err，推进 171→308）。
                self.solve_multi_trait_ref(bump, &fake, this_meta, true)
                    .map_err(|e| {
                        let msg = e.clone();
                        Error(name.clone().map(move |_| msg.clone()), vec![])
                    })?;
                // no_metas 三元检查 + Nat 默认化重试 + 丰富错误文案
                if let Some((meta_names, oty)) =
                    no_metas(bump, self, &fake, t_tm)
                {
                    // --- Nat 默认化（Lean 式回退）：把类型值 meta 批量解成
                    // Nat 再重试 trait 求解，失败回滚 ---
                    let saved_meta = self.metas.clone();
                    let nat_val = cxt.decls.get("Nat").map(|e| e.val).unwrap_or_else(v_u0);
                    let nat_ok = is_nat_sum_v(nat_val);
                    let nat_solved = if nat_ok {
                        let to_default: Vec<usize> = {
                            // 先拷出 Unsolved 类型值，避免闭包内 self.force_v(&mut)
                            // 与 self.metas 借用冲突
                            let unsolved: Vec<(usize, V)> = self
                                .metas
                                .iter()
                                .enumerate()
                                .filter_map(|(i, entry)| match entry {
                                    MetaEntry::Unsolved(ty, ..) => Some((i, *ty)),
                                    _ => None,
                                })
                                .collect();
                            unsolved
                                .into_iter()
                                .filter(|(_, ty)| v_tag(self.force_v(bump, cxt, *ty)) == 3)
                                .map(|(i, _)| i)
                                .collect()
                        };
                        if to_default.is_empty() {
                            false
                        } else {
                            for idx in &to_default {
                                if let MetaEntry::Unsolved(ty, ..) = &self.metas[*idx] {
                                    let ty = *ty;
                                    self.metas[*idx] = MetaEntry::Solved(nat_val, ty);
                                }
                            }
                            let _ = self.solve_multi_trait_ref(bump, &fake, this_meta, false);
                            if no_metas(bump, self, &fake, t_tm).is_none() {
                                true
                            } else {
                                self.metas = saved_meta;
                                false
                            }
                        }
                    } else {
                        false
                    };
                    if !nat_solved {
                        return Err(self.mk_unsolved_meta_err(
                            bump, &fake, t_tm, meta_names, oty, &name.data,
                        ));
                    }
                }
                // 登记值：无参 def 的 body 含全局副作用（REPLAY_GLOBAL_OPS）
                // 时存 `Decl(name)` 占位不求值（副作用对当前 mutable 状态生
                // 效在调用点重放——`def_needs_replay`）；否则在**含存根的
                // fake 表**下求值（自引用停在国内）。
                let vt = if params.is_empty() {
                    let mut visiting = std::collections::HashSet::new();
                    let mut found = false;
                    tm_scan_global_ops(&self.mutable, &fake.decls, t_tm, &mut visiting, &mut found);
                    if found {
                        v_xcell(bump.alloc(XCell::Decl { name: bump.alloc_str(&name.data) }))
                    } else {
                        self.eval(bump, &fake, fake.env, t_tm)
                    }
                } else {
                    self.eval(bump, &fake, fake.env, t_tm)
                };
                // 观察面：def 无显式返回类型 → inlay 推断返回类型
                // （参考版 1157-1176：peel_pi 后 quote 于 ret_lvl，no_metas
                // 干净才推；锚点 = 最后参数结束+1，无参则名结束）
                if matches!(*ret_type, Raw::Hole(_)) {
                    let (ret_val, ret_lvl, peeled) = self.peel_pi_collect(bump, cxt, vtyp);
                    let ret_tm = self.quote(bump, cxt, ret_lvl, ret_val);
                    if no_metas(bump, self, cxt, ret_tm).is_none() {
                        let mut names = types_names_list(cxt.types);
                        // peeled 为外→内剥集序；List 头 = 最内层 → 逆序 prepend
                        for pn in peeled.iter().rev() {
                            names = names.prepend(pn.clone());
                        }
                        let mut label = format!(
                            ": {}",
                            pretty_tm(0, names, &export(&self.symbol_table, ret_tm))
                        );
                        const MAX_LEN: usize = 80;
                        if label.chars().count() > MAX_LEN {
                            let truncated: String =
                                label.chars().take(MAX_LEN.saturating_sub(1)).collect();
                            label = format!("{}\u{2026}", truncated);
                        }
                        let pos = params
                            .last()
                            .map(|p| p.1.to_span().end_offset + 1)
                            .unwrap_or_else(|| name.to_span().end_offset);
                        self.inlay_hint_table.push((pos, label));
                    }
                }
                // 观察面：def 名定义处 hover（参考版 1153 同点位）
                self.push_hover(bump, cxt, name.to_span(), name.to_span(), vtyp);
                let out = self.decl_reg(bump, cxt, &name.data, name.to_span(), t_tm, vt, typ_tm, vtyp, None);
                Ok((DeclOut::Def { name: bump.alloc_str(&name.data) }, out))
            }
            Decl::Println(t) => {
                // 立即 nf + pretty（参考版 run() 口径；defer_println 不移植）
                let (tm, _) = self.infer_expr(bump, cxt, t)?;
                let t_pretty = {
                    let v = self.eval(bump, cxt, cxt.env, tm);
                    let q = self.quote(bump, cxt, cxt.lvl, v);
                    let e = export(&self.symbol_table, q);
                    let names = types_names_list(cxt.types);
                    pretty_tm(0, names, &e)
                };
                Ok((DeclOut::Println(tm, t_pretty), clone_cxt(cxt)))
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
                let new_params: Vec<(crate::parser_lib::Span<SmolStr>, Icit, Raw)> = params
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
                let new_cases: Vec<(crate::parser_lib::Span<SmolStr>, Raw)> = cases
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
                let cases_spanned: Vec<crate::parser_lib::Span<SmolStr>> = new_cases
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
                // 登记值在含存根的 fake 表下求值（注意用**原 cxt 的 decl**：
                // Enum 臂与 Def 臂不同，参考版在此用 `cxt.decl`）
                let vt = self.eval(bump, cxt, fake.env, t_tm);
                let mut cxt = self.decl_reg(bump, cxt, &name.data, name.to_span(), t_tm, vt, typ_tm, vtyp, None);
                // 逐构造子注册：体 = λ(隐式参数, 字段) → SumCase{typ: ret, datas: 字段自身}；
                // **限定键 `EnumName.caseName` 登记**（无裸名别名——裸名靠 Var
                // 的后缀 fallback 解析；参考版 1322 同款）
                for ((case_name, binders, ret), (_, ctor_ty)) in
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
                    let case_key = format!("{}.{}", name.data, case_name.data);
                    cxt = self.decl_reg(bump, &cxt, &case_key, case_name.to_span(), t_tm, vt, typ_tm, vtyp, None);
                }
                Ok((DeclOut::Enum, cxt))
            }
            // trait 声明（参考版 1672-1767）：supertrait 经前缀解析 + DFS
            // 合并方法（路径集环检测，钻石不误报）；Self + params 组 enum
            // 参数（outParam 参数类型是 `outParam(...)` 应用）；方法表（含
            // 默认体）记入 trait_definition 与 solver.set_trait_out_params；
            // 本体脱糖成单构造子（`{Name}.mk`）的 trait enum（is_trait=true）
            Decl::TraitDecl { name, params, supertraits, methods, assoc_defaults } => {
                // X3：supertrait 名经 namespace 前缀解析
                let resolved_supertraits: Vec<crate::parser_lib::Span<SmolStr>> = supertraits
                    .iter()
                    .map(|s| {
                        let bare = s.data.clone();
                        let resolved = if self.tstate.definition.contains_key(&bare) {
                            bare
                        } else if let Some(prefix) = &cxt.namespace_prefix {
                            let qualified = SmolStr::new(format!("{}.{}", prefix, bare));
                            if self.tstate.definition.contains_key(&qualified) {
                                qualified
                            } else {
                                bare
                            }
                        } else {
                            bare
                        };
                        s.clone().map(|_| resolved.clone())
                    })
                    .collect();
                // DFS 合并 supertrait 方法（路径环检测）
                let mut all_methods = methods.clone();
                let mut stack: Vec<(SmolStr, std::collections::HashSet<SmolStr>)> =
                    resolved_supertraits
                        .iter()
                        .map(|s| {
                            let mut path = std::collections::HashSet::new();
                            path.insert(name.data.clone());
                            (s.data.clone(), path)
                        })
                        .collect();
                while let Some((st_name, path)) = stack.pop() {
                    if path.contains(&st_name) {
                        return Err(Error(
                            empty_span(format!(
                                "cyclic supertrait: `{}` appears twice in the chain",
                                st_name
                            )),
                            vec![],
                        ));
                    }
                    let mut path = path;
                    path.insert(st_name.clone());
                    if let Some((_, _, st_sts, st_methods)) =
                        self.tstate.definition.get(&st_name).cloned()
                    {
                        for st_st in &st_sts {
                            if path.contains(&st_st.data) {
                                return Err(Error(
                                    empty_span(format!(
                                        "cyclic supertrait: `{}` appears twice in the chain",
                                        st_st.data
                                    )),
                                    vec![],
                                ));
                            }
                            stack.push((st_st.data.clone(), path.clone()));
                        }
                        for st_m in &st_methods {
                            let name_exists = all_methods.iter().any(|(mn, _, _, _)| mn.data == st_m.0.data);
                            if !name_exists {
                                all_methods.push(st_m.clone());
                            }
                        }
                    }
                }
                self.tstate.solver.new_trait(name.data.clone());
                let mut param = vec![(
                    name.clone().map(|_| SmolStr::new("Self")),
                    Raw::Hole(name.to_span()),
                    Icit::Impl,
                )];
                param.append(&mut params.clone());
                let out_param = param
                    .iter()
                    .map(|x| match &x.1 {
                        Raw::App(t, ..)
                            if matches!(t.as_ref(), Raw::Var(d) if d.data == "outParam") =>
                        {
                            true
                        }
                        _ => false,
                    })
                    .collect::<Vec<_>>();
                self.tstate
                    .solver
                    .set_trait_out_params(name.data.clone(), out_param.clone());
                self.tstate.definition.insert(
                    name.data.clone(),
                    (param.clone(), out_param.clone(), resolved_supertraits.clone(), all_methods.clone()),
                );
                self.tstate.out_param.insert(name.data.clone(), out_param);
                // 关联类型默认值
                for (aname, adefault) in assoc_defaults {
                    self.tstate
                        .assoc_defaults
                        .insert((name.data.clone(), aname.clone()), adefault.clone());
                }
                let cxt2 = clone_cxt(cxt);
                let new_cases = vec![(
                    name.clone().map(|x| SmolStr::new(format!("{x}.mk"))),
                    all_methods
                        .iter()
                        .map(|(mn, mparams, mret, _mb)| {
                            (
                                mn.clone(),
                                std::iter::once((
                                    mn.clone().map(|_| SmolStr::new("this")),
                                    Raw::Var(mn.clone().map(|_| SmolStr::new("Self"))),
                                    Icit::Expl,
                                ))
                                .chain(mparams.iter().cloned())
                                .rev()
                                .fold(mret.clone(), |a, b| {
                                    Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a))
                                }),
                                Icit::Expl,
                            )
                        })
                        .collect(),
                    None,
                )];
                let (_, c) = self.infer_after_prefix(bump, &cxt2, &Decl::Enum {
                    is_trait: true,
                    name: name.clone(),
                    params: param,
                    cases: new_cases,
                })?;
                Ok((DeclOut::Trait, c))
            }
            // impl 声明（参考版 1333-1671）：inherent（方法注册进类型
            // namespace，`x.m` 经 namespace 条目分派 + 算符方法登记
            // symbol_table）/ trait（实例注册 + from_class 过滤 + 默认方法
            // 填充 + assoc 默认补全 + `Trait.mk` 组装）。
            Decl::ImplDecl { name, params, trait_name, trait_params, methods, inherent, from_class } => {
                let mut cxt = clone_cxt(cxt);
                if *inherent {
                    // ── inherent impl（`impl Foo { ... }`）──
                    let name_raw = params
                        .iter()
                        .rev()
                        .fold(name.clone(), |a, b| {
                            Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a))
                        });
                    let (name_t, _) = self.infer_expr(bump, &cxt, &name_raw)?;
                    let name_v = self.eval(bump, &cxt, cxt.env, name_t);
                    let type_name = raw_ctor_name(name).unwrap_or_else(|| SmolStr::new(""));
                    // 只有实例方法参与 `x.method` 分派
                    let method_names: Vec<SmolStr> = methods
                        .iter()
                        .filter(|(_, is_static)| !is_static)
                        .filter_map(|(x, _)| match x {
                            Decl::Def { name, .. } => Some(name.data.clone()),
                            _ => None,
                        })
                        .collect();
                    cxt.namespace = Some(bump.alloc(NsCons {
                        val: name_v,
                        methods: bump.alloc_slice_fill_iter(method_names.iter().cloned()),
                        type_name: bump.alloc_str(&type_name),
                        next: cxt.namespace,
                    }));
                    for (decl, is_static) in methods.iter() {
                        match decl {
                            Decl::Def { name: name_d, params: p, ret_type, body } => {
                                if !is_static {
                                    // 算符方法登记 symbol_table（体是 helper
                                    // 直接应用时记 (helper, 元数) → 算符）
                                    if is_operator_method_name(&name_d.data) {
                                        if let Some(head) = raw_ctor_name(body) {
                                            self.symbol_table.insert(
                                                (head, params.len() + 1 + p.len()),
                                                name_d.data.clone(),
                                            );
                                        }
                                    }
                                    // 实例方法：前置 `this` 参数、注册为
                                    // `TypeName.method`（走 infer_after_prefix
                                    // 免二次前缀——方法名已全限定）
                                    let t = self.infer_after_prefix(bump, &cxt, &Decl::Def {
                                        name: name_d.clone().map(|x| {
                                            SmolStr::new(format!("{}.{x}", type_name))
                                        }),
                                        params: params
                                            .iter()
                                            .cloned()
                                            .chain(std::iter::once((
                                                name_d.to_span().map(|_| SmolStr::new("this")),
                                                name.clone(),
                                                Icit::Expl,
                                            )))
                                            .chain(p.iter().cloned())
                                            .collect(),
                                        ret_type: ret_type.clone(),
                                        body: body.clone(),
                                    })?;
                                    cxt = t.1;
                                } else {
                                    let static_name = format!("{}.{}", type_name, name_d.data);
                                    let t = self.infer_after_prefix(bump, &cxt, &Decl::Def {
                                        name: name_d.clone().map(|_| SmolStr::new(static_name.clone())),
                                        params: params.iter().cloned().chain(p.iter().cloned()).collect(),
                                        ret_type: ret_type.clone(),
                                        body: body.clone(),
                                    })?;
                                    cxt = t.1;
                                }
                            }
                            _ => {
                                return Err(Error(
                                    name.to_span().map(|_| {
                                        "unsupported method declaration in inherent impl".to_string()
                                    }),
                                    vec![],
                                ));
                            }
                        }
                    }
                } else {
                    // ── trait impl（`impl Trait for Ty`）──
                    // I3b：trait 名经 namespace 前缀解析（裸名优先）
                    let trait_full: SmolStr = {
                        let bare = trait_name.data.clone();
                        if self.tstate.out_param.contains_key(&bare) {
                            bare
                        } else if let Some(prefix) = &cxt.namespace_prefix {
                            let qualified = SmolStr::new(format!("{}.{}", prefix, bare));
                            if self.tstate.out_param.contains_key(&qualified) {
                                qualified
                            } else {
                                bare
                            }
                        } else {
                            bare
                        }
                    };
                    let mut temp_cxt = clone_cxt(&cxt);
                    for (x, a, _) in params.iter() {
                        let (a_checked, _) = self.check_universe(bump, &temp_cxt, a)?;
                        let a_eval = self.eval(bump, &temp_cxt, temp_cxt.env, a_checked);
                        let a_t = self.quote(bump, &temp_cxt, temp_cxt.lvl, a_eval);
                        temp_cxt = self.bind_name(bump, &temp_cxt, &x.data, x.to_span(), a_t, a_eval);
                    }
                    let (typ_tm, _) = self.check_universe(bump, &temp_cxt, name)?;
                    let typ_val = self.eval(bump, &temp_cxt, temp_cxt.env, typ_tm);
                    // 观察面（参考版 1452-1486 impl header hover 对）：
                    //  A) trait 名 token → trait 声明处（点 trait_name 跳声明，
                    //     而非实现自跳）；B) 实现方法名 token → trait 方法声明
                    //     名 span，值 = 方法自身 Pi 类型（实现参数上下文求值）。
                    if let Some(e) = cxt.decls.get(trait_full.as_str()) {
                        let (espan, evty) = (e.span, e.vty);
                        self.push_hover(bump, &cxt, trait_name.to_span(), espan, evty);
                    }
                    if let Some((_, _, _, trait_methods)) =
                        self.tstate.definition.get(&trait_full).cloned()
                    {
                        for (decl, _) in methods.iter() {
                            if let Decl::Def { name: def_name, params: m_params, ret_type: m_ret, .. } = decl {
                                if let Some((tm_name, _, _, _)) =
                                    trait_methods.iter().find(|(mn, _, _, _)| mn.data == def_name.data)
                                {
                                    let mty = m_params.iter().rev().fold(m_ret.clone(), |a, b| {
                                        Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a))
                                    });
                                    let mty_val = self
                                        .infer_expr(bump, &temp_cxt, &mty)
                                        .map(|(t, _)| self.eval(bump, &temp_cxt, temp_cxt.env, t))
                                        .unwrap_or_else(|_| v_u(0));
                                    self.push_hover(bump, &temp_cxt, def_name.to_span(), tm_name.to_span(), mty_val);
                                }
                            }
                        }
                    }
                    // 保留全部参数（含 outParam）——求解器要区分仅 out 参数
                    // 不同的实例（Into[String] vs Into[Bool]）
                    let mut trait_param: Vec<Rc<CVal>> = {
                        let fv = self.force_v(bump, &cxt, typ_val);
                        vec![v_to_ref_val(&self.spine, &self.defs, fv)]
                    };
                    for a in trait_params.iter() {
                        let (a_checked, _) = self.infer_expr(bump, &temp_cxt, a)?;
                        let a_eval = self.eval(bump, &temp_cxt, temp_cxt.env, a_checked);
                        let fv = self.force_v(bump, &cxt, a_eval);
                        trait_param.push(v_to_ref_val(
                            &self.spine,
                            &self.defs,
                            fv,
                        ));
                    }
                    let out_param = self
                        .tstate
                        .out_param
                        .get(&trait_full)
                        .ok_or(Error(
                            trait_name.clone().map(|n| format!("trait `{}` not declared", n)),
                            vec![],
                        ))?
                        .clone();
                    let typ_name = format!("{:?}{:?}", trait_full, trait_param);
                    let inst = Instance {
                        assertion: Assertion {
                            name: trait_full.clone(),
                            arguments: trait_param,
                        },
                        dependencies: crate::list::List::new(),
                        lvl: trait_name
                            .clone()
                            .to_span()
                            .map(|_| SmolStr::new(typ_name.clone())),
                    };
                    self.tstate.solver.impl_trait_for(trait_full.clone(), inst);
                    // from_class 过滤 + 默认方法填充
                    let mut methods = methods.clone();
                    let mut class_method_count = methods.len();
                    if let Some((_, _, _, trait_methods)) =
                        self.tstate.definition.get(&trait_full).cloned()
                    {
                        if *from_class {
                            methods.retain(|(decl, is_static)| {
                                !is_static
                                    && match decl {
                                        Decl::Def { name, .. } => trait_methods
                                            .iter()
                                            .any(|(tm, _, _, _)| tm.data == name.data),
                                        _ => false,
                                    }
                            });
                        }
                        class_method_count = methods.len();
                        for (tm_name, tm_params, tm_ret, tm_default_body) in trait_methods {
                            let has_impl = methods.iter().any(|(decl, _)| match decl {
                                Decl::Def { name, .. } => name.data == tm_name.data,
                                _ => false,
                            });
                            if !has_impl {
                                if let Some(default_body) = tm_default_body {
                                    methods.push((
                                        Decl::Def {
                                            name: tm_name,
                                            params: tm_params,
                                            ret_type: tm_ret,
                                            body: default_body,
                                        },
                                        false,
                                    ));
                                } else {
                                    return Err(Error(
                                        tm_name.map(|n| {
                                            format!("method `{}` has no default implementation", n)
                                        }),
                                        vec![],
                                    ));
                                }
                            }
                        }
                    }
                    // 关联类型缺省补全（trailing 顺序）
                    let mut trait_params = trait_params.clone();
                    if let Some((trait_params_def, _, _, _)) =
                        self.tstate.definition.get(&trait_full).cloned()
                    {
                        let assoc_names: Vec<(usize, SmolStr)> = trait_params_def
                            .iter()
                            .enumerate()
                            .filter_map(|(i, (pname, _, _))| {
                                if self
                                    .tstate
                                    .assoc_defaults
                                    .contains_key(&(trait_full.clone(), pname.data.clone()))
                                {
                                    Some((i, pname.data.clone()))
                                } else {
                                    None
                                }
                            })
                            .collect();
                        if !assoc_names.is_empty() {
                            let expected_total = trait_params_def.len() - 1;
                            let expected_explicit = expected_total - assoc_names.len();
                            let provided_total = trait_params.len();
                            let provided_assoc = provided_total.saturating_sub(expected_explicit);
                            let missing_count = assoc_names.len().saturating_sub(provided_assoc);
                            if missing_count > 0 {
                                for (_, aname) in assoc_names.iter().skip(provided_assoc) {
                                    if let Some(default_type) = self
                                        .tstate
                                        .assoc_defaults
                                        .get(&(trait_full.clone(), aname.clone()))
                                    {
                                        trait_params
                                            .push(default_type.clone().unwrap_or(Raw::Hole(empty_span(()))));
                                    } else {
                                        return Err(Error(
                                            empty_span(format!(
                                                "associated type `{}` has no default value",
                                                aname
                                            )),
                                            vec![],
                                        ));
                                    }
                                }
                            }
                        }
                    }
                    let mut ret = std::iter::once(name.clone())
                        .chain(trait_params.iter().cloned())
                        .fold(
                            Raw::Var(empty_span(SmolStr::new(format!("{}.mk", trait_full)))),
                            |ret, x| {
                                Raw::App(Box::new(ret), Box::new(x), Either::Icit(Icit::Impl))
                            },
                        );
                    // class 生成的 impl：方法已由 inherent impl 以
                    // `TypeName.method` 登记——引用这些 def 而不是把体重查
                    // 成 λ（单一 elaboration、单一语义源，方法体内可经 this
                    // 调兄弟方法）
                    let class_type_name = if *from_class { raw_ctor_name(name) } else { None };
                    for (i, (decl, _)) in methods.into_iter().enumerate() {
                        if let Decl::Def { name: def_name, params, ret_type: _, body } = decl {
                            if is_operator_method_name(&def_name.data) {
                                if let Some(head) = raw_ctor_name(&body) {
                                    if class_type_name.is_none() {
                                        self.symbol_table.insert(
                                            (head, params.len() + 1),
                                            def_name.data.clone(),
                                        );
                                    }
                                }
                            }
                            let method_expr = match &class_type_name {
                                Some(ty) if i < class_method_count => Raw::Var(
                                    def_name.map(|n| SmolStr::new(format!("{}.{}", ty, n))),
                                ),
                                _ => Raw::Lam(
                                    def_name.map(|_| SmolStr::new("this")),
                                    Either::Icit(Icit::Expl),
                                    Box::new(
                                        params
                                            .iter()
                                            .rev()
                                            .fold(body, |ret, x| {
                                                Raw::Lam(
                                                    x.0.clone(),
                                                    Either::Icit(x.2),
                                                    Box::new(ret),
                                                )
                                            }),
                                    ),
                                ),
                            };
                            ret = Raw::App(
                                Box::new(ret),
                                Box::new(method_expr),
                                Either::Icit(Icit::Expl),
                            );
                        }
                    }
                    // 实例本身登记为合成名 def
                    let (_, c) = self.infer_after_prefix(bump, &cxt, &Decl::Def {
                        name: empty_span(SmolStr::new(typ_name.clone())),
                        params: params.clone(),
                        ret_type: trait_params.into_iter().fold(
                            Raw::App(
                                Box::new(Raw::Var(empty_span(trait_full.clone()))),
                                Box::new(name.clone()),
                                Either::Icit(Icit::Impl),
                            ),
                            |a, b| {
                                Raw::App(Box::new(a), Box::new(b), Either::Icit(Icit::Impl))
                            },
                        ),
                        body: ret,
                    })?;
                    cxt = c;
                }
                Ok((DeclOut::TraitImpl, cxt))
            }
            Decl::Package { path } => {
                let pkg_path = path
                    .iter()
                    .map(|s| s.data.as_str())
                    .collect::<Vec<_>>()
                    .join(".");
                let mut cxt = clone_cxt(cxt);
                cxt.namespace_prefix = Some(SmolStr::new(&pkg_path));
                // G6：声明的 package 记为可见 namespace（后缀 fallback 准入）
                Rc::make_mut(&mut cxt.namespaces).insert(SmolStr::new(&pkg_path));
                Ok((DeclOut::Package, cxt))
            }
            Decl::Import { prefix, names, wildcard } => {
                let prefix_str = prefix.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(".");
                let mut cxt = clone_cxt(cxt);
                // G6：import 的 namespace 记为可见
                if !prefix_str.is_empty() {
                    Rc::make_mut(&mut cxt.namespaces).insert(SmolStr::new(&prefix_str));
                }
                // G4：拒绝单名 import
                if prefix.is_empty() && !names.is_empty() {
                    return Err(Error(
                        empty_span(format!(
                            "single-name import `{}` is not supported; import a package namespace instead (e.g. `import ns.{}`)",
                            names.join(", "),
                            names.join(", ")
                        )),
                        vec![],
                    ));
                }
                // 收集 (alias, 全键) 对——不动 decl 表（import 是文件局部可见性）
                let mut aliases: Vec<(SmolStr, SmolStr)> = vec![];
                if *wildcard {
                    let prefix_search = format!("{}.", prefix_str);
                    let matched: Vec<SmolStr> = cxt
                        .decls
                        .keys()
                        .filter(|k| k.starts_with(&prefix_search))
                        .cloned()
                        .collect();
                    if matched.is_empty() {
                        return Err(Error(
                            empty_span(format!(
                                "cannot import '{}': no such namespace in scope",
                                prefix_str
                            )),
                            vec![],
                        ));
                    }
                    for full in matched {
                        let stripped = SmolStr::new(full.strip_prefix(&prefix_search).unwrap());
                        aliases.push((stripped, full));
                    }
                    // prefix 自身是 decl（如 `import mylib.Tree` 且
                    // `mylib.Tree` 是类型）时也带进来
                    if let Some(k) = cxt
                        .decls
                        .keys()
                        .find(|k| k.as_str() == prefix_str)
                        .cloned()
                    {
                        let last = prefix.last().unwrap().clone();
                        aliases.push((last, k));
                    }
                } else {
                    for n in names {
                        let full_name = SmolStr::new(format!("{}.{}", prefix_str, n));
                        if !cxt.decls.contains_key(full_name.as_str()) {
                            return Err(Error(
                                empty_span(format!(
                                    "cannot import '{}': not in scope",
                                    full_name
                                )),
                                vec![],
                            ));
                        }
                        aliases.push((n.clone(), full_name.clone()));
                        // 点状成员别名：`import mylib.Tree` 带进 `Tree.mk`
                        // / `Tree.leaf`…（`.mk` 简写与限定成员访问保活）
                        let member_prefix = format!("{}.", full_name);
                        let members: Vec<SmolStr> = cxt
                            .decls
                            .keys()
                            .filter(|k| k.starts_with(&member_prefix))
                            .cloned()
                            .collect();
                        for full in members {
                            let stripped = full.strip_prefix(&member_prefix).unwrap();
                            aliases.push((
                                SmolStr::new(format!("{}.{}", n, stripped)),
                                full,
                            ));
                        }
                    }
                }
                // I1：冲突别名拒绝
                for (alias, full) in aliases {
                    if let Some(existing) = self.import_map.get(&alias) {
                        if existing != &full {
                            return Err(Error(
                                empty_span(format!(
                                    "ambiguous import: '{}' refers to both '{}' and '{}'",
                                    alias, existing, full
                                )),
                                vec![],
                            ));
                        }
                    } else {
                        self.import_map.insert(alias, full);
                    }
                }
                Ok((DeclOut::Import, cxt))
            }
            Decl::Derive { .. } => {
                panic!("Derive should have been expanded before elaboration")
            }
            Decl::Class { name, params, items, traits } => {
                // ══ Phase A：在 create 的参数上下文里逐字段推类型（struct
                // 尚不存在）══（参考版 1861-1967 逐句）
                let mut a_cxt = clone_cxt(cxt);
                for (pname, pty, _) in params.iter() {
                    let (a_checked, _) = self.check_universe(bump, &a_cxt, pty)?;
                    let a_eval = self.eval(bump, &a_cxt, a_cxt.env, a_checked);
                    let a_t = self.quote(bump, &a_cxt, a_cxt.lvl, a_eval);
                    a_cxt = self.bind_name(bump, &a_cxt, &pname.data, pname.to_span(), a_t, a_eval);
                }
                if traits.iter().any(|(t, _)| t.data == "Module") {
                    let (a_checked, _) = self.check_universe(
                        bump,
                        &a_cxt,
                        &Raw::Var(empty_span(SmolStr::new("BindingName"))),
                    )?;
                    let a_eval = self.eval(bump, &a_cxt, a_cxt.env, a_checked);
                    let a_t = self.quote(bump, &a_cxt, a_cxt.lvl, a_eval);
                    a_cxt = self.bind_name(
                        bump,
                        &a_cxt,
                        "bn",
                        empty_span(()),
                        a_t,
                        a_eval,
                    );
                }
                let mut struct_field_types: Vec<(crate::parser_lib::Span<SmolStr>, Raw)> =
                    Vec::new();
                // Phase-A 复用数据（参考版 Rc 四元组的导出侧；本机侧经
                // 指针导入表取回）
                struct PreA {
                    name: crate::parser_lib::Span<SmolStr>,
                    rc_tm: Rc<CTm>,
                    rc_a: Rc<CTm>,
                    rc_ty: Rc<CVal>,
                }
                let mut prechecked: Vec<PreA> = Vec::new();
                let mut bn_refs: Vec<bool> = Vec::new();
                let mut stmt_idx = 0usize;
                let mut bind_idx = 0usize;
                for item in items.iter() {
                    let (n, ty, val) = match item {
                        ClassItem::Field(n, t, v) => (n.clone(), t.clone(), v.clone()),
                        ClassItem::Stmt(expr) => {
                            let n = empty_span(SmolStr::new(format!("_s{stmt_idx}")));
                            stmt_idx += 1;
                            (n.clone(), Raw::Hole(n.to_span()), expr.clone())
                        }
                        ClassItem::Method(_, _) => continue,
                    };
                    let (a_checked, _) = self.check_universe(bump, &a_cxt, &ty)?;
                    let va = self.eval(bump, &a_cxt, a_cxt.env, a_checked);
                    // 未注解字段直解 fresh meta 为推断类型；注解字段按注解查
                    let cxt_named = a_cxt.with_binding_name(n.data.clone());
                    let t_checked = self.check(bump, &cxt_named, &val, va)?;
                    let vt = self.eval(bump, &a_cxt, a_cxt.env, t_checked);
                    if matches!(ty, Raw::Hole(_)) {
                        if v_tag(va) == 5 {
                            let m = v_meta_of(va);
                            if let MetaEntry::Unsolved(mty, ..) = &self.metas[m as usize] {
                                let mty = *mty;
                                self.metas[m as usize] = MetaEntry::Solved(vt, mty);
                            }
                        }
                    }
                    let raw_ty = if matches!(ty, Raw::Hole(_)) {
                        // 未注解：字段类型 = 推断类型（重表达为 Raw；不可表
                        // 达则回退 Hole——参考版同款）
                        let field_ty = self.force_v(bump, &a_cxt, va);
                        let q = self.quote(bump, &a_cxt, a_cxt.lvl, field_ty);
                        let e = export(&self.symbol_table, q);
                        let names = types_names_list(a_cxt.types);
                        tm_to_raw_type(&names, &e).unwrap_or(Raw::Hole(n.to_span()))
                    } else {
                        ty.clone()
                    };
                    if matches!(item, ClassItem::Field(..)) {
                        struct_field_types.push((n.clone(), raw_ty));
                    }
                    bn_refs.push(tm_refs_bn(t_checked, bind_idx));
                    bind_idx += 1;
                    let a_t = self.quote(bump, &a_cxt, a_cxt.lvl, va);
                    a_cxt = self.define_name(
                        bump,
                        &a_cxt,
                        &n.data,
                        n.to_span(),
                        a_checked,
                        t_checked,
                        vt,
                        va,
                    );
                    // 导出参考版 (name, t_checked, va, a_checked) + 全部登记
                    // 指针导入表（parser 的 build_class_chain_tm /
                    // maybe_prechecked_method_body 会以 (t, va) 与
                    // (a_checked, va) 两种组合嵌 Raw::Tm）
                    let rc_tm = export(&self.symbol_table, t_checked);
                    let rc_a = export(&self.symbol_table, a_checked);
                    let rc_ty = v_to_ref_val(&self.spine, &self.defs, va);
                    self.tm_import.insert(
                        Rc::as_ptr(&rc_tm) as usize,
                        unsafe {
                            std::mem::transmute::<&Tm<'a>, &'static Tm<'static>>(t_checked)
                        },
                    );
                    self.tm_import.insert(
                        Rc::as_ptr(&rc_a) as usize,
                        unsafe {
                            std::mem::transmute::<&Tm<'a>, &'static Tm<'static>>(a_checked)
                        },
                    );
                    self.val_import.insert(Rc::as_ptr(&rc_ty) as usize, va);
                    prechecked.push(PreA {
                        name: n,
                        rc_tm,
                        rc_a,
                        rc_ty,
                    });
                }
                // ══ Phase B：组装 struct + create + inherent impl + trait
                // impls（共享 parser 的 expand_class_decls；Raw::Tm 经指针
                // 导入表复用 Phase A 结果）══
                let prechecked_items: Vec<(
                    crate::parser_lib::Span<SmolStr>,
                    Rc<CTm>,
                    Rc<CVal>,
                    Rc<CTm>,
                )> = prechecked
                    .into_iter()
                    .map(|p| (p.name, p.rc_tm, p.rc_ty, p.rc_a))
                    .collect();
                let pc = super::parser::PrecheckedItems {
                    items: prechecked_items,
                    bn_refs: bn_refs.clone(),
                };
                let decls = super::parser::expand_class_decls(
                    name.clone(),
                    params.clone(),
                    items.clone(),
                    traits.clone(),
                    struct_field_types.clone(),
                    Some(&pc),
                );
                let mut cxt2 = clone_cxt(cxt);
                for dd in decls {
                    let (_, c) = self.infer_after_prefix(bump, &cxt2, &dd)?;
                    cxt2 = c;
                }
                Ok((DeclOut::Class, cxt2))
            }
        }
    }

    /// `wrap_match_in_call`（参考版 mod.rs:1029）：λ 链体顶端的 Match 包成
    /// `Call(name, Var 链+icit, Match)`——eval 的 Call 帧由此产出
    /// `Val::Call`（println 卡住 match 的显示走 `name(args)`）。
    fn wrap_match_in_call<'a>(
        &mut self,
        bump: &'a Bump,
        name: &str,
        tm: &'a Tm<'a>,
    ) -> &'a Tm<'a> {
        // 迭代剥 λ 链，Match 顶点时组装（icit 收集序 = 参考版）
        fn go<'a>(bump: &'a Bump, name: &str, tm: &'a Tm<'a>, l: u32, icits: &mut Vec<Icit>) -> &'a Tm<'a> {
            match tm {
                Tm::Lam(span_n, i, body) => {
                    icits.push(*i);
                    let r = go(bump, name, body, l + 1, icits);
                    icits.pop();
                    bump.alloc(Tm::Lam(span_n, *i, r))
                }
                Tm::Match(scru, cases) => {
                    // List 序（参考版 prepend 构造）：head = Var(l-1) … 尾 =
                    // Var(0)；icit 平行 [icits[0], …, icits[l-1]]
                    let mut argv: Vec<(&'a Tm<'a>, Icit)> = Vec::with_capacity(l as usize);
                    for i in 0..l {
                        argv.push((
                            bump.alloc(Tm::Var(l - 1 - i)),
                            icits[i as usize],
                        ));
                    }
                    bump.alloc(Tm::Call(
                        bump.alloc_str(name),
                        bump.alloc_slice_copy(&argv),
                        bump.alloc(Tm::Match(scru, cases)),
                    ))
                }
                _ => tm,
            }
        }
        let _ = self;
        go(bump, name, tm, 0, &mut Vec::new())
    }

    /// Def 臂的未解 meta 报错（参考版 1015-1090 的文案族）：trait 型给
    /// "cannot infer typeclass / no instance / no matching instance +
    /// available instances"（Into 特判给 resize 提示）；否则 "find unsolved
    /// meta with type"。meta_names 为 no_metas 给出的名字表。
    #[allow(clippy::too_many_arguments)]
    fn mk_unsolved_meta_err<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t_tm: &'a Tm<'a>,
        meta_names: crate::list::List<SmolStr>,
        oty: V,
        _def_name: &str,
    ) -> Error {
        let _ = t_tm;
        let oty_f = self.force_v(bump, cxt, oty);
        if v_tag(oty_f) == 7 {
            if let XCell::Sum { name, params, is_trait: true, .. } = v_xcell_of(oty_f) {
                let has_flex = params
                    .iter()
                    .any(|p| v_tag(self.force_v(bump, cxt, p.val)) == 5);
                let instances = self
                    .tstate
                    .solver
                    .class_instances
                    .get(&SmolStr::new(name))
                    .cloned();
                if has_flex {
                    return Error(
                        empty_span(format!(
                            "cannot infer typeclass `{}`: type parameter is unknown",
                            name
                        )),
                        vec![],
                    );
                } else if params.is_empty() {
                    return Error(
                        empty_span(format!("no instance of typeclass `{}`", name)),
                        vec![],
                    );
                } else {
                    // 参数 pretty（借用 meta 上下文名单——近似参考版 meta_cxt）
                    let names = match meta_names.head() {
                        Some(_) => types_names_list(cxt.types),
                        None => types_names_list(cxt.types),
                    };
                    let pretty_val = |mach: &mut Machine, v: V| -> String {
                        let q = mach.quote(bump, cxt, cxt.lvl, v);
                        let e = export(&mach.symbol_table, q);
                        pretty_tm(0, names.clone(), &e)
                    };
                    let first = pretty_val(self, params[0].val);
                    let rest: Vec<String> = params[1..]
                        .iter()
                        .map(|p| pretty_val(self, p.val))
                        .collect();
                    let trait_repr = if rest.is_empty() {
                        name.to_string()
                    } else {
                        format!("{}[{}]", name, rest.join(", "))
                    };
                    if instances.as_ref().map_or(true, |i| i.is_empty()) {
                        return Error(
                            empty_span(format!(
                                "no instance of typeclass `{}` for types `{}`",
                                trait_repr, first
                            )),
                            vec![],
                        );
                    } else {
                        let insts = instances.unwrap();
                        return Error(
                            empty_span(format!(
                                "no matching instance of typeclass `{}` for types `{}`\navailable instances: {}",
                                trait_repr,
                                first,
                                insts.iter().map(|i| i.lvl.data.to_string()).collect::<Vec<_>>().join(", "),
                            )),
                            vec![],
                        );
                    }
                }
            }
        }
        // 其余：find unsolved meta with type
        let q = self.quote(bump, cxt, cxt.lvl, oty);
        let e = export(&self.symbol_table, q);
        let names = types_names_list(cxt.types);
        Error(
            empty_span(format!(
                "find unsolved meta with type `{}`",
                pretty_tm(0, names, &e)
            )),
            vec![],
        )
    }
}

/// 参考版 `nat_chain_len`（elaboration.rs 一带）：SumCase 链是否是具体
/// `succ^k zero`（Nat 类型）——是则给 k。
fn nat_chain_len_ref(tm: &CTm) -> Option<u64> {
    let mut k = 0u64;
    let mut cur = tm;
    loop {
        match cur {
            CTm::SumCase {
                typ: t2,
                index: 0,
                datas,
                ..
            } if matches!(t2.as_ref(), CTm::Sum(name, _, _, false) if name.data == "Nat")
                && datas.is_empty() =>
            {
                return Some(k)
            }
            CTm::SumCase {
                typ: t2,
                index: 1,
                datas,
                ..
            } if matches!(t2.as_ref(), CTm::Sum(name, _, _, false) if name.data == "Nat")
                && datas.len() == 1
                && datas[0].0.data == "n" =>
            {
                k += 1;
                cur = &datas[0].1;
            }
            _ => return None,
        }
    }
}

/// 参考 `Infer::tm_to_raw_type`：已导出的 CTm → 可作注解的 Raw（Var 按名字
/// 表回名；Sum/SumCase 复原应用形；Nat 链复原字面量；不可表达 → None，
/// 调用方回退 Hole）。
fn tm_to_raw_type(names: &crate::list::List<SmolStr>, tm: &CTm) -> Option<Raw> {
    fn go(tm: &CTm, names: &crate::list::List<SmolStr>) -> Option<Raw> {
        match tm {
            CTm::Var(ix) => {
                let name = names.iter().nth(ix.0 as usize)?;
                Some(Raw::Var(empty_span(name.clone())))
            }
            CTm::Decl(n) => Some(Raw::Var(n.clone())),
            CTm::Obj(f, n) => Some(Raw::Obj(Box::new(go(f, names)?), Some(n.clone()))),
            CTm::App(f, a, i) => Some(Raw::App(
                Box::new(go(f, names)?),
                Box::new(go(a, names)?),
                Either::Icit(*i),
            )),
            CTm::AppPruning(f, _) => go(f, names),
            CTm::Lam(x, i, b) => Some(Raw::Lam(
                x.clone(),
                Either::Icit(*i),
                Box::new(go(b, &names.prepend(x.data.clone()))?),
            )),
            CTm::Pi(x, i, a, b) => Some(Raw::Pi(
                x.clone(),
                *i,
                Box::new(go(a, names)?),
                Box::new(go(b, &names.prepend(x.data.clone()))?),
            )),
            CTm::U(u) => Some(Raw::U(*u)),
            CTm::Sum(name, params, _, _) => {
                let mut acc = Raw::Var(name.clone());
                for (_, v, _, i) in params.iter() {
                    acc = Raw::App(Box::new(acc), Box::new(go(v, names)?), Either::Icit(*i));
                }
                Some(acc)
            }
            CTm::SumCase { is_trait, typ, index, datas } => {
                if !*is_trait {
                    if let Some(k) = nat_chain_len_ref(tm) {
                        return Some(Raw::Nat(empty_span(k)));
                    }
                }
                let case_name = match typ.as_ref() {
                    CTm::Sum(_, _, cases, _) => cases.iter().nth(*index as usize)?.clone(),
                    _ => return None,
                };
                let ds = datas
                    .iter()
                    .map(|(n, d, i)| Some((n.clone(), go(d, names)?, *i)))
                    .collect::<Option<Vec<_>>>()?;
                Some(Raw::SumCase {
                    is_trait: *is_trait,
                    typ: Box::new(go(typ, names)?),
                    case_name,
                    datas: ds,
                })
            }
            // 项专属 / 不可表达节点：调用方回退 Hole
            _ => None,
        }
    }
    go(tm, names)
}

/// decl 名字的 package 前缀（参考版 `prefix_decl_name`，elaboration.rs:36
/// 一带）：Def/Enum/TraitDecl/Class 的名字加前缀；嵌套 Package.path 逐段
/// 累加；方法名一律不加。
fn prefix_decl_name(d: &Decl, prefix: &str) -> Decl {
    let qual = |n: &crate::parser_lib::Span<SmolStr>| {
        n.clone().map(|x| SmolStr::new(format!("{}.{}", prefix, x)))
    };
    match d {
        Decl::Def { name, params, ret_type, body } => Decl::Def {
            name: qual(name),
            params: params.clone(),
            ret_type: ret_type.clone(),
            body: body.clone(),
        },
        Decl::Enum { is_trait, name, params, cases } => Decl::Enum {
            is_trait: *is_trait,
            name: qual(name),
            params: params.clone(),
            cases: cases.clone(),
        },
        Decl::TraitDecl { name, params, supertraits, methods, assoc_defaults } => {
            Decl::TraitDecl {
                name: qual(name),
                params: params.clone(),
                supertraits: supertraits.clone(),
                methods: methods.clone(),
                assoc_defaults: assoc_defaults.clone(),
            }
        }
        Decl::Class { name, params, items, traits } => Decl::Class {
            name: qual(name),
            params: params.clone(),
            items: items.clone(),
            traits: traits.clone(),
        },
        Decl::Package { path } => {
            let new_path: Vec<crate::parser_lib::Span<SmolStr>> =
                vec![empty_span(SmolStr::new(prefix))]
                    .into_iter()
                    .chain(path.iter().cloned())
                    .collect();
            Decl::Package { path: new_path }
        }
        other => other.clone(),
    }
}

/// Raw 的头构造子名（参考版 `raw_ctor_name`）。
fn raw_ctor_name(raw: &Raw) -> Option<SmolStr> {
    match raw {
        Raw::Var(name) => Some(name.data.clone()),
        Raw::App(head, _, _) => raw_ctor_name(head),
        _ => None,
    }
}

/// 算符方法名判定（参考版 `is_operator_method_name`）。
fn is_operator_method_name(name: &str) -> bool {
    name.chars().next().map(super::is_operator_char).unwrap_or(false)
}

/// 项是否引用第 `bind_idx` 个（非方法）绑定的层级（bn 引用判定——参考版
/// `tm_refs_bn`；twin 的 Var 是相对索引，转换见内）。
fn tm_refs_bn(tm: &Tm<'_>, bind_idx: usize) -> bool {
    // 参考版按 Var 的绝对层级判定；快版 Var 是相对索引——沿 λ 深度换算：
    // Var(i) 在深度 d 下引用的绑定 = 当前绑定序 + (i - d)。保守近似：任何
    // 项内出现 Var 且其相对索引 ≥ λ 深度时指向外层绑定——用与参考版同构
    // 的"绝对层级 = 相对索引 + 该点深度"重算。
    fn go(tm: &Tm<'_>, depth: usize, target_from_top: usize, binder_seen: &mut usize) -> bool {
        match tm {
            Tm::Var(i) => {
                let abs = binder_seen_plus(depth, *i as usize);
                abs == target_from_top
            }
            Tm::Decl(_) | Tm::U(_) | Tm::Meta(_) | Tm::LiteralType | Tm::LiteralIntro(_) => false,
            Tm::Obj(h, _) => go(h, depth, target_from_top, binder_seen),
            Tm::Lam(_, _, b) => go(b, depth + 1, target_from_top, binder_seen),
            Tm::App(f, a, _) => {
                go(f, depth, target_from_top, binder_seen)
                    || go(a, depth, target_from_top, binder_seen)
            }
            Tm::AppPruning(h, _) => go(h, depth, target_from_top, binder_seen),
            Tm::Pi(_, _, a, b) => {
                go(a, depth, target_from_top, binder_seen)
                    || go(b, depth + 1, target_from_top, binder_seen)
            }
            Tm::Let(_, a, t, u) => {
                go(a, depth, target_from_top, binder_seen)
                    || go(t, depth, target_from_top, binder_seen)
                    || go(u, depth + 1, target_from_top, binder_seen)
            }
            Tm::Sum(_, ps, _, _) => ps.iter().any(|p| {
                go(p.val, depth, target_from_top, binder_seen)
                    || go(p.ty, depth, target_from_top, binder_seen)
            }),
            Tm::SumCase { typ, datas, .. } => {
                go(typ, depth, target_from_top, binder_seen)
                    || datas.iter().any(|d| go(d.val, depth, target_from_top, binder_seen))
            }
            Tm::Match(s, cases) => {
                go(s, depth, target_from_top, binder_seen)
                    || cases.iter().any(|(_, b)| {
                        go(b, depth, target_from_top, binder_seen)
                    })
            }
            Tm::Call(_, args, body) => {
                args.iter().any(|(a, _)| go(a, depth, target_from_top, binder_seen))
                    || go(body, depth, target_from_top, binder_seen)
            }
        }
    }
    fn binder_seen_plus(depth: usize, i: usize) -> usize {
        // Var(i) 在 λ 深度 d 的项里引用“向外数第 i 个”绑定；绑定序（源码
        // 序）从外向内递增，绝对层级 = d + i
        depth + i
    }
    go(tm, 0, bind_idx, &mut 0)
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
        namespace: cxt.namespace,
        namespace_prefix: cxt.namespace_prefix.clone(),
        namespaces: cxt.namespaces.clone(),
        binding_name: cxt.binding_name.clone(),
    }
}

/// trait 定义 / 合成状态（参考版 `Infer` 的 trait_solver / trait_definition /
/// trait_out_param 三表同构；Clone 供 temp-infer 快照换入换出）。L13：
/// definition 多 supertraits 与方法默认体两元（参考版同构）。
#[derive(Clone, Default)]
pub(crate) struct TraitState {
    /// Prolog 式实例求解器。
    solver: Synth,
    /// trait 名 → (参数表（含 Self）, out_param 掩码, supertrait 链, 方法表)。
    /// 方法表条目：(名字, 参数表, 返回类型, 默认体)。
    definition: HashMap<
        SmolStr,
        (
            Vec<(crate::parser_lib::Span<SmolStr>, Raw, Icit)>,
            Vec<bool>,
            Vec<crate::parser_lib::Span<SmolStr>>,
            Vec<(
                crate::parser_lib::Span<SmolStr>,
                Vec<(crate::parser_lib::Span<SmolStr>, Raw, Icit)>,
                Raw,
                Option<Raw>,
            )>,
        ),
    >,
    /// trait 名 → 参数 out_param 掩码。
    out_param: HashMap<SmolStr, Vec<bool>>,
    /// (trait, 关联类型名) → 默认类型（参考版 `Infer.assoc_defaults`）。
    assoc_defaults: HashMap<(SmolStr, SmolStr), Option<Raw>>,
}

/// 类型值的确定性结构键（参考版 `val_cache_key` 的快版对应）——trait 方法
/// Π 链缓存的键。不可缓存（per-call meta / 开放类型 / 超深结构）→ None。
fn val_cache_key_t(spine: &Spine, v: V, depth: u32) -> Option<SmolStr> {
    if depth > 64 {
        return None;
    }
    match v_tag(v) {
        3 => Some(SmolStr::new(format!("u{}", v_u_of(v)))),
        6 => Some(SmolStr::new("lt")),
        7 => match v_xcell_of(v) {
            XCell::Lit(s) => Some(SmolStr::new(format!("l:{}", s))),
            XCell::Nat(k) => Some(SmolStr::new(format!("n{}", k))),
            XCell::Sum { name, params, .. } => {
                let mut s = String::from(*name);
                s.push('(');
                for (i, p) in params.iter().enumerate() {
                    if i > 0 {
                        s.push(',');
                    }
                    s.push_str(&val_cache_key_t(spine, p.val, depth + 1)?);
                }
                s.push(')');
                Some(SmolStr::new(s))
            }
            XCell::SumCase { index, datas, .. } => {
                let mut s = format!("sc{}({}", index, datas.len());
                for d in datas.iter() {
                    s.push(',');
                    s.push_str(&val_cache_key_t(spine, d.val, depth + 1)?);
                }
                s.push(')');
                Some(SmolStr::new(s))
            }
            _ => None,
        },
        _ => None,
    }
}

/// 快版 V → 参考版 `Rc<Val>` 的解码（trait 求解器是 Val 级匹配——L12
/// typeclass.rs 移除 Typ 桥接；解码只用于 solving 边界，非热路径）。
/// 支持：Rigid（裸）/U/LiteralType/LiteralIntro/Sum/SumCase/Flex（未解
/// meta 立即数）；其余形态 unreachable（参考版 solve_trait 的实参是
/// 已 force 的类型实参，实际只会出现这些形态）。
pub(crate) fn v_to_ref_val(spine: &Spine, defs: &[V], v: V) -> Rc<CVal> {
    fn nspan(x: &str) -> crate::parser_lib::Span<SmolStr> {
        crate::parser_lib::Span {
            data: SmolStr::new(x),
            start_offset: 0,
            end_offset: 0,
            path_id: 0,
        }
    }
    fn unmatchable() -> Rc<CVal> {
        Rc::new(CVal::LiteralIntro(crate::parser_lib::Span {
            data: "$unmatchable$".to_string(),
            start_offset: 0,
            end_offset: 0,
            path_id: 0,
        }))
    }
    match v_tag(v) {
        0 => Rc::new(CVal::Rigid(super::Lvl(v_lvl_of(v)), CList::new())),
        2 => {
            // 链：头解码 + 实参逐个挂上（参考版 spine 是 List（最新在前）；
            // collect_args 产出的正是最新在前序，逐个 prepend 即还原同序）。
            // **必须保留真实头**：先前把每步 acc 整体换成
            // `Flex(MetaVar(u32::MAX), [该实参])`，既丢了头（`?A x` 变成
            // 通配 `?_ x`，val_match 对任何实例恒真）又丢了更早的实参——
            // trait 求解 Phase 1 的候选集被污染成全部实例，再按登记序选中
            // 错误实例（core prelude `a + 0` 命中 Add[String,String] for
            // String，报 `can't unify expected: String find: Nat`）。
            let h = v_spine_of(v);
            let hd = spine.spine_head(h);
            let mut acc = match v_tag(hd) {
                5 => Rc::new(CVal::Flex(super::MetaVar(v_meta_of(hd)), CList::new())),
                0 => Rc::new(CVal::Rigid(super::Lvl(v_lvl_of(hd)), CList::new())),
                7 => match v_xcell_of(hd) {
                    XCell::Decl { name } => Rc::new(CVal::Decl(nspan(name), CList::new())),
                    XCell::Obj { val, name } => Rc::new(CVal::Obj(
                        v_to_ref_val(spine, defs, *val),
                        nspan(name),
                        CList::new(),
                    )),
                    _ => return unmatchable(),
                },
                _ => return unmatchable(),
            };
            let mut args: Vec<(V, Icit)> = Vec::new();
            spine.collect_args(h, &mut args); // 最新在前
            for (a, i) in args.iter() {
                let av = v_to_ref_val(spine, defs, *a);
                acc = match acc.as_ref() {
                    CVal::Flex(m, sp) => {
                        Rc::new(CVal::Flex(*m, sp.prepend((av, *i))))
                    }
                    CVal::Rigid(l, sp) => {
                        Rc::new(CVal::Rigid(*l, sp.prepend((av, *i))))
                    }
                    CVal::Decl(n, sp) => {
                        Rc::new(CVal::Decl(n.clone(), sp.prepend((av, *i))))
                    }
                    CVal::Obj(x, n, sp) => {
                        Rc::new(CVal::Obj(x.clone(), n.clone(), sp.prepend((av, *i))))
                    }
                    _ => return unmatchable(),
                };
            }
            acc
        }
        3 => Rc::new(CVal::U(v_u_of(v))),
        5 => Rc::new(CVal::Flex(super::MetaVar(v_meta_of(v)), CList::new())),
        6 => Rc::new(CVal::LiteralType),
        7 => match v_xcell_of(v) {
            XCell::Lit(s) => Rc::new(CVal::LiteralIntro(crate::parser_lib::Span {
                data: s.to_string(),
                start_offset: 0,
                end_offset: 0,
                path_id: 0,
            })),
            // 原生 Nat（L13）
            XCell::Nat(k) => Rc::new(CVal::Nat(*k)),
            XCell::Sum {
                name,
                params,
                cases,
                is_trait,
            } => {
                let mut ps: Vec<(crate::parser_lib::Span<SmolStr>, Rc<CVal>, Rc<CVal>, Icit)> =
                    Vec::with_capacity(params.len());
                for p in params.iter() {
                    ps.push((
                        nspan(p.name),
                        v_to_ref_val(spine, defs, p.val),
                        v_to_ref_val(spine, defs, p.ty),
                        p.icit,
                    ));
                }
                let cs: Vec<crate::parser_lib::Span<SmolStr>> =
                    cases.iter().map(|c| nspan(c)).collect();
                Rc::new(CVal::Sum(nspan(name), Rc::new(ps), Rc::new(cs), *is_trait))
            }
            XCell::SumCase {
                typ,
                index,
                datas,
                is_trait,
            } => {
                let mut ds: Vec<(crate::parser_lib::Span<SmolStr>, Rc<CVal>, Icit)> =
                    Vec::with_capacity(datas.len());
                for d in datas.iter() {
                    ds.push((nspan(d.name), v_to_ref_val(spine, defs, d.val), d.icit));
                }
                Rc::new(CVal::SumCase {
                    is_trait: *is_trait,
                    typ: v_to_ref_val(spine, defs, *typ),
                    // index 制（L13）：快版值在解码点拿不到所属 Sum 的 cases
                    // 表，直接透传 index——消费端 val_match 同为 index 比较，
                    // 与参考版解码路径（index 相等）一致。
                    index: *index,
                    datas: Rc::new(ds),
                })
            }
            XCell::Call { name, args, body } => {
                let mut list: CList<(Rc<CVal>, Icit)> = CList::new();
                for (a, i) in args.iter().rev() {
                    list = list.prepend((v_to_ref_val(spine, defs, *a), *i));
                }
                Rc::new(CVal::Call(SmolStr::new(name), list, v_to_ref_val(spine, defs, *body)))
            }
            // Pi / 卡住 Match 等形态：参考版 val_match 对非构造子 goal 一律
            // false——降级为永不匹配的标记值，观察面相同。
            _ => unmatchable(),
        },
        _ => unmatchable(),
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
    /// println：elaboration 期即算好的 pretty 串（参考版 DeclTm::Println）。
    Println(&'a Tm<'a>, String),
    Enum,
    Trait,
    TraitImpl,
    Package,
    Import,
    Class,
}

// 模式匹配编译（参考版 pattern_match.rs 的逐句移植）
// --------------------------------------------------------------------------------

type Var = i32;

#[derive(Debug, Clone)]
pub(crate) enum Warning {
    Unreachable(Raw),
    Unmatched(Pattern),
}

/// Display 文案与参考版 pattern_match.rs 同款（match 非穷尽/不可达作为
/// 错误文案输出：`warnings.iter().map(|w| w.to_string()).join("; ")`）。
impl std::fmt::Display for Warning {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Warning::Unreachable(body) => write!(f, "unreachable pattern: {}", body),
            Warning::Unmatched(pat) => write!(f, "non-exhaustive pattern: `{}` not covered", pat),
        }
    }
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
                            PatternDetail::Con(_, _, x) => {*x = t;},
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

    /// 把累积的模式构造子树转成 `Raw` 表达式（参考版 pattern_match.rs 81
    /// —`to_raw`）：**含**匹配期间发现的隐式参数（如 `cons[l](x, xs)` 的
    /// `l`），它们以 `PatternDetail::Any` 入栈、转成 Implicit `Raw::App`
    /// 实参，从而让 `check_pm_final` 的推断复用已绑定的 Rigid 而非新建
    /// 独立 meta。快版 leaf 分支必须用它（而非原始 `Raw`——原始用户模式
    /// 是完整构造子 `succ(x)`，用它去 check 字段类型会越界崩溃）。
    fn to_raw(&self) -> Raw {
        let pat = self.clone().clean();
        match pat.root_detail() {
            Some(d) => Self::detail_to_raw(d),
            None => Raw::Hole(empty_span(())),
        }
    }

    /// 自全 clean 栈提取根构造子 detail（栈底 index 0 是根 Con）。
    fn root_detail(&self) -> Option<&PatternDetail> {
        if self.data.is_empty() || self.data[0].1.is_empty() {
            return None;
        }
        Some(&self.data[0].1[0])
    }

    fn detail_to_raw(d: &PatternDetail) -> Raw {
        match d {
            PatternDetail::Con(_idx, name, subs) => {
                subs.iter().fold(Raw::Var(name.clone()), |acc, sub| {
                    let icit = match sub {
                        PatternDetail::Any(var_name, param_name, Icit::Impl) => {
                            if var_name.data.is_empty() {
                                // 无名隐式 → 让 elaborated 自动填充
                                Either::Icit(Icit::Impl)
                            } else if let Some(pname) = param_name {
                                // 具名隐式 + 显式参数名：`[pi_param=var]`
                                // 让 insert_go 自动填充前置 Impl 且只绑定本个
                                Either::Name(pname.clone())
                            } else {
                                // 兼容：剥离 `_` 前缀派生参数名
                                Either::Name(var_name.clone().map(|s| SmolStr::new(&s[1..])))
                            }
                        }
                        PatternDetail::Any(_, _, Icit::Expl) => Either::Icit(Icit::Expl),
                        PatternDetail::Bind(_) => Either::Icit(Icit::Expl),
                        PatternDetail::Con(_, _, _) => Either::Icit(Icit::Expl),
                    };
                    Raw::App(Box::new(acc), Box::new(Self::detail_to_raw(sub)), icit)
                })
            }
            PatternDetail::Any(name, _, _) | PatternDetail::Bind(name) => {
                if name.data.is_empty() {
                    Raw::Hole(empty_span(()))
                } else {
                    Raw::Var(name.clone())
                }
            }
        }
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
        constr: crate::parser_lib::Span<SmolStr>,
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
    heads: Vec<(Var, V, crate::parser_lib::Span<SmolStr>, Icit)>,
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
                Self::fill_context(parent, &Pattern::Con(constr.clone(), new_before, Either::Icit(*icit)))
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
                [] => Self::next_hole(parent, &Pattern::Con(constr.clone(), before.clone(), Either::Icit(*icit))),
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
        all_constrs: &[crate::parser_lib::Span<SmolStr>],
    ) -> Result<Vec<crate::parser_lib::Span<SmolStr>>, Error> {
        self.filter_accessible_constrs_inner(mach, bump, cxt, typ, all_constrs)
    }

    fn filter_accessible_constrs_inner(
        &mut self,
        mach: &mut Machine,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        typ: V,
        all_constrs: &[crate::parser_lib::Span<SmolStr>],
    ) -> Result<Vec<crate::parser_lib::Span<SmolStr>>, Error> {
        let mut accessible = Vec::new();

        let forced_type = mach.force_v(bump, cxt, typ);
        if !(v_tag(forced_type) == 7 && matches!(v_xcell_of(forced_type), XCell::Sum { .. })) {
            // 非和类型：所有构造子按"可达"处理（参考版同款退路）
            for constr_def in all_constrs {
                accessible.push(constr_def.clone());
            }
            return Ok(accessible);
        }
        // 无显式索引参数的和类型（Nat / Bool / Box / Expr 等）所有构造子恒
        // 可达——fast path，避免逐构造子的 check_pm 探测（该探测在 multiline
        // 源码的 span 不匹配时会误判可达性并导致编译决策树死循环；参考版
        // pattern_match.rs 同款：`has_indices` 短路）。
        if let XCell::Sum { params, .. } = v_xcell_of(forced_type) {
            if !params.iter().any(|p| p.icit == Icit::Expl) {
                for constr_def in all_constrs {
                    accessible.push(constr_def.clone());
                }
                return Ok(accessible);
            }
        }

        // 逐构造子可达性探测是**纯探测**：infer_expr（逐层 Pi 强制）与 check_pm
        // 都可能分配 fresh meta 并解掉已有 meta/trait meta，探测期状态无需存活
        // （本函数只带出可达构造子**名字列表**）。统一走 `run_pure_probe` 入口做
        // 快照/回滚，杜绝各处手写快照漏掉错误路径（AV 根因）。构造子以**限定名**
        // `Sum.constru` 探测（参考版同款：sum_name 非空时用 `Raw::Obj(Var(sum),
        // Some(constr))`，否则裸 Var——限定名在 multiline 枚举的 span 下也能稳定
        // 解析，避免后缀 fallback 歧义）。
        mach.run_pure_probe(|mach| -> Result<Vec<crate::parser_lib::Span<SmolStr>>, Error> {
            let mut accessible = Vec::new();
            for constr_name in all_constrs {
                // 1. 为构造子自身实参造 fresh meta（类型经逐层推断取得；推断在
                //    真实 `mach` 上跑，但**探测整体回滚**，meta 分配不外泄）。
                let sum_name = match v_xcell_of(forced_type) {
                    XCell::Sum { name, .. } => *name,
                    _ => "",
                };
                let to_check = if sum_name.is_empty() {
                    Raw::Var(constr_name.clone())
                } else {
                    Raw::Obj(
                        Box::new(Raw::Var(empty_span(SmolStr::new(sum_name)))),
                        Some(constr_name.clone()),
                    )
                };
                let mut to_check = to_check;
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
                        cur_cxt = mach.bind_name(bump, &cur_cxt, &name, empty_span(()), q, p.dom);
                    } else {
                        break;
                    }
                }

                // 2. 可访问性判定（temp infer；状态由外层快照统一回滚）
                let r = mach.check_pm(bump, &cur_cxt, &to_check, forced_type);
                if std::env::var("L09_TRACE").is_ok() {
                    eprintln!("FILTER {} {}", constr_name.data, if r.is_ok() {"ok"} else {"err"});
                }
                if r.is_ok() {
                    // 构造子可访问
                    accessible.push(constr_name.clone());
                }
            }

            Ok(accessible)
        })
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
            &[(0, typ, empty_span(SmolStr::new("")), Icit::Expl)],
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
        heads: &[(Var, V, crate::parser_lib::Span<SmolStr>, Icit)],
        arms: &[Arm<'a>],
        context: &MatchContext,
    ) -> Result<bool, Error> {
        self.compile_aux_inner(mach, bump, heads, arms, context)
    }

    fn compile_aux_inner(
        &mut self,
        mach: &mut Machine,
        bump: &'a Bump,
        heads: &[(Var, V, crate::parser_lib::Span<SmolStr>, Icit)],
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
                            .map(|x| matches!(x, Pattern::Any(sp, _) if sp.data == false))
                            == Some(true) =>
                {
                    // check_pm 失败 → Ok(false)（参考版同款：整个构造子
                    // 分支回退 false）。用 `patcon.to_raw()` 而非原始
                    // `arm.raw`（参考版 pattern_match.rs 365 同款）——累积
                    // 的 patcon 已把子模式绑定成精确的 `Var("...")`，用原始
                    // 用户模式（完整构造子 `succ(x)`）去 check 字段类型会在
                    // infer 内部越界（STATUS_ACCESS_VIOLATION）
                    let patcon_raw = arm.patcon.clone().to_raw();
                    let (_, cxt) = match mach.check_pm_final(
                        bump, &arm.cxt, &patcon_raw, arm.target_typ, arm.ori,
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
                    Err(Error(msg, vec![]))
                }
                [] => Ok(false),
            },
            [(var, typ, head_name, icit), heads_rest @ ..] => {
                // 构造子名集（非 Sum 头为空集），用于区分**真构造子模式**与
                // **裸变量模式**：裸变量 parse 成 `Con(name, [], _)`，名字不在
                // 构造子集里，必须当作 catch-all（绑定一次），而不是被复制到该
                // Sum 头的每个构造子分支里重复展开（参考版 pattern_match.rs
                // 431-440 的 `is_var_like` 同款——缺了它会指数级爆炸 / 多行枚举
                // 直接越界崩溃）。
                //
                // `arms` 可为空（上一轮 not_necessary 递归剥完 heads 前的臂表
                // 已耗尽）：此时 is_var_like/not_necessary 对空表恒真、两者
                // 都不被读取，故不必 force（参考版直接读已求值的 typ，无此
                // 依赖；快版 typ 是待 force 的 V，需要一个 cxt，空臂时取不到）。
                let (is_sum, constrs_name): (bool, std::collections::BTreeSet<SmolStr>) =
                    match arms.first() {
                        Some(a) => {
                            let f = mach.force_v(bump, &a.cxt, *typ);
                            if v_tag(f) == 7 {
                                if let XCell::Sum { cases, .. } = v_xcell_of(f) {
                                    (
                                        true,
                                        cases.iter().map(|c| SmolStr::new(*c)).collect(),
                                    )
                                } else {
                                    (false, std::collections::BTreeSet::new())
                                }
                            } else {
                                (false, std::collections::BTreeSet::new())
                            }
                        }
                        None => (false, std::collections::BTreeSet::new()),
                    };
                let is_var_like = |pat: &Pattern, icit: &Icit| -> bool {
                    match pat {
                        Pattern::Any(_, i) => &i.to_icit() == icit,
                        Pattern::Con(name, subs, i) => {
                            subs.is_empty()
                                && &i.to_icit() == icit
                                && (!is_sum || !constrs_name.contains(&name.data))
                        }
                    }
                };
                let not_necessary = arms
                    .iter()
                    .all(|arm| arm.arm.pats.first().map(|p| is_var_like(p, icit)).unwrap_or(false));

                if not_necessary {
                    let new_context =
                        Self::next_hole(context, &Pattern::Any(empty_span(true), Either::Icit(*icit)));
                    let mut new_arms: Vec<Arm<'a>> = Vec::with_capacity(arms.len());
                    for arm in arms {
                        // L10：首模式是虚通配（data=false）的臂**不绑定**、
                        // patcon 原样（参考版同款）
                        let fake_first = matches!(
                            arm.arm.pats.first(),
                            Some(Pattern::Any(sp, _)) if sp.data == false
                        );
                        // 裸变量模式 `Con(name, [], _)` 且名字不在构造子集：按
                        // 变量自身名字绑定一次（参考版 456-486），后续
                        // check_pm_final 复用已绑定的 Rigid（emit `Bind`）
                        let bare_con = match arm.arm.pats.first() {
                            Some(Pattern::Con(name, subs, i))
                                if subs.is_empty()
                                    && i.to_icit() == *icit
                                    && (!is_sum || !constrs_name.contains(&name.data)) =>
                            {
                                Some(name.clone())
                            }
                            _ => None,
                        };
                        let (cxt2, patcon2) = if let Some(constr_name) = bare_con {
                            if fake_first {
                                (clone_cxt(&arm.cxt), arm.patcon.clone())
                            } else {
                                let q = mach.quote(bump, &arm.cxt, arm.cxt.lvl, *typ);
                                (
                                    mach.bind_name(bump, &arm.cxt, &constr_name.data, constr_name.to_span(), q, *typ),
                                    arm.patcon.clone().clean().push(PatternDetail::Bind(constr_name)),
                                )
                            }
                        } else {
                            let cxt2 = if fake_first {
                                clone_cxt(&arm.cxt)
                            } else {
                                let q = mach.quote(bump, &arm.cxt, arm.cxt.lvl, *typ);
                                let name = head_name.clone().map(|x| format!("_{}", x));
                                let cname = name.data.clone();
                                mach.bind_name(bump, &arm.cxt, &cname, empty_span(()), q, *typ)
                            };
                            let patcon2 = if fake_first {
                                arm.patcon.clone()
                            } else if *icit == Icit::Impl {
                            // 隐式头：具名（imp 名与绑定的 `_x` 同源——参考
                            // 版 make_implicit_name）
                            let imp = head_name
                                .clone()
                                .map(|x| SmolStr::new(format!("_{}", x)));
                            arm.patcon
                                .clone()
                                .clean()
                                .push(PatternDetail::Any(imp, Some(head_name.clone()), *icit))
                        } else {
                            arm.patcon
                                .clone()
                                .clean()
                                .push(PatternDetail::Any(
                                    empty_span(SmolStr::new("")),
                                    None,
                                    *icit,
                                ))
                        };
                        (cxt2, patcon2)
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
                        if let XCell::Sum { name, params, cases, .. } = v_xcell_of(f) {
                            // 值层 cases 只有名字；构造子**定义 span** 从 decl 表回填
                            // （参考版 Val::Sum.cases 直接带 Span<SmolStr>，其 PM 路径的
                            // hover/def 键都落在这个声明 token 上——这里对齐）。
                            let cs: Vec<crate::parser_lib::Span<SmolStr>> = cases
                                .iter()
                                .map(|c| {
                                    let key = format!("{}.{}", name, c);
                                    let sp = arms[0]
                                        .cxt
                                        .decls
                                        .get(key.as_str())
                                        .or_else(|| arms[0].cxt.decls.get(*c))
                                        .map(|e| e.span)
                                        .unwrap_or_else(|| empty_span(()));
                                    crate::parser_lib::Span {
                                        data: SmolStr::new(*c),
                                        start_offset: sp.start_offset,
                                        end_offset: sp.end_offset,
                                        path_id: sp.path_id,
                                    }
                                })
                                .collect();
                            (params.to_vec(), cs)
                        } else {
                            (vec![], vec![empty_span(SmolStr::new("$any$"))])
                        }
                    } else {
                        (vec![], vec![empty_span(SmolStr::new("$any$"))])
                    }
                };

                let constrs_name: std::collections::BTreeSet<SmolStr> = constrs
                    .iter()
                    .map(|x| x.data.clone())
                    .collect();

                let mut any_valid = false;
                for (constr_idx, constr) in constrs.iter().enumerate() {
                    // remaining_arms：每臂一个 Option（None = 该臂不参与本
                    // 构造子分支——参考版 filter_map 的 Some(None)/None 同型）
                    let mut remaining: Vec<Option<Arm<'a>>> = Vec::new();
                    for arm in arms {
                        let mut new_heads: Vec<(Var, V, crate::parser_lib::Span<SmolStr>, Icit)> =
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
                                            empty_span(SmolStr::new(p.name)),
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
                            [Pattern::Any(x, i), ..] if i.to_icit() == *icit => {
                                let name = head_name.clone().map(|x| SmolStr::new(format!("_{}", x)));
                                let cname = name.data.clone();
                                let (cxt2, patcon2) = if !x.data {
                                    (clone_cxt(&arm.cxt), arm.patcon.clone())
                                } else {
                                    let q = mach.quote(bump, &arm.cxt, arm.cxt.lvl, *typ);
                                    let imp = name.clone();
                                    (
                                        mach.bind_name(bump, &arm.cxt, &cname, empty_span(()), q, *typ),
                                        arm.patcon
                                            .clone()
                                            .clean()
                                            .push(PatternDetail::Any(
                                                imp.map(|x| x),
                                                Some(head_name.clone()),
                                                *icit,
                                            )),
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
                                                        Either::Icit(n.3),
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
                                if i.to_icit() == *icit
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
                                                        Either::Icit(n.3),
                                                    )
                                                })
                                                .collect::<Vec<_>>(),
                                            arm.arm.pats[1..].to_vec(),
                                        ]
                                        .concat(),
                                        body: arm.arm.body.clone(),
                                    },
                                    idx: arm.idx,
                                    cxt: mach.bind_name(bump, &arm.cxt, &constr_.data, constr_.to_span(), q, *typ),
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
                                if i.to_icit() == *icit && constr_ == constr => {
                                // 观察面：case 构造子 pattern token 的 hover（对应参考版
                                // pattern_match 862-907）。此点在 arm 构造路径（可达性
                                // 探针之后），只读 decls + quote，不建 meta、不触探针回滚
                                // 纪律（避开 filter_accessible_constrs 的 AV 雷区）。
                                // 参数化构造子（值 tag==1 闭包）渲染其 Pi 类型（vty），
                                // 无参构造子渲染 SumCase 值（如 `Tree::leaf`）；def_span
                                // 取登记项回填的构造子定义 span。
                                {
                                    let sum_name: SmolStr = if v_tag(*typ) == 7 {
                                        match v_xcell_of(*typ) {
                                            XCell::Sum { name, .. } => SmolStr::new(name),
                                            _ => SmolStr::new(""),
                                        }
                                    } else {
                                        SmolStr::new("")
                                    };
                                    let qualified = if sum_name.is_empty() {
                                        constr.data.clone()
                                    } else {
                                        SmolStr::new(format!("{}.{}", sum_name, constr.data))
                                    };
                                    match arm.cxt
                                        .decls
                                        .get(qualified.as_str())
                                        .or_else(|| arm.cxt.decls.get(constr.data.as_str()))
                                    {
                                        Some(e) => {
                                            let val = if v_tag(e.val) == 1 { e.vty } else { e.val };
                                            mach.push_hover(bump, &arm.cxt, constr_.to_span(), e.span, val);
                                        }
                                        None => {
                                            mach.push_hover(bump, &arm.cxt, constr_.to_span(), constr.to_span(), *typ);
                                        }
                                    }
                                }
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
                                        .push(PatternDetail::Con(
                                            constr_idx as u32,
                                            constr_.clone(),
                                            vec![],
                                        ))
                                        .new_level(new_heads_len),
                                    is_impl: false,
                                })
                            }
                            _ => {
                                if *icit == Icit::Impl {
                                    let q = mach.quote(bump, &arm.cxt, arm.cxt.lvl, *typ);
                                    let name = head_name.clone().map(|x| SmolStr::new(format!("_{}", x)));
                                    let cname = name.data.clone();
                                    Some(Arm {
                                        arm: MatchArm {
                                            pats: arm.arm.pats.clone(),
                                            body: arm.arm.body.clone(),
                                        },
                                        idx: arm.idx,
                                        cxt: mach.bind_name(bump, &arm.cxt, &cname, empty_span(()), q, *typ),
                                        heads: vec![],
                                        raw: arm.raw.clone(),
                                        target_typ: arm.target_typ,
                                        ori: arm.ori,
                                        patcon: arm
                                            .patcon
                                            .clone()
                                            .clean()
                                            .push(PatternDetail::Any(
                                                name.clone(),
                                                Some(head_name.clone()),
                                                Icit::Impl,
                                            )),
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
                                    &Pattern::Con(constr.clone(), vec![], Either::Icit(*icit)),
                                )
                            }
                        } else {
                            MatchContext::InCons {
                                parent: Rc::new(context.clone()),
                                constr: constr.clone(),
                                icit: *icit,
                                before: vec![],
                                after: vec![
                                    Pattern::Any(empty_span(true), Either::Icit(*icit));
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
                            &Pattern::Con(constr.clone(), vec![], Either::Icit(*icit)),
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
            XCell::Call { name, .. } => out.push_str(&format!("Call({})", name)),
            XCell::Nat(k) => out.push_str(&format!("Nat({})", k)),
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
            XCell::SumCase { is_trait, typ, index, datas } => {
                out.push_str(&format!(
                    "SumCase {{ is_trait: {}, typ: {}, index: {}, datas: [",
                    is_trait,
                    debug_val(spine, defs, *typ),
                    index
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
        PatternDetail::Any(name, _, _) => {
            out.push_str(&format!("Any({})", dbg_span_str(&name.data)));
        }
        PatternDetail::Bind(name) => {
            out.push_str(&format!("Bind({})", dbg_span_str(&name.data)));
        }
        PatternDetail::Con(idx, name, subs) => {
            out.push_str(&format!("Con({}, {}, [", idx, dbg_span_str(&name.data)));
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
        Tm::SumCase { typ, index, datas, .. } => {
            out.push_str(&format!(
                "SumCase {{ typ: {}, index: {}, datas: [",
                {
                    let mut tmp = String::new();
                    debug_tm_go(typ, &mut tmp);
                    tmp
                },
                index
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
        Tm::Call(name, args, body) => {
            out.push_str(&format!("Call({}, [", dbg_span_str(name)));
            for (k, (a, _)) in args.iter().enumerate() {
                if k > 0 {
                    out.push_str(", ");
                }
                debug_tm_go(a, out);
            }
            out.push_str("], ");
            debug_tm_go(body, out);
            out.push(')');
        }
    }
}

// export 与对外入口
// --------------------------------------------------------------------------------

/// 把 bump 结果项转回参考版的 `Box` 树（迭代任务栈；icit/掩码随任务
/// 携带），复用参考版的 pretty。
fn export(symbols: &FxHashMap<(SmolStr, usize), SmolStr>, t: &Tm<'_>) -> Rc<CTm> {
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
            index: u32,
            datas: &'a [SumDataT<'a>],
            is_trait: bool,
        },
        /// Call 装配：`symbol` 命中（实参全 Expl 且 1-2 个）→ OpCall
        Call2 {
            name: &'a str,
            symbol: Option<SmolStr>,
            icits: Vec<Icit>,
        },
    }
    fn name(x: &str) -> crate::parser_lib::Span<SmolStr> {
        empty_span(SmolStr::new(x))
    }
    let mut tasks: Vec<J<'_>> = vec![J::Do(t)];
    let mut done: Vec<Rc<CTm>> = Vec::new();
    while let Some(j) = tasks.pop() {
        match j {
            J::Do(Tm::Var(i)) => done.push(Rc::new(CTm::Var(Ix(*i)))),
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
            J::Do(Tm::U(l)) => done.push(Rc::new(CTm::U(*l))),
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
            J::Do(Tm::Meta(m)) => done.push(Rc::new(CTm::Meta(MetaVar(*m)))),
            J::Do(Tm::LiteralType) => done.push(Rc::new(CTm::LiteralType)),
            J::Do(Tm::LiteralIntro(s)) => done.push(Rc::new(CTm::LiteralIntro(
                crate::parser_lib::Span {
                    data: s.to_string(),
                    start_offset: 0,
                    end_offset: 0,
                    path_id: 0,
                },
            ))),
            J::Do(Tm::Decl(x)) => done.push(Rc::new(CTm::Decl(name(x)))),
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
                index,
                datas,
                is_trait,
            }) => {
                let is_trait = *is_trait;
                tasks.push(J::SumCase2 {
                    index: *index,
                    datas,
                    is_trait,
                });
                for d in datas.iter().rev() {
                    tasks.push(J::Do(d.val));
                }
                tasks.push(J::Do(typ));
            }
            J::Do(Tm::Call(nm, args, body)) => {
                // OpCall 决策（参考版 quote 的 Call 臂）：实参全 Expl 且
                // 1-2 个且 symbol_table 命中 → 显示专用 OpCall（保留全部
                // call 数据保证 eval 往返恒等）
                let icits_buf: Vec<Icit> = args.iter().map(|(_, i)| *i).collect();
                let sym_hit = if args.iter().all(|(_, i)| *i == Icit::Expl) {
                    symbols.get(&(SmolStr::new(nm), args.len())).cloned()
                } else {
                    None
                }
                .filter(|_| args.len() == 1 || args.len() == 2);
                tasks.push(J::Call2 {
                    name: nm,
                    symbol: sym_hit,
                    icits: icits_buf,
                });
                tasks.push(J::Do(body));
                for (a, _) in args.iter() {
                    tasks.push(J::Do(a));
                }
            }
            J::Do(Tm::Match(s, cases)) => {
                // 分支体逐个内联导出（递归深度 = match 嵌套深度）；模式直接
                // 克隆（PatternDetail 是参考版类型，两版共用）
                let s2 = export(symbols, s);
                let mut cs: Vec<(PatternDetail, Rc<CTm>)> = Vec::with_capacity(cases.len());
                for (p, b) in cases.iter() {
                    cs.push((p.clone(), export(symbols, b)));
                }
                done.push(Rc::new(CTm::Match(s2, cs)));
            }
            J::Lam2(x, i) => {
                let b = done.pop().expect("export 栈：Lam 缺体");
                done.push(Rc::new(CTm::Lam(name(x), i, b)));
            }
            J::Pi2(x, i) => {
                let cod = done.pop().expect("export 栈：Pi 缺余定义域");
                let dom = done.pop().expect("export 栈：Pi 缺定义域");
                done.push(Rc::new(CTm::Pi(name(x), i, dom, cod)));
            }
            J::Let2(x) => {
                let u = done.pop().expect("export 栈：Let 缺体");
                let t = done.pop().expect("export 栈：Let 缺值");
                let a = done.pop().expect("export 栈：Let 缺类型");
                done.push(Rc::new(CTm::Let(name(x), a, t, u)));
            }
            J::App2(i) => {
                let a = done.pop().expect("export 栈：App 缺实参");
                let f = done.pop().expect("export 栈：App 缺函数");
                done.push(Rc::new(CTm::App(f, a, i)));
            }
            J::AppPrun2(pr) => {
                let h = done.pop().expect("export 栈：AppPruning 缺头");
                done.push(Rc::new(CTm::AppPruning(h, pr)));
            }
            J::Obj2(n) => {
                let h = done.pop().expect("export 栈：Obj 缺接收者");
                done.push(Rc::new(CTm::Obj(h, name(n))));
            }
            J::Sum2 {
                name: nm,
                params,
                cases,
                is_trait,
            } => {
                let mut ps: Vec<(crate::parser_lib::Span<SmolStr>, Rc<CTm>, Rc<CTm>, Icit)> =
                    Vec::with_capacity(params.len());
                for p in params.iter().rev() {
                    let ty = done.pop().expect("export 栈：Sum 缺参数类型");
                    let val = done.pop().expect("export 栈：Sum 缺参数值");
                    ps.push((name(p.name), val, ty, p.icit));
                }
                ps.reverse();
                let cs: Vec<crate::parser_lib::Span<SmolStr>> =
                    cases.iter().map(|c| name(c)).collect();
                // L13 CTm::Sum 携带 Rc<Vec>（O(1) 克隆）
                done.push(Rc::new(CTm::Sum(
                    name(nm),
                    Rc::new(ps),
                    Rc::new(cs),
                    is_trait,
                )));
            }
            J::SumCase2 {
                index,
                datas,
                is_trait,
            } => {
                let mut ds: Vec<(crate::parser_lib::Span<SmolStr>, Rc<CTm>, Icit)> =
                    Vec::with_capacity(datas.len());
                for d in datas.iter().rev() {
                    let val = done.pop().expect("export 栈：SumCase 缺字段");
                    ds.push((name(d.name), val, d.icit));
                }
                ds.reverse();
                let typ = done.pop().expect("export 栈：SumCase 缺 typ");
                done.push(Rc::new(CTm::SumCase {
                    typ,
                    index,
                    datas: Rc::new(ds),
                    is_trait,
                }));
            }
            J::Call2 { name: nm, symbol, icits } => {
                // done 自底向上是 (a_{n-1}, ..., a0, body)（body 最后导、在顶）
                let body = done.pop().expect("export 栈：Call 缺体");
                let mut items: Vec<Rc<CTm>> = Vec::with_capacity(icits.len());
                for _ in 0..icits.len() {
                    items.push(done.pop().expect("export 栈：Call 缺实参"));
                }
                // 弹出序 = a0..a_{n-1}；List 序 head = 首实参 → 逆序 prepend
                let mut args: CList<(Rc<CTm>, Icit)> = CList::new();
                for (t, i) in items.into_iter().zip(icits.iter().copied()).rev() {
                    args = args.prepend((t, i));
                }
                match symbol {
                    Some(symbol) => done.push(Rc::new(CTm::OpCall {
                        symbol,
                        name: SmolStr::new(nm),
                        args,
                        body,
                    })),
                    None => done.push(Rc::new(CTm::Call(SmolStr::new(nm), args, body))),
                }
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
            | Tm::LiteralIntro(_) => {}
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
            Tm::Sum(_, params, _, _) => {
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
            Tm::Call(_, args, body) => {
                for (a, _) in args.iter() {
                    stack.push(a);
                }
                stack.push(body);
            }
        }
    }
    n
}

impl Machine {
    /// 每轮注册（参考版 `Cxt::new` 逐条对应）：String 类型 + 15 个内建
    /// （string_concat / str_eq / str_indent2 / report_check_issue /
    /// string_to_global_type / create_global / change_mutable / get_global /
    /// get_global_default / change_mutable_default / file_read_all_text /
    /// file_write_all_text / file_append_all_text / file_exists /
    /// file_delete）。值/类型形态按参考版手工构造——类型项经 `tm_pi` 同序
    /// 折叠、空环境求值；登记项是自引用 `Tm::Decl(name)` 占位 + 卡住
    /// `Decl` 单元 + prim 挂表，真正行为在 force / v_app 的 Decl 臂按
    /// [`PrimId`] 分派（`def_needs_replay` 对内建恒 false）。
    fn prime_round<'a>(&mut self, bump: &'a Bump) -> Cxt<'a> {
        let empty = Cxt::empty();
        // String : U(0)，值 = LiteralType（参考版 Cxt::new 首项）
        let cxt = self.decl_reg(
            bump, &empty, "String", empty_span(()),
            bump.alloc(Tm::LiteralType),
            v_lit_ty(),
            bump.alloc(Tm::U(0)),
            v_u(0),
            None,
        );
        // ── 15 个内建（参考版 add_builtin 逐字）：登记项是自引用
        // `Tm::Decl(name)` 占位 + 卡住 Decl 单元 + prim 挂表——真正行为在
        // force / v_app 的 Decl 臂按 PrimId 分派（def_needs_replay 对内建
        // 恒 false）。类型项按参考版 tm_pi 链手工构造，空环境求值。──
        let st = bump.alloc(Tm::Decl(bump.alloc_str("String"))); // String
        let stgt = |bump: &'a Bump, var: u32| -> &'a Tm<'a> {
            bump.alloc(Tm::App(
                bump.alloc(Tm::Decl(bump.alloc_str("string_to_global_type"))),
                bump.alloc(Tm::Var(var)),
                Icit::Expl,
            ))
        };
        let u0 = || bump.alloc(Tm::U(0));
        // Π 链折叠（head = 首参数；与参考 tm_pi 同序）
        let pi = |bump: &'a Bump, args: Vec<(&'static str, &'a Tm<'a>)>, ret: &'a Tm<'a>| -> &'a Tm<'a> {
            args.iter().rev().fold(ret, |acc, (n, d)| {
                bump.alloc(Tm::Pi(bump.alloc_str(n), Icit::Expl, *d, acc))
            })
        };
        let str_str = || pi(bump, vec![("x", st), ("y", st)], st);
        let boolean = || bump.alloc(Tm::Decl(bump.alloc_str("Boolean")));
        let builtins: Vec<(&'static str, PrimId, &'a Tm<'a>)> = vec![
            ("string_concat", PrimId::StringConcat, str_str()),
            ("str_eq", PrimId::StrEq, pi(bump, vec![("x", st), ("y", st)], boolean())),
            ("str_indent2", PrimId::StrIndent2, pi(bump, vec![("x", st)], st)),
            (
                "report_check_issue",
                PrimId::ReportCheckIssue,
                pi(bump, vec![("code", st), ("module", st), ("signal", st), ("message", st)], u0()),
            ),
            ("string_to_global_type", PrimId::StringToGlobalType, pi(bump, vec![("x", st)], u0())),
            (
                "create_global",
                PrimId::CreateGlobal,
                pi(bump, vec![("x", st), ("y", stgt(bump, 0))], u0()),
            ),
            (
                "change_mutable",
                PrimId::ChangeMutable,
                pi(
                    bump,
                    vec![
                        ("x", st),
                        (
                            "f",
                            pi(bump, vec![("_", stgt(bump, 0))], stgt(bump, 1)),
                        ),
                    ],
                    u0(),
                ),
            ),
            ("get_global", PrimId::GetGlobal, pi(bump, vec![("x", st)], stgt(bump, 0))),
            (
                "get_global_default",
                PrimId::GetGlobalDefault,
                pi(bump, vec![("x", st), ("z", stgt(bump, 0))], stgt(bump, 1)),
            ),
            (
                "change_mutable_default",
                PrimId::ChangeMutableDefault,
                pi(
                    bump,
                    vec![
                        ("x", st),
                        (
                            "f",
                            pi(bump, vec![("_", stgt(bump, 0))], stgt(bump, 1)),
                        ),
                        ("z", stgt(bump, 1)),
                    ],
                    u0(),
                ),
            ),
            ("file_read_all_text", PrimId::FileReadAllText, pi(bump, vec![("path", st)], st)),
            (
                "file_write_all_text",
                PrimId::FileWriteAllText,
                pi(bump, vec![("path", st), ("content", st)], u0()),
            ),
            (
                "file_append_all_text",
                PrimId::FileAppendAllText,
                pi(bump, vec![("path", st), ("content", st)], u0()),
            ),
            ("file_exists", PrimId::FileExists, pi(bump, vec![("path", st)], st)),
            ("file_delete", PrimId::FileDelete, pi(bump, vec![("path", st)], u0())),
        ];
        let mut cxt = cxt;
        for (name, pid, ty_tm) in builtins {
            let vty = self.eval(bump, &cxt, EMPTY_ENV, ty_tm);
            let nm = bump.alloc_str(name);
            let placeholder = bump.alloc(Tm::Decl(nm));
            let val = v_xcell(bump.alloc(XCell::Decl { name: nm }));
            cxt = self.decl_reg(bump, &cxt, name, empty_span(()), placeholder, val, ty_tm, vty, Some(pid));
        }
        cxt
    }

    /// nat 族内建注册（参考版 `Cxt::register_nat_builtins` 逐条对应）：
    /// `nat_to_dec` / `width_range` / `nat_is_ground` + 五则算术 primop。
    /// **时机**：参考版在 nat.typort 加载后调用（该文件的 `+`/`-` impl 体要
    /// 能解析这些名字，故先有递归 def 兜底、再由 prim 覆盖）。
    fn register_nat_builtins<'a>(&mut self, bump: &'a Bump, cxt: &Cxt<'a>) -> Cxt<'a> {
        let nat = bump.alloc(Tm::Decl(bump.alloc_str("Nat")));
        let st = bump.alloc(Tm::Decl(bump.alloc_str("String")));
        let boolean = bump.alloc(Tm::Decl(bump.alloc_str("Boolean")));
        let pi = |bump: &'a Bump, args: Vec<(&'static str, &'a Tm<'a>)>, ret: &'a Tm<'a>| -> &'a Tm<'a> {
            args.iter().rev().fold(ret, |acc, (n, d)| {
                bump.alloc(Tm::Pi(bump.alloc_str(n), Icit::Expl, *d, acc))
            })
        };
        let nat2 = || pi(bump, vec![("x", nat), ("y", nat)], nat);
        let builtins: Vec<(&'static str, PrimId, &'a Tm<'a>)> = vec![
            ("nat_to_dec", PrimId::NatToDec, pi(bump, vec![("n", nat)], st)),
            ("width_range", PrimId::WidthRange, pi(bump, vec![("w", nat)], st)),
            ("nat_is_ground", PrimId::NatIsGround, pi(bump, vec![("w", nat)], boolean)),
            ("nat_add", PrimId::NatAdd, nat2()),
            ("nat_mul", PrimId::NatMul, nat2()),
            ("nat_sub", PrimId::NatSub, nat2()),
            ("nat_div", PrimId::NatDiv, nat2()),
            ("nat_rem", PrimId::NatRem, nat2()),
        ];
        let mut cxt = clone_cxt(cxt);
        for (name, pid, ty_tm) in builtins {
            let vty = self.eval(bump, &cxt, EMPTY_ENV, ty_tm);
            let nm = bump.alloc_str(name);
            let placeholder = bump.alloc(Tm::Decl(nm));
            let val = v_xcell(bump.alloc(XCell::Decl { name: nm }));
            cxt = self.decl_reg(bump, &cxt, name, empty_span(()), placeholder, val, ty_tm, vty, Some(pid));
        }
        cxt
    }

    /// Verilog 兼容具名端口连接内建 `vconnT`（参考版 `Cxt::
    /// register_vconn_builtin` 对应）：`ModuleTree -> Expr -> Expr -> U(0)`。
    /// **时机**：prelude 全部装载后（nat 内建之后）——签名引用的
    /// ModuleTree/Expr 只有 prelude 里有；提前登记的 `tm_decl("ModuleTree")`
    /// 是悬空 neutral，会让后续 unify 打转（参考版注释同款）。
    fn register_vconn_builtin<'a>(&mut self, bump: &'a Bump, cxt: &Cxt<'a>) -> Cxt<'a> {
        let mt = bump.alloc(Tm::Decl(bump.alloc_str("ModuleTree")));
        let expr = bump.alloc(Tm::Decl(bump.alloc_str("Expr")));
        let pi = |bump: &'a Bump, args: Vec<(&'static str, &'a Tm<'a>)>, ret: &'a Tm<'a>| -> &'a Tm<'a> {
            args.iter().rev().fold(ret, |acc, (n, d)| {
                bump.alloc(Tm::Pi(bump.alloc_str(n), Icit::Expl, *d, acc))
            })
        };
        let ty_tm = pi(
            bump,
            vec![("childTree", mt), ("port", expr), ("sig", expr)],
            bump.alloc(Tm::U(0)),
        );
        let vty = self.eval(bump, cxt, EMPTY_ENV, ty_tm);
        let nm = bump.alloc_str("vconnT");
        let placeholder = bump.alloc(Tm::Decl(nm));
        let val = v_xcell(bump.alloc(XCell::Decl { name: nm }));
        self.decl_reg(bump, cxt, "vconnT", empty_span(()), placeholder, val, ty_tm, vty, Some(PrimId::VconnT))
    }

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

/// 参考版 `Tm::no_metas`（L12）：项里第一个**未解** meta 的（上下文快照,
/// 原始类型）——已解 meta **递归进解**（quote 后继续查，参考版同款）。
fn no_metas<'a>(
    bump: &'a Bump,
    m: &mut Machine,
    cxt: &Cxt<'a>,
    t: &'a Tm<'a>,
) -> Option<(crate::list::List<SmolStr>, V)> {
    let mut stack: Vec<&Tm<'a>> = vec![t];
    while let Some(x) = stack.pop() {
        match x {
            Tm::Meta(mm) => match &m.metas[*mm as usize] {
                MetaEntry::Unsolved(_, snap, oty, _) => {
                    // 名单取快照的 telescope（参考版用整个快照 cxt 的
                    // names()——错误消息 pretty 用的名字表）
                    let snap: &MetaSnap<'_> =
                        unsafe { &*(snap.as_ref() as *const MetaSnap<'static> as *const MetaSnap<'_>) };
                    return Some((types_names_list(snap.types), *oty));
                }
                MetaEntry::Solved(v, _) => {
                    let q = m.quote(bump, cxt, cxt.lvl, *v);
                    stack.push(q);
                }
            },
            Tm::Var(_) | Tm::Decl(_) | Tm::U(_) | Tm::LiteralType | Tm::LiteralIntro(_) => {}
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
            Tm::Call(_, args, body) => {
                for (a, _) in args.iter() {
                    stack.push(a);
                }
                stack.push(body);
            }
        }
    }
    None
}

/// 参考版 Def 臂的未解 meta 报错（elaboration.rs 逐字——类型类是 trait
/// Sum 时给类型类消息，否则 `find unsolved meta with type ...`）。
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

    // ── 观察面访问器（`run_decls*` 返回后读取本轮快照；契约与参考版 `Infer`
    // 的三张表逐字段同型，接线时消费端可按同一套逻辑处理两引擎）──
    pub(crate) fn hover_table(&self) -> &[(crate::parser_lib::Span<()>, crate::parser_lib::Span<()>, String)] {
        &self.machine.hover_table
    }
    pub(crate) fn completion_table(&self) -> &[(crate::parser_lib::Span<()>, SmolStr)] {
        &self.machine.completion_table
    }
    pub(crate) fn inlay_hint_table(&self) -> &[(u32, String)] {
        &self.machine.inlay_hint_table
    }
    pub(crate) fn hover_entry_at(
        &self,
        path_id: u32,
        offset: usize,
    ) -> Option<&(crate::parser_lib::Span<()>, crate::parser_lib::Span<()>, String)> {
        self.machine.hover_entry_at(path_id, offset)
    }

    /// 参考版 `run` 的等价物：preprocess + parse 由调用方完成（与参考版
    /// 共用 parser；参考版对 parse 失败 unwrap panic、对 parse 错误只
    /// 打印后继续——快版同口径：None panic、错误静默），本方法做轮重置 +
    /// builtin 重注册 + 逐 decl 推断，println 的 nf 经 pretty 输出（quote
    /// 走记忆化口径——与无记忆化输出逐字节一致，L03-L06 已证）。
    pub(crate) fn run_decls(&mut self, ast: &[Decl]) -> Result<String, Error> {
        self.run_decls_bounded(ast, &[])
    }

    /// [`Tycker::run_decls`] 的带 nat 注册边界变体：`nat_after` 的下标后注册
    /// nat 内建（镜像参考版按文件边界调用 `register_nat_builtins`）。
    pub(crate) fn run_decls_bounded(
        &mut self,
        ast: &[Decl],
        nat_after: &[usize],
    ) -> Result<String, Error> {
        self.bump.reset();
        self.machine.clear_round();
        force_memo_clear();
        let bump = &self.bump;
        let mut cxt = self.machine.prime_round(bump);
        let mut ret = String::new();
        for (i, d) in ast.iter().enumerate() {
            cxt = Self::step_round_decl(&mut self.machine, bump, &cxt, d, i, nat_after, &mut ret)?;
        }
        Ok(ret)
    }

    /// 轮内推进单个 decl：infer + nat 边界 + CheckIssues 逐 decl 排水 +
    /// println 收集（[`Tycker::run_decls_bounded`] 与
    /// [`Tycker::run_decls_with_prelude`] 的用户段共用）。显式取
    /// `&mut Machine`——调用方持有 `&self.bump`，字段不相交方可借用。
    fn step_round_decl<'a>(
        machine: &mut Machine,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        d: &Decl,
        i: usize,
        nat_after: &[usize],
        ret: &mut String,
    ) -> Result<Cxt<'a>, Error> {
        let (out, nc) = machine.infer_decl(bump, cxt, d)?;
        let mut cxt = nc;
        if nat_after.contains(&i) {
            cxt = machine.register_nat_builtins(bump, &cxt);
        }
        // HDL 自检警告：逐 decl 排水（行级去重——参考版
        // take_fresh_check_issues + format_check_warning）
        {
            let mut m = machine.mutable.borrow_mut();
            let pending = m
                .map
                .get("CheckIssues")
                .and_then(|v| match v_xcell_of(*v) {
                    XCell::Lit(s) => Some(s.to_string()),
                    _ => None,
                })
                .unwrap_or_default();
            if !pending.is_empty() {
                m.map.insert(
                    SmolStr::new("CheckIssues"),
                    v_xcell(bump.alloc(XCell::Lit(bump.alloc_str("")))),
                );
                let seen = m
                    .map
                    .get("CheckIssuesSeen")
                    .and_then(|v| match v_xcell_of(*v) {
                        XCell::Lit(s) => Some(s.to_string()),
                        _ => None,
                    })
                    .unwrap_or_default();
                let mut seen2 = seen.clone();
                for line in pending.split('\n').filter(|l| !l.is_empty()) {
                    if !seen2.split('\n').any(|l| l == line) {
                        seen2 = if seen2.is_empty() {
                            line.to_string()
                        } else {
                            format!("{}\n{}", seen2, line)
                        };
                        *ret += &super::format_check_warning(line);
                        *ret += "\n";
                    }
                }
                if seen2 != seen {
                    m.map.insert(
                        SmolStr::new("CheckIssuesSeen"),
                        v_xcell(bump.alloc(XCell::Lit(bump.alloc_str(&seen2)))),
                    );
                }
            }
        }
        if let DeclOut::Println(_, out_s) = out {
            // elaboration 期即算好的 pretty 串（参考版 DeclTm::Println）
            *ret += &out_s;
            *ret += "\n";
        }
        Ok(cxt)
    }

    /// **阶段 2（prelude 装载）整轮入口**：本轮 = prelude 重放 + 用户 decls。
    /// `prelude_decls`/`prelude_file_ends`/`prelude_nat_after` 来自共享
    /// `super::parse_prelude_files`（参考版 `load_prelude_state_impl` 同
    /// 口径的 parse 段）。装载段镜像参考版：逐 decl 推断（println/排水
    /// 不收集——参考版加载器丢弃输出同款）、nat 边界注册 nat 内建、每
    /// 文件边界清 force memo（参考版逐文件清空的内存口径）、全部完成后
    /// 注册 vconnT → 短名别名 or_insert → HdlLoopIdx 复位 → 清观察表
    /// （缓存态不参与 hover/completion）。用户段与
    /// [`Tycker::run_decls_bounded`] 同一推进。
    ///
    /// 每 kick 都从 prime_round 重放整个 prelude（bump 一次性口径）——
    /// 这是接线文档阶段 3a 要实测的 seed 开销基线。
    pub(crate) fn run_decls_with_prelude(
        &mut self,
        prelude_decls: &[Decl],
        prelude_file_ends: &[usize],
        prelude_nat_after: &[usize],
        user_ast: &[Decl],
    ) -> Result<String, Error> {
        self.bump.reset();
        self.machine.clear_round();
        force_memo_clear();
        let bump = &self.bump;
        let mut cxt = self.machine.prime_round(bump);
        let mut file_i = 0usize;
        for (i, d) in prelude_decls.iter().enumerate() {
            let (_out, nc) = self.machine.infer_decl(bump, &cxt, d)?;
            cxt = nc;
            if prelude_nat_after.contains(&i) {
                cxt = self.machine.register_nat_builtins(bump, &cxt);
            }
            if file_i < prelude_file_ends.len() && prelude_file_ends[file_i] == i {
                force_memo_clear();
                file_i += 1;
            }
        }
        cxt = self.machine.register_vconn_builtin(bump, &cxt);
        cxt = insert_prelude_aliases(cxt);
        {
            let mut m = self.machine.mutable.borrow_mut();
            m.map.insert(
                SmolStr::new("HdlLoopIdx"),
                v_xcell(bump.alloc(XCell::Decl {
                    name: bump.alloc_str("hdlLoopIdxEmpty"),
                })),
            );
        }
        self.machine.clear_observation_tables();
        let mut ret = String::new();
        for (i, d) in user_ast.iter().enumerate() {
            cxt = Self::step_round_decl(&mut self.machine, bump, &cxt, d, i, &[], &mut ret)?;
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
        force_memo_clear();
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
        force_memo_clear();
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

    /// 带 nat 注册边界的 check+nf 口径（bench 用）：与 [`Tycker::bench_check_nf`]
    /// 同，但在 `nat_after` 的下标后注册 nat 内建（镜像参考版按文件边界调用
    /// `register_nat_builtins`）。多文件 prelude 拼成单一 decl 序列时用。
    pub(crate) fn bench_check_nf_bounded(&mut self, ast: &[Decl], nat_after: &[usize]) -> u64 {
        self.bump.reset();
        self.machine.clear_round();
        force_memo_clear();
        let bump = &self.bump;
        let mut cxt = self.machine.prime_round(bump);
        let mut last: Option<V> = None;
        for (i, d) in ast.iter().enumerate() {
            match self.machine.infer_decl(bump, &cxt, d) {
                Ok((out, nc)) => {
                    cxt = nc;
                    if nat_after.contains(&i) {
                        cxt = self.machine.register_nat_builtins(bump, &cxt);
                    }
                    if let DeclOut::Def { name } = out {
                        last = cxt.decls.get(name).map(|e| e.val);
                    }
                }
                Err(_) => return 0,
            }
        }
        let Some(v) = last else {
            return 0;
        };
        let q = self.machine.quote(bump, &cxt, 0, v);
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

/// church 2^(k+1)（L13 合法版）：**具体 Nat 类型上的高阶迭代倍增**——`d0`
/// 是"两次 succ"的自函数，`d{i} = n => d{i-1} (d{i-1} n)` 每层翻倍，末位
/// `total : Nat = d{k} zero` 把组合链完全展开成 2^(k+1) 个 succ 的深正规式。
///
/// 注：原 impredicative Church 编码（`Nat = (N : Type 0) -> (N -> N) -> N -> N`
/// 配 `add p p` 式高阶应用）在 L13 **两版一致**判型失败——把 pattern-free 的
/// 多态 church 数嵌套应用于其自身绑定的类型变量 `N`（`a N s (b N s z)`）触发
/// `can't unify expected: N → N find: N`，单层 eta（`a N s z`）则可过。这是该
/// elaborator 语言面限制（非孪生分叉），故换成本形态：同样是高阶函数复合驱动
/// 的 2^(k+1) 深归一化，但两版都能过、可对照计时。
pub(crate) fn church_src(k: u32) -> String {
    let mut s = String::from(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\
         def d0 : Nat -> Nat = n => succ (succ n)\n",
    );
    for i in 1..=k {
        s += &format!("def d{i} : Nat -> Nat = n => d{} (d{} n)\n", i - 1, i - 1);
    }
    s += &format!("def total : Nat = d{k} zero\n");
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
/// + 递归 length/rep——覆盖 Sum/SumCase 值的 unify / quote / rename 全链路。
///
/// 注（L13 合法化，两版一致）：
/// - 构造子应用用元组形式 `cons (x, xs)`；分离位置形式 `cons zero (...)`
///   在本语言面两版一致报 `can't unify expected: (x: ?) → ? x find: Nat`。
/// - `rep` 体内不对 pattern 精化出的 `xs : Vec[Nat] l` 调用**类型泛型**的
///   `length[T]`——把精化 existential 再喂进另一索引多态函数，两版一致报
///   `expected: (x': ? _l h xs) → ? _l h xs x' find: Nat`（已知偏差 2 家族，
///   非孪生分叉）。故 `rep` 走自身递归 `succ (rep xs)`，`add`/`length` 各自
///   独立用 `println` 触发、互不嵌套。
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

def t = cons (zero, cons (two, nil))

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

println (add two two)

def rep[n: Nat](x: Vec[Nat] n): Nat =
    match x {
        case nil => zero
        case cons(_, xs) => succ (rep xs)
    }

println (rep (cons (two, cons (two, nil))))

println (length (cons (two, cons (two, nil))))
"#,
    )
}

/// 最小 struct + inherent impl（`impl Name { def ... }`）+ 依赖索引 Vec
/// —— HDL prelude decl 171（`impl $trait_name$ModuleTree`）unify 失败的
/// 最小化形态：struct 脱糖出的 inherent impl，方法体带 `succ(this.num)`
/// 构造子链与 `m :: this.data` 的 cons 链。
pub(crate) fn moduletree_src() -> String {
    String::from(
        r#"enum Nat {
    zero
    succ(n: Nat)
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

struct ModuleDef {
    expr_num: Nat
}

struct ModuleTree {
    num: Nat
    data: Vec[ModuleDef] num
}

impl ModuleTree {
    def insert(m: ModuleDef): ModuleTree = ModuleTree.mk(succ(this.num), cons m this.data)
}

def md: ModuleDef = ModuleDef.mk(zero)

def t: ModuleTree = ModuleTree.mk(zero, nil)

println (t.insert md).num
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

// 观察面（LSP 接线阶段 1）测试
// --------------------------------------------------------------------------------

#[cfg(test)]
mod observation_tests {
    use super::*;

    /// 同一段源分别过孪生与参考版：全局声明使用处的 hover 条目必须逐字节
    /// 一致（渲染字符串 + def span），证明孪生 push 期 quote→export→pretty
    /// 管线与参考版同界。
    #[test]
    fn hover_global_decl_use_matches_reference() {
        let src = "def foo = \"hello\"\ndef bar = foo\n";
        let ast = parse(src, 42).expect("parse");
        let use_off = src.rfind("foo").unwrap();

        // twin
        let mut t = Tycker::new();
        t.run_input(src, 42).expect("twin check");
        let tw = t
            .hover_entry_at(42, use_off)
            .expect("twin hover entry at `foo` use");

        // reference
        let mut infer = crate::L13_namespace::Infer::new();
        let mut cxt = crate::L13_namespace::cxt::Cxt::new(&infer);
        for d in &ast {
            let (_, _, nc) = infer.infer(&cxt, d.clone()).expect("ref check");
            cxt = nc;
        }
        let rf = infer
            .hover_entry_at(42, use_off)
            .expect("ref hover entry at `foo` use");

        assert_eq!(&tw.2, &rf.2, "rendered hover string");
        assert_eq!(
            (tw.1.start_offset, tw.1.end_offset, tw.1.path_id),
            (rf.1.start_offset, rf.1.end_offset, rf.1.path_id),
            "def-site span"
        );
    }

    /// Local variable (lambda binder) use-site hover: rendered string and
    /// def_span (pointing at the binder token) agree with the reference.
    #[test]
    fn hover_local_var_use_matches_reference() {
        let src = "enum Nat {
    zero
    succ(x: Nat)
}
def d0 : Nat -> Nat = n => succ n
";
        let ast = parse(src, 43).expect("parse");
        let line = src.rfind("succ n").unwrap();
        let use_off = line + "succ ".len();
        let binder_off = src.find("= n =").unwrap() + 2;

        let mut t = Tycker::new();
        t.run_input(src, 43).expect("twin check");
        let tw = t.hover_entry_at(43, use_off).expect("twin local hover");

        let mut infer = crate::L13_namespace::Infer::new();
        let mut cxt = crate::L13_namespace::cxt::Cxt::new(&infer);
        for d in &ast {
            let (_, _, nc) = infer.infer(&cxt, d.clone()).expect("ref check");
            cxt = nc;
        }
        let rf = infer.hover_entry_at(43, use_off).expect("ref local hover");

        assert_eq!(&tw.2, &rf.2, "local rendered type");
        assert_eq!(
            (tw.1.start_offset, tw.1.end_offset),
            (binder_off as u32, (binder_off + 1) as u32),
            "local def_span points at binder token"
        );
        assert_eq!(
            (tw.1.start_offset, tw.1.end_offset, tw.1.path_id),
            (rf.1.start_offset, rf.1.end_offset, rf.1.path_id),
            "local def_span matches reference"
        );
    }

    /// Struct field projection hover: rendered field type agrees with the
    /// reference (def_span intentionally degrades to the field token until
    /// Sum values carry binder spans - see wiring doc).
    #[test]
    fn hover_field_projection_matches_reference() {
        let src = "struct P {\n    x: String\n}\ndef get(p: P): String = p.x\n";
        let ast = parse(src, 44).expect("parse");
        let use_off = src.rfind(".x").unwrap() + 1;

        let mut t = Tycker::new();
        t.run_input(src, 44).expect("twin check");
        let tw = t.hover_entry_at(44, use_off).expect("twin field hover");

        let mut infer = crate::L13_namespace::Infer::new();
        let mut cxt = crate::L13_namespace::cxt::Cxt::new(&infer);
        for d in &ast {
            let (_, _, nc) = infer.infer(&cxt, d.clone()).expect("ref check");
            cxt = nc;
        }
        let rf = infer.hover_entry_at(44, use_off).expect("ref field hover");

        assert_eq!(&tw.2, &rf.2, "field rendered type");
        assert_eq!(tw.2, "String", "field type is String");
    }

    /// Type-ahead completion on a struct receiver: the set of offered field
    /// names keyed at the receiver span agrees with the reference.
    #[test]
    fn completion_struct_fields_matches_reference() {
        let src = "struct P {\n    x: String\n    y: String\n}\ndef get(p: P): String = p.x\n";
        let ast = parse(src, 45).expect("parse");

        let mut t = Tycker::new();
        t.run_input(src, 45).expect("twin check");
        let mut twin_set: Vec<(u32, u32, String)> = t
            .completion_table()
            .iter()
            .map(|(sp, n)| (sp.start_offset, sp.end_offset, n.to_string()))
            .collect();
        twin_set.sort();

        let mut infer = crate::L13_namespace::Infer::new();
        let mut cxt = crate::L13_namespace::cxt::Cxt::new(&infer);
        for d in &ast {
            let (_, _, nc) = infer.infer(&cxt, d.clone()).expect("ref check");
            cxt = nc;
        }
        let mut ref_set: Vec<(u32, u32, String)> = infer
            .completion_table
            .iter()
            .map(|(sp, n)| (sp.start_offset, sp.end_offset, n.to_string()))
            .collect();
        ref_set.sort();

        assert!(!twin_set.is_empty(), "twin offered no completions");
        assert_eq!(twin_set, ref_set, "completion sets (span-keyed) agree");
    }

    /// Inlay hints for inferred returns / un-annotated lets: label text and
    /// anchor offsets agree with the reference (plain, dependent-telescope,
    /// and let cases).
    #[test]
    fn inlay_hints_match_reference() {
        let src = "def g = \"hi\"\ndef id(a: String): String = a\ndef h(b: String) = b\n";
        let ast = parse(src, 46).expect("parse");

        let mut t = Tycker::new();
        t.run_input(src, 46).expect("twin check");
        let mut twin_v: Vec<(u32, String)> = t
            .inlay_hint_table()
            .iter()
            .map(|(o, l)| (*o, l.clone()))
            .collect();
        twin_v.sort();

        let mut infer = crate::L13_namespace::Infer::new();
        let mut cxt = crate::L13_namespace::cxt::Cxt::new(&infer);
        for d in &ast {
            let (_, _, nc) = infer.infer(&cxt, d.clone()).expect("ref check");
            cxt = nc;
        }
        let mut ref_v: Vec<(u32, String)> = infer
            .inlay_hint_table
            .iter()
            .map(|(o, l)| (*o, l.clone()))
            .collect();
        ref_v.sort();

        assert!(!ref_v.is_empty(), "fixture must produce inlay hints");
        assert_eq!(twin_v, ref_v, "inlay (offset, label) sets agree");
    }

    /// PM constructor-pattern hover: `case leaf` / `case node(x)` tokens must
    /// hover like constructor expressions (nullary -> `Tree::leaf`,
    /// parameterized -> Pi signature), keyed at the user's token with def
    /// span at the enum declaration.
    #[test]
    fn hover_pm_constructor_patterns_match_reference() {
        let src = "enum Tree {\n    leaf\n    node(x: Tree)\n}\ndef depth(t: Tree): Tree =\n    match t {\n        case leaf => leaf\n        case node(x) => x\n    }\n";
        let ast = parse(src, 48).expect("parse");

        let mut t = Tycker::new();
        t.run_input(src, 48).expect("twin check");
        let mut twin_v: Vec<(u32, u32, u32, u32, String)> = t
            .hover_table()
            .iter()
            .map(|(ts, ds, r)| {
                (ts.start_offset, ts.end_offset, ds.start_offset, ds.end_offset, r.clone())
            })
            .collect();
        twin_v.sort();

        let mut infer = crate::L13_namespace::Infer::new();
        let mut cxt = crate::L13_namespace::cxt::Cxt::new(&infer);
        for d in &ast {
            let (_, _, nc) = infer.infer(&cxt, d.clone()).expect("ref check");
            cxt = nc;
        }
        let mut ref_v: Vec<(u32, u32, u32, u32, String)> = infer
            .hover_table
            .iter()
            .map(|(ts, ds, r)| {
                (ts.start_offset, ts.end_offset, ds.start_offset, ds.end_offset, r.clone())
            })
            .collect();
        ref_v.sort();

        // 允许两类已知缺项（均登记在接线文档，非本测试核心）：
        //  A) start=0 的参考版 artifact（其 Val::Sum cases 的 Span 丢 start，
        //     PM push 键跟着畸变；孪生值层 cases 只有名字，无从复现 end）；
        //  B) 构造子定义处（use==def-span 形态）条目——孪生 Enum 臂尚未接
        //     def-site push（下一组待接项）。
        let missing: Vec<_> = ref_v
            .iter()
            .filter(|x| !twin_v.contains(x))
            .filter(|x| {
                let start_zero_artifact = x.0 == 0 && x.1 != 0;
                let def_site_entry = x.0 == x.2 && x.1 == x.3;
                !(start_zero_artifact || def_site_entry)
            })
            .map(|x| format!("{}..{}@{}..{} {:?}", x.0, x.1, x.2, x.3, x.4))
            .collect();
        assert!(
            missing.is_empty(),
            "twin PM hover missing unexplained reference entries: {:?}",
            missing
        );
        // 关键断言（从 src 真实计算 token 偏移，不硬编码）：case 的构造子
        // token 必须渲染构造子标识（无参→`Tree::leaf`；参数化→Pi 签名串）。
        let leaf_tok = src.find("case leaf").unwrap() + "case ".len();
        let node_tok = src.find("case node").unwrap() + "case ".len();
        let leaf_entries: Vec<&String> = twin_v
            .iter()
            .filter(|x| x.0 == leaf_tok as u32 && x.1 == (leaf_tok + 4) as u32)
            .map(|x| &x.4)
            .collect();
        let node_entries: Vec<&String> = twin_v
            .iter()
            .filter(|x| x.0 == node_tok as u32 && x.1 == (node_tok + 4) as u32)
            .map(|x| &x.4)
            .collect();
        println!("LEAF token entries: {:?}", leaf_entries);
        println!("NODE token entries: {:?}", node_entries);
        assert!(
            leaf_entries.iter().any(|r| r.as_str() == "Tree::leaf"),
            "`case leaf` token must also hover as Tree::leaf; got {:?}",
            leaf_entries
        );
        assert!(
            node_entries.iter().any(|r| r.starts_with("(x")),
            "`case node` token must also hover as its Pi signature; got {:?}",
            node_entries
        );
    }

    /// Impl-header hover pair: `impl Trait for Ty` — the trait-name token
    /// resolves to the trait declaration, and each implementing `def` name
    /// resolves to the trait method's declaration span.
    #[test]
    fn hover_impl_header_matches_reference() {
        let src = "enum Nat {\n    zero\n    succ(x: Nat)\n}\ntrait Pick[T] {\n    def pick(t: T): T\n}\nimpl Pick[Nat] for Nat {\n    def pick(t: Nat): Nat = t\n}\n";
        let ast = parse(src, 49).expect("parse");

        let mut t = Tycker::new();
        t.run_input(src, 49).expect("twin check");
        let mut twin_v: Vec<(u32, u32, u32, u32, String)> = t
            .hover_table()
            .iter()
            .map(|(ts, ds, r)| {
                (ts.start_offset, ts.end_offset, ds.start_offset, ds.end_offset, r.clone())
            })
            .collect();
        twin_v.sort();

        let mut infer = crate::L13_namespace::Infer::new();
        let mut cxt = crate::L13_namespace::cxt::Cxt::new(&infer);
        for d in &ast {
            let (_, _, nc) = infer.infer(&cxt, d.clone()).expect("ref check");
            cxt = nc;
        }
        let mut ref_v: Vec<(u32, u32, u32, u32, String)> = infer
            .hover_table
            .iter()
            .map(|(ts, ds, r)| {
                (ts.start_offset, ts.end_offset, ds.start_offset, ds.end_offset, r.clone())
            })
            .collect();
        ref_v.sort();

        // 断言两版各自的 impl-header 关键条目存在（trait 名 token、实现
        // 方法名 token），且两版 key 集合一致（渲染串允许偏差 4 的 prime 差）。
        let trait_tok = src.find("impl Pick").unwrap() + "impl ".len();
        let method_tok = src.rfind("def pick").unwrap() + 4;
        let key = |x: &(u32, u32, u32, u32, String)| x.0;
        for (name, off, len) in [("trait-name", trait_tok, 4), ("method-name", method_tok, 4)] {
            let _ = key;
            let in_ref = ref_v.iter().any(|x| x.0 == off as u32 && x.1 == (off + len) as u32);
            let in_twin = twin_v.iter().any(|x| x.0 == off as u32 && x.1 == (off + len) as u32);
            assert!(in_ref, "reference lacks {} hover entry", name);
            assert!(in_twin, "twin lacks {} hover entry", name);
        }
    }

    /// Trait-dispatched member access (`x.pick` resolved through the trait
    /// dictionary, not an inherent namespace entry): the method-name token
    /// must hover with the trait method's declaration span on both engines.
    #[test]
    fn hover_trait_dispatched_method_matches_reference() {
        let src = "enum Nat {\n    zero\n    succ(x: Nat)\n}\ntrait Pick {\n    def pick: Nat\n}\nimpl Pick for Nat {\n    def pick: Nat = zero\n}\ndef use(n: Nat): Nat = n.pick\n";
        let ast = parse(src, 50).expect("parse");

        let mut t = Tycker::new();
        t.run_input(src, 50).expect("twin check");
        let mut twin_v: Vec<(u32, u32, String)> = t
            .hover_table()
            .iter()
            .map(|(ts, _, r)| (ts.start_offset, ts.end_offset, r.clone()))
            .collect();
        twin_v.sort();

        let mut infer = crate::L13_namespace::Infer::new();
        let mut cxt = crate::L13_namespace::cxt::Cxt::new(&infer);
        for d in &ast {
            let (_, _, nc) = infer.infer(&cxt, d.clone()).expect("ref check");
            cxt = nc;
        }
        let mut ref_v: Vec<(u32, u32, String)> = infer
            .hover_table
            .iter()
            .map(|(ts, _, r)| (ts.start_offset, ts.end_offset, r.clone()))
            .collect();
        ref_v.sort();

        // 使用处的 pick token（`n.pick`）两版都必须有条目
        let use_pick = src.rfind("n.pick").unwrap() + 2;
        let in_ref = ref_v.iter().any(|x| x.0 == use_pick as u32 && x.1 == (use_pick + 4) as u32);
        let in_twin = twin_v.iter().any(|x| x.0 == use_pick as u32 && x.1 == (use_pick + 4) as u32);
        assert!(in_ref, "reference lacks trait-dispatch method hover");
        assert!(in_twin, "twin lacks trait-dispatch method hover");
    }

    /// Whole-table parity on a package + qualified-access + bare-name
    /// fallback fixture: every (use-span, rendered-type) entry the reference
    /// table holds must be present in the twin table (twin may hold a few
    /// extra prefix-walk entries; the reference does the same walk, so in
    /// practice sets are equal — assert full equality).
    #[test]
    fn hover_table_full_matches_reference_on_qualified_fixture() {
        let src = "package mylib\n\nenum Tree {\n    leaf\n    node(x: Tree)\n}\n\ndef t: Tree = leaf\n\ndef u: Tree = Tree.node(t)\n";
        let ast = parse(src, 47).expect("parse");

        let mut t = Tycker::new();
        t.run_input(src, 47).expect("twin check");
        let mut twin_v: Vec<(u32, u32, String)> = t
            .hover_table()
            .iter()
            .map(|(ts, _, r)| (ts.start_offset, ts.end_offset, r.clone()))
            .collect();
        twin_v.sort();

        let mut infer = crate::L13_namespace::Infer::new();
        let mut cxt = crate::L13_namespace::cxt::Cxt::new(&infer);
        for d in &ast {
            let (_, _, nc) = infer.infer(&cxt, d.clone()).expect("ref check");
            cxt = nc;
        }
        let mut ref_v: Vec<(u32, u32, String)> = infer
            .hover_table
            .iter()
            .map(|(ts, _, r)| (ts.start_offset, ts.end_offset, r.clone()))
            .collect();
        ref_v.sort();

        // 已知偏差 5：孪生构造子体 datas 的 Raw::Var(参数名) 复用 infer 路径，
        // 产生与 binder 条目同 span 同串的**重复**（参考版该处在值层合成、
        // 不过 infer）。对 LSP 无行为影响（min_by_key 平手取先、串相同）。
        // 断言方向：参考版每条都在孪生（无缺失），且孪生每条都能在参考版
        // 找到同 (span, 串) 项（孪生只允许重复、不允许异质条目）。
        let missing: Vec<_> = ref_v
            .iter()
            .filter(|x| !twin_v.contains(x))
            .map(|(a, b, r)| format!("{}..{} {:?}", a, b, &src[*a as usize..*b as usize]))
            .collect();
        assert!(missing.is_empty(), "twin missing reference entries: {:?}", missing);
        let foreign: Vec<_> = twin_v
            .iter()
            .filter(|x| !ref_v.contains(x))
            .collect();
        assert!(
            foreign.is_empty(),
            "twin has entries absent from reference (should only duplicate): {:?}",
            foreign
        );
    }
}
