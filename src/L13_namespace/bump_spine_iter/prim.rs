//! prim：内建 prim 标识（`PrimId`）与可变全局表（`Mutable`）、def-replay
//! 设施（`REPLAY_GLOBAL_OPS`/`def_needs_replay`/`scan_def_replay`/
//! `tm_scan_global_ops`）、原生 Nat 值设施（`is_nat_sum_v`/`nat_step_value`/
//! `count_nat_forced`/`nat_concrete`/`nat_succ_inner`/`nat_succ_shape`）、
//! decl 表（`DeclEntry`/`Decls`）、字面量读取（`lit_of`）与卡住存根 +
//! 内建归约执行体（`stuck_decl`/`prim_exec`）。原 bump_spine_iter.rs 的
//! 文件头 prim/decl 基础设施块、"values" 节 decl 表条目与 "metacontext"
//! 节 prim 执行段，逐行搬运（2026-09-23 拆分）。

use bumpalo::Bump;
use rustc_hash::{FxHashMap, FxHashSet};
use smol_str::SmolStr;
use std::cell::RefCell;
use std::rc::Rc;

use super::parser::syntax::Icit;

use super::env::EMPTY_ENV;
use super::eval::{eval_iter, W};
use super::force::{force, STUCK_DECL_INTERN, vapp1};
use super::machine::{state_journal_record, StateUndo};
use super::spine::{MetaEntry, Spine};
use super::syntax::{SumDataV, Tm, V, XCell, v_tag, v_u, v_xcell, v_xcell_of};


/// 内建 prim 标识（参考版 `PrimFunc` 闭包挂在 decl 表条目的 `.5` 槽；
/// bump 内不能携带闭包，以枚举替代）。执行点 = force 的 Decl 臂（结果再
/// force）+ v_app 的 Decl 臂（结果直接返回）；实参逆 spine 序收集后转
/// 正序传入；返回 `None` = 卡住（留 spine 上等再 force）。nat 算术 prim
/// 与 `vconnT` 仅在 prelude 挂载（register_nat_builtins /
/// register_vconn_builtin），run() 口径不出现。
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum PrimId {
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
/// Clone 供常驻检查点（阶段 3b）每 kick 恢复。
#[derive(Clone)]
pub(super) struct Mutable {
    pub(super) map: FxHashMap<SmolStr, V>,
    /// 无参 def 的 body 是否含全局副作用（`def_needs_replay` 按名缓存）。
    pub(super) replay: FxHashMap<SmolStr, bool>,
    /// CheckIssues 行缓存（评审机会 5）：`report_check_issue` 追加的行
    /// （插入序）+ 未排水行成员集 + 已排水行成员集。行串不再在 mutable
    /// map 里累积（`CheckIssues`/`CheckIssuesSeen` 两个键退役——全仓无
    /// get_global 读者，prelude 只经 `report_check_issue` 写、
    /// `step_round_decl` 排水读），成员判定 O(1)、追加免整串 clone；
    /// 输出字节序由插入序 Vec 保持（append-only 语义逐字节不变）。
    /// 随 Mutable 一起 Clone，常驻检查点恢复语义不变。
    pub(super) check_lines: Vec<SmolStr>,
    pub(super) check_line_set: FxHashSet<SmolStr>,
    pub(super) check_seen: FxHashSet<SmolStr>,
}

impl Mutable {
    pub(super) fn clear(&mut self) {
        self.map.clear();
        self.replay.clear();
        self.check_lines.clear();
        self.check_line_set.clear();
        self.check_seen.clear();
    }
}

/// `REPLAY_GLOBAL_OPS`（参考版 mod.rs 同名常量）：求值 `Tm::Decl` 命中这些
/// 名字（直接或经其它 def 传递）时走重放路径。
const REPLAY_GLOBAL_OPS: &[&str] =
    &["create_global", "change_mutable", "change_mutable_default", "get_global"];

/// `def_needs_replay`：无参 def 的求值是否带全局副作用（按名 memo，环安全）。
/// builtin（prim 挂载）永不重放（登记项是自引用 `Tm::Decl(name)` 占位，
/// 真正行为经 prim 走）——参考版 `scan_def_replay` 同款。
pub(super) fn def_needs_replay(mutable: &RefCell<Mutable>, decl: &Decls<'_>, name: &str) -> bool {
    if let Some(m) = mutable.borrow().replay.get(name) {
        return *m;
    }
    let mut visiting = std::collections::HashSet::new();
    let result = scan_def_replay(mutable, decl, name, &mut visiting);
    // kick 撤销帧记账（评审 B#2 二期）：memo 只增，撤销 = 移除本键。
    let k = SmolStr::new(name);
    let old = mutable.borrow_mut().replay.insert(k.clone(), result);
    state_journal_record(StateUndo::MutableReplay(k, old));
    result
}

pub(super) fn scan_def_replay(
    mutable: &RefCell<Mutable>,
    decl: &Decls<'_>,
    name: &str,
    visiting: &mut std::collections::HashSet<SmolStr>,
) -> bool {
    // memo 读：已扫描过的名字直接用其独立答案（与 def_needs_replay 的顶层
    // memo 同源同值）。无此读则引用链上每个 def 的扫描都从头走整条链——
    // 依赖链负载（strchain）每 decl O(D)、全轮 O(D²)（perf-debt P4）。
    if let Some(m) = mutable.borrow().replay.get(name) {
        return *m;
    }
    if !visiting.insert(SmolStr::new(name)) {
        return false; // 环：无新信息
    }
    let mut truncated = false;
    let result = match decl.get(name) {
        Some(e) if e.prim.is_some() => false,
        Some(e) => {
            let mut found = false;
            tm_scan_global_ops(mutable, decl, e.tm, visiting, &mut found, &mut truncated);
            found
        }
        None => false,
    };
    visiting.remove(name);
    // memo 写（带截断守卫）：子扫描途中命中过环守卫的结果可能是保守假
    // （op 经由在扫祖先才可达），存表会毒化后续查询——只在全程无截断
    // （链形/树形引用，独立重扫必得同值）时入表。kick 撤销帧同步记账
    // （memo 只增，撤销 = 移除本键）。
    if !truncated {
        let k = SmolStr::new(name);
        let old = mutable.borrow_mut().replay.insert(k.clone(), result);
        state_journal_record(StateUndo::MutableReplay(k, old));
    }
    result
}

/// 深度优先扫闭合项里的 REPLAY_GLOBAL_OPS 调用（`Tm::Decl` 头）或对其它
/// 需重放 def 的引用（参考版 `tm_scan_global_ops` 逐句）。`truncated` =
/// 扫描途中命中过环守卫（调用方据此决定 memo 是否可存）。
pub(super) fn tm_scan_global_ops(
    mutable: &RefCell<Mutable>,
    decl: &Decls<'_>,
    tm: &Tm<'_>,
    visiting: &mut std::collections::HashSet<SmolStr>,
    found: &mut bool,
    truncated: &mut bool,
) {
    if *found {
        return;
    }
    match tm {
        Tm::Decl(x) => {
            if REPLAY_GLOBAL_OPS.contains(x) {
                *found = true;
            } else if decl.get(*x).is_some() {
                if let Some(m) = mutable.borrow().replay.get(*x) {
                    if *m {
                        *found = true;
                    }
                } else if !visiting.insert(SmolStr::new(*x)) {
                    *truncated = true;
                } else {
                    // 内联 scan_def_replay 主体（memo 读已做，子扫描后按
                    // 截断守卫回填 memo）
                    let result = match decl.get(*x) {
                        Some(e) if e.prim.is_some() => false,
                        Some(e) => {
                            let mut f2 = false;
                            tm_scan_global_ops(mutable, decl, e.tm, visiting, &mut f2, truncated);
                            f2
                        }
                        None => false,
                    };
                    visiting.remove(*x);
                    if !*truncated {
                        // kick 撤销帧记账（评审 B#2 二期）：内联回填 memo。
                        let k = SmolStr::new(*x);
                        let old = mutable.borrow_mut().replay.insert(k.clone(), result);
                        state_journal_record(StateUndo::MutableReplay(k, old));
                    }
                    if result {
                        *found = true;
                    }
                }
            }
        }
        Tm::Obj(t, _) => tm_scan_global_ops(mutable, decl, t, visiting, found, truncated),
        Tm::Lam(_, _, b) => tm_scan_global_ops(mutable, decl, b, visiting, found, truncated),
        Tm::App(f, u, _) => {
            tm_scan_global_ops(mutable, decl, f, visiting, found, truncated);
            tm_scan_global_ops(mutable, decl, u, visiting, found, truncated);
        }
        Tm::AppPruning(t, _) => {
            tm_scan_global_ops(mutable, decl, t, visiting, found, truncated)
        }
        Tm::Pi(_, _, a, b) => {
            tm_scan_global_ops(mutable, decl, a, visiting, found, truncated);
            tm_scan_global_ops(mutable, decl, b, visiting, found, truncated);
        }
        Tm::Let(_, _, t, u) => {
            tm_scan_global_ops(mutable, decl, t, visiting, found, truncated);
            tm_scan_global_ops(mutable, decl, u, visiting, found, truncated);
        }
        Tm::SumCase { typ, datas, .. } => {
            tm_scan_global_ops(mutable, decl, typ, visiting, found, truncated);
            for d in datas.iter() {
                tm_scan_global_ops(mutable, decl, d.val, visiting, found, truncated);
            }
        }
        Tm::Match(t, cases) => {
            tm_scan_global_ops(mutable, decl, t, visiting, found, truncated);
            for (_, b) in cases.iter() {
                tm_scan_global_ops(mutable, decl, b, visiting, found, truncated);
            }
        }
        Tm::Call(_, args, body) => {
            for (t, _) in args.iter() {
                tm_scan_global_ops(mutable, decl, t, visiting, found, truncated);
            }
            tm_scan_global_ops(mutable, decl, body, visiting, found, truncated);
        }
        Tm::Sum(_, params, _, _) => {
            for p in params.iter() {
                tm_scan_global_ops(mutable, decl, p.val, visiting, found, truncated);
                tm_scan_global_ops(mutable, decl, p.ty, visiting, found, truncated);
            }
        }
        Tm::Var(_) | Tm::U(_) | Tm::Meta(_) | Tm::LiteralType | Tm::LiteralIntro(_) => {}
    }
}

/// 值是否为 `Nat` sum 类型本体（参考版 `is_nat_sum` 的快版对应）。
#[inline]
pub(super) fn is_nat_sum_v(v: V) -> bool {
    v_tag(v) == 7
        && matches!(v_xcell_of(v), XCell::Sum { name: "Nat", is_trait: false, .. })
}

/// SumCase 装配点的原生 Nat 折叠（参考版 `nat_step_value`）：typ 已求值为
/// `v`；`zero`（index 0 空）→ 0，`succ (Nat k)`（index 1 单字段且内层是
/// Nat）→ k+1；其余 None（保持 SumCase 形状）。
pub(super) fn nat_step_value(typ: V, index: u32, datas: &[SumDataV<'_>]) -> Option<u64> {
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
    /// [`Machine::decl_reg`] 一次 quote→export→pretty）。**消费方是 LSP
    /// def-site 悬浮（参考版 lib.rs Path1 直读 decl 行同款）**——使用处
    /// 悬浮走实时渲染（`push_hover_cached`，阶段 2 起：登记期缓存串可能
    /// 是 meta 解出前的旧形态）。prelude 装载段跳过渲染（`observe` 门控，
    /// 见 [`Machine::decl_reg`]）。
    pub(crate) typ_pretty: Option<Rc<String>>,
    /// `typ_pretty` 可安全复用旗：登记期引出项无未解 meta（`no_metas`
    /// 闸）——此时串与使用处实时渲染逐字节一致，`push_hover_cached` 直推
    /// 免重复 quote/export/pretty（评审 B#1）。`false`（含 None）保持实时
    /// 渲染，语义与旧路径一致。
    pub(crate) typ_pretty_final: bool,
    /// 登记项（参考版行的 .1；eval 的 `Tm::Decl` 臂 replay 路径取它重放）。
    pub(crate) tm: &'a Tm<'a>,
    /// 类型**项**（参考版行的 .3 `a_quote`）：登记处 `check_universe` 出的
    /// 类型项，非引出的类型值。LSP 参考域导出（阶段 4）需要真实存它——
    /// `pretty_sum_definition` 靠它渲染构造子签名、并判定尾随 `→ ret`
    /// 是否省略（codomain 头是否 `Tm::Decl(enum)`）。此前快版无读取点故
    /// 省略，导出层一来它就成了必需字段。
    pub(crate) ty: &'a Tm<'a>,
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

/// 从实参值取字面量内容（非字面量 → None）。返回值的 `'a` 与入参无
/// link——健全性依赖全局不变式：所有 `V` 的 XCell 都指向**当前轮的
/// bump**或 `'static` 钉串，跨轮 `bump.reset()` 前一切句柄已消亡。
#[inline]
pub(super) fn lit_of<'a>(v: V) -> Option<&'a str> {
    match v_tag(v) {
        7 => match v_xcell_of(v) {
            XCell::Lit(s) => Some(s),
            _ => None,
        },
        _ => None,
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
pub(super) fn count_nat_forced(
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
pub(super) fn nat_concrete(
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
pub(super) fn nat_succ_inner(v: V) -> Option<V> {
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
pub(super) fn nat_succ_shape<'a>(bump: &'a Bump, decl: &Decls<'a>, inner: V) -> Option<V> {
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
///
/// 裸基座 intern（表见 [`STUCK_DECL_INTERN`]）：同名字存根轮内共享同一
/// bump 单元——参考版的 `Val::Decl` 基座本就是 decl 表共享的 Rc，位相等
/// 捷径与 conv.memo 键因此常命中；孪生旧实现每次新造单元，两条捷径系统性
/// miss。轮界 `force_memo_clear()` 清空（bump 句柄不跨轮）。
pub(super) fn stuck_decl<'a>(bump: &'a Bump, spine: &mut Spine, name: &str, args: &[V]) -> V {
    let base = match STUCK_DECL_INTERN.with(|c| c.borrow().get(name).copied()) {
        Some(v) => v,
        None => {
            let v = v_xcell(bump.alloc(XCell::Decl { name: bump.alloc_str(name) }));
            STUCK_DECL_INTERN.with(|c| {
                c.borrow_mut().insert(SmolStr::new(name), v);
            });
            v
        }
    };
    let mut acc = base;
    for a in args {
        acc = spine.push(acc, *a, Icit::Expl);
    }
    acc
}

/// 崩溃（parity 套件不触达；与参考版行为一致）。
#[allow(clippy::too_many_arguments)]
pub(super) fn prim_exec<'a>(
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
    // tick 补点：force 的未打点调用方（tag-7 区间归因用）。
    #[cfg(feature = "sampler")]
    crate::sampler::tick();
    // 实参统一 force 到 WHNF 再进分派：非纯 prim 在 eval 点直呼时
    // （lazy_pure_prim 只拦纯 prim），实参可能是 eval 惰性产生的纯 prim
    // 中性 spine——不 force 则 lit_of / Nat / HDL 形状检查全部失准
    // （vconnT 输出 parity 破坏的根因）；force 入口已各 force 一次，此处
    // 重复 force 对 WHNF 是 O(1) 直通。参考版 prim_fn 的"实参先 force"
    // 纪律同款。
    let forced: Vec<(V, Icit)> = args
        .iter()
        .map(|(v, i)| (force(bump, spine, defs, metas, decl, mutable, *v), *i))
        .collect();
    let args: &[(V, Icit)] = &forced;
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
            // 行级去重走行集缓存（评审机会 5）：原实现每次整串 clone +
            // split 线性扫，串长随未排水行数线性增长；成员判定 O(1)，
            // 行串只在排水时拼（插入序 Vec 保持 append-only 字节序）。
            let key = SmolStr::new(line);
            if !m.check_line_set.contains(&key) {
                m.check_line_set.insert(key.clone());
                m.check_lines.push(key.clone());
                // kick 撤销帧记账（评审 B#2 二期）：仅新键推送。
                state_journal_record(StateUndo::CheckLinesPush(key));
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
            // kick 撤销帧记账（评审 B#2 二期）：insert 返回值即旧值。
            let k = SmolStr::new(name);
            let old = mutable.borrow_mut().map.insert(k.clone(), arg(1).unwrap());
            state_journal_record(StateUndo::MutableMap(k, old));
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
                    bump, spine, &mut w2, &mut v2, &mut i2, defs, metas, decl, mutable, false, f, x,
                    Icit::Expl,
                );
                // kick 撤销帧记账（评审 B#2 二期）。
                let k = SmolStr::new(name);
                let prev = mutable.borrow_mut().map.insert(k.clone(), nx);
                state_journal_record(StateUndo::MutableMap(k, prev));
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
                        bump, spine, &mut w2, &mut v2, &mut i2, defs, metas, decl, mutable, false, f, x,
                        Icit::Expl,
                    );
                    // kick 撤销帧记账（评审 B#2 二期）。
                    let k = SmolStr::new(name);
                    let prev = mutable.borrow_mut().map.insert(k.clone(), nx);
                    state_journal_record(StateUndo::MutableMap(k, prev));
                }
                None => {
                    // kick 撤销帧记账（评审 B#2 二期）。
                    let k = SmolStr::new(name);
                    let prev = mutable.borrow_mut().map.insert(k.clone(), default);
                    state_journal_record(StateUndo::MutableMap(k, prev));
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
                    XCell::SumCase { typ, index, .. } => {
                        // typ 守卫同 [`project`]（:939 惯例）——tag 检查是
                        // v_xcell_of 解引用的前置守卫，非 Sum 形态回 noop
                        if v_tag(*typ) != 7 {
                            return None;
                        }
                        match v_xcell_of(*typ) {
                            XCell::Sum { cases, .. } => cases.get(*index as usize).copied(),
                            _ => None,
                        }
                    }
                    _ => None,
                }
            };
            if ctor_name(port) != Some("subSignal") {
                return Some(noop);
            }
            let pname = match v_xcell_of(port) {
                XCell::SumCase { datas, .. } => match datas.get(1) {
                    Some(d) => {
                        if v_tag(d.val) != 7 {
                            return Some(noop);
                        }
                        match v_xcell_of(d.val) {
                            XCell::Lit(s) => *s,
                            _ => return Some(noop),
                        }
                    }
                    None => return Some(noop),
                },
                _ => return Some(noop),
            };
            // 参考版 field() 只认 SumCase 的 datas（不查 Sum 参数槽）；
            // 非构造子值（宇宙/中性/λ……）→ None → noop（参考版 match
            // Val::SumCase 的 `_ => None` 同款——tag 检查即解引用守卫）。
            let field = |v: V, name: &str| -> Option<V> {
                if v_tag(v) != 7 {
                    return None;
                }
                match v_xcell_of(v) {
                    XCell::SumCase { datas, .. } => {
                        datas.iter().find(|d| d.name == name).map(|d| d.val)
                    }
                    _ => None,
                }
            };
            let field_str = |v: V, name: &str| -> Option<&str> {
                let x = field(v, name)?;
                if v_tag(x) != 7 {
                    return None;
                }
                match v_xcell_of(x) {
                    XCell::Lit(s) => Some(*s),
                    _ => None,
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
                    bump, spine, &mut w2, &mut v2, &mut i2, defs, metas, decl, mutable, false, emit, b,
                    Icit::Expl,
                );
                let e = vapp1(
                    bump, spine, &mut w2, &mut v2, &mut i2, defs, metas, decl, mutable, false, e, port,
                    Icit::Expl,
                );
                let _ = vapp1(
                    bump, spine, &mut w2, &mut v2, &mut i2, defs, metas, decl, mutable, false, e, sig,
                    Icit::Expl,
                );
            }
            Some(noop)
        }
    }
}
