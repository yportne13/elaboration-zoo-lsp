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
//! 一致**（互检测试 + `tests/l13_fast_parity.rs`）。
//!
//! **已移植（观察面 / LSP 接线阶段 1-4，docs/lsp-twin-wiring-2026-09.md）**：
//! hover/completion/inlay 三张 owned 观察表（push 期渲染）、prelude 装载轮
//! （[`Tycker::run_decls_with_prelude`]，nat/vconnT 内建 + 短名别名 +
//! HdlLoopIdx 口径；**无 PreludePool 池化**——每 kick 从 prime_round 重放，
//! 装载段 `observe=false` 关观察面 push）、以及 **force 记忆化**
//! （[`FORCE_MEMO`]，`d85a759` 移植：HDL prelude 由 11.0s 降到 1.8s，是 LSP
//! 接线的前提；bump 同代不回收，故免 keepalive，每轮入口 `force_memo_clear`）。
//! LSP 侧 `Engine::Twin` 已接线（`lib.rs::twin_observe` / `twin_elaborate`），
//! 走**常驻 prelude 检查点**（阶段 3b：`prime_resident` 一次装载 +
//! `observe_user` 多次复用，线程局部挂分析主循环），并在**阶段 4 接管单文件
//! 诊断**（错误 span 保真 + 逐 decl 累积 + 导出声明并回参考域）——稳态 kick
//! 98ms vs 参考版 359ms（约 3.5×），常驻态经 arena 压实 1835MB → 429MB。
//! 不移植（仍仅参考版）：retry 闭包、FUNC_PROF 的**计时**版、Tm/Val 迭代
//! Drop（bump 免疫）、PreludePool 池化/defer_println（run() 口径为 false）、
//! canonical/iddfs（只在参考版 Err 路径的重试闭包里，不影响判定与输出）。
//! FUNC_PROF 的**计数**探针已接（`super::prof_count`，与参考版同一组计数器，
//! 仅 `enabled` 时一次原子加）——双引擎调用量 A/B 用（`TYPORT_PRELUDE_PROF`
//! 或直接置 `FUNC_PROF.enabled`），孪生侧刻意不取 `Instant`，避免给热路径
//! 加计时开销。
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
//! 4. 观察面（LSP 接线阶段 1）：~~全局名使用的 hover 串取登记处缓存~~
//!    **已修复（阶段 2）**：使用处（含 qualified 三连、后缀回退）一律
//!    实时渲染（`push_hover_cached` = push_hover），登记期 `typ_pretty`
//!    仅保留给 LSP def-site 悬浮。残余仅 fresh 后缀显示差异（参考版在使用
//!    处上下文渲染，binder 遮蔽时 `x` vs `x'`）。
//! 5. 观察面表形态：孪生 Enum 臂构造子体 `datas` 复用 `Raw::Var(参数名)`
//!    过 infer，产生与 binder 条目**同 span 同串的重复项**（参考版该处在
//!    值层合成、不过 infer）。`hover_entry_at` 平手取先且串相同，对 LSP
//!    行为无影响；全表互检按「无缺失 + 无异质」口径断言（见
//!    `observation_tests::hover_table_full_matches_reference_on_qualified_fixture`）。
//!    **扩展（阶段 2）**：PM 构造子 pattern token 同理可推**同串重复**
//!    （PM 臂 + Var 臂各一），set 级互检不可见。
//! 6. 观察面表形态（阶段 2）：tuple 字段访问 `p._2` 反糖出的合成构造子
//!    Var 无源码 span，`.name` 后缀回退 push 的 t_span=0（参考版同场景推
//!    声明 span 形态）——push 键畸变，串与 def_span 一致。
//!
//! # 分模块导览（2026-09-23 拆分：单文件 → 目录模块）
//!
//! 本文件原为约 15.7k 行单文件；按既有 `// xxx ----` 分节线拆为同目录
//! `bump_spine_iter/` 下的子模块（纯机械搬运：函数体与注释逐行未动，
//! 仅补各子模块 `use` 与跨子系统引用所需的 `pub(super)` 可见性）：
//!
//! - `syntax`：bump 项 Tm/PrCons/LCons + 打包值 V/XCell/SumParamV/SumDataV
//!   与 v_* 构造/访问器；
//! - `env`：复合环境（平坦 defs 区 + binder 链）与 CloCell/PiCell 及
//!   packed-word 对齐断言；
//! - `prim`：内建 prim 标识与可变全局表（PrimId/Mutable）、def-replay
//!   设施、原生 Nat 值设施、decl 表（DeclEntry/Decls）、字面量读取与
//!   卡住存根 + 内建归约执行体（stuck_decl/prim_exec）；
//! - `spine`：扁平中性栈（Spine/Entry/HK_*）与 metacontext
//!   （MetaSnap/MetaEntry/meta_val_of）及其就地写撤销日志；
//! - `force`：force/force_inner + vapp1/project + force 记忆化与孪生缓存
//!   读数块（FORCE_MEMO/force_memo_clear/TWIN_STAT_*/twin_mem_stats/
//!   ReclaimOnClear；全模块共用的轮界清空 thread_local 缓存表挂此处）；
//! - `eval`：双栈迭代 eval（W/eval_iter）+ 运行时分支选择（eval_aux）；
//! - `quote`：任务栈 quote（QJob/quote_iter + QuoteMemo）+ quote_nat_chain；
//! - `unify`：工作表 unify（UItem/unify_iter + NO_CONV_MEMO 消融/
//!   ConvScratch/declb_of 缓存）+ intersect/flex-flex/lockstep +
//!   solve_flex_side_bump；
//! - `rename`：solve 族（RenBuf/invert/solve/rename/prune/lams，全迭代）；
//! - `machine`：稳态 Machine + state journal（STATE_JOURNAL/StateUndo）+
//!   Elaboration 上下文（Cxt/TCons/NsCons）+ elaboration 全量
//!   （check/check_universe/insert 族/模式特化/refresh/主 infer/
//!   infer_expr/infer_decl/wrap_match_in_call）+ 名字解析与参考域助手；
//! - `typeclass`：trait 求解（solve_multi_trait_ref/solve_trait_ref）与
//!   trait_wrap/mk_no_object_err（两者均以独立 `impl Machine` 块承载，
//!   L10 先例）+ TraitDefEntry/TraitState/head_key_v/val_cache_key_t/
//!   v_to_ref_val 解码桥；
//! - `debug`：错误消息内嵌 `{:?}` 输出的 Debug 复刻（L09 同款独立模块）；
//! - `compiler`：模式匹配编译（Compiler/Warning + 覆盖检查）；
//! - `observe`：观察面（LSP 接线阶段 1）——观察表 push 方法
//!   （clear_observation_tables/push_hover 族，独立 `impl Machine` 块）+
//!   "观察面（LSP 接线阶段 1）测试" 节（observation_tests）；
//! - `entry`：export 与对外入口（export/tm_size/no_metas 族/builtin 注册/
//!   常驻检查点/Tycker/run_fast/parse/SourceDecl）；
//! - `bench_src`：基准负载生成器（bins 引用）；
//! - `compact`：常驻检查点 arena 压实（拆分前已存在的子模块，一字未动）。
//!
//! 本层没有而省略的标准子模块：`subst`（L13 无显式替换设施——无
//! SubstV/SpecSolve/σ 族）、`struct_eq`（无该分节；结构比较由 unify 的
//! 快路径承担）。原文件的命名空间/模块系统设施（package/import/五级名字
//! 解析/decl 后缀索引）无独立分节，与 `Machine` 的结构体字段及 impl 方法
//! 交织，为守住纯机械搬运不单独成模块，随 `machine` 走。
//!
//! 对外可见性面在下方以 `pub(crate) use` 原样恢复（外部消费者
//! `L13_namespace::bump_spine_iter::XXX` 路径零改动）。与 L10 拆分同款：
//! 本层参考版自带 `typeclass` 求解器模块，与子模块 `mod typeclass` 同名，
//! 需要其类型的子模块直接 `use crate::L13_namespace::typeclass::{…}`
//! 全路径导入；`super::typeclass::GENERIC_SELF_HEAD` 经 typeclass 子模块
//! 自身的全路径 use 绑定解析。

mod bench_src;
mod compact;
mod compiler;
mod debug;
mod entry;
mod env;
mod eval;
mod force;
mod machine;
mod observe;
mod prim;
mod quote;
mod rename;
mod spine;
mod syntax;
mod typeclass;
mod unify;

/// 构造子可达性探测次数（`compiler::probe_accessible` 入口自增）。与参考版
/// `pattern_match::PROBE_COUNT` 同口径，用于"次数差异 vs 单价差异"的判别——
/// `l13lspsample` 打印采样窗口内的增量（累计值含 prelude 与预热 kick，不可
/// 直接跨引擎比）。
thread_local! {
    pub static PROBE_COUNT: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

// L13_namespace 的外部项（parser / pretty / mod.rs 项）：以本模块的私有
// use 绑定恢复原 `super::` 路径面——子模块内 `use super::parser::…` 等
// 与拆分前单文件逐字一致。（`typeclass` 求解器模块与子模块同名，见上。）
use crate::L13_namespace::parser;
use crate::L13_namespace::pretty;
use crate::L13_namespace::pretty::pretty_tm;
#[allow(unused_imports)]
use crate::L13_namespace::parser::syntax::{ClassItem, Decl, Either, Icit, Pattern, Raw};
use crate::L13_namespace::{cover_at, empty_span, fmt_path, Error, Ix, MetaVar, PatternDetail, PosCover, Tm as CTm};
use crate::L13_namespace::{
    ExportedDecl, Lvl, PreludeParse, FUNC_PROF, format_check_warning, is_operator_char,
    nat_primop_symbol, preprocess, prof_count, prof_enter,
};
#[allow(unused_imports)]
use crate::L13_namespace::typeclass::{Assertion, Instance, Synth};
use crate::L13_namespace::Val as CVal;
#[allow(unused_imports)]
use crate::L13_namespace::MetaVar as CMetaVar;
#[allow(unused_imports)]
use crate::list::List as CList;
use crate::parser_lib::ToSpan;

// 原单文件头部的 std / 外部 crate 绑定：保持 `use super::*`（observe /
// compact）与拆分前作用域等价。
use bumpalo::Bump;
#[allow(unused_imports)]
use rustc_hash::{FxHashMap, FxHashSet};
use smol_str::SmolStr;
#[allow(unused_imports)]
use std::cell::RefCell;
#[allow(unused_imports)]
use std::collections::HashMap;
use std::rc::Rc;
#[allow(unused_imports)]
use std::sync::Arc;

// compact.rs / observe.rs（`use super::*`）所需的跨子模块私有项：以本模块
// 私有 use 绑定接入原单文件作用域（子模块可见父模块的私有绑定）。
#[allow(unused_imports)]
use entry::{export, no_metas, RESIDENT_BUMP_LIMIT};
#[allow(unused_imports)]
use force::{twin_stat_record, ReclaimOnClear, CACHE_SHRINK_MIN_ENTRIES, TWIN_STAT_QUOTE};
use machine::{qualified_path_str, types_names_list, Cxt, Names, TCons};
#[allow(unused_imports)]
use machine::{clone_cxt, insert_prelude_aliases};
use prim::Mutable;
use spine::Entry;
use syntax::LCons;

// 原 pub(crate) 可见面（拆分前单文件的全部 pub(crate) 项，逐一恢复）。
#[allow(unused_imports)]
pub(crate) use bench_src::{
    church_src, enum_src, gadt_src, match_src, moduletree_src, natadd_src, struct_src,
    strchain_src, wide_enum_src,
};
#[allow(unused_imports)]
pub(crate) use compiler::{Compiler, Warning};
#[allow(unused_imports)]
pub(crate) use entry::{parse, run_fast, SourceDecl, Tycker};
#[allow(unused_imports)]
pub(crate) use env::{
    env_collect, env_ext, env_ext_defs, env_len, env_nth, CloCell, Env, EnvCons, PiCell,
};
#[allow(unused_imports)]
pub use force::twin_mem_stats;
#[allow(unused_imports)]
pub(crate) use machine::{Machine, NsCons};
#[allow(unused_imports)]
pub(crate) use prim::{DeclEntry, Decls};
#[allow(unused_imports)]
pub(crate) use spine::{meta_unsolved, MetaEntry, MetaSnap, Spine};
#[allow(unused_imports)]
pub(crate) use syntax::{
    PrCons, SumDataT, SumDataV, SumParamT, SumParamV, Tm, V, XCell, v_clo, v_clo_of, v_lit_ty,
    v_lvl, v_lvl_of, v_meta, v_meta_of, v_pi, v_pi_of, v_spine, v_spine_of, v_tag, v_u, v_u_of,
    v_xcell, v_xcell_of,
};
#[allow(unused_imports)]
pub(crate) use typeclass::{TraitState, v_to_ref_val};
// 原 pub(super) 面：typeclass.rs（参考域 typeclass.rs 的孪生镜像）的 Synth
// 写点直接记账。
#[allow(unused_imports)]
pub(super) use machine::{state_journal_record, StateUndo};
// 原 pub(crate)（仅 #[cfg(test)]）：observe 的 observation_tests 使用。
#[cfg(test)]
#[allow(unused_imports)]
pub(crate) use entry::{resident_compactions, set_resident_bump_budget};

