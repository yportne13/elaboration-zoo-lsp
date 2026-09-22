//! L09 核心机（eval / quote / unify / rename / solve / prune / check /
//! infer / check_universe / 模式编译）的极致性能版：L08 冠军配方
//! （`bump_spine_iter`）向 MLTT/universe 层的移植。继承 L05-L08 的全部
//! 机制（见 L06/L08 版模块注释与 readme）：bump arena、打包值 [`V`]、
//! 扁平中性 + spine 栈（含链头种类 `Entry.hk` 的 O(1) 头判定）、复合环境、
//! 迭代内核（eval 双栈 / quote 任务栈 / unify 工作表 / rename 任务栈）、
//! quote 记忆化、O(1) 名字解析、`Tycker` 稳态复用。
//!
//! **L09 自己的增量与差异**（参考版 = `super` 的分文件实现，语义以其为
//! 准）——参考版是 init 时期架构的现代残存层，与 L06-L08 的 decl 表世界
//! 有系统性不同，孪生版逐项对齐：
//!
//! - **宇宙层级**：`U(u32)`（`Type N` 语法；裸 `U` 只是普通变量名）。
//!   打包值 tag 3 从立即数改为携带层级（`V = lvl<<3|3`，61 位余量）。
//!   类型注解一律过 [`Machine::check_universe`]（参考版完整版：可解
//!   meta——pren.dom==0 时 meta 类型 force 后是 U 即解 `U(0)`，否则
//!   rename 出 `U(0)` 的解；两分支都返回层级 0）。
//! - **全局 = env 外的 `global` 表 + 大下标**：没有 decl 表。def/enum 在
//!   `Infer.global: HashMap<Lvl, Val>` 里按 `global_idx` 登记，项层引用是
//!   `Tm::Var(Ix(global_idx + 1919810))`（[`GLOBAL_BASE`] 哨兵）；eval 的
//!   Var 臂对越过哨兵的下标查 global 表，quote/rename 对越过哨兵的 Rigid
//!   原样产出大下标 Var。递归 def = fake_bind（src_names 里以全局层级占
//!   位）+ 检查前 global 表放 `VVar(自身大层级)` 占位 + 检查后覆盖真值。
//! - **builtin 只有 `string_concat`**：名字 lambda 链的体是**无名的**
//!   `Tm::Prim`，求值时读 env 前两槽（全为字面量则拼接，否则卡
//!   `Val::Prim`——**不带 spine**，参考版 v_app 对它 panic，故永无
//!   Prim 头的链）。没有可变全局 / 文件 IO / 其余 builtin。
//! - **卡住 match 无 pending、force 只展开 Flex**：v_app 对 Match panic
//!   （不可能吸收实参）；参考版 force 只有一个 Flex 臂——meta 解开后
//!   不会重选 match、不展开投影/decl。卡住投影 `Val::Obj` 只在 eval 的
//!   Tm::Obj 臂产生（接收者 Rigid 才卡，其余 panic）。
//! - **模式特化不走 pm_defs**：参考版走 `check_pm`/`unify_pm` +
//!   `Cxt::update_cxt`/`refresh`——把精化等式**直接改写进环境**（目标槽
//!   替换 + 全槽在"更新后 env"下重求值重锚定），src_names 按层级取类型
//!   （BiMap 的 map2 持久），快版镜像为 `lvl_types` 表 + 双轨迹撤销。
//!   模式编译器（Compiler）与参考版 pattern_match.rs 同步维护（2026-09-18
//!   自决策树矩阵重写为 L07 逐臂下钻，L10-L12 同款）：walk_pat 绑槽 +
//!   check_pm_final 特化 + subst_cxt 臂上下文；覆盖探测 = 值级结构探测
//!   （`run_pure_probe` 快照回滚）。
//! - **unify 无燃料、无 pm 臂、无 (Obj,Obj)/宽松臂**：臂序 = U/Pi/Rigid/
//!   Flex/Flex/Lam/η/Flex 求解/LiteralType 宽松/Sum/SumCase/Match；
//!   flex_flex 单方向尝试无快照回滚；SumCase/SumCase 比 typ+datas（L07+
//!   只比 datas）；Match/Match 分支体在**中性 global 克隆**下重求值
//!   （参考版 avoid_recursive 同款——快版传中性 globals 视图）。
//! - **重定义静默覆盖**（参考版无 redefine 检查）；构造子只以**裸名**登记
//!   （无 `Enum.case` 别名；struct 的 case 名本身是 `Name.mk`）。
//!
//! 与参考版共用 parser / pretty / preprocess，**Ok 输出逐字节一致**（互检
//! 测试 + `tests/l09_fast_parity.rs`）。已知偏差（仅错误消息内容，不影响
//! 判定与 Ok 输出）：快版错误里内嵌的 Debug-Val/Tm 的名字 Span 全零
//! （参考版携带源码偏移），套件比对前按 `start_offset/end_offset/path_id`
//! 归一化。
//!
//! # 分模块导览（2026-09-23 拆分：单文件 → 目录模块）
//!
//! 本文件原为约 7.5k 行单文件；按既有 `// xxx ----` 分节线拆为同目录
//! `bump_spine_iter/` 下的子模块（纯机械搬运：函数体与注释逐行未动，
//! 仅补各子模块 `use` 与跨子系统引用所需的 `pub(super)` 可见性）：
//!
//! - `syntax`：bump 项 Tm/PrCons/LCons + 打包值 V/XCell 与 v_* 构造/
//!   访问器 + global 大下标哨兵 `GLOBAL_BASE`；
//! - `subst`：显式替换 SubstV、σ 跨轮回收（`vsub_reclaim`）、
//!   `mentions_level`、`wrap_sub`、`SpecSolve`；
//! - `env`：复合环境（平坦 defs 区 + binder 链）与 CloCell/PiCell；
//! - `spine`：扁平中性栈（Spine/Entry/HK_*）与 metacontext（MetaEntry/
//!   meta_val_of/lit_of）；
//! - `force`：force/frcs/force_arg + 展开燃料（`UNIFY_FUEL`/refuel/burn）+
//!   vapp1/vapp_ok/project + val_mentions_lvl（条目按原行序跨三处拼装）；
//! - `eval`：运行时分支选择（eval_aux/eval_aux_case）+ 双栈迭代 eval
//!   （W/eval_iter）；
//! - `quote`：任务栈 quote（QJob/quote_iter + QuoteMemo 记忆化）；
//! - `unify`：工作表 unify（UItem/unify_iter + intersect/flex-flex/
//!   lockstep + NO_CONV_MEMO 消融 + ReclaimOnClear 缓冲归还口径）；
//! - `rename`：solve 族（RenBuf/invert/solve/rename/prune/lams，全迭代）；
//! - `machine`：稳态 Machine + elaboration（Cxt/TCons/DeclOut）+ builtin
//!   注册（每轮 prime + string_concat 源项）；
//! - `compiler`：模式匹配编译（特化合一/覆盖探测，L07 逐臂下钻款）；
//! - `debug`：错误消息内嵌 `{:?}` 的 Debug 复刻（L09 特有分节，独立成模块）；
//! - `entry`：export/tm_size/Tycker/run_fast/parse；
//! - `bench_src`：基准负载生成器（bins 引用）。
//!
//! 与 L07 拆分的差异（按本层实际内容）：无 decl 表/prim 归约与 struct_eq
//! 快路径（省略 `prim`/`struct_eq` 子模块）；燃料块随 force、
//! ReclaimOnClear 按原文件位置留在 unify；内嵌测试本层没有（entry 无
//! 测试段）。
//!
//! 对外可见性面在下方以 `pub(crate) use` 原样恢复（外部消费者
//! `L09_mltt::bump_spine_iter::XXX` 路径零改动）。

mod bench_src;
mod compiler;
mod debug;
mod entry;
mod env;
mod eval;
mod force;
mod machine;
mod quote;
mod rename;
mod spine;
mod subst;
mod syntax;
mod unify;

// L09_mltt 的外部项（parser / pretty / mod.rs 项）：以本模块的私有
// use 绑定恢复原 `super::` 路径面——子模块内 `use super::parser::…` 等
// 与拆分前单文件逐字一致。
use crate::L09_mltt::parser;
use crate::L09_mltt::pretty;
use crate::L09_mltt::{Error, Ix, MetaVar, PatternDetail, PosCover, cover_at, empty_span, fmt_path, preprocess};

// 原 pub(crate) 可见面（拆分前单文件的全部 pub(crate) 项，逐一恢复）。
#[allow(unused_imports)]
pub(crate) use bench_src::{church_src, enum_src, match_src, strchain_src, struct_src};
#[allow(unused_imports)]
pub(crate) use compiler::{Compiler, Warning};
#[allow(unused_imports)]
pub(crate) use entry::{SourceDecl, Tycker, parse, run_fast};
#[allow(unused_imports)]
pub(crate) use env::{CloCell, Env, EnvCons, PiCell, env_collect, env_ext, env_ext_defs, env_len, env_nth};
#[allow(unused_imports)]
pub(crate) use machine::{Machine, neutral_of};
#[allow(unused_imports)]
pub(crate) use spine::{MetaEntry, Spine};
#[allow(unused_imports)]
pub(crate) use subst::{SpecSolve, SubstV, SUBSTV_ALIVE};
#[allow(unused_imports)]
pub(crate) use syntax::{PrCons, SumDataT, SumDataV, SumParamT, SumParamV, Tm, V, XCell, v_clo, v_clo_of, v_lit_ty, v_lvl, v_lvl_of, v_meta, v_meta_of, v_pi, v_pi_of, v_spine, v_spine_of, v_tag, v_u, v_u_of, v_xcell, v_xcell_of};
