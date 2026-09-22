//! L10 核心机（eval / quote / unify / rename / solve / prune / check /
//! infer / check_universe / 模式编译 / trait 求解）的极致性能版：L09
//! 冠军配方（`bump_spine_iter`）向 typeclass 层的移植。继承 L05-L09 的全部
//! 机制（见 L06/L08/L09 版模块注释与 readme）：bump arena、打包值 [`V`]、
//! 扁平中性 + spine 栈（含链头种类 `Entry.hk` 的 O(1) 头判定）、复合环境、
//! 迭代内核（eval 双栈 / quote 任务栈 / unify 工作表 / rename 任务栈）、
//! quote 记忆化、O(1) 名字解析、`Tycker` 稳态复用。
//!
//! **L10 自己的增量与差异**（参考版 = `super` 的分文件实现，语义以其为
//! 准）——L10 参考版 = L09 的 init 时期架构 + trait 脱糖与求解：世界口径
//! （`U(u32)`、`Infer.global` 大下标哨兵、模式特化走显式替换、无燃料
//! unify）逐条沿用 L09 版注释，下方"要点"重述；此处先记 L10 的增量。
//!
//! - **trait = `is_trait` 的 Sum**：trait 声明脱糖为 enum（构造子即实例），
//!   另在 [`TraitState`] 里维护 `definition`（trait 名 → 方法表）与
//!   `out_param`（参数 out 掩码）；`Tm::Sum`/`Tm::SumCase` 带 `is_trait`
//!   标记，trait 的 fresh_meta 走实例合成。
//! - **trait 求解镜像参考版 `Infer::solve_trait`**（`Machine::solve_trait_ref`）：
//!   头是 trait Sum 时以 `Synth` 求解器按实例表匹配，命中给 (实例项,
//!   实例值)，失败给 `solve trait failed` 文案，非 trait 给 None。
//! - **快版 → 求解器的 `Typ` 桥**（[`val_to_typ`]，参考版 `Val::to_typ`）：
//!   L10 的求解器在 `Typ` 级匹配，故实参经 `Typ` 而非 `Val`——Flex 与带
//!   spine 的链给 None（参考版 `Rigid(_, _)` 非空 spine 即 None），裸 Rigid
//!   → `Var`、`U(n)`/`Sum` → `Val`/`Construct`；字面量/Prim 分支参考版是
//!   `todo!()`——同款不可达即崩。只在求解边界用，非热路径。
//!
//! **要点**（与 L09 共有，孪生版逐项对齐参考版）：
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
//! - **卡住 match 无 pending、force 展开 Flex + Obj**：v_app 对 Match panic
//!   （不可能吸收实参）；参考版 force 只有 Flex + Obj 两臂——meta 解开后
//!   不会重选 match、不展开 Decl。卡住投影 `Val::Obj` 只在 eval 的 Tm::Obj
//!   臂产生：接收者 force 后非 Sum/SumCase 一律卡成 Obj（Flex、卡住 match、
//!   卡住投影、字面量都在其内）。**L09 才是**仅 Rigid 卡、其余 panic。
//! - **模式特化 = 显式替换（SubstV/VSub/frcs）**：参考版走 `check_pm`/
//!   `unify_pm` 累积 σ + `Cxt::subst_cxt` 包裹上下文——特化解**不改写既有
//!   值**，只把 σ 包在外面（[`XCell::VSub`]），`force` 在读点把 σ 推进值
//!   结构（[`frcs`]）；`unify_pm` 的可解臂把解累加进 `SpecSolve.acc`，臂
//!   边界回滚 = Rc 指针赋值。旧 `update_cxt`/`refresh`（改写 env 槽 + 全量
//!   重求值 + 名字表/轨迹双撤销）已整体删除（值过期/槽位错位 bug 族的
//!   载体）。`subst_cxt` 包 env 槽 + `names.by_lvl` 影子索引 + `types` 链，
//!   布局（槽位 = 运行时布局）不变。模式编译器（Compiler）逐句移植参考版
//!   pattern_match.rs：逐臂下钻（walk_pat / check_pm_final）、可达性探测 =
//!   值级 `probe_accessible`（`resolve_name` 取构造子类型 + Π 链实例化 +
//!   索引方程，快版 = metas/unsolved 两表快照换入换出）、checked_ret 备忘，
//!   叶处 `subst_cxt` 后检查分支体。
//! - **unify 无燃料、无 pm 臂、无 (Obj,Obj)/宽松臂**：臂序 = U/Pi/Rigid/
//!   Flex/Flex/Lam/η/Flex 求解/LiteralType 宽松/Sum/SumCase/Match；
//!   flex_flex 单方向尝试无快照回滚；SumCase/SumCase 比 typ+datas（L07+
//!   只比 datas）；Match/Match 分支体在**中性 global 克隆**下重求值
//!   （参考版 avoid_recursive 同款——快版传中性 globals 视图）。
//! - **重定义静默覆盖**（参考版无 redefine 检查）；构造子只以**裸名**登记
//!   （无 `Enum.case` 别名；struct 的 case 名本身是 `Name.mk`）。
//!
//! 与参考版共用 parser / pretty / preprocess，**Ok 输出逐字节一致**（互检
//! 测试 + `tests/l10_fast_parity.rs`）。已知偏差（仅错误消息内容，不影响
//! 判定与 Ok 输出）：快版错误里内嵌的 Debug-Val/Tm 的名字 Span 全零
//! （参考版携带源码偏移），套件比对前按 `start_offset/end_offset/path_id`
//! 归一化。

//!
//! # 分模块导览（2026-09-23 拆分：单文件 → 目录模块）
//!
//! 本文件原为约 9.2k 行单文件；按既有 `// xxx ----` 分节线拆为同目录
//! `bump_spine_iter/` 下的子模块（纯机械搬运：函数体与注释逐行未动，
//! 仅补各子模块 `use` 与跨子系统引用所需的 `pub(super)` 可见性）：
//!
//! - `syntax`：bump 项 Tm/PrCons/LCons + 打包值 V/XCell 与 v_* 构造/访问器；
//! - `subst`：显式替换 SubstV、σ 跨轮回收（VSUB_REGS/vsub_reclaim）、
//!   wrap_sub、mentions_level、SpecSolve；
//! - `env`：复合环境（平坦 defs 区 + binder 链）与 CloCell/PiCell、
//!   DN_TIP/DN_FB 探针计数、packed-word 对齐断言（原文件无独立分节线，
//!   按 "SpecSolve 之后、spine 栈之前" 的内容段归属）；
//! - `spine`：扁平中性栈（Spine/Entry/HK_*）+ metacontext（MetaEntry/
//!   meta_val_of/lit_of）；
//! - `force`：force/frcs/frcs_env/force_deep/force_arg + val_mentions_lvl +
//!   vapp1/vapp_ok/project + 精化展开燃料（PM_FUEL/refuel/burn；project/
//!   vapp/fuel 块原文件位于 metacontext 节尾，按内容归属）；
//! - `eval`：运行时分支选择（eval_aux）+ 双栈迭代 eval（W/eval_iter）；
//! - `quote`：任务栈 quote（QJob/quote_iter + QuoteMemo 记忆化）；
//! - `unify`：工作表 unify（UItem/unify_iter + intersect/flex-flex/
//!   lockstep）+ ReclaimOnClear 清空归还口径与两个阈值常量；
//! - `rename`：solve 族（RenBuf/invert/solve/rename/prune/lams，全迭代）；
//! - `machine`：solve_probe 临时探针 + 稳态 Machine + elaboration（两个
//!   impl Machine 块）+ Elaboration 上下文（Cxt/subst_cxt）+ Debug 复刻
//!   （L10 特有分节，唯一消费者是错误消息构造，故并入）+ builtin 注册
//!   （prime_round/elab_all）+ GLOBAL_BASE 哨兵；
//! - `typeclass`：L10 特有——trait 求解三方法（solve_multi_trait_ref/
//!   solve_trait_ref/solve_trait_ref_inner，以独立 `impl Machine` 块承载）+
//!   neutral_of/TraitState/val_to_typ；
//! - `compiler`：模式匹配编译（Compiler/Warning + covers/is_catch_all/
//!   walk_pat）；
//! - `entry`：export/tm_size/Tycker/run_fast/parse/SourceDecl；
//! - `bench_src`：基准负载生成器。
//!
//! 本层没有而省略的标准子模块：`prim`（L10 无 decl 表，builtin 只有
//! string_concat，其注册随 machine）、`struct_eq`（无该分节；结构比较由
//! unify 承担）。原文件无内嵌 `#[cfg(test)]` 测试，故 entry 无测试段。
//!
//! 对外可见性面在下方以 `pub(crate) use` 原样恢复（外部消费者
//! `L10_typeclass::bump_spine_iter::XXX` 路径零改动）。与 L07 拆分的一处
//! 命名差异：本层参考版自带 `typeclass` 求解器模块，与子模块 `mod
//! typeclass` 同名，入口不能以 `use crate::L10_typeclass::typeclass;`
//! 恢复其路径面——需要求解器类型的子模块（machine/typeclass）直接
//! `use crate::L10_typeclass::typeclass::{…}` 全路径导入。

mod bench_src;
mod compiler;
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
mod typeclass;
mod unify;

// L10_typeclass 的外部项（parser / pretty / mod.rs 项）：以本模块的私有
// use 绑定恢复原 `super::` 路径面——子模块内 `use super::parser::…` 等
// 与拆分前单文件逐字一致。（`typeclass` 求解器模块与子模块同名，见上。）
use crate::L10_typeclass::parser;
use crate::L10_typeclass::pretty;
use crate::L10_typeclass::{
    cover_at, empty_span, fmt_path, preprocess, Error, Ix, MetaVar, PatternDetail,
    PosCover,
};

// 原 pub(crate) 可见面（拆分前单文件的全部 pub(crate) 项，逐一恢复）。
#[allow(unused_imports)]
pub(crate) use bench_src::{church_src, enum_src, match_src, strchain_src, struct_src};
#[allow(unused_imports)]
pub(crate) use compiler::{Compiler, Warning};
#[allow(unused_imports)]
pub(crate) use entry::{parse, run_fast, SourceDecl, Tycker};
#[allow(unused_imports)]
pub(crate) use env::{
    env_collect, env_ext, env_ext_defs, env_len, env_nth, CloCell, Env, EnvCons, PiCell,
};
#[allow(unused_imports)]
pub(crate) use machine::Machine;
#[allow(unused_imports)]
pub(crate) use spine::{MetaEntry, Spine};
#[allow(unused_imports)]
pub(crate) use subst::{SpecSolve, SubstV, SUBSTV_ALIVE};
#[allow(unused_imports)]
pub(crate) use syntax::{
    PrCons, SumDataT, SumDataV, SumParamT, SumParamV, Tm, V, XCell, v_clo, v_clo_of,
    v_lit_ty, v_lvl, v_lvl_of, v_meta, v_meta_of, v_pi, v_pi_of, v_spine, v_spine_of,
    v_tag, v_u, v_u_of, v_xcell, v_xcell_of,
};
#[allow(unused_imports)]
pub(crate) use typeclass::{neutral_of, TraitState, val_to_typ};
