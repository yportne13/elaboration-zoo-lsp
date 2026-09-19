//! L07 核心机（eval / quote / unify / force / rename / solve / prune / check /
//! infer / decl 表 / builtin prim / enum 注册 / 模式编译）的极致性能版：
//! L06 冠军配方（`bump_spine_iter`）向 sum-type 层的移植。继承 L05/L06 的
//! 全部机制（见 L06 版模块注释与 readme）：
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
//! L07 的增量（sum-type 层语义的落地；参考版 = `super` 的分文件实现，语义
//! 以其为准。**机制对齐（2026-09）**：参考版的显式替换精化已移植——
//! `SubstV`（持久化单链）/ `XCell::VSub` / `frcs` + [`SpecSolve`] 穿参，
//! 与参考版 `Subst`/`Val::VSub`/`frcs` + `SpecSolve` 逐点同构（见
//! `docs/l07-dpm-refactor-design.md`）。两条参考版侧的关键语义选择在此
//! 复刻：design doc §4 的槽位纪律（spine/Sum/SumCase 槽只包裹不物化、
//! Lam/Pi 闭包 env 逐槽包裹、Match scrutinee 单独推进）与 `frcs` 对
//! "已解 rigid + 非空 spine"的解析应用选择（tests.rs 的
//! `test_fn_typed_index_slot_applied_after_refine` 钉死）；fuel 燃烧点
//! 对齐（VSub 推开入口不烧，frcs 的 lookup 命中烧 1，耗尽返回裸 rigid））：
//!
//! - **值编码**：tag 7 的 [`XCell`] 从 Lit/Decl 扩到 `Prim`（卡住内建应用
//!   头）、`Obj`（卡住投影）、`Sum` / `SumCase`（和类型与构造子值）、
//!   `Match`（卡住 match：scrutinee + 捕获 env + 编译分支 + pending 实参）、
//!   `VSub`（显式替换下的值，σ = std `Rc<SubstV>`）。注意 σ 的"单次模式
//!   编译"只对**可读性**成立：bump `reset()` 不跑 Drop，arena 内 `XCell::VSub`
//!   持有的 Rc 克隆跨轮不递减（无 UB——reset 后无人再读、链无环——但长
//!   生命周期 Machine 下是无上界慢泄漏，LSP 式接入前需评估量级或加回收）。
//!   带实参的 Prim/Obj/Decl 与 Rigid/Flex 一样表示为 spine 栈上的链（头 =
//!   `Entry.hk` 记录的头种类，push 时随函数侧传播，O(1) 判定）。
//! - **builtin 触发点后移**：L06 在应用时触发（`decl_apply`）；L07 参考版
//!   的 builtin 值是 `λ 参数链 → ((Tm::Prim(名) p1) p2 …)` App 链，
//!   `Tm::Prim` 是**零元卡住头**（实参经 App 显式应用，不读现场 env——
//!   quote → eval 往返在任意 env 下 spine 保真），归约统一在 force 的
//!   `prim_reduce`（L06 cxt.rs 函数体的逐句移植）。
//! - **模式特化 = 显式替换**：解入 `SpecSolve.acc`（模式编译器的 σ 链，
//!   臂边界 Rc 指针赋值回滚）；"解前构建、解后消费"的值在读点用
//!   `wrap_sub` 包裹，force 的 `frcs` 读点惰性推开；上下文经
//!   `subst_cxt` 包裹（env 槽 + 类型表，布局不动）。[`force_arg`] 逐层
//!   解包 VSub、不推开精化、不重选 Match（invert / prune_vflex 专用——
//!   槽位引用是作用域事实）。
//! - **unify_fuel**：force 的每次展开与 unify 的每次递归各消耗 1；耗尽即把
//!   值当未解处理 / Err。充值点与参考版一致（unify_catch / 编译入口 / nf）；
//!   frcs 的 lookup 命中烧 1（对齐旧 pm_defs 时代 force(Rigid) 查表的
//!   燃烧剖面，`(fuel exhausted)` 尾注语义依赖它）。
//! - **卡住 match 的三处特殊处理**：unify 的 Match/Match（struct_eq 快路径
//!   + 逐分支在 fresh rigid 槽下用简化 decl 表重求值再比）、quote/rename
//!   的分支体重求值（`simpl_decl` 防递归重展开）、v_app 的 pending 累积
//!   （分支选中后在值层逐个应用——项层 splice 会把实参自由变量引到错误
//!   上下文，参考版 `v_app` 的 Match 臂同款）。
//! - **decl 表写时复制**：`Rc<FxHashMap>` + `Rc::make_mut` 镜像参考版
//!   `Cxt::decl_insert`——递归 def 的"占位 → 覆盖"只对本定义可见；源码
//!   名字解析 = 局部 name_map 之后查 decl 表（参考版 `Raw::Var` 同序）。
//!
//! 与参考版共用 parser / pretty / preprocess，**Ok 输出逐字节一致**（互检
//! 测试 + `tests/l07_fast_parity.rs`）。已知偏差（仅错误消息内容，不影响
//! 判定与 Ok 输出）：快版导出项的名字 Span 全零，参考版错误文案里的
//! Debug-Span 携带源码偏移，同构但数字不同。unify 的位相等捷径对 tag 7
//! 与 **Obj 头的链**关闭（参考版无 `(Lit, Lit)` / `(Obj, Obj)` 臂——同
//! 单元也不可合一，捷径放行会误 Accept）。

//!
//! # 分模块导览（2026-09-19 拆分：单文件 → 目录模块）
//!
//! 本文件原为约 8.5k 行单文件；按既有 `// xxx ----` 分节线拆为同目录
//! `bump_spine_iter/` 下的子模块（纯机械搬运：函数体与注释逐行未动，
//! 仅补各子模块 `use` 与跨子系统引用所需的 `pub(super)` 可见性）：
//!
//! - `syntax`：bump 项 Tm/PrCons/LCons + 打包值 V/XCell/PendingCons 与
//!   v_* 构造/访问器；
//! - `subst`：显式替换 SubstV、σ 跨轮回收（VSUB_REGS/vsub_reclaim）、
//!   wrap_sub、mentions_level、InlineStack、SpecSolve、simpl_decl 旁路缓存；
//! - `env`：复合环境（平坦 defs 区 + binder 链）与 CloCell/PiCell；
//! - `spine`：扁平中性栈（Spine/Entry/HK_*）与 metacontext（MetaEntry）；
//! - `prim`：decl 表基础设施（DeclEntryF/MutableMap/Fuel）与 builtin
//!   归约 prim_reduce；
//! - `force`：force/frcs/force_arg + vapp1/vapp_ok/project +
//!   val_mentions_lvl；
//! - `eval`：双栈迭代 eval（W/eval_iter）+ 运行时分支选择（eval_aux）；
//! - `quote`：任务栈 quote（QJob/quote_iter + QuoteMemo 记忆化）；
//! - `unify`：工作表 unify（UItem/unify_iter + intersect/flex-flex/
//!   lockstep）；
//! - `rename`：solve 族（RenBuf/invert/solve/rename/prune/lams，全迭代）；
//! - `struct_eq`：结构相等快路径（SEqTask/seq_run + budget）；
//! - `machine`：稳态 Machine + elaboration（Cxt/decl 表/builtin 注册/
//!   prime_round/elab_all）；
//! - `compiler`：模式匹配编译（特化合一/覆盖检查/嵌套记账）；
//! - `entry`：export/Tycker/run_fast/parse + 内嵌 deep_value_tests；
//! - `bench_src`：基准负载生成器（bins 引用）。
//!
//! 对外可见性面在下方以 `pub(crate) use` 原样恢复（外部消费者
//! `L07_sum_type::bump_spine_iter::XXX` 路径零改动）。

mod bench_src;
mod compiler;
mod entry;
mod env;
mod eval;
mod force;
mod machine;
mod prim;
mod quote;
mod rename;
mod spine;
mod struct_eq;
mod subst;
mod syntax;
mod unify;

// L07_sum_type 的外部项（parser / pretty / mod.rs 项）：以本模块的私有
// use 绑定恢复原 `super::` 路径面——子模块内 `use super::parser::…` 等
// 与拆分前单文件逐字一致。
use crate::L07_sum_type::parser;
use crate::L07_sum_type::pretty;
use crate::L07_sum_type::{
    cover_at, empty_span, fmt_path, preprocess, Error, Ix, MetaVar, PatternDetail, PosCover,
};

// 原 pub(crate) 可见面（拆分前单文件的全部 pub(crate) 项，逐一恢复）。
#[allow(unused_imports)]
pub(crate) use bench_src::{church_src, enum_src, globals_src, match_src, strchain_src};
#[allow(unused_imports)]
pub(crate) use entry::{parse, run_fast, SourceDecl, Tycker};
#[allow(unused_imports)]
pub(crate) use env::{env_ext, env_ext_defs, env_len, env_nth, CloCell, Env, EnvCons, PiCell};
#[allow(unused_imports)]
pub(crate) use force::val_mentions_lvl;
#[allow(unused_imports)]
pub(crate) use machine::Machine;
#[allow(unused_imports)]
pub(crate) use prim::{DeclEntryF, Fuel, MutableMap};
#[allow(unused_imports)]
pub(crate) use spine::{MetaEntry, Spine};
#[allow(unused_imports)]
pub(crate) use subst::{SpecSolve, SubstV, SUBSTV_ALIVE};
#[allow(unused_imports)]
pub(crate) use syntax::{
    PendingCons, PrCons, SumDataT, SumDataV, SumParamT, SumParamV, Tm, V, XCell, v_clo,
    v_clo_of, v_lit_ty, v_lvl, v_lvl_of, v_meta, v_meta_of, v_pi, v_pi_of, v_spine,
    v_spine_of, v_tag, v_u, v_xcell, v_xcell_of,
};
