//! L12 核心机（eval / quote / unify / rename / solve / prune / check /
//! infer / check_universe / 模式编译 / trait 求解）的极致性能版：L11
//! 冠军配方（`bump_spine_iter`）向 canonical 层的移植。继承 L05-L11 的全部
//! 机制（见 L06/L08/L10/L11 版模块注释与 readme）：bump arena、打包值 [`V`]、
//! 扁平中性 + spine 栈（含链头种类 `Entry.hk` 的 O(1) 头判定）、复合环境、
//! 迭代内核（eval 双栈 / quote 任务栈 / unify 工作表 / rename 任务栈）、
//! quote 记忆化、O(1) 名字解析、`Tycker` 稳态复用。
//!
//! **L12 自己的增量与差异**（参考版 = `super` 的分文件实现，语义以其为
//! 准）——L12 参考版 = L11 的 decl 表引擎 + canonical 搜索（`canonical.rs`
//! 的 `iddfs`/`search`）+ 参考版全面 SmolStr 化；世界口径逐条沿用 L11 版
//! 注释（下方"要点"重述），此处先记 L12 的增量。
//!
//! - **未解 meta 保留上下文快照**：`MetaEntry::Unsolved` 从 L11 的一元扩为
//!   参考版三元同构（闭类型, [`MetaSnap`], 原始类型）。[`MetaSnap`] =
//!   { 创建时层级, 名字 telescope, decls }，`Rc<MetaSnap<'static>>` 存放
//!   （跨轮 reset 前句柄已消亡，两步 transmute 入 `'a`），服务
//!   `no_metas` 错误路径的 pretty/lvl/decls 重建与 `meta_contrains` 挂账。
//! - **快版 → 求解器的 `Val` 桥**（[`v_to_ref_val`]，取代 L11 的
//!   `val_to_typ`）：L12 的 `typeclass.rs` 移除了 `Typ` 桥接、求解器改为
//!   `Val` 级匹配，故实参逐项解码成 `Arc<CVal>`（支持 Rigid 裸/U/
//!   LiteralType/LiteralIntro/Sum/SumCase/Flex 立即数；Pi/Match/Decl 链等
//!   形态降级为永不匹配的标记值——参考版 `val_match` 对非构造子 goal 一律
//!   false，观察面相同）。只在求解边界用，非热路径。
//! - **`solve_trait_ref` 对齐参考版 L12**：实参 force 后直通 `Val`，**任一
//!   仍是 Flex 即 Ok(None)** 交回合一；命中给 (实例项, 实例值)，失败给
//!   `{}[{:?}]` + 类实例表逐行的文案。方法名命中 trait 时以
//!   `Flex(MetaVar(u32::MAX))` 通配参数试探，能解出实例才包装。
//! - **canonical/`iddfs` 不移植**：参考版只在 Err 路径的重试闭包
//!   （`elaboration.rs` 的 `ret = move || infer.iddfs(...)`）里调用，
//!   不影响判定与 Ok 输出，快版无搜索机。
//!
//! **要点**（与 L11 共有，孪生版逐项对齐参考版）：
//!
//! - **全局 = decl 表（名字键）+ `Tm::Decl`/`Val::Decl`**：没有
//!   `Infer.global` 表与 1919810 哨兵。顶层 def/enum/构造子/内建全部登记
//!   在 `Cxt.decl: HashMap<SmolStr, (Span, Tm, Val, Ty, VTy)>`（快版 =
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
//!   模式编译器（Compiler）逐句移植参考版 pattern_match.rs：逐臂下钻
//!   （walk_pat / check_pm_final）、可达性探测 = 值级
//!   `probe_accessible`（decls 取构造子类型 + Π 链实例化 + 索引方程，
//!   快版 = metas 快照换入换出）、checked_ret 备忘。
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
//! 测试 + `tests/l12_fast_parity.rs`）。已知偏差（仅错误消息内容，不影响
//! 判定与 Ok 输出）：快版错误里内嵌的 Debug-Val/Tm 的名字 Span 全零
//! （参考版携带源码偏移），套件比对前按 `start_offset/end_offset/path_id`
//! 归一化。

//!
//! # 分模块导览（2026-09-23 拆分：单文件 → 目录模块）
//!
//! 本文件原为约 8.7k 行单文件；按既有 `// xxx ----` 分节线拆为同目录
//! `bump_spine_iter/` 下的子模块（纯机械搬运：函数体与注释逐行未动，
//! 仅补各子模块 `use` 与跨子系统引用所需的 `pub(super)` 可见性）：
//!
//! - `syntax`：bump 项 Tm/PrCons/LCons + 文件头部零散定义 `PrimId`
//!   （builtin 函数标识，按内容归属）+ 打包值 V/XCell/SumParamV/SumDataV
//!   与 v_* 构造/访问器；
//! - `subst`：显式替换 SubstV、σ 跨轮回收（VSUB_REGS/vsub_reclaim）、
//!   wrap_sub、mentions_level、SpecSolve（原文件位于 σ 回收节尾、env 段
//!   之前，按内容归属）；
//! - `env`：复合环境（平坦 defs 区 + binder 链）与 CloCell/PiCell、
//!   packed-word 对齐断言（原文件无独立分节线，位于 DeclEntry 之后、
//!   spine 栈之前，按内容归属）；
//! - `spine`：扁平中性栈（Spine/Entry/HK_*）+ metacontext（MetaEntry/
//!   MetaSnap/meta_unsolved/meta_val_of）+ lit_of；
//! - `force`：force（Flex + Obj 两臂）+ frcs/frcs_env/force_deep/force_arg
//!   + val_mentions_lvl（原文件位于 σ 回收节内，按内容归属）+ vapp1/
//!   vapp_ok/project + 精化展开燃料（PM_FUEL/refuel/burn；原文件位于
//!   metacontext 节尾，按内容归属）；
//! - `eval`：运行时分支选择（eval_aux/eval_aux_case）+ 双栈迭代 eval
//!   （W/eval_iter，含 5 个 builtin 的 PrimId 分派）；
//! - `quote`：任务栈 quote（QJob/quote_iter + QuoteMemo 记忆化）；
//! - `unify`：工作表 unify（UItem/unify_iter + intersect/flex-flex/
//!   lockstep）+ declb 存根表缓存（DECLB_CACHE/declb_of）+ ReclaimOnClear
//!   清空归还口径与两个阈值常量（原文件位于本节头部，unify/machine 双侧
//!   消费）；
//! - `rename`：solve 族（RenBuf/invert/solve/rename/prune/lams，全迭代）；
//! - `machine`：稳态 Machine + elaboration（check/infer/insert 族，两个
//!   impl Machine 块）+ Elaboration 上下文（Cxt/TCons/subst_cxt）+ decl
//!   表条目（DeclEntry/Decls，原文件位于 σ 回收节尾，按内容归属）+ trait
//!   合成状态（TraitState/v_to_ref_val，本层无独立 typeclass 分节，按
//!   内容并入）+ Debug 复刻 + builtin 注册（prime_round/elab_all/
//!   no_metas/err_unsolved_meta）；
//! - `compiler`：模式匹配编译（Compiler/Warning + covers/is_catch_all/
//!   walk_pat——后三者原文件位于 bench 生成器节尾，按内容归属）；
//! - `entry`：export/tm_size/Tycker/run_fast/parse/SourceDecl（Tycker 与
//!   入口四件套原文件位于 builtin 注册节内，按内容归属）；
//! - `bench_src`：基准负载生成器（church/natadd/gadt/strchain/match/enum/
//!   struct 源码串）。
//!
//! 本层没有而省略的标准子模块：`prim`（decl 表基础设施 DeclEntry/Decls
//! 并入 machine）、`struct_eq`（无该分节）、`canonical`（canonical/iddfs
//! 搜索快版不移植，参考版 `canonical.rs` 因此不与任何 `mod` 撞名）、
//! `typeclass`（trait 求解三方法随 Machine 的 impl 块留在 machine，参考
//! 版 `typeclass.rs` 同理不撞名）。原文件无内嵌 `#[cfg(test)]` 测试，故
//! entry 无测试段。
//!
//! 对外可见性面在下方以 `pub(crate) use` 原样恢复（外部消费者
//! `L12_canonical::bump_spine_iter::XXX` 路径零改动）。入口另以私有 use
//! 绑定恢复子模块所需的 `super::Lvl`/`super::PrimFunc`/`super::Val` 名字
//! 面（原单文件以 `super::` 全路径内联引用、未在文件头 use 的三项）。

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
mod unify;

// L12_canonical 的外部项（parser / pretty / mod.rs 项）：以本模块的私有
// use 绑定恢复原 `super::` 路径面——子模块内 `use super::parser::…` 等
// 与拆分前单文件逐字一致。
use crate::L12_canonical::parser;
use crate::L12_canonical::pretty;
use crate::L12_canonical::MetaVar as CMetaVar;
use crate::L12_canonical::{
    cover_at, empty_span, fmt_path, preprocess, Error, Ix, Lvl, MetaVar, PatternDetail,
    PosCover, PrimFunc, Val,
};

// 原 pub(crate) 可见面（拆分前单文件的全部 pub(crate) 项，逐一恢复）。
#[allow(unused_imports)]
pub(crate) use bench_src::{
    church_src, enum_src, gadt_src, match_src, natadd_src, strchain_src, struct_src,
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
pub(crate) use machine::{DeclEntry, Decls, Machine, TraitState, v_to_ref_val};
#[allow(unused_imports)]
pub(crate) use spine::{meta_unsolved, MetaEntry, MetaSnap, Spine};
#[allow(unused_imports)]
pub(crate) use subst::{SpecSolve, SubstV, SUBSTV_ALIVE};
#[allow(unused_imports)]
pub(crate) use syntax::{
    PrCons, SumDataT, SumDataV, SumParamT, SumParamV, Tm, V, XCell, v_clo, v_clo_of,
    v_lit_ty, v_lvl, v_lvl_of, v_meta, v_meta_of, v_pi, v_pi_of, v_spine, v_spine_of,
    v_tag, v_u, v_u_of, v_xcell, v_xcell_of,
};
