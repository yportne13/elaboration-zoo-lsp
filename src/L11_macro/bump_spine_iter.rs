//! L11 核心机（eval / quote / unify / rename / solve / prune / check /
//! infer / check_universe / 模式编译 / trait 求解）的极致性能版：L10
//! 冠军配方（`bump_spine_iter`）向宏层的移植。继承 L05-L10 的全部机制
//! （见 L06/L08/L10 版模块注释与 readme）：bump arena、打包值 [`V`]、
//! 扁平中性 + spine 栈（含链头种类 `Entry.hk` 的 O(1) 头判定）、复合环境、
//! 迭代内核（eval 双栈 / quote 任务栈 / unify 工作表 / rename 任务栈）、
//! quote 记忆化、O(1) 名字解析、`Tycker` 稳态复用。
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
//!   模式编译器（Compiler）逐句移植参考版 pattern_match.rs：逐臂下钻
//!   （walk_pat / check_pm_final）、可达性探测 = 值级
//!   `probe_accessible`（decls 取构造子类型 + Π 链实例化 + 索引方程，
//!   快版 = metas 快照换入换出）、checked_ret 备忘。
//! - **unify 无 pm 臂、无 (Obj,Obj)/宽松臂**：臂序 = U/Pi/Rigid/
//!   Decl/Decl 同名/Flex/Flex/Lam/η/Flex 求解/LiteralType/Prim 带类型/
//!   Sum/SumCase/Match/Obj；flex_flex 单方向尝试无快照回滚；SumCase/
//!   SumCase **先比 Sum 头名字**（2026-09-18 评审修复，跨 enum 重名构造子
//!   直接失败）再比 **typ+datas**（L09 参考版与 L07+ 的 datas-only 不同）；
//!   Match/Match 分支体在 **declb 存根表**下重求值（参考版同款）。
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

//!
//! # 分模块导览（2026-09-23 拆分：单文件 → 目录模块）
//!
//! 本文件原为约 8.7k 行单文件；按既有 `// xxx ----` 分节线拆为同目录
//! `bump_spine_iter/` 下的子模块（纯机械搬运：函数体与注释逐行未动，
//! 仅补各子模块 `use` 与跨子系统引用所需的 `pub(super)` 可见性）：
//!
//! - `syntax`：bump 项 Tm/PrCons/LCons + 打包值 V/XCell 与 v_* 构造/访问器
//!   + 内建标识 PrimId（原文件首）+ 值层槽 SumParamV/SumDataV（原文件
//!   位于 "显式替换 σ" 节内，按内容归属）；
//! - `subst`：显式替换 SubstV、σ 跨轮回收（VSUB_REGS/vsub_reclaim）、
//!   wrap_sub、mentions_level、SpecSolve；
//! - `env`：decl 表基础设施（DeclEntry/Decls，原文件无独立分节线）+
//!   复合环境（平坦 defs 区 + binder 链）与 CloCell/PiCell、packed-word
//!   对齐断言；
//! - `spine`：扁平中性栈（Spine/Entry/HK_*）+ metacontext 头段
//!   （MetaEntry/meta_val_of/lit_of）；
//! - `force`：force/frcs/frcs_env/force_deep/force_arg + val_mentions_lvl
//!   （原文件位于 σ 节内，按内容归属）+ 精化展开燃料（PM_FUEL/refuel/
//!   burn）+ metacontext 节尾的 project/vapp1/vapp_ok 块（按内容归属）；
//! - `eval`：运行时分支选择（eval_aux/eval_aux_case）+ 双栈迭代 eval
//!   （W/eval_iter：decl 表查名、带类型 Prim 五路分派）；
//! - `quote`：任务栈 quote（QJob/quote_iter + QuoteMemo 记忆化）；
//! - `unify`：工作表 unify（UItem/unify_iter + intersect/flex-flex/
//!   lockstep）+ ReclaimOnClear 清空归还口径与两个阈值常量 + declb
//!   存根表缓存（DECLB_CACHE/declb_of）；
//! - `rename`：solve 族（RenBuf/invert/solve/rename/prune/lams，全迭代）；
//! - `machine`：稳态 Machine + elaboration（Cxt/subst_cxt/模式特化/trait
//!   方法包装/infer_decl）+ Debug 复刻（唯一消费者是错误消息构造，故并入）
//!   + builtin 注册（prime_round/elab_all）+ no_metas/err_unsolved_meta；
//! - `typeclass`：trait 求解两方法（solve_multi_trait_ref/solve_trait_ref，
//!   以独立 `impl Machine` 块承载）+ TraitState/val_to_typ；
//! - `compiler`：模式匹配编译（Compiler/Warning/probe_accessible/嵌套记账）
//!   + 文件尾的 sum_case_names/covers/is_catch_all/walk_pat 段；
//! - `entry`：export/tm_size/Tycker/run_fast/parse/SourceDecl；
//! - `bench_src`：基准负载生成器。
//!
//! 本层没有而省略的标准子模块：`prim`（无独立 decl 归约分节：DeclEntry/
//! Decls 并入 env，PrimId 并入 syntax，builtin 归约在 eval 的 Prim 臂）、
//! `struct_eq`（无该分节）、`macro`（L11 章的 macro_rules 脱糖在 parser/
//! preprocess 层，核心机内无宏展开分节）。原文件无内嵌 `#[cfg(test)]`
//! 测试，故 entry 无测试段。
//!
//! 对外可见性面在下方以 `pub(crate) use` 原样恢复（外部消费者
//! `L11_macro::bump_spine_iter::XXX` 路径零改动）。与 L07 拆分的一处
//! 命名差异同 L10：本层参考版自带 `typeclass` 求解器模块，与子模块
//! `mod typeclass` 同名，入口不能以 `use crate::L11_macro::typeclass;`
//! 恢复其路径面——需要求解器类型的子模块（machine/typeclass）直接
//! `use crate::L11_macro::typeclass::{…}` 全路径导入。

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

// L11_macro 的外部项（parser / pretty / mod.rs 项）：以本模块的私有
// use 绑定恢复原 `super::` 路径面——子模块内 `use super::parser::…` 等
// 与拆分前单文件逐字一致。（`typeclass` 求解器模块与子模块同名，见上。）
use crate::L11_macro::parser;
use crate::L11_macro::pretty;
use crate::L11_macro::{
    cover_at, empty_span, fmt_path, preprocess, Error, Ix, MetaVar, PatternDetail, PosCover,
    PrimFunc, Val,
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
    env_collect, env_ext, env_ext_defs, env_len, env_nth, CloCell, DeclEntry, Decls, Env,
    EnvCons, PiCell,
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
pub(crate) use typeclass::{TraitState, val_to_typ};
