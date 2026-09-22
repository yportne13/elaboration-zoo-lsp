//! L06 核心机（eval / quote / unify / force / rename / solve / prune / check /
//! infer / decl 表 / builtin prim）的极致性能版：L05 冠军配方
//! （`bump_spine_iter`）向 string 层的移植。继承 L05 的全部机制（见其模块
//! 注释与 readme）：
//!
//! 1. bump arena；打包值 [`V`]（低 3 位 tag）；扁平中性 + spine 栈；
//! 2. 复合环境（平坦 def 区域 + 持久 binder 链）；
//! 3. 迭代内核：eval 双栈 / quote 任务栈 / unify 工作表 / rename 任务栈 /
//!    force 循环；
//! 4. quote 记忆化（默认口径）+ unify 判等记忆化（`L06_NO_CONV_MEMO=1`
//!    消融）+ O(1) 名字解析（`L06_NO_NAME_MAP=1` 消融）；
//! 5. `Tycker` 稳态复用（跨轮 `Bump::reset`）、热路径草稿常驻、
//!    `Pruning` 跳段（none-run）、`RenBuf` 换代缓冲、fresh meta 免 eval
//!    快捷路径。
//!
//! L06 的增量（string 层语义的落地）：
//!
//! - **值编码**：tag 6 = `LiteralType` 立即数（`V(6)`，同 U）；tag 7 = 指向
//!   [`XCell`]（`Lit(&str)` / `Decl(&str)`）的指针。字面量值惰性无害（quote
//!   /rename 直出）；Decl 既是卡住的按名头（求值 miss decl 表时现造单元），
//!   也是 builtin 的触发载体。
//! - **builtin prim 的增量触发**：参考版 `v_app` 的 Decl 臂——每次对 Decl 头
//!   的应用都把**全条**累积实参交给 prim（自然序），`None`（元数不足 / 实参
//!   非字面量）保持卡住。快版把该臂集中到 [`decl_apply`]，所有应用点
//!   （eval 的 Apply/ChainWrap/AppPrunOne、force 的解值应用、unify 的 η 臂、
//!   prim 的 `change_mutable`）经 [`is_declheaded`] O(1) 判定后走它。判定靠
//!   [`Entry::decl`] 标志（push 时随函数侧传播），不 walks 链。
//! - **decl 表 + 可变全局**：`Machine.decls`（名 → 值/类型/prim）与
//!   `Machine.mutable_map`（RefCell，名 → 值）随轮清空并重新注册（参考版
//!   每次调用新建 `Infer` 的稳态等价）。
//! - **unify 的 L06 臂**：`(6,6)`、`(6,7Decl)`、`(7Decl,6)` 成立；
//!   同名 `(7Decl,7Decl)` 逐实参；`(7Lit,7Lit)` **恒败**（参考版无该臂，
//!   连相同字面量也不可合一——位相等捷径对 tag 7 关闭以复刻之，内联环的
//!   实参位相等跳过与 intersect 回落同理加 tag 7 守卫）。Span 的
//!   PartialEq 只比 data（parser_lib.rs 自定义实现），同名 Decl 头按名
//!   比较、命名 λ 按名匹配 Π——与参考版一致。
//!
//! 与参考版（`super`，分文件：elaboration/cxt/unification/syntax/pretty）
//! 共用 parser / pretty / preprocess，**Ok 输出逐字节一致**（互检测试 +
//! `tests/l06_blackbox.rs`）。已知偏差（仅错误消息内容，不影响判定与
//! Ok 输出）：参考版错误文案 `{:?}` 直接 Debug 打印引读项 / 名字 Span，
//! 携带源码偏移；快版项不存偏移（导出 span 全零），同构但数字不同。判定
//! （Err/Ok）与 println 输出不受影响。

//!
//! # 分模块导览（2026-09-23 拆分：单文件 → 目录模块）
//!
//! 本文件原为约 4.6k 行单文件；按既有 `// xxx ----` 分节线拆为同目录
//! `bump_spine_iter/` 下的子模块（纯机械搬运：函数体与注释逐行未动，
//! 仅补各子模块 `use` 与跨子系统引用所需的 `pub(super)` 可见性）：
//!
//! - `syntax`：bump 项 Tm/PrCons/LCons + 打包值 V/XCell 与 v_* 构造/
//!   访问器（"syntax（bump 内的项表示）" + "values（打包值）" 两节）；
//! - `env`：复合环境（平坦 defs 区 + binder 链）与 CloCell/PiCell（原
//!   "values" 节内的复合环境段）；
//! - `spine`：扁平中性栈（Spine/Entry/is_declheaded/decl_name）与
//!   metacontext（MetaEntry/meta_val_of）；
//! - `prim`：builtin prim（decl 表 + 可变全局 + 按名触发；`decl_apply`/
//!   `vapp1` 增量触发）；
//! - `eval`：force（迭代）+ 双栈迭代 eval（W/eval_iter）——force 节不足
//!   200 行，按拆分纪律并入内容最近的 eval；
//! - `quote`：任务栈 quote（QJob/quote_iter + QuoteMemo 记忆化）；
//! - `unify`：工作表 unify（UItem/unify_iter + intersect/flex-flex +
//!   判等记忆化）；
//! - `rename`：solve 族（RenBuf/invert/solve_with_pren/solve + rename/
//!   prune/lams，全迭代）；
//! - `machine`：稳态 Machine + elaboration（Cxt/decl 表/builtin 注册/
//!   prime_round/elab_all）；
//! - `entry`：export/tm_size/Tycker/run_fast + NO_NAME_MAP + 内嵌测试；
//! - `bench_src`：基准负载生成器（l06bench 引用）。
//!
//! 对外可见性面在下方以 `pub(crate) use` 原样恢复（外部消费者
//! `L06_string::bump_spine_iter::XXX` 路径零改动）。

mod bench_src;
mod entry;
mod env;
mod eval;
mod machine;
mod prim;
mod quote;
mod rename;
mod spine;
mod syntax;
mod unify;

// L06_string 的外部项（parser / pretty / mod.rs 项）：以本模块的私有
// use 绑定恢复原 `super::` 路径面——子模块内 `use super::parser::…` 等
// 与拆分前单文件逐字一致。
use crate::L06_string::parser;
use crate::L06_string::pretty;
use crate::L06_string::{empty_span, preprocess, Error, Ix, MetaVar};

// 内嵌测试在 entry 子模块里经 `super::super::` 取 mod.rs 项——拆分后其
// `super::super` 即本模块，下列私有绑定让原测试路径逐字可用。
#[cfg(test)]
use crate::L06_string::{DEMO_SRC, FILE_IO_LOCK, run};

// 原 pub(crate) 可见面（拆分前单文件的全部 pub(crate) 项，逐一恢复）。
#[allow(unused_imports)]
pub(crate) use bench_src::{church_src, globals_src, implicit_src, prune_src, solve_src, strchain_src};
#[allow(unused_imports)]
pub(crate) use entry::{run_fast, Tycker};
#[allow(unused_imports)]
pub(crate) use env::{env_ext, env_ext_defs, env_nth, CloCell, Env, EnvCons, PiCell};
#[allow(unused_imports)]
pub(crate) use machine::Machine;
#[allow(unused_imports)]
pub(crate) use prim::{DeclEntryF, MutableMap, Prim};
#[allow(unused_imports)]
pub(crate) use spine::{MetaEntry, Spine};
#[allow(unused_imports)]
pub(crate) use syntax::{PrCons, Tm, V, XCell, v_clo, v_clo_of, v_lit_ty, v_lvl, v_lvl_of, v_meta, v_meta_of, v_pi, v_pi_of, v_spine, v_spine_of, v_tag, v_u, v_xcell, v_xcell_of};
