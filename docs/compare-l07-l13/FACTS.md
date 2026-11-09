# L07–L13 对比分析 · 公共事实底稿（Lead 核对，分析员可引用，修正请报 Lead）

> 生成时点：工作树 HEAD `8443586e`（2026-11-08，master，工作区另有未跟踪的 docs/wip 等）。
> 统计口径：`src/` 下 `.rs` 行数（PowerShell 行计数，不含 `*.bak`）；测试数为**静态** grep
> `^\s*#\[test\]`，**未执行**。见 CONVENTIONS.md 的引用规则。

## 1. 环境

- cargo 1.98.1 / rustc 1.98.1（`rust-toolchain.toml` 固定 1.98.1）。
- **F 盘剩余空间 < 1 GB ⇒ 禁止 cargo build/check/test**（会写数 GB）。可只读运行
  `target/release/*.exe`（2026-11-08 构建，全部 bench/cli 二进制在位）。
- 测试要求大栈（参考版 64–256 MB 线程；libtest 每测试一线程），串行/多线程差异敏感。

## 2. 各层代码规模（物理行 = `[IO.File]::ReadAllLines().Count`；含空行/注释；参考版生产不含测试文件；孪生 = `bump_spine_iter*`）

| 层 | 参考版生产 | 参考版测试 | 孪生 | 合计 | 形态 |
|---|---:|---:|---:|---:|---|
| L07_sum_type | 7215 | 2354 | 9051 | 18620 | 参考版分文件 + 孪生子目录（16 个 .rs：根聚合 + 15 子模块） |
| L08_product_type | 6117 | 2018 | 8733 | 16868 | 同 L07 结构 |
| L09_mltt | 5598 | 0 | 7749 | 13347 | 参考版分文件；孪生 15 文件（2026-09-23 从单文件拆出） |
| L10_typeclass | 7115 | 0 | 9541 | 16656 | 参考版分文件；孪生拆子模块（machine.rs 最大） |
| L11_macro | 10344 | 0 | 9018 | 19362 | 参考版分文件；孪生拆子模块（machine.rs ≈2.9k 最大） |
| L12_canonical | 10442 | 0 | 9016 | 19458 | 参考版分文件；孪生拆子模块（machine.rs ≈3.1k 最大） |
| L13_namespace | 24946 | 15270 | 19111 | 59327 | 参考版 26 文件 + 17 个 `*_tests/probe`；孪生 15 文件（含 compact/observe） |

合计 **163,638 物理行**：参考版生产 ≈71.8k + 参考版测试 ≈19.6k + 孪生 ≈72.2k。
参考版生产 + 孪生（不含测试）≈ **144.0k**，即"两套完整实现"的真实体量；七层含测试 ≈16.4 万行。

**口径警告**：不同工具统计差 10–20%（`Measure-Object -Line` 少算空行；部分报告用非空行口径得到
~126.8k / 143.8k 等数字）。**引用时请统一用本表物理行口径**，或明确写"非空行口径"。
`src/` 全域另有 L01–L06、LSP、doc/format/sim/bins 等；本表只统计 L07–L13。
另注：L07 README 与 L13 README 的行号锚点整体漂移（如 L07 `mod.rs` 实测 2203 行、L13 `mod.rs`
实测 8510 行；README 记 1832/7628），分析员报告已尽量改用实测行号。

## 3. 测试静态盘点（未执行；`#[test]` 出现次数）

| 层 | 参考侧 src | 孪生侧 src | 集成套件（`tests/`） |
|---|---:|---:|---|
| L07 | 69 | 1 | l07_blackbox 49 / v2 53 / v3 47 / l07_fast_parity 27 |
| L08 | 60 | 0 | l08_blackbox 58 / v2 53 / l08_fast_parity 35 |
| L09 | 10 | 0 | l09_fast_parity 29 |
| L10 | 25 | 0 | l10_fast_parity 21 |
| L11 | 33 | 0 | l11_fast_parity 19 |
| L12 | 35 | 0 | l12_fast_parity 15 |
| L13 | 587 | 25 | l13_fast_parity 15（多源循环）+ tests/ 下 11 套 LSP/namespace/hover/completion 等 |

注：集成 parity 套件通过 `#[path]` 把本层 `mod.rs` 编入，因此会把该层部分 lib 测试再跑一遍
（README 里的"parity 数"通常 = 套件自有 + 带入，如 L10 42 = 21+21）。这是**重复执行**而非重复覆盖。

## 4. 双引擎与 parity 闸门

**生产接线（lib.rs / 文档已核）**：LSP 默认引擎 = **L13 孪生**（`Engine::lsp_default()`，
`TYPORT_LSP_ENGINE=reference` 是逃生口）；带 `import`/`package` 的文件自动回落参考版；
`typort check` 是参考版专属管线（不认引擎开关）。稳态 HDL 负载 kick 359 ms → 102 ms（~3.5×），
常驻孪生 prelude 内存 ~429 MB 稳态 / ~730 MB 峰值 vs 参考版 ~200 MB（~2.2× 内存换 CPU）。
即：**产品路径 = L13 双引擎混合**，不是"参考版或孪生版任选"。

- 每层两份实现：参考版（Rc/Box 树 + 递归，可读性优先）与 `bump_spine_iter*` 孪生版
  （bump arena + 打包值 tag + 迭代内核 + 记忆化 + 稳态复用，性能优先）。
- 闸门：`cargo test --test lXX_fast_parity`，判据 = **Ok 输出逐字节一致 / Err 判定一致**；
  错误正文归一化：span 偏移（`@ N,M`、`start_offset/end_offset/path_id`）全层剥；
  meta 编号 `?N` 仅 L11–L13 剥（L10 认为分配序列一致）。
- 已知 parity 偏差/缺口（据各层 README，需分析员核实）：
  L11/L12/L13 有"既有分叉家族"剔除用例（GADT 索引宇宙 × trait、struct 接收者实例、
  单臂构造子匹配、Prim 求值时机）；L12 enum/traitchain 孪生既有失败；L13 单行 enum
  两版同错（假阴性）；L13 观察面表形态残余。
- **只在参考版存在**：L12 `canonical.rs` 的 `iddfs`（Err 重试路径，run/run_fast 不经）；
  L13 `PreludePool`、`FUNC_PROF`、retry 闭包、Tm/Val 迭代 Drop（孪生 bump 免疫）。
- **只在孪生版存在**：L13 常驻 prelude 检查点/`prime_resident`/`compact` 压实；各层
  `L0x_NO_CONV_MEMO` 等消融开关。

## 5. 最新性能矩阵（docs/bench-matrix-2026-09-20.md，隔离进程、rounds=3、每格 min；match k=11）

| 层 | match basic (ms) | fast_ss (ms) | 孪生/参考 | 备注 |
|---|---:|---:|---:|---|
| L07 | 0.145 | 0.049 | 0.34× | 逐臂+σ，参考版已是第二实现 |
| L08 | 0.144 | 0.052 | 0.36× | 同 L07 机制 |
| L09 | 0.557 | 0.055 | 0.10× | 参考版引擎地板慢（非 match 负载也慢 L10 2.5–4.5×） |
| L10 | 0.171 | 0.053 | 0.31× | 参考版有 trait 开销 |
| L11 | 0.202 | 0.044 | 0.47× | fast_run 0.094 |
| L12 | 1.431 | 0.195 | 0.22× | 参考版含无条件 `eprintln!` 回归（0.43 ms）与嵌套覆盖探测；该行 HEAD 已不存在（见 §7） |
| L13 | 0.215 | 0.172 | 0.80× | 生产层，孪生领先最小；twin 0.673→0.172 |

其它关键量级（同矩阵）：L07 strchain 122.7 ms / L08 123.6 / L09 2669 / L10 917 / L11 708 /
L12 645 / L13 4537（basic）；孪生普遍 3–20 ms，故大值负载倍率 L07≈23×、L08≈38×、L09≈867×、
L10≈282×、L11≈125×、L12≈83×、L13≈533×。**跨层比"倍率"会误导**（参考版地板不同），
要比就比绝对时间或同层倍率。
**时效性**：矩阵采于 2026-09-20，之后有 L07/L08 加固（11-08）与 L13 σ 迁移实验（未落地），
数字代表 09-20 状态；引用时须注明。

**L09 数字已过期（重要，artist-l09 发现）**：HEAD（master）含 2026-09-20 提交
`866f23e5`「perf(L09/L10): 参考版全局名搬 Infer + Locals/close_ty Rc 化（strchain 42x/16x、
universe 664x/238x）」。`git merge-base --is-ancestor 866f23e5 HEAD` = 真（在 HEAD 内）；
而 09-20 矩阵工作区 `e36b76b` 早于该提交。⇒ 本表 L09 basic（strchain 2668.9 / struct 4269.2 /
universe 3191.7 ms）与 875×/1189×/1856× 倍率是**修复前**数字；HEAD 上 L09 参考版非 match
地板大概率已显著缩小。引用 L09 性能时必须注明"09-20 矩阵 / 修复前"。L10 同提交受益
（"16x/238x" 侧）但矩阵数字同属修复前。

## 6. 近期时间线（git log，关键节点）

- 2026-09-18/19：L09–L13 匹配编译器决策树 → 逐臂（`09b9ee8`/`4e97743`/`6ae12a6`/`45330e6`/`448775c`），
  参考版+孪生同步；嵌套覆盖两段式恢复（`f774703`/`aafa5ed`/`c53cbf3`/`521e57f`）。
- 2026-09：显式替换重构（σ）落地 L07–L12（`docs/explicit-subst-refactor-status.md`）；
  **L13 未落地**（五轮尝试后回退，补丁与评审存档 `docs/wip/`）。
- 2026-10/11：L07 加固轮 P1–P11（`008f42ed` 合并 20 commits + `6bd1926e` 修复轮 + `8443586e` 终报）；
  L08 迁移 P1/P2/P9 等部分项；L09–L13 未回灌。
- 2026-11-08：Lean oracle 形式化（`ca53c1da`，lean/OracleMain.lean + tests/lean_oracle_parity.rs）。

## 7. 已知文档/代码不一致（引用时小心）

1. **L13 README §7** 称 lib `#[test]` 341；静态 grep 得 612（参考侧 587 + 孪生 25），
   `legacy_tests.rs` 138。README 自身也写"例数口径历史 372→389→412——未核实"。以静态数
   为参考、执行数未知。
2. **L09–L12 README 的 lib 测试数**（L09 5 / L10 21 / L11 29 / L12 17）是**参考侧过滤口径**，
   与静态全量（10/25/33/35，含解析器等）不同；引用时写清口径。
3. **bench-matrix-2026-09-20 的 L12 `eprintln!` 回归**（`pattern_match.rs:273`）：HEAD 该行
   已不存在（grep `DBG nc` 0 命中；273 行现为 `eval_aux` 签名），引用该回归须注明"09-20 时点"。
4. **L07/L08 README 的测试计数**多处写"以 Lead 实跑为准"；本报告只用静态数与套件规模。
5. 各层 README 的"已知偏差/限制"是作者诚实清单，不等于已修复；分析员应区分
   "时代缺口（刻意不修）"与"当前缺陷（待修）"。
6. `src/L11_macro/**/*.bak` 与 `src/L12_canonical/**/*.bak` 存在整文件副本（未跟踪、被
   .gitignore 忽略，git 不感知）；HEAD 代码与 .bak 的差异需按文件对比，勿当作实现的一部分。
7. L13 参考版有 FB 常见调试残留/探针（`debug_test.rs`、`struct_refine_probe.rs`、`FUNC_PROF`），
   属于生产层自带的诊断设施，不是死代码；分析时注意区分。
8. **L09 README §2 已过期**：现为 `src_names`（局部）+ `Infer.global_names`（顶层名，
   append-only，不随 Cxt 克隆）+ `global: HashMap<Lvl, VTy>` 三件套，不再是"名字解析只走
   src_names"的单表（`cxt.rs:10-23` 的 2026-09-20 注释与 `mod.rs:446-456`）。
9. **工作区 `.bak` 残渣**：`src/L11_macro/bump_spine_iter*/*.bak` 13 个 + `src/L12_canonical/...`
   4 个 = 17 个文件、约 541 KB，多数与 HEAD 不同（仅 L11 `unify.rs.bak` 与 HEAD 相同）；
   被 `.gitignore` 忽略、git 不感知。工程卫生问题，不影响构建（不被 `mod` 引用）。
10. **仓库有多个 git worktree**（`elaboration-zoo-lsp-review-l13`、`-web`、`target/bbwt`、
    `ezl-perf-analysis`、`wt-l13-solvecache`）挂着其它分支；本次分析范围 = 主工作树
    master `8443586e`，引用历史提交时注意分支归属（866f23e5 已确认在 master 内）。

## 8. 必须预先掌握的术语

- **σ / 显式替换**：`Subst`（持久化单链）+ `Val::VSub` 包裹 + `force` 的 `frcs` 读点推进 +
  `SpecSolve{acc}` 穿参；替代旧"改写 env 槽 + refresh"。
- **`update_cxt`/`refresh`**：旧精化载体，解直接改写 cxt env 槽并全量重求值重锚定；
  L13 现行路线（L09–L12 移植前同款）。
- **逐臂下钻 vs 决策树矩阵**：前者按用户书写顺序逐臂 walk+特化方程，后者先建矩阵再填叶；
  2026-09-18 后全仓统一为逐臂。
- **decl 表 / `Infer.global` 哨兵**：L06–L08、L11–L13 用名字键 decl 表（L07 起 `Val::Decl`）；
  L09/L10 用 `Tm::Var(Ix(global_idx + 1919810))` 大下标哨兵 + `Infer.global: HashMap<Lvl, VTy>`。
- **bump arena 孪生**：`bumpalo` 分配 + `V = tag|payload` 打包字 + 显式工作栈迭代内核；
  不是"同一算法的优化"，而是第二套值表示/求值器/合一器（约 8k 行/层）。
