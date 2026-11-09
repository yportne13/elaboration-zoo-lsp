# D6 分支 / WIP / 补丁考古：已测结果、可收割项、死胡同

> 分析员：branch-archaeologist｜**只读 git/diff/docs，未跑 cargo/bench，未改任何分支/工作树**。
> 时点：master `8443586e`（2026-11-08 工作区）+ 6 个 worktree + 3 个 stash + `docs/wip/` 未跟踪存档。
> 证据标记：`[码]`=源码/仓库对象核实、`[历史实测]`=仓库既有实验数字（注明文档与日期）、`[文档]`=文档陈述、
> `[推断]`=判断。分支数字用 `git rev-list --count master..branch`（ahead）口径。

## 1. 清点总表

### 1.1 规模与分布（本地 90 个分支；`git branch` 实点）

| 类别 | 约数 | 代表 | 生存状态 |
|---|---:|---|---|
| `task/*`（L13/HDL/LSP 特性，6–8 月） | ~46 | `task/hdl-improve`、`task/l13-backport2/3`、`task/l13-bugs2`、`task2/module-macro` | 绝大多数已并入 master（58/90 ahead=0）；未并的多为被后续 HDL/L13 重写覆盖 |
| `backup*`（快照） | ~11 | `backup-pre-coauthor-cleanup`（ahead=95，历史分叉快照）、`backup/master-pre-remote-merge-20261008`（ahead=0） | 只作回滚点；**不收割** |
| `perf/` `analysis/` | ~11 | `perf/l13-twin-sigma`、`perf/solve-trait-ref-phase2-20260924`、`analysis/l04-l07-perf`、`analysis/l13-perf{,-current,-r13}` | 3 个未并入（见 §2），其余已并入/被取代 |
| `fix/*` | ~8 | `fix/l07-match-unify`（ahead=0，已并入）、`fix/L02-L05-unify-soundness`（已并入） | 基本吸收 |
| `wip/` `probe-*` `debug-*` `refactor/*` | ~9 | `refactor/revert-unify-pm`（ahead=13）、`perf/diag-module`、`perf/cache-constr-heads` | 7–8 月结构实验，被 9 月「逐臂 + σ」重写取代 |
| 其余（`feat/` `test/` `web-demo` 等） | ~6 | `web-demo`（ahead=3）、`feat/l07-*`（ahead=0） | 见 §2 |

**关键统计**：90 分支中 **58 个已完全并入 master**（ahead=0）；32 个未并入，但 only **6 个 ahead>5**
（95/53/13/8/8/7）。**"乱七八糟"的主体不是未合并代码，而是 6 个 worktree + 未跟踪文档 + 大量已并入的
一次性特性分支的视觉噪音**——这是本报告的总判断。

### 1.1b 全部 32 个未并入分支的逐条处置（`git rev-list --count master..branch`+末提交日期）

| ahead | 日期 | 分支 | 处置 | 依据 |
|---:|---|---|---|---|
| 95 | 09-10 | `backup-pre-coauthor-cleanup` | 不收割 | 旧历史线快照（非 master 祖先），仅回滚点 |
| 53 | 09-09 | `task/sync-stale-fn-quote-l08-l13` | 不收割 | C-11：锚点消失 |
| 13 | 07-09 | `refactor/revert-unify-pm` | 不收割 | C-9：被逐臂重写取代 |
| 8 | 08-08 | `task/l13-backport2` | 不收割 | C-10：被 9 月重写覆盖 |
| 8 | 08-14 | `task/l13-backport3` | 不收割 | C-10 |
| 7 | 06-27 | `debug-pm-struct-multi-field-gadt` | 不收割 | 单 bug 调试分支；GADT 多字段 struct 问题已由后续重写/测试覆盖 [推断] |
| 5 | 08-08 | `task/l13-bugs2` | 不收割 | C-10 |
| 4 | 09-12 | `web-demo` | 低（产品另议） | C-8：`web/` 不在 master，编译核心无关 |
| 4 | 08-15 | `analysis/l13-perf-current` | 不收割 | review-6 文档被 `docs/l13-perf-review-4.md` 与 22/23 轮取代 |
| 3 | 09-21 | `perf/l13-twin-sigma` | **中（设计证据高）** | C-2 |
| 3 | 09-08 | `analysis/l04-l07-perf` | **高** | C-1 |
| 3 | 07-02 | `fix/patcon-implicit-refinement` | 不收割 | `Pattern::Con` 隐式绑定；逐臂重写已覆盖该域 [推断] |
| 2 | 08-16 | `analysis/l13-perf-r13` | 不收割 | review-13 文档同 C-10 的旧轮次 |
| 2 | 07-22 | `perf/cache-constr-heads` | 不收割 | C-9：profile 设施已被 FUNC_PROF/sampler 取代 |
| 2 | 08-08 | `task/hdl-improve` | 不收割 | `regInit` 在 master prelude 99 处命中 ⇒ 已被后续 HDL 轮吸收 |
| 2 | 06-15 | `close-ty-trait-metas` | 不收割 | trait meta 关闭实验；L13 trait 求解已多轮重写 [推断] |
| 2 | 07-13 | `fix/l13-eval-call-args` | 不收割 | switch 基础设施后由正式 switch 实现取代 [推断] |
| 1 | 08-10 | `task/l13-perf3` | 不收割 | review-3 文档被 review-4 取代 |
| 1 | 08-06 | `task/tree-data-flat` | 不收割 | HDL class-body 扁平化 plan C2，后续 HDL 已重写该路线 [推断] |
| 1 | 08-04 | `perf/diag-module` | 不收割 | C-9 |
| 1 | 07-18 | `fix/gadt-pm-refinement` | 不收割 | GADT pm 精化早期修复，逐臂重写覆盖 [推断] |
| 1 | 07-21 | `fix/def-body-error-recovery` | 不收割 | parser 恢复早期补丁；resilient parser 已换代 |
| 1 | 07-01 | `probe-experiments` | 不收割 | 探针备份 |
| 1 | 06-17 | `wip/switch-ctx-changes` | 不收割 | switch 机制已正式实现 |
| 1 | 06/07 月 | 8 个 `backup*`（`prove-term-pure-test` 4、`current-wip`、`other-changes`、`wip-changes`、`working-changes-20260731`、`2026-07-07-wip-namespace-changes`、`2026-06-25-approach3-check-pm`、`backup-solve-multi-trait-fix`） | 不收割 | 快照/单修复备份；内容已被后续历史吸收或不可定位 |

### 1.2 Worktree（6 个，`git worktree list`）

| 路径 | 分支/HEAD | 状态 | 处置建议 |
|---|---|---|---|
| `…/elaboration-zoo-lsp` | master `8443586e` | 干净，仅未跟踪 docs（`optimal-design/`、`compare-l07-l13/`、`l13-perf-replace-*`、`.commandcode/`） | 主树；未跟踪文档需归档（见 §5） |
| `…/elaboration-zoo-lsp-review-l13` | `review/l13-shared-perfect` `86195126` | **已并入 master**（ahead=0，产出 `docs/L13-code-review.md` 68KB 在 master）、工作树干净 | 可直接 `worktree remove`（仅剩清理价值） |
| `…/elaboration-zoo-lsp-web` | `web-demo` `5784ba64` | ahead=3，干净；`web/` 不在 master | 见 C-8；不并入主线 |
| `…/elaboration-zoo-lsp/target/bbwt` | detached `52ba09ba` | **路径已不存在**（`Test-Path` False），仅注册残留 | `git worktree prune` 候选 |
| `F:/projects/hermes/ezl-perf-analysis` | `analysis/l04-l07-perf` `eeae05f5` | ahead=3；未跟踪 `.zcode/`（探针脚本 + `l07_fix.patch` 等 40+ 文件） | **最高价值未收割项**（C-1）；先归档 `.zcode/` 再收敛 |
| `F:/projects/hermes/wt-l13-solvecache` | `perf/solve-trait-ref-phase2-20260924` `58c35646` | **已并入 master**（ahead=0）；未跟踪 `ab/` 只有两个编译产物（`l13bench.exe` 3.8MB、`l06l13mem.exe` 12MB） | 纯产物目录，可 remove |

### 1.3 Stash（3 个）

| stash | 日期 | 内容 | 判断 |
|---|---|---|---|
| `@{0}` | 2026-09-27 | HDL R1 评审修复 WIP | 已被 master 后续 HDL 提交覆盖 [推断]，不建议恢复 |
| `@{1}` | 2026-09-16 | L13 第三轮移植诊断 WIP（对应 `docs/wip/` 存档） | 与 patch 系列重复；不收割 |
| `@{2}` | 2026-09-10 | "fast build/test channel"（aliases + test-fast profile + docs） | 可能有小工具价值（加速测试通道），**唯一值得看一眼的 stash**；恢复成本低、风险低 |

### 1.4 未跟踪文档（不进 git，最易丢失的资产）

`docs/wip/README.md`（318 行）+ 5 个 L13 σ 补丁（144–244 KB/个，round1→round5 累积超集）+ `docs/wip/l13-perf-round3/`
（4 个未落地补丁 + README）+ `docs/wip/l13-perf-replace-2026-09-27/{A-perf,B-replace}.md`（41/56 KB）+
`docs/l13-perf-replace-2026-09-27.md`（260 行）。**这些是最新的高价值实验记录，但都未提交**——工作区一旦清理即消失；
建议 Lead 在 D6 阶段先把它们 `git add` 或 tar 归档（见 §5 教训 8）。

## 2. 重点候选卡片

### C-1 `analysis/l04-l07-perf` —— **L04–L07 prune O(n³) 根治 + Machine 常驻**｜收割价值 **高**

- **改了什么**：3 commits（`c5c59ce6` 分析、`05ff9c7e` 修复、`eeae05f5` L08–L10 分析）。修复 A：`fresh_meta`
  闭型快路径——`bind_prefix_of_telescope` 判定「头 bind 段 + 全 define」时只闭 bind 段为 Π、define 槽由
  `cxt.env` 快照供给，免全 close 的 Θ(层深²) Let 链重建；修复 B：eval/unify/quote 工作栈 Machine 常驻
  （lifetime 洗白，进核即 clear）。改动落 `src/L04…L07/bump_spine_iter.rs` + Cargo.toml + 探针。
- **实测数字** `[历史实测]`（`git show 05ff9c7e` commit message + 分支内 `PERF_ANALYSIS_L04-L07.md` §0/§5）：
  prune k=9 **7.9 s → 36–76 ms（>100×）**，k=10 从跑不完 → ~0.3 s，k=12 可达；Machine 常驻 L04 chain k=13 **−12%**；
  当时回归：lib 647/647 + 8 个黑盒/parity 套件全绿。
- **是否在 master**：**否**（ahead=3；master 无对应 commit）。且现役矩阵仍复现病灶：`docs/bench-matrix-2026-09-20.md:193/202`
  L05 prune k=9 fast_ss **8.090 ms**、L06 **7.369 ms**（L05 参考版超时，同文档 :261/265 登记）。
- **为何未合并**：基于 `5cae365`（2026-09-08）的 worktree 实验分支，之后主线 587 commits 且架构变动剧烈：
  `git diff --stat 5cae365 master` 对 L05 孪生仅 **603 行变动**（仍单文件，补丁最易重落），L06/L07 孪生分别
  **4,247 / 6,765 行变动**（已拆分重写、净删 11,116 行）⇒ 直接 cherry-pick 不可行，需按概念重写两三个 hunk。
  **不是失败，是没回头收**。
- **收割方式**：优先在 L05（结构最稳定）复现修复 A 并跑 parity；L06/L07 按拆分后子模块重落。前置：先确认 prune
  仍是目标负载（若判定为病态负载，则只收修复 B）。**收益/风险比最高的一项**。

### C-2 `perf/l13-twin-sigma` —— **L13 孪生移植显式替换 σ**｜收割价值 **中（设计证据价值 高）**

- **改了什么**：3 commits（`8c53542f` σ 移植、`a2989b81` 读路径清理、`a722b773` run7 复核）；仅孪生两文件
  `bump_spine_iter.rs` +1074/−296、`bump_spine_iter/compact.rs` +12/−2；新增 `XCell::VSub`/`SubstV`/`SpecSolve`/
  `wrap_sub`/`frcs`/`subst_cxt`/`force_arg`/`PM_FUEL`，删除 `update_cxt`/`update_cxt_impl`/`refresh` **143 行**；
  参考版零改动。
- **实测数字** `[历史实测]`（分支内 `docs/perf-l13-twin-sigma-port-2026-09-20.md` §4/§5）：
  match k=11 **−2.5%**、prelude-core **−5.5%**（7.60 vs 8.06）、examples-hdl **−5.5%**、prelude-hdl **+9~11%（回归）**；
  门禁 `l13_fast_parity` **417 passed/0 failed**、全量 lib 766 全绿；run6/run7 全量矩阵：23 格改善、仅 prelude-hdl 1.099×。
  回归被证明**无法用 σ 链路微优化收回**（插桩显示 σ 全链 ~93 ms 与 +120 ms 不匹配；剩余是 force_arg 进入 invert 308K 次/轮
  + 热函数新臂 + 布局漂移，§6）。
- **是否在 master**：**否**。master 孪生仍是旧载体：`src/L13_namespace/bump_spine_iter/machine.rs:2766/2780/2862`
  （`update_cxt`/`update_cxt_impl`/`refresh` 在位）。且分支产出的"σ 必选件"三条坑（`force_arg` 必选、
  `vapp1` 需 VSub 臂、kick 界 σ 归还 UAF）在 master 结构里没有对应物。
- **为何未合并**：① prelude-hdl +9~11% 回归未解；② 分支 269 commits 落后，且目标文件已被拆成 16 子模块
  （`c199d210`）⇒ 重落成本 ≈ 重做一次。**建议：不直接合并，作为 D5/D7 的关键证据**——它证明"σ 可移植到 L13 孪生且
  真实负载更快，但 HDL 大 prelude 有反向交换"，是"统一精化载体 vs 分层最优"决策的唯一实测材料。

### C-3 `l13-perf-replace-2026-09-27`（未跟踪文档）—— **"性能版完全取代参考版"路线图**｜收割价值 **高（路线）**

- **内容**：`docs/l13-perf-replace-2026-09-27.md`（260 行，含 §1 引擎归属/回落全集、§5 R0–R6 路线与 22–44 人天估算）+
  `A-perf.md`（性能机会清单 #1–#7 + "已经证伪不要再做"清单）+ `B-replace.md`（取代阻塞项 B2-1…B2-10 + 删除条件 DoD）。
- **可引用的实测** `[历史实测]`（同目录 §1.5/§5，A/B 稿）：examples 30 文件中 **29/30 由 twin 接管**（唯一 `18-utils`
  因 `untrusted-error` 回落）；kick 成本 **11,281 ms → 0.57×**（总比 1.64×，adder_proof 修复后 1.78×）；native 常驻
  twin ~429 MB 稳态/730 MB 峰 vs 参考版 ~200 MB；wasm 大证明 ~1.2 GB vs 0.33 GB（2 GiB 硬顶，超限静默 trap）。
- **是否在 master**：文档未提交；**代码未落地**（R0–R6 均未开始；`twin_can_own` 闸仍在 `src/lib.rs:1398-1402`）。
- **判断**：这不是"分支代码"，而是**当前最高质量的下一步路线**：R0（可复跑的引擎对拍报告）→ R1（项目会话/视野闸）
  → R2（18-utils 分叉根因）。A-perf §"最值得先做的 3-5 条"已给出排序。**建议 Lead 把 R0 定为 D4/EXP-8 的下一实验**。

### C-4 `docs/wip/` L13 σ 五轮补丁系列｜收割价值 **低（方案教训 中）**

- **内容**：round5 累积补丁 244 KB（round1 144 KB → round5 超集），核心是①LSP 表总闸（prelude 期不收集
  hover/completion，`typort check` **21.1 s → 9.3 s** `[历史实测]` wip README §4.1）；②第 5 轮 GADT 覆盖修复
  （`ArmEntry.refine: Rc<Subst>` 逐列携带 σ，探测前 `wrap_sub`，3 个 legacy GADT 测试转绿 §5）；③诊断探针
  DIAG8–11/DEEPPATH 等。
- **是否在 master**：**否**（master 保持 `update_cxt`；docs/wip README :24-26 明言"master 有意不含它"）。
- **未合并原因（已定案）**：σ 在 L13 规模下有 4 个既有 parity 失败 + meta 解链（最深 12,287 层，默认测试栈必爆，
  wip README §4.2）+ prelude-hdl 性能回归；**L13 已决定留在 update_cxt**。
- **真正可收割的是"方案"不是代码**：①GADT per-arm refine 的根因（σ 机制下 `force(Rigid(l))` 不再查全局解表，
  探测必须用当前 σ 包裹"解前构建的值"）是 σ 路线的必修课；②孪生镜像的实施要点（heads 加第五元 head_val、6 个
  Arm 构造点、探测点 wrap_sub，README :186-207）若未来重启 σ 可直接照做；③"勿再重复"清单（force_chain/quote
  链式 VSub 解包会破坏"顶层非 VSub"不变式）。**补丁本体不重放。**

### C-5 `docs/wip/l13-perf-round3/` 四补丁｜收割价值 **不收割（证伪存档）**

- `l13-matchidx-backlog2.patch`（eval.rs +164/force.rs +4）：per-node 懒建分派索引，A/B **−0.2~3.4%**（默认 ≤1.4%，
  未达 <3% 门槛）；证伪 wide_enum 主成本在编译期覆盖检查（已由 `CoversIndex` 落地 −89.8%）。
- `p4a-item1-app-clone-lazy.patch`：prelude-core fast **+3.1%** / fast_ss **−1.7%**（符号不一致）⇒ 回退。
- `s8-scratch-reuse.patch`（294 行）：size-32 草稿栈复用，**0% / −0.02%** ⇒ 证伪；教训是"l06l13mem 官方计数下
  size-32 首块的归因不复现"。
- `s7-task2-compact-casesmap.patch`：**零命中**（cases 切片天然单引用）⇒ 作防退化护栏备查。
- 判断：四补丁全部有实现+门禁+负面实测，**保留文档即可**；重做等于重复劳动。

### C-6 `perf/solve-trait-ref-phase2-20260924`（+ `wt-l13-solvecache`）｜**已并入 master，不收割**

- 分支 ahead=0（全并入）。近期实质内容都在 master：`f9f080f1` 撤 HDL 自检闸（twin 接管面 8/30 → **29/30**）、
  `6c3b8464` `typort check` 显式取参考引擎（不再白付 prime ~1.8–2.0 s）、`06362c71` examples 逐文件 kick
  **0.93× → 0.57×** `[历史实测]`、`cf740c82` 门禁补 `twin_engine_tests`、`1324f31f` lvl2ix 下溢加固。
- worktree `wt-l13-solvecache` 只剩两个未跟踪 exe，**无源码/补丁**；"solvecache"实验结论已体现在
  master 的 `solve_trait_ref` 现状（如 `d5c59d32` 双 force、`748bc237` META_JOURNAL）。

### C-7 `review/l13-shared-perfect`｜**已并入，工作树可清**

- ahead=0；产出 `docs/L13-code-review.md`（68 KB）已在 master。worktree 干净，只等 `git worktree remove`。

### C-8 `web-demo`（3 commits，+10,732/−15）｜收割价值 **低**

- 内容：`web/api/{l01…l13}` 每章独立 wasm cdylib 适配器 + 静态演示页 + smoke 工具（`web/build.sh`、`serve.mjs`、
  `www/main.js` 627 行）。与编译核心设计无关，且**不在 master**（`web/` 目录不存在）。
- 判断：若用户要"演示"，也应在 master 现状（twin/参考双引擎 + 现有 wasm 宿主路线，见 C-3 B1.e）上重做，而不是合 9 月分支。
- 注：`web-demo` 与 `l13-perf-replace` B1.e 的 wasm 内存结论（2 GiB 硬顶）**互相印证**，后者更权威。

### C-9 旧结构实验三连（`refactor/revert-unify-pm` 13、`perf/cache-constr-heads` 2、`perf/diag-module` 1）｜**不收割**

- `refactor/revert-unify-pm`（2026-07-09）："hole-based 构造子可达性化简"，13 commits 未并；该函数域已被
  2026-09-18 逐臂重写（`45330e6` 等五层）整体替换，**代码锚点消失**。
- `perf/cache-constr-heads`（07-22）：`profiling.rs` + 4 文件插桩，是 L13 观察面/profile 的前身；master 已有
  `FUNC_PROF`/sampler/`debug_test.rs` 等更强设施。
- `perf/diag-module`（08-04）：module flat redesign 诊断 + statement-sinking（含 `docs/module-flat-redesign-notes.md`），
  该文档不在 master；module 机制后来以别的实现进入 master（`module_tests` 系列），**方案已被取代**。

### C-10 8 月 L13 backport 三连（`task/l13-backport2` 8、`-backport3` 8、`task/l13-bugs2` 5）｜收割价值 **低/不收割**

- backport2/3 把 L13 修复回灌 L07–L12（`pattern_match.rs`/`pretty.rs`/`parser` 等），分支文档
  `docs/l13-backport-candidates.md`、`docs/l13-backport-round3.md` **均不在 master**；9 月五层 match 编译器整体重写后，
  这些逐行回灌已无锚点。
- `task/l13-bugs2` 的修复 commit（`d00eab9`/`32d8d22`/`423b703`/`94211fe`）**不是 master 祖先**（`git merge-base --is-ancestor`
  exit=1），其中 lvl2ix 加固已以 `1324f31f` 在另一条线并入（见 C-6）；其余项在 L13 后续多轮重写中大概率已无关。
  **逐项验证成本 > 收益**。

### C-11 `task/sync-stale-fn-quote-l08-l13`（ahead=53）｜**不收割**

- 内容：L05 孪生 quote 链陈旧函数修复回灌 L08–L13（53 commits、`Cargo.toml` + 19 个文件 + `docs/l13-twin-bench-2026-09.md`）。
  分支 576 commits 落后；L06/L07 孪生已被拆分重写（master `L06_string/bump_spine_iter.rs` 净 −4247 行），
  quote 链问题域后被 9 月缓存轮（QUOTE_MEMO/DECLB 缓存/declb_of）覆盖。**大分支 ≠ 高价值**的典型。

### C-12 已并入但值得知道的分支（不收割，避免误当候选）

`fix/l07-match-unify`（ahead=0，occurs 链传递已并入 master）、`hdl-perf-probe`（ahead=0，`force` Sum 叶子优化已并入）、
`fix/L02-L05-unify-soundness`、`refactor/l05-bump-spine-iter`、`feat/l07-{clean,dpm-refactor,polish}`、
`task/l13-perf-review`、`backup/master-pre-remote-merge-20261008`（交付快照，已并入）。
`task/hdl-improve`（ahead=2）：`regInit`/`RegInit` 在 master prelude 有 **99 处**命中 ⇒ 已被后续 HDL 轮吸收。
`analysis/l13-perf`（ahead=0，空 diff）；`analysis/l13-perf-current`（4，docs review-6 未并入）、`analysis/l13-perf-r13`
（2，docs review-13 未并入）、`task/l13-perf3`（1，review-3 未并入）：**均被 master 的 `docs/l13-perf-review-4.md`
（59 KB）与 22/23 轮取代**；最多当历史数字，不重放。

### C-13 清理项（无代码价值）

`target/bbwt` 失效 worktree 注册（路径不存在）；3 个 stash（`@{2}` 可选）；`src/L12_canonical/bump_spine_iter/*.bak`
3 个忽略副本（3,642 行，与现行文件同尺寸异哈希）；各分支 worktree 里的 `.zcode/` 探针脚本与 `ab/*.exe` 产物；
`.commandcode/` 未跟踪目录。

## 3. Top 5 值得复现 / 合并（按 ROI 排序）

| # | 项 | 预期收益（证据） | 前置/代价 | 建议动作 |
|---:|---|---|---|---|
| 1 | **L04–L07 prune 修复 A + Machine 常驻**（C-1） | prune k=9 **>100×**（7.9 s→36–76 ms）、chain −12%；当前矩阵仍 8.09 s `[历史实测 09-20:193]` | 按当前拆分重写 2–3 个 hunk；跑 L04–L07 parity + 黑盒 | EXP-8 首要：先在 L05 单文件复现修复 A |
| 2 | **L13 取代路线 R0/R1**（C-3） | 引擎归属对拍可量化；视野闸 L1 0.5–1 人天即可把 cross-file 回落类别消掉一部分；double-pay 消除 | 文档未提交→先归档；R0 报告是后续一切前提 | Lead 把 R0 立为 D4 实验；B-replace DoD 作验收清单 |
| 3 | **σ 统一精化载体的 L13 孪生证据**（C-2） | prelude-core/examples-hdl **−5.5%**、417 parity 全绿、删 update_cxt 143 行；prelude-hdl **+9–11%** 反向证据 | 269 commits 漂移 + 16 子模块拆分 ⇒ 重做而非合分支 | 进 D5/D7 选型：作为"σ 可扩展性"唯一实测，附回归条件 |
| 4 | **L10 close 路径残留二次项**（perf-debt-2026-09-12 §"实现轮遗留清单" #1'） | traitchain ~6×/翻倍（k=9 12.2 s→93 ms 已落地后剩余项；L10 traitchain 22.2 s 是矩阵最差格） | 需 def 项值预求值/平坦区手法（同 P2）；风险中 | 立为 D5 技术候选 + 需 perf-experimenter 复测 |
| 5 | **A-perf 零语义风险小项 #2/#3**（压实路径两处白付、`FORCE_PRIM_MEMO` 键零分配化）+ `stash@{2}` 快速测试通道 | 压实 150–190 ms/kick 中的白付份额；键构造零分配 | 需 A/B 同窗口复测；门槛 <3% 不落地纪律 | 交给 perf 轮次排期，不进架构决策 |

## 4. Top 5 不要再碰（负结果/死胡同）

| # | 项 | 为什么 |
|---:|---|---|
| 1 | **`docs/wip/` L13 σ 五轮补丁重放** | L13 已定案留在 update_cxt（master 有意不含）；补丁基于旧单文件架构，且已知 4 项 parity 失败 + prelude-hdl 回归 + meta 解链栈溢出。只提取"GADT per-arm refine 方案 + 勿重复清单"。 |
| 2 | **`docs/wip/l13-perf-round3/` 四补丁** | 全部有实现+门禁+负实测：−0.2~3.4%（未达门槛）、符号不一致（+3.1/−1.7）、0%/−0.02%、零命中。重做=重复劳动。 |
| 3 | **`refactor/revert-unify-pm` + `perf/cache-constr-heads` + `perf/diag-module`（7–8 月结构实验族）** | 全部围绕"决策树/旧 profile 设施"的局部化简，被 2026-09-18 逐臂重写与 L13 diag 设施取代；基线漂移 900–1000 commits，重放风险高、收益为负。 |
| 4 | **`task/sync-stale-fn-quote-l08-l13`（53 commits）** | L06/L07 孪生已拆分重构、quote 缓存机制已换代；分支锚点消失，收益已被后续轮覆盖。"大分支=大价值"的错觉样本。 |
| 5 | **`task/l13-backport2/3` + `task/l13-bugs2`（8 月 backport 三连）** | 回灌内容被 9 月五层 match 重写取代；文档未并入 master；bug2 的修复 commit 不在 master 祖先但对应缺陷已由后续重写/另一条线处理（如 `1324f31f`）。逐项验证成本高于收益。 |

## 5. 实验方法教训（给 D4/D5 与后续轮次，按证据编号）

1. **口径先于数字**：`basic`/`fast_ss`/`fast`/`fast_run` 语义不同；跨窗口/跨构建不可直接比——同一模块布局漂移可达
   ±8–15%（`perf-l13-twin-sigma-port` §5 prelude-hdl / strchain 摆动），只认**同窗口交错 A/B 的比值**。
2. **符号不一致 = 噪声，不是收益**：`p4a` 的 +3.1%/−1.7% 直接回退（wip round3 README）。规则：结论需同一符号的
   多口径/多次重复一致。
3. **<3% 门槛应由纪律执行**：四个未落地补丁三个因门槛被拒（round3 README），这是仓库里最有效的"防自欺"机制。
4. **负结果必须写档**：证伪清单（round3 四补丁、A-perf §"已经证伪不要再做"、wip"勿重复"三项）比成功清单更省未来时间。
5. **探针要门控/剥离且记录二进制指纹**：wip 多轮"临时探针已从树中移除"；`l13-perf-replace` §6 明确记录了
   `target/release` 构建于 `804c4dd` 与源码 HEAD 的偏差——引用这类数字必须带指纹。
6. **worktree 隔离有效，但必须回收**：`ezl-perf-analysis` 隔离干净；对比 `target/bbwt` 路径已消失仍挂在
   `worktree list`、`review-l13`/`web` 长期挂载。实验结束即 remove + 归档数字，否则"乱七八糟"的观感一半来自这里。
7. **分支漂移会杀死收割价值**：>200 commits 落后时（twin-sigma 269、backport 800+、sync-quote 576），
   合并成本指数上升；**性能分支的生命期以"master 未重构该文件"为界**。
8. **未跟踪文档等于未保存**：`docs/wip/`（318 行 + 5×200 KB 补丁）与 `l13-perf-replace`（含 A/B 47+56 KB）都不在 git；
   一次清理就全没。建议 `docs/wip/` 与 `docs/optimal-design/experiments/raw/` 纳入版本控制或统一 tar 归档。
9. **先确认"谁在跑"**：LSP 默认 twin、CLI `check` 走参考版、测试默认参考版（`l13-perf-replace` §1.2/§1.3）——
   同一负载不同入口会得出相反的"快/慢"结论；`18-utils` 的 0.74× 正是双付形状。
10. **CPU 与内存必须分记**：FRCS_MEMO 强持结果把长链重建图钉到 **8 GB**（wip README §5）、常驻 twin 429 MB/峰 730 MB
    vs 参考 200 MB、wasm 1.2 GB vs 2 GiB 硬顶 ⇒ "更快"不等于"能用"。
11. **病态负载先判定再修**：L05/L06 prune 参考版在 k≥10 超时使 `l05bench` 不可用（矩阵 :261/265），因此 C-1 的
    ">100×"必须先确认 prune 是否仍是目标负载；否则只收 Machine 常驻（−12%）这一半。
12. **架构拆分是补丁的最大杀手**：L13 孪生单文件 → 16 子模块（`c199d210`）、L06/L07 孪生拆分，使 twin-sigma、
    sync-quote、backport 三组补丁全部失去锚点。**教训：性能/机制实验应在拆分前合入，或实验时就写成可重放的步骤文档。**

## 6. 交接与一句话结论

- 给 D5（技术矩阵）：C-2（σ 在 L13 的三种坑 + prelude-hdl 反向交换）、C-1（fresh_meta 闭型快路径/常驻 Machine）应进
  "技术→实测增益→代价"表；C-5 四补丁进"负结果"表。
- 给 D7（架构）：C-3 的 R0–R6 是现成的迁移路线；C-2 决定"精化载体是否值得统一"；C-4 的 GADT refine 是 σ 路线的必修项。
- 给 Lead：**最该先做的两件**＝① EXP-8 复现 C-1 的 L05 prune 修复（唯一 >100× 且未收割的实测）；
  ② 把未跟踪的 `docs/wip/` 与 `l13-perf-replace` 纳入版本控制（否则本报告引用的证据随时会消失）。
- **一句话结论**：90 分支里真正值得回头收的只有 3 个（L04–L07 prune/Machine、L13 σ 孪生证据、取代参考版路线），
  其余"乱七八糟"是已并入的一次性特性分支、7–8 月死胡同与未归档文档——**分支数量不是复杂度，worktree/未跟踪文档/拆分后的旧补丁才是**。
