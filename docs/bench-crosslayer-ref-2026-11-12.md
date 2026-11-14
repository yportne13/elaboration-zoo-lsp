# L07–L13 参考版跨层性能复测（2026-11-12）

> 目标：只测**参考版**（不看孪生版），在完全相同的用例上复测 L07–L13 的性能。
> 这是 `docs/bench-crosslayer-ref-2026-11-11.md` 之后的第一次复测：期间 L08/L09 的
> 参考版回灌了 L07 的加固（`docs/compare-l07-l13/BACKPORT-2026-11-11.md`），
> L07/L10/L11/L12/L13 的参考版源码未动。
>
> - HEAD `ae8ccb6c`（分支 `port/l07-hardening-l08-l09`），工作树干净（仅 `.deltawork/` 未跟踪）
> - bench 二进制全部当前源码产物：l07/l08/l10–l13/realbench 于 21:22–21:24 重建，
>   l09bench 01:06 已由同一源码构建（源码最后改动 01:03，故未重编）
> - 测量窗口 2026-11-12 21:28–21:42；同机串行、进程隔离、每配置 min-of-rounds、
>   **6 遍完整遍历**（奇偶遍反向层序）后跨遍取 min
> - 环境：Windows 10 / AMD Ryzen 5 5600（6C/12T）/ 32 GB / rustc 1.98.1 / release / mimalloc
> - 原始日志：`target/bench_real/ref_2026-11-12/`（403 个文件，不入库）；机器汇总：同目录 `summary.md`
> - 复现：`tools/run_crosslayer_ref.ps1` + `tools/crosslayer_ref_report.py`（§7）
>
> **2026-11-13 更新**：本文 L09 列是**载体切换前**的历史值。L09 参考版随后完成
> 「顶层声明移出 Cxt」的载体切换：L09 common 112.7→96.5 ms、L09 自有真实语料
> 1777.9→11.4 ms、Eq 证明阶梯 1691.9→3.6 ms（详见
> `docs/l09-carrier-switch-2026-11-12.md`）；L07/L08/L10/L13 列不受影响（控制项 ±2%）。

## 0. 结论

1. **跨层形态与 11-11 一致，没有翻转**：L10 最快（**41.7 ms**，0.62× L07）→ L12 46.1（0.69×）
   → L11 52.5（0.78×）→ L13 62.7（0.94×，与 L07 基本持平）→ **L07 67.1** → L08 68.7（1.02×）
   → **L09 113.5 ms（1.69× L07，最慢）**。
2. **层间差距仍集中在「顶层 def 多」这一形态轴**：798-decl 阶梯 `ladder_large` 的 L09 单文件
   106.2 ms 占其总耗时 **93.5%**；L09 相对 L07 多出的 46.5 ms 里 43.9 ms（94%）来自这一个文件。
   两个最小词法用例各层只有 10–29 µs，跨层无差距。
3. **L08/L09 参考版回灌后没有性能回退**：同文件总耗时 L08 **68.7 ms**（11-11：70.4，**0.98×**）、
   L09 **113.5 ms**（11-11：115.2，**0.99×**）；同期**未改代码**的 L07 对照为 0.97×，
   即 0.98/0.99× 落在测量窗口漂移带内，不是回退。合成负载同向（§5）。
4. **顶层 def 链（strchain k=11，4096 defs）**：L07/L08 7.8/7.8 ms，L09–L12
   **61.7/55.9/48.8/46.5 ms**（是 L07 的 6.0–7.9×），L13 13.2 ms（1.7×）。
5. **struct k=10（2048 decls）**：L08 5.6 ms → L09 **48.1**（8.6× L08）→ L10 42.3（7.6×）
   → L11 19.9 → L12 17.6 → L13 19.1。
6. **universe k=10**：L09/L10 2.4/2.4 ms → L11/L12 21.8/20.7 ms → L13 3.2 ms；
   注意 L11/L12 的 `basic` 是全流程口径（含 parse+pretty+stdout），与 L09/L10/L13 的
   parse-out 口径不同轴，**不要逐格横比**。
7. **小负载**：L13 比 L07 慢（church 2.08 vs 1.44 ms，1.45×；match 0.143 vs 0.095 ms，1.51×；
   enum 0.330 vs 0.167 ms，1.98×），但 natadd 更快（2.39 vs 3.46 ms，0.69×）；
   L09 在 match/church/enum 上比 L07 慢（1.24×/1.72×/4.0×）。
8. **数据可信度**：6 遍总耗时 pass 间散布 **2.9–6.6%**（common 各层）；单个小负载格
   最大 ~77%，但绝对值只有几十 µs。各层真实语料 total 与 11-11 主报告相差 **0.97–1.02×**、
   L13 prelude-hdl 0.96–1.02×——同一台机器跨会话可比，结论不依赖单次采样。

## 1. 口径与环境

| 层 | `basic` 定义（参考版） | 计时位置 |
|---|---|---|
| L07–L10 | `bench_check_nf`（参考版类型检查到 nf） | parse 在计时外 |
| L11/L12 | 全流程 `run`（含 parse + pretty + `println` 输出） | 全流程 |
| L13 | `l13bench` 参考版 check（内建 nf parity 预检，通过才计时） | parse 在计时外 |

- **严格同文件**：`tools/bench_corpus/common/` 的 6 个文件（3 个最小词法/互递归用例 +
  48/198/798 decls 三档同形态阶梯），L07–L13 全部 PASS（闸门：参考版 run Ok 且
  参考版/孪生版 nf 一致；L13 用 `--with-prelude none` 对齐无 prelude 口径）。
- **同族合成负载**：各层自己的 bench bin（`l07bench`…`l13bench`），只跑该层支持的族；
  k 沿用跨层口径（match/church/natadd/strchain=11，enum=9，struct/universe/macro=10）。
- **真实语料（附录）**：各层自身 `tools/bench_corpus/L0X/` 整目录（层内有效，跨层不可横比）；
  L13 用 `l13bench` 的 `prelude-core` / `prelude-hdl` / `examples-hdl` 负载。
- 轮数与遍数：common/synth 每 pass 每配置 5 轮、real 3 轮；共 **6 pass**，奇偶 pass 反向层序
  （L07→L13 / L13→L07），汇总时对同一格跨 pass 取 min（等价于 30 轮取 min，同时消除顺序偏置）。

## 2. 严格同一文件（跨层可比）

单位 ms，min-of-6-passes（每 pass 内部已 min-of-5-rounds）：

| 文件 | L07 | L08 | L09 | L10 | L11 | L12 | L13 |
|---|---:|---:|---:|---:|---:|---:|---:|
| ex_block_comments.typort（3 decls） | 0.020 | 0.021 | 0.018 | 0.014 | 0.029 | 0.028 | 0.021 |
| ex_even_odd.typort（6） | 0.043 | 0.044 | 0.039 | 0.031 | 0.057 | 0.054 | 0.051 |
| ex_line_comments.typort（3） | 0.016 | 0.016 | 0.013 | 0.010 | 0.023 | 0.021 | 0.021 |
| ladder_l07_small.typort（48） | 0.407 | 0.413 | 0.530 | 0.285 | 0.546 | 0.485 | 0.493 |
| ladder_l07_medium.typort（198） | 4.262 | 4.433 | 6.749 | 2.781 | 3.990 | 3.516 | 4.311 |
| ladder_l07_large.typort（798） | 62.307 | 63.758 | **106.178** | 38.568 | 47.820 | 41.965 | 57.821 |
| **合计 (ms)** | **67.055** | **68.685** | **113.527** | **41.689** | **52.465** | **46.069** | **62.718** |
| **相对 L07** | 1.00× | 1.02× | **1.69×** | **0.62×** | 0.78× | 0.69× | 0.94× |
| 11-11 合计 | 68.795 | 70.372 | 115.248 | 42.748 | 54.707 | 49.540 | 64.174 |
| **new / 11-11** | 0.97× | 0.98× | 0.99× | 0.98× | 0.96× | 0.93× | 0.98× |

- 合计的 pass 间散布（max/min−1）：L07 5.9% / L08 6.6% / L09 3.1% / L10 3.3% / L11 4.6% /
  L12 2.9% / L13 3.6%。本表为散布下界（跨遍取 min），不冒充精确值。
- L11/L12 的 `basic` 含 parse+pretty+stdout，与其它层 parse-out 口径不同；本组文件小
  （≤37 KB、nf ≤1406），11-11 已估算口径差 <5%，跨层读法仍以阶梯行为主。
- 与 11-11 的差异（0.93–0.99×）**不是代码变化**：L07/L10–L13 参考版源码自 11-11 起未变，
  1 天两次会话的整体偏移约 −7%…0%（L12 最大 −7%，属该层 stdout 敏感 + 窗口负载）。

## 3. 同族合成负载（各层最大 k，参考版 `basic`）

单位 ms，min-of-6-passes：

| 负载（k） | L07 | L08 | L09 | L10 | L11 | L12 | L13 |
|---|---:|---:|---:|---:|---:|---:|---:|
| match (11) | 0.095 | 0.096 | 0.118 | 0.086 | 0.164* | 0.159* | 0.143 |
| church (11) | 1.435 | 1.427 | 2.468 | 1.390 | 1.392* | 1.404* | 2.082 |
| natadd (11) | 3.455 | 3.320 | 4.491 | **1.820** | 1.679* | 1.483* | 2.389 |
| strchain (11) | 7.785 | 7.759 | **61.663** | 55.948 | 48.819* | 46.457* | 13.184 |
| enum (9) | 0.167 | 0.168 | 0.671 | – | – | – | 0.330 |
| struct (10) | – | 5.604 | **48.070** | 42.319 | 19.881* | 17.591* | 19.141 |
| universe (10) | – | – | 2.402 | 2.377 | 21.821* | 20.702* | 3.171 |
| macro (10) | – | – | – | – | 18.752* | 18.442* | 16.798 |

- `*`：L11/L12 参考版没有 `bench_check_nf`，`basic` = 全流程 `run`（含 parse+pretty+stdout），
  与其它层 parse-out 口径不同轴；只作形态看，不逐格横比。
- `–`：该层参考版无此负载（L10/L11/L12 的 `enum` 在既有 bench 中已知不可测）。
- **读法**（与 11-11 同形）：
  - 同轴小负载（L07–L10、L13 均为 parse-out）：match 0.086（L10）–0.143（L13），1.7×；
    church 1.390（L10）–2.468（L09），1.8×；natadd 差最大，L10 1.82 vs L09 4.49（2.5×），
    L13 居中（2.39）。L11/L12 带 `*`，其小负载值含 parse+pretty，不与上述逐格比。
  - 「顶层 def 多」的 strchain(4096 defs) 与 struct(2048 decls) 把 L09–L12 与 L07/L08 拉开
    6–8×；L13 分别只有 1.7×（strchain，相对 L07）与 3.4×（struct，相对 L08），
    是 L09–L12 里唯一把这两形态压下来的层。
  - L11/L12 的 macro 与 L13 接近（18.8/18.4 vs 16.8），universe 上 L11/L12 明显贵
    （21.8/20.7 vs L09/L10 2.4、L13 3.2；但前两者是全流程口径）。
- **与 11-11 的逐格比值不可读成代码变化**：11-11 的合成负载用 `rounds=1`（首轮冷启动），
  本次是 rounds=5×6 pass 取 min。连**未改代码**的 L13 strchain 也从 18.4 → 13.2 ms（0.72×），
  L07 strchain 0.88×、L10 0.92×——同一形态整体快 8–28% 全是暖机/采样效应。
  故本节只与 11-11 比「形态」，不逐格比数值；L08/L09 的回灌影响见 §5。

## 4. 附录：各层自身真实语料（层内有效，跨层不可横比）

参考版 `basic`，3 轮 × 6 pass 取 min；11-11 列为 `docs/bench-realistic-l07l13-2026-11-11.md` §3.1。

| 层 | 用例数 | TOTAL min (ms) | TOTAL max (ms) | 11-11 basic (ms) | new / 11-11 |
|---|---:|---:|---:|---:|---:|
| L07 | 27 | 74.9 | 76.9 | 76.6 | 0.98× |
| L08 | 26 | 29.5 | 29.8 | 29.0 | 1.02× |
| L09 | 34 | 1804.7 | 1843.0 | 1792.5 | 1.01× |
| L10 | 22 | 16.6 | 18.5 | 17.0 | 0.97× |
| L11 | 25 | 18.5 | 20.3 | 19.1 | 0.97× |
| L12 | 30 | 39.1 | 40.1 | 39.8 | 0.98× |

L13 真实负载（参考版 `basic`，ms）：

| 负载 | 样本 | new min–max | 11-11 basic | new / 11-11 |
|---|---|---:|---:|---:|
| prelude-core（208 decls） | 6 | 40.5–44.5 | 45.8 | 0.88×–0.97× |
| prelude-hdl（1,439 decls） | 6 | 4589.2–4882.8 | 4796.4 | 0.96×–1.02× |
| examples-hdl（6 块，214–226 decls） | 36 | 39.8–52.7 | – | – |

- 这张表是**同机跨会话的校准**：L07–L12 整目录 total 全部落在 11-11 的 **0.97–1.02×**，
  L13 prelude-hdl 0.96–1.02×，说明今天窗口的机器状态与 11-11 基本一致，
  §2/§3 的跨层结论不受窗口漂移影响。
- L09 的 1804.7 ms 仍是 `ladder_large` 单文件主导（与 11-11 的 1723 ms 同形态，本次 +5%），
  参考版在真实项目规模（几百个顶层 def）上依然不可用。
- L11 的 `basic` 含 stdout，绝对值对 harness 敏感（历史 19→65 ms），此处 18.5 与 11-11 的 19.1
  同量级但不宜跨 harness 比。
- `examples-hdl` 是两版同在 217–226 decls 处失败的**失败路径计时**，只作规模参考。

## 5. L08/L09 参考版回灌后的影响（对照 11-11）

变化点（`docs/compare-l07-l13/BACKPORT-2026-11-11.md`）：

- **L08**：参考版整层重定基 = L07 参考版 HEAD + 积类型增量（`602c4188`），P1–P11 加固
  与 09-18 深值轮一次性到位；
- **L09**：按架构适配移植深值栈安全（quote/rename/occurs/struct_eq/pretty）、pending splice、
  P2 预算、P3 三档、P5 环守卫（`608843f7` 等），并新增 65 例黑盒；
- **L07/L10–L13**：参考版源码在 11-11 跨层基准之后**未变**（
  `git diff --name-only 0464150c..HEAD -- src/L07_sum_type src/L10_typeclass src/L11_macro
  src/L12_canonical src/L13_namespace` 为空），因此它们的 11-11→今天差异只能归因于窗口漂移。

结果：

| 指标 | L08 | L09 | 未改代码的对照 |
|---|---:|---:|---|
| common 合计 new/11-11 | 0.98× | 0.99× | L07 0.97× |
| strchain k=11 new/11-11 | 0.80× | 0.94× | L07 0.88× / L10 0.92× |
| struct k=10 new/11-11 | 0.99× | 0.91× | L10 0.94× / L12 0.85× |
| church k=11 new/11-11 | 0.97× | 1.03× | L07 0.89× / L13 0.97× |
| natadd k=11 new/11-11 | 1.10× | 1.04× | L07 0.92× / L10 0.94× |
| enum/match new/11-11 | 1.01× / 1.07× | 1.02× / 1.05× | L13 0.80× / 0.92× |

- **common（同口径、同文件）**：L08 0.98×、L09 0.99×；未改代码层自身跨会话在 **0.93–0.98×**
  （L07 0.97 / L10 0.98 / L11 0.96 / L12 0.93 / L13 0.98）——L08/L09 与对照同带，无回退。
- **合成负载**：L08/L09 的 new/11-11 为 **0.80–1.10×**；未改代码层自身就在 0.55–1.04× 浮动
  （11-11 的合成数据是 `rounds=1` 冷启动，方向两侧都有噪声：L12 match 0.55、L11 macro 1.04）。
  L08 natadd 1.10× 是 3 ms 量级负载上的 +10%，落在该表 pass 间散布量级内，不构成系统性变慢——
  L08/L09 的比值既不全 >1，也不集中在某一负载族。
- 因此「回灌无性能回退」的主证据仍是 BACKPORT §5 的**同会话旧/新二进制交错 A/B**；
  本报告从跨层侧独立复核，结论一致。
- **结构性结论不变**：L09 参考版仍是最慢层（1.69× L07），struct k=10 仍是 L08 的 8.6×；
  根因不在「回灌 L07 加固」范围内：主项是 L09 定基后顶层声明进入类型检查上下文（无 decl 表）导致的
  O(D) 全局引用 + `fresh_meta` 缺 L06 `close_meta_ty` 快捷（定位与证据见
  `docs/l09-perf-gap-2026-11-12.md`；旧稿「src_names 逐 decl 克隆」说法已被 `866f23e5` 修复，属半过期）。
  L08 在 common 上是 1.02× L07（与 11-11 的 1.02× 相同）。

## 6. 局限

1. **单机单窗口**：小负载 ±5–10%；`match` 这类 <0.2 ms 的格子 pass 间可达 ~77%
   （绝对值只差 40–80 µs），本报告用 6 遍取 min 压噪，但不代表可重复到 µs 级。
2. **L11/L12 绝对值对 harness 敏感**：`basic` 含 `println` 输出，只宜同轴比较；
   本报告沿用 11-11 的 PowerShell 口径。
3. **与 11-11 合成负载不可逐格比**：旧数据 `rounds=1` 冷启动；只比形态（§3 已注明）。
   11-11 的 L13 单文件是 `rounds=3`、真实负载用默认 5 轮，与本次 rounds=3×6 pass 可比
   （§4 校准 0.96–1.02×）。
4. **参考版 vs 孪生版不在本报告范围**：见 `docs/bench-realistic-l07l13-2026-11-11.md`。
5. **L13 是产品层**：其 `basic` 已含 prelude 相关机制（`--with-prelude none` 对齐后仍比 L07 重），
   本报告只回答「同用例上慢多少」，不做产品路径（LSP/CLI）结论。

## 7. 复现

```powershell
# 1) 用当前源码重建所有基准二进制
cargo build --release --bin realbench --bin l07bench --bin l08bench --bin l09bench `
    --bin l10bench --bin l11bench --bin l12bench --bin l13bench

# 2) 跑 6 遍（每遍 common 5 轮 / synth 5 轮 / real 3 轮；奇偶遍反向层序）
powershell -ExecutionPolicy Bypass -File tools/run_crosslayer_ref.ps1 -Passes 3
powershell -ExecutionPolicy Bypass -File tools/run_crosslayer_ref.ps1 -PassStart 4 -Passes 3

# 3) 汇总表（写到 target/bench_real/ref_2026-11-12/summary.md）
python tools/crosslayer_ref_report.py

# 单点复现示例
target/release/realbench.exe --layer L09 --corpus tools\bench_corpus\common --rounds 5 --only basic
target/release/l09bench.exe  --workload strchain --max-k 11 --rounds 5 --only basic
target/release/l13bench.exe  --workload strchain --max-k 11 --rounds 5 --only basic
target/release/l13bench.exe  --file tools\bench_corpus\common\ladder_l07_large.typort `
    --with-prelude none --rounds 5 --only basic
```

## 8. 本次产物

| 文件 | 说明 |
|---|---|
| `tools/run_crosslayer_ref.ps1` | 跨层参考版基准驱动（common/synth/real 三组、多遍交错、UTF-8 日志） |
| `tools/crosslayer_ref_report.py` | 日志→Markdown 汇总（跨遍取 min、pass 间散布、11-11 对照） |
| `target/bench_real/ref_2026-11-12/` | 原始日志 403 个 + `summary.md`（未跟踪，不入库） |
| `docs/bench-crosslayer-ref-2026-11-12.md` | 本报告 |
