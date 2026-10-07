# task-9 预注册：L02 新码 A/B（影子副本，写于取数之前）

状态：**取数前冻结**（2026-10-06）。范围按 Lead 时间盒：**只做 C1、C2 及跨树对照 A vs A'**；
C3 及以后不要求本轮完成（未试原因写入 `02-experiments.md` 第二部分）。

## 0. 交付与约束

- 影子树 `/tmp/l02-exp`（`git clone --no-hardlinks` 主树 HEAD `4a0a136`，无 `target/`），
  独立 `CARGO_TARGET_DIR=/tmp/l02-exp-target`；**主树 `src/**` 零改动**。
- 编译在 `docs/perf-l02/.benchlock` 内（协议同 task-8 驱动）；每个补丁先过
  `cargo test --release --lib L02_tyck`（readme 26 用例）与 `cargo test --release --bin l02bench`。
  用 release 而非 debug 以复用 release 依赖产物；bench 节点数断言/输出必须与基线一致。
- 二进制：`/tmp/l02-exp/l02bench-{base,c1,c2}`（各带 sha256）。

## 1. 补丁（详见 `02-experiments.md` 第二部分；`src/L02_tyck/bump_spine_iter.rs`）

- **C1（`W` 40B→24B）**：`W::PiBody(&str,&Tm,Option<&EnvCons>)`（32B payload）
  → `W::PiBody(&Tm,Option<&EnvCons>)`（16B），弹出时从 Π 节点取 name/cod。
  落点：定义 `:217`、构造 `:244-247`、执行 `:328-332`。
  **语义不变**（同一节点、同一求值顺序）；预期 1–4%。
- **C2（β/let 尾任务寄存器化）**：`W::Apply`/`W::ApplyKnown`/`W::LetBody` 三处
  「push 后必然立刻 pop」的 `W::Tm` 体改放循环局部 `cur: Option<W>`，免一次 40B
  store+load 与一轮 jump-table 分发。落点：循环头 `:236`、三处 push `:304/:313/:326`。
  **严格 LIFO 等价**；预期 2–6%；审计自评「最可能被证伪（store-forwarding 吃掉搬运）」。

**C1 与 C2 分别单独 A/B，不叠加**（C1 落地会降低 C2 的每次 push 成本）。

## 2. A/B 协议（沿用 task-8 §2 的结论）

同一窗口内三段、段内严格交错、**pair 内顺序按 pair 奇偶交替**、每 rep 记
`scaling_cur_freq`、`--only` 单口径隔离、`taskset -c 7` + keep-alive + 独占锁：

| 段 | 两侧二进制 | 作用 |
|---|---|---|
| `nullA` | A' vs A'（同二进制） | 该批地板（含单二进制噪声） |
| `ab` | A' vs 补丁二进制 | 实验 |
| `nullB` | 补丁 vs 补丁（同二进制） | 补丁二进制下的地板（跨二进制比较的对称控制） |

- **对照实验（必做）**：`A = 主树 target/release/l02bench` vs `A' = 影子树未改动重建`
  （同源、不同树/不同次构建）→ 跨树混杂量级。L01 实测 ≤3%，L02 自测。
- reps：**42/侧**（Lead：1–2% 分辨率需要 42/侧）。
- 工作负载：`church` 与 `conv`（β 密度主导，C1/C2 的靶子），`--only fast`；
  时间允许再补 `fast_ss`。
- 判定格：k=13/15（必要时含 k=11）。

**统计（预注册，同 task-8）**：主判定 = 配对相对差中位数 vs 同批 null 配对 bootstrap p95
（下限 0.5%）；非配对值照报但不作门槛；C1/C2 的判定必须**先扣除 A vs A' 对照的混杂量级**
（若对照本身 > 地板，则把对照差值视为该批的附加系统项并显式说明）。

**确定性旁证（硬要求，Lead 指定）**：C1/C2 都是纯数据搬运 ⇒ `l02l05mem` 的
`fast`/`fast_ss growth`/`churn` 的 **allocs 与 bytes 必须逐字不变**；
若变化 ⇒ 补丁写偏（例如改变了分配次数/容量），先修补丁再谈时间。用
`exp-mem-run.sh` 的 `BIN=` 指向影子二进制复跑同一矩阵。

## 3. 预期与证伪条件（预注册）

| 实验 | 预期 | 证伪（判死）条件 |
|---|---|---|
| A vs A' | ≤3%（L01 经验），本机仅作地板/系统项 | 若 >5% 且方向一致 ⇒ 本轮所有 A/B 的判定要显式扣该项 |
| C1 | +1–4%（church 与 conv 同向） | 配对差 ≤ 同批地板 → 未判定/无收益；**不得**用「机制上应该更快」续命 |
| C2 | +2–6%（β 密度主导） | 同上；或与 C1 叠加后增量 ≤ 地板（本轮不叠加） |

## 4. 若判不出来怎么办（预注册的收口方式）

- 1–6% 效应受 task-8 §2.6 的分辨率限制（地板 ≲1% 才可判）。若某批地板 >2%：
  **重跑该批**（换时间窗）；仍不行则如实写「未判定（地板 X%）」，并给出
  **可判定所需条件**（reps/侧、需要的地板），不硬判。
- 无论判定与否，`l02l05mem` 的分配计数不变性 + 跨树对照数字都要写进文档。
