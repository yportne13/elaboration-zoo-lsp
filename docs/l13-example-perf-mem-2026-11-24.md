# L13 跑 example 的性能与内存分析（2026-11-24）

> 工具：`l13bench --file`、`l06l13mem --chapter L13`、`typort stats`（`--features mem-profile`，
> dhat + Windows heap walk）、`typort check` 的 `infer` 相位计时。数据全部本机实测（Windows，release）。

## 0. 速览

| 口径 | 数值 | 说明 |
|---|---|---|
| `typort check` 端到端 | **4.6–5.3 s** | 其中 prelude 装载 ~4.6 s 是**固定成本** |
| `l13bench --file`（core prelude） | **40–51 ms** | 不含 HDL prelude 的纯文件检查 |
| 峰值工作集（`check`） | **~303 MB** | 空文件同样是 303 MB ⇒ **全是 prelude** |
| `stats` 峰值（prelude + heap walk） | 520 MB peak / 467 MB 当前 | mem-profile 构建含 dhat 开销 |
| 稳态堆（`stats`） | **356.9 MB** / 137.6 万块 | — |
| 参考版 vs 孪生（L13 benchmark 稳态） | **0.24×–2.05×** 字节 | 见 §5 |

**结论先行**：跑 example 的时间与内存在这个阶段**几乎全部由 prelude 决定**。文件本身的成本
（40–51 ms、几百 KB）相比 prelude（4.6 s、303 MB）小两个数量级。

## 1. 端到端：prelude 就是全部

| 输入 | 墙钟 | 峰值 RSS |
|---|---|---|
| 空文件 | — | **303.1 MB** |
| `def one : Nat = 1` | — | 302.9 MB |
| `alu.typort`（719 B） | 4.80 s | 303.1 MB |
| `hdl_ops.typort`（4.7 KB） | 5.28 s | 302.6 MB |
| `typeclass_complex.typort`（7.5 KB） | 4.88 s | 303.0 MB |
| `theorem_proving.typort`（10.6 KB） | 4.66 s | 303.0 MB |
| `adder_proof.typort`（21 KB） | 5.10 s | 302.9 MB |

峰值内存与文件大小**完全无关**（719 B 与 21 KB 都是 303 MB）。

## 2. 文件自身的成本（去掉 prelude）

`l13bench --file --with-prelude core --ref-only --rounds 3`：

| example | decls | basic（min） | med |
|---|---|---|---|
| alu | 216 | 40.8 ms | 42.6 ms |
| typeclass_complex | 279 | 50.2 ms | 51.0 ms |
| theorem_proving | 248 | 50.5 ms | 51.1 ms |

`--with-prelude hdl` 时 alu / hdl_ops 的 `basic` 是 4574 / 4721 ms（1396 / 1396 decls）——
那是 prelude 的 1396 个 decl 在跑，不是文件。

## 3. 堆构成（`typort stats`，prelude 装载完的稳态）

### 3.1 总量与块分布

```
heap total: 356.9 MB in 1,376,139 blocks
```

| 尺寸档 | 块数 | 字节 |
|---|---|---|
| **524289+** | **8** | **177.3 MB** |
| 81–96 | **918,007** | 80.9 MB |
| 385–512 | 167,253 | 78.3 MB |
| 33–48 | 223,987 | 9.5 MB |
| 32769–65536 | 71 | 3.9 MB |
| 129–192 | 13,480 | 2.4 MB |

两个特征显眼：**8 个 >512KB 的巨块占 177 MB**（约总量一半），**81–96 字节档有 91.8 万块**。
`Val` = 80 B、`Tm` = 72 B（见 `type_sizes`）——81–96 档基本就是这两类节点。

### 3.2 按来源归因（`per_source_breakdown`，91.0 MB 可归因部分）

| 来源 | 合计 | Tm 堆 | Val 堆 | arc/span | Tm 节点 | Val 节点 | closure |
|---|---|---|---|---|---|---|---|
| **solved_meta_vals** | **75.7 MB** | 48.5 | 21.2 | 6.1 | **577,346** | **231,318** | **81,962** |
| top_level_cxt | 9.1 MB | 8.7 | 0.5 | 0.0 | 103,107 | 5,316 | 3,413 |
| cxt_in_unsolved_meta | 5.9 MB | 5.4 | 0.5 | 0.0 | 64,387 | 5,186 | 2,559 |
| unsolved_meta_vals | 0.2 MB | 0.2 | 0.0 | 0.0 | 2,028 | 500 | 218 |
| trait_solver_vals | 0.1 MB | 0.0 | 0.1 | 0.0 | 0 | 700 | 0 |

**已解 meta 的解值占可归因内存的 83%**：8.2 万个 closure、57.7 万个 `Tm` 节点、23.1 万个 `Val` 节点。

### 3.3 dhat 峰值归因（`stats` 那次运行）

| 位置 | 峰值 | 生命周期合计 |
|---|---|---|
| `Infer::quote`（`mod.rs:3392`） | **403.1 MB** | 471 MB |
| `Iterator::collect`（PatternDetail/VSub map） | 340.1 MB | 373 MB |
| `Infer::quote_sp`（`mod.rs:3385`） | 311.2 MB | 324 MB |
| `Iterator::collect`（同上，另一站点） | 241.6 MB | 246 MB |
| `Infer::quote_inner`（`mod.rs:3400`） | 159.5 MB | 168 MB |
| `collect`（`slice::iter` over 声明） | 153.8 MB | 157 MB |
| `collect`（同上） | 123.6 MB | 136 MB |
| `map_fold`（PatternDetail 克隆） | 102.9 MB | 166 MB |
| `Infer::lams_go`（`unification.rs:497`） | 67.1 MB | **1002 MB** |

**`quote` 家族（`quote` / `quote_sp` / `quote_inner`）合计峰值 ~874 MB**，是最大的单一瞬时热点；
`lams_go` 峰值只有 67 MB 但**生命周期累计 1002 MB**（churn 最大）。

## 4. prelude-core 的分配账（`l06l13mem`）

| 阶段 | 分配次数 | 字节 |
|---|---|---|
| parse（15 文件 208 decls） | 13,238 | 5.1 MB |
| **basic（参考版）** | **771,110** | **145.8 MB** |
| fast（孪生 one-shot） | 266,632 | 49.4 MB |
| fast_ss growth | 266,602 | 49.2 MB |
| fast_ss churn（稳态 3 轮均值） | 266,492 | 36.3 MB |

参考版比孪生多 **2.9× 分配次数 / 3.0× 字节**（145.8 vs 49.4 MB）。
孬生的 arena：5 个 16.06 MB chunk（1/2/4/8/16 MB 倍增），`reset` 后保留 8.03 MB。

## 5. 各负载的参考版 vs 孪生（`l06l13mem --chapter L13`）

| 负载 | 参考版字节 | 孪生字节 | 比值 | 分配次数比 |
|---|---|---|---|---|
| church | 1.51 MB | 1.38 MB | 1.10× | 7.67× |
| natadd | 2.55 MB | 1.59 MB | 1.60× | 10.21× |
| gadt | 0.86 MB | 1.49 MB | **0.58×** | 3.41× |
| strchain | 9.69 MB | 5.43 MB | 1.78× | 4.35× |
| match | 0.34 MB | 1.40 MB | **0.24×** | 1.65× |
| enum | 1.02 MB | 1.57 MB | **0.65×** | 3.02× |
| struct | 12.81 MB | 6.24 MB | 2.05× | 5.14× |
| moduletree | 0.36 MB | 1.38 MB | **0.26×** | 2.06× |

**孪生在 4/8 个负载上内存更高**：gadt 0.58×、match 0.24×、enum 0.65×、moduletree 0.26×
（比值 = 参考版/孪生，<1 即孪生占得更多）。原因：孪生的 arena chunk 有**最小 1 MB** 下限，
小负载时固定开销占主导（如 moduletree 参考版 0.36 MB vs 孪生 1.38 MB）。

大负载上孪生明显更省：struct 2.05×、strchain 1.78×、natadd 1.60×。

## 6. 关键结论与可操作项

| 观察 | 判定 |
|---|---|
| example 端到端 4.6–5.3 s **全部是 prelude** | 优化 example 先优化 prelude |
| 峰值 303 MB 与文件大小无关 | 同上 |
| 已解 meta 的解值占可归因堆 83%（75.7 MB） | 已解 meta 的解值持有大量 `Tm`/`Val` 节点，且**只在后续 force 时才被消费**——可考虑按需保留或压缩 |
| `quote` 家族峰值 ~874 MB | 引用（quote）时构造整棵 `Tm`，是最大瞬时热点；与 L07 观察到的「物化即开销」同源 |
| `lams_go` churn 1002 MB | 每次 unify 都重建 λ 前缀项，值得看能否复用 |
| 孪生小负载固定 1 MB arena 下限 | 小文件场景孪生内存反而更高 |
| 91.8 万块 81–96 B | 就是 `Tm`(72)/`Val`(80) 节点，节点数 ≈ 100 万 |

## 7. 复跑方法

```powershell
# 内存分配账（确定性口径）
target/release/l06l13mem.exe --chapter L13 --workload all --k 9 --rounds 3

# 堆剖面（需 mem-profile）
cargo build --release --features mem-profile --bin typort
target/release/typort.exe stats   # 输出 JSON + dhat-heap.json

# 文件自身成本（去 prelude 影响）
target/release/l13bench.exe --file examples/theorem_proving.typort --with-prelude core --ref-only
```
