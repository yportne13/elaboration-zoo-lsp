# VSpan 合入 L07/L08 后的 L07–L10 跨层对比（2026-11-13）

> 任务：用户「2 可以合入 L07 ~ L09。然后再测下 L07 ~ L10 的对比」。
> 「2」= `Val` 名字 span 句柄化（`VSpan = Rc<Span<String>>`，见
> [l09-value-span-rc-2026-11-13.md](l09-value-span-rc-2026-11-13.md)）。
> L09 已落地；本轮把它移植到 **L07_sum_type / L08_product_type 参考引擎**
> （L07→L08→L09 继承链同机制），然后重测 L07–L10。
> 基线日志：`target/perf09/crosslayer_vspan/baseline/`；
> 改后日志：`target/perf09/crosslayer_vspan/after/`。

## 1. 改动（L07/L08）

- 照 L09 `0df5bcbe` 模板逐点搬：`VSpan(Rc<Span<String>>)` + `Deref` + 三向
  `PartialEq`（只比 data）+ **`Debug` 委托内层 `Span<String>`**；`Val` 的
  Obj 字段名 / Lam·Pi binder / LiteralIntro / Sum 头+参数+cases / SumCase
  名+datas 全部改 `VSpan`；Val→Tm 回写用 `tmspan`；两个 deep 收集器
  （quote/rename）FrameKind 同步。
- 10 文件 **+305/−171**（`src/L07_sum_type/{mod,elaboration,pattern_match,unification,tests}.rs`
  与 L08 同名五件）。Tm、孪生 `bump_spine_iter`/CTm、Cxt 的 Tm 语义、
  L09–L13 均未动；`cxt.rs` 无需改（L07/L08 的 builtin 经 `Tm→eval` 注册，
  无直接 `Val::Lam/Pi` 构造）。
- 测试计数改前=改后、0 failed：L07 fast_parity **97** / blackbox **48+1 ignored**
  / lib **70**；L08 **116** / **57+1 ignored** / **81**；`cargo check --all-targets` 0 errors。
  parity（参考版↔孪生错误正文逐字节）全绿 ⇒ `VSpan::Debug` 形状与孪生
  `Span<String>` 一致。

## 2. L07/L08 改前 → 改后

| 口径（min-of-3，`--only basic`） | L07 改前 | L07 改后 | Δ | L08 改前 | L08 改后 | Δ |
|---|---:|---:|---:|---:|---:|---:|
| `realbench` common TOTAL（6 文件） | 69.550 ms | **50.874 ms** | **−26.8%** | 69.026 ms | **51.144 ms** | **−25.9%** |
| 本层自有真实语料整目录 | 75.638 ms | **59.226 ms** | **−21.7%** | 29.833 ms | **27.049 ms** | −9.3% |
| Eq 阶梯单文件（同一 801-decl 文件） | 2.492 ms* | **2.377 ms** | −4.6% | 2.487 ms* | **2.375 ms** | −4.5% |
| l07bench/l08bench church k=11 | 1.473 ms | **1.307 ms** | −11.3% | 1.544 ms | **1.323 ms** | −14.3% |
| strchain k=11 | 7.756 ms | **7.100 ms** | −8.5% | 8.041 ms | **7.805 ms** | −2.9% |
| natadd k=11 | 3.247 ms | **2.763 ms** | −14.9% | 3.176 ms | **2.828 ms** | −10.9% |
| struct k=10 | — | — | — | 5.681 ms | **4.967 ms** | −12.6% |
| match k=11 | 0.100 ms | **0.094 ms** | −6.0% | 0.098 ms | **0.095 ms** | −3.1% |
| enum k=9 | 0.179 ms | **0.173 ms** | −3.4% | 0.176 ms | 0.176 ms | 0 |
| global k=11 | 14.102 ms | 14.209 ms | +0.8%（噪声） | 14.594 ms | 14.187 ms | −2.8% |

\* 阶梯单文件的"改前"取上一轮同机 `ab_recheck2` 的 L07/L08 2.492/2.487 ms；
本窗口改后为四引擎同批测量值。收益形态与 L09 一致：值复制/构造子密集的
负载（common、church、natadd、struct、strchain）受益最大，`global`（名字走
`SmolStr` 的 `Decl`，不经 `Span<String>`）不受影响。

## 3. L07–L10 跨层对比（改后）

### 3.1 同文件 common（L07 风格 798-decl 阶梯主导）

| 引擎 | TOTAL (ms) | 相对 L09 |
|---|---:|---:|
| L07 | 50.874 | 1.01× |
| L08 | 51.144 | 1.02× |
| L09 | **50.348** | 1.00× |
| L10 | **40.966** | **0.81×** |

L07/L08/L09 收敛到 **50.3–51.1 ms（彼此差 ≤1.6%）**——三者现在共享同一条
「名字 span 句柄化」表示技巧；L10 仍快 1.23×，来自其整机 `Rc<Val>` 世代差
（见 [l10-perf-advantages-2026-11-13.md](l10-perf-advantages-2026-11-13.md)）。

### 3.2 同一 Eq 阶梯单文件（801 decls，最能区分载体）

| 引擎 | 时间 |
|---|---:|
| L07 | 2.377 ms |
| L08 | 2.375 ms |
| L09 | 2.663 ms |
| L10 | **1,078.871 ms（454× 慢）** |

L09 比 L07/L08 多 12%（宇宙/构造子检查常数），但 L10 的旧载体
（顶层声明仍在 `Cxt`）在此崩掉；这是 L10 的债，与 L10 的 Rc 收益无关。

### 3.3 各层自有真实语料（不同文件集，仅供参考）

| 引擎 | 语料 | 文件数 | PASS | TOTAL (ms) |
|---|---|---:|---:|---:|
| L07 | `tools/bench_corpus/L07` | 27 | 27 | 59.226 |
| L08 | `tools/bench_corpus/L08` | 26 | 26 | 27.049 |
| L09 | `tools/bench_corpus/L09` | 34 | 34 | **8.680** |
| L10 | `tools/bench_corpus/L10` | 22 | 22 | 16.419 |

L09 自有语料远快于其它层，是因为这批文件里有 801-decl Eq 阶梯/大 decl 数
负载，L09 的载体切换把它从 1.8s 级压到 9ms 级；L07/L08/L10 的语料不含这类
极端形态，故数字不可横向相减。

### 3.4 micro-bench 家族（各层自己的生成器；k=11，enum k=9，struct k=10）

| 负载 | L07 | L08 | L09 | L10 |
|---|---:|---:|---:|---:|
| church | **1.307** | 1.323 | 1.427 | 1.355 |
| strchain | **7.100** | 7.805 | 7.494 | **56.03（7.5× 慢）** |
| match | 0.094 | 0.095 | 0.093 | **0.088** |
| enum k=9 | **0.173** | 0.176 | 0.215 | n/a（l10bench 现 nf-parity panic） |
| struct k=10 | — | **4.967** | 5.117 | **42.794（8.6× 慢）** |
| natadd | 2.763 | 2.828 | 2.704 | **1.905** |
| universe | — | — | **4.006** | 5.374 |
| global | 14.209 | 14.187 | n/a（无该语言面） | n/a |

> 注意这是各层**自家生成器**的同族负载（church/natadd 的源文件不同），只用于
> 同层改前/改后与量级对照；严格同文件的对照看 §3.1/§3.2。

## 4. 解读

1. **L07→L08→L09 现在同水位**：common 上三层 50.3/51.1/50.3 ms；VSpan 是
   纯表示层、跨层可继承的廉价优化，收益形态可预测（值/构造子密集负载
   −11~−27%，名字走 SmolStr 的 `global` 负载不动）。
2. **L09 的残差**：church 1.427 vs L07 1.307（1.09×）、strchain 1.06×、
   enum 1.24×、Eq 阶梯 1.12×——宇宙/构造子检查的固定常数，不再有量级问题。
3. **L10 的「两极」更清晰**：common/natadd/match 上它仍是全场最快
   （whole-engine `Rc<Val>` → 值复制几乎零成本）；但旧载体让它在对
   「声明数/全局引用」敏感的负载上灾难性落后：strchain 7.5×、struct 8.6×、
   801-decl ladder **454×**、L09 语料 1.1s。这正是 L10–L12 重定基 P0
   （载体切换）优先级最高的原因（排期见 `docs/l10-perf-advantages-2026-11-13.md` §5）。
4. 控制项：各层 `--validate` 全 PASS（L07 27/0、L08 26/0、L09 34/0、L10 22/0），
   无 SKIP、无行为变化。

## 5. 复现

```powershell
cargo build --release --bin realbench --bin l07bench --bin l08bench --bin l09bench --bin l10bench
foreach ($L in 'L07','L08','L09','L10') {
  target\release\realbench.exe --layer $L --corpus tools\bench_corpus\common --rounds 3 --only basic
  target\release\realbench.exe --layer $L --corpus "tools\bench_corpus\$L" --rounds 3 --only basic
  target\release\realbench.exe --layer $L --corpus target\perf09\corpus_real_l09\ladder_large_only --rounds 3 --only basic
}
target\release\l07bench.exe --workload all --max-k 11 --rounds 3 --only basic   # l08bench/l09bench 同
```

> 已知问题（未修、不阻塞）：`l10bench --workload enum`（及其 all 模式）在
> 当前版本触发 `match/enum/universe/traitchain 节点数双实现不一致` 的
> nf-parity panic（`src/bin/l10bench.rs:289`），与本次 VSpan 改动无关
> （L10 源码未动）；跨层表里 L10 的 enum 因此留空。
