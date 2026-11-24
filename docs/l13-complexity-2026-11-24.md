# L13 观察面升级的复杂度分析（2026-11-24）

> 承接 `docs/l13-raw-pretty-2026-11-23.md`（五步改动）。本文只用实测数据回答一个问题：
> **这些改动到底让复杂度变好还是变坏？** 每项都给出可复跑的探针。

## 0. 结论速览

| 改动 | 复杂度 | 证据 |
|---|---|---|
| 源码注解渲染（`raw_pretty`） | **O(1) 而非 O(k)** | §1：K=10000 时 0.30 µs vs **2140.6 µs**（约 7000×） |
| 全局名 hover 复用登记串 | **每使用点省一次 quote+pretty** | §2 |
| `lsp_surface()` 统一快照 | **≈ 0**（比直接 clone 还略快） | §3：delta = −0.06…−1.49 µs |
| 惰性采集（`hover_wanted`） | **持平到略好** | §4：ratio = 0.96–1.02× |
| 形状认回（`match_to_decl`） | **O(#shapes)，但常数极小** | §5：200 条全扫 = 0.35 µs（1.8 ns/条） |
| 端到端（带 prelude） | **无增长** | §6：def 数 0/10/50/200 的墙钟 111/133/114/134 ms |

## 1. 源码注解渲染：O(k) → O(1)（最大收益）

探针：`complexity_probe_old_vs_source`（`#[ignore]`，需 `--ignored` 显式跑）

```
cargo test --release --lib \
  L13_namespace::debug_test::complexity_probe_old_vs_source -- --ignored --nocapture
```

对 `def big(n: Nat): Box K = n` 的类型渲染：

| K | 源码路径（`raw_pretty`） | 旧路径（`nf → quote → quote_nat`） | 倍数 |
|---|---|---|---|
| 10 | 0.54 µs | 3.0 µs | 5.6× |
| 100 | 0.30 µs | 19.9 µs | 66× |
| 1000 | 0.30 µs | 190.5 µs | **635×** |
| 10000 | 0.30 µs | **2140.6 µs** | **7135×** |

**旧路径是严格线性的**（3.0 / 19.9 / 190.5 / 2140.6 ≈ 每 1000 个节点 +190 µs），
因为它要为 `Val::Nat(K)` 建 K 层 `SumCase` 链（`quote_nat` 的 `for _ in 0..k`）。
源码路径是**常数**（0.30 µs，只拼一次字符串）。

这条曲线正是 `NAT_CHAIN_LIMIT = 2^22` 护栏的来源：2026-10-07 实测 `nat_mul 100000 100000`
（K = 10^10）把进程提交量顶到 **121.8 GB**，Windows 事件 2004，主机非正常重启（3 小时 3 次）。
按上表线性外推，K = 10^10 对应的渲染时间约 **21 亿秒**（22 年）——护栏是唯一出路。

## 2. 全局名 hover 复用登记串

改动前：**每个使用点**都 `quote + pretty`（一次 `push_hover` = 一次完整引读）。
改动后：命中 decl 表就直接取 `e.6`（登记期算好的串）。

收益 = `#使用点 × (quote+pretty)`，而 quote+pretty 的成本与**值的规模**成正比；
对含大 Nat 的类型，这个规模正是 §1 的 O(k)。所以这条与 §1 同阶，只是乘上了使用点数量。

未单独计时（改动前后不在同一工作树），但可从 §1 的对照推断量级。

## 3. `lsp_surface()` 统一快照：≈ 0 开销

`lsp_surface()` 做的是六次 `clone`（与原先逐字段读一模一样）。实测：

| hover 条目数 | `lsp_surface()` | 直接 `hover_table.clone()` | delta |
|---|---|---|---|
| 90 | 3.05 µs | 3.10 µs | **−0.06 µs** |
| 410 | 14.17 µs | 14.38 µs | **−0.21 µs** |
| 1610 | 55.53 µs | 57.02 µs | **−1.49 µs** |

delta **为负**（统一入口反而略快：少一次跨分支的重复借用）。即**零成本抽象**。

## 4. 惰性采集：持平到略好

`push_hover` 的闸门从 `lsp_collect` 换成 `hover_wanted(span)`——光标不在 span 上时
**连 quote+pretty 都不做**。对照实验（唯一变量 = 采集开关）：

| def 数（每个都有 match 类型） | 采集开 | 采集关 | 比值 |
|---|---|---|---|
| 10 | 10,391 µs | 10,829 µs | **0.959×** |
| 50 | 38,684 µs | 38,602 µs | 1.002× |
| 200 | 154,809 µs | 151,326 µs | 1.023× |

注：这里的「采集关」是 `lsp_collect = false`（全不采），而真实 LSP 场景是「开 + 按偏移过滤」，
此时只有光标命中的那 1–2 个条目会渲染——**远低于**「全采」。所以这个 1.0–1.02× 是**上界**。

## 5. 形状认回：O(#shapes) 但常数极小

`match_to_decl` 线性扫形状表（每个 def 一条，按优先级四轮）。实测扫描成本：

| 形状表条目 | 全表扫描 | 每条目 |
|---|---|---|
| 1 | 0.00 µs | 0.002 µs |
| 10 | 0.02 µs | 0.002 µs |
| 50 | 0.09 µs | 0.002 µs |
| 200 | 0.35 µs | 0.002 µs |

**1.8 ns/条**。而且这条只在**渲染路径**上跑（`push_hover` 的候选），不在语义/热路径上；
并且有个 O(1) 早退：`decl_shapes.borrow().is_empty()` 时直接返回 `None`（默认不采集时恒真）。

理论风险：如果将来有几千个 def 都登记形状、且 hover 密集触发，200 → 2000 条会到 ~3.5 µs/次。
目前实测的 L13 prelude 只有个位数形状（类型级 def 本来就少），可以忽略。

## 6. 端到端（带 prelude）

同一份源码，加 0 / 10 / 50 / 200 个「有注解 + match 类型」的 def：

| def 数 | 墙钟 |
|---|---|
| 0 | 111 ms |
| 10 | 133 ms |
| 50 | 114 ms |
| 200 | 134 ms |

**平**（波动在 ±20 ms 的进程启动噪声内）。即：观察面改动没有给端到端引入任何可测增长。

## 7. 复跑方法

```powershell
$env:CARGO_PROFILE_TEST_DEBUG='0'   # 规避 MSVC 的 LNK2019 anon.llvm.*
cargo test --release --lib L13_namespace::debug_test::complexity_probe -- --ignored --nocapture
cargo test --release --lib L13_namespace::debug_test::complexity_probe_old_vs_source -- --ignored --nocapture
```

两个探针都 `#[ignore]`（只打印不断言、~10 s），不进默认门禁。

## 8. 复核（2026-11-24 第二轮）：发现并修掉了两个真实问题

第一轮只测了「我新增的东西」，没测「我改坏了什么」。用 baseline worktree（`2ad6b1b4` =
观察面改动之前）逐例对照后，发现两个问题：

### 8.1 问题 1（**正确性**）：`clear_observation_tables` 多清了表

我合并两处 prelude 清表点时，把 `accumulated_errors` 与 `failed_decls` 也清了。但原代码
**只清 3 张显示表**：

| 表 | 原代码 | 我（错） | 为什么不能清 |
|---|---|---|---|
| `hover` / `completion` / `inlay` | clear | clear | — |
| `accumulated_errors` | **不清** | clear | 消费方逐 decl `drain`，整表清会丢诊断 |
| `failed_decls` | **不清** | clear | 携带 A2 根因抑制语义；清了会让下游退化成二阶 not-in-scope |

已修正：`clear_observation_tables` 只清 3 张显示表 + `decl_shapes`（方案 3 的显示旁表）。

### 8.2 问题 2（**性能**）：`lsp_surface()` 让单请求克隆全部六通道

原 `hover_entries_owned` 只 clone **一张**表；改成 `lsp_surface().hover` 后，每次请求连带
克隆 completion / inlay / 迭代 `println_jobs` / 复制 errors 与 failed_decls。
把三张表填到同量级后实测：

| 每表条目 | `lsp_surface()` | 单通道 clone | 比值 |
|---|---|---|---|
| 410 | 29.2 µs | 13.6 µs | **2.15×** |
| 1610 | 124.7 µs | 56.0 µs | **2.22×** |

修法：新增三个**单通道**入口 `lsp_hover()` / `lsp_completion()` / `lsp_inlay()`（都是 `clone`，
零额外逻辑），`src/lib.rs` 的三个单请求路径改走它们；`lsp_surface()` 保留给需要多通道的
调用方（goto / references 扫全表）。

## 9. example 实测（baseline vs 现在）

### 9.1 `l13bench --file`（bench 口径，core prelude，7 轮 × 3 次取最小）

| example | baseline | 现在 | 变化 |
|---|---|---|---|
| typeclass_complex | 48.8 ms | **47.5 ms** | −2.7% |
| theorem_proving | 51.5 ms | **49.8 ms** | −3.2% |

（`alu` / `hdl_ops` 需要 HDL prelude，core 口径下 prelude 阶段就失败，不参与对比。）

### 9.2 HDL prelude（`--with-prelude hdl`）

| example | baseline | 现在 | 变化 |
|---|---|---|---|
| alu | 4574.0 ms | 4619.8 ms | +1.0% |
| hdl_ops | 4721.2 ms | 4724.8 ms | +0.1% |

（HDL prelude 的 ~4.6 s 是**固定成本**（1396 decls），不是观察面引入的；见
`docs/l13-hdl-prelude-cost-2026-11-20.md`。）

### 9.3 LSP 路径（`typort check` 的 infer 相位，3 次取最小）

| example | baseline | 现在 | 变化 |
|---|---|---|---|
| alu | 116.5 ms | **114.7 ms** | −1.5% |
| typeclass_complex | 44.4 ms | 44.6 ms | +0.5% |
| theorem_proving | 28.7 ms | 29.9 ms | +4.2% |
| adder_proof | 345.7 ms | 346.9 ms | +0.3% |
| hdl_ops | 606.1 ms | 607.3 ms | +0.2% |

全部在 ±4% 内，且这是**含进程启动 + prelude 装载**的端到端口径。

## 10. 结论（第二轮）

| 项 | 判定 |
|---|---|
| 源码注解渲染 | **O(k) → O(1)**（K=10000 时 7000×），各 example 均有小幅**提升** |
| 单通道 API | 修掉 2.15–2.22× 的回退，回到「只付一张表」 |
| `clear_observation_tables` | 范围修正为 3 张显示表 + `decl_shapes`（正确性） |
| 端到端 | **±4% 内**，无系统性回退 |

## 11. 第三轮：整表克隆 → 借用扫描

### 11.1 先量清楚「谁在克隆」

| 路径 | 原先做什么 | 是否真的需要整表 |
|---|---|---|
| hover | `hover_entry_owned` → `hover_entry_at`（**只取赢家**） | 否，早已是单条目 |
| goto | `hover_entries_owned()` 克隆整表 → 自己扫 | **否** |
| inlay | `inlay_entries_owned()` 克隆整表 → 自己遍历 | **否** |
| completion | `completion_entries_owned()` 克隆整表 → 自己过滤 | **否** |

先验证 hover 的扫描成本（探针 G）：

| 表条目 | `hover_entry_at` 每次查询 |
|---|---|
| 410 | 0.00 µs |
| 1,610 | 0.00 µs |
| 6,410 | 0.01 µs |
| 25,610 | 0.04 µs |

**≈ 0**（`contains` 是两次整数比较，`min_by_key` 只维护一个槽）。所以 hover 不需要改。

再量真实 example 的表规模（探针 I）：

| example | hover 条目 | 查询 | **克隆整表** |
|---|---|---|---|
| alu | 320 | 0.00 µs | **13.2 µs** |
| typeclass_complex | 927 | 0.01 µs | **36.2 µs** |
| theorem_proving | 1,156 | 0.00 µs | **43.4 µs** |
| hdl_ops | 1,807 | 0.01 µs | **74.8 µs** |

克隆比扫描贵 **3–4 个数量级**。合成放大后（探针 H）：

| 表条目 | 克隆+扫 | 借用扫 | 倍数 |
|---|---|---|---|
| 1,610 | 57.5 µs | 0.77 µs | **74×** |
| 6,410 | 223.9 µs | 3.58 µs | **63×** |
| 25,610 | 1,084.8 µs | 13.9 µs | **78×** |

### 11.2 修法：借用式访问器

新增三个闭包式入口（`src/lib.rs`）：

```rust
fn with_hover_entries<R>(&self, uri: &str, f: impl FnOnce(&[(Span, Span, String)]) -> R) -> Option<R>
fn with_inlay_entries<R>(&self, uri: &str, f: impl FnOnce(&[(u32, String)]) -> R) -> Option<R>
fn with_completion_entries<R>(&self, uri: &str, f: impl FnOnce(&[(Span, SmolStr)]) -> R) -> Option<R>
```

三者都只取一次 `DashMap` 读锁、把借用交给闭包，**不克隆任何条目**。goto / inlay / completion
三条路径改为在闭包里扫完、只带出真正需要的结果（goto 只带出赢家的两个 span，inlay 只带出
逐条的 `InlayHint`，completion 只 push 命中的项）。

`hover_entries_owned()`（公开 + 测试用）保留：内部改为 `with_hover_entries(uri, |t| t.to_vec())`，
语义不变。

### 11.3 过程中踩到的语义坑

goto 的原始逻辑是：

```rust
let hover_entries = self.hover_entries_owned(uri)?;   // 表缺失 → 整体返回 None
let interval = hover_entries.iter()....and_then(...);  // 无赢家 → interval = None
if interval.is_some() { return interval; }
self.goto_macro_definition(uri, offset)                 // → 宏回退
```

我第一版写成 `self.with_hover_entries(...)??`，**把「无赢家」也当成「整体失败」提前返回了**，
于是 `goto_module_macro_full_path_keeps_fallbacks` 挂了（光标落在宏调用里、语义表无条目时应
走第 3 步宏回退）。修正为：

```rust
let winner = self.with_hover_entries(uri.as_str(), |entries| { ... })?;  // 只让「表缺失」短路
let Some(winner) = winner else { return self.goto_macro_definition(uri, offset); };
```

区分了「表不存在」与「表里没有命中」这两种 `None`。

### 11.4 门禁

| 套件 | 结果 |
|---|---|
| `hover_tests` / `hover_stress` | 20 / 1 |
| `lsp_protocol_robustness` / `r9_lsp_probes` | 11 / 30 |
| `macro_goto_tests` | **10**（修正语义坑后） |
| `twin_engine_tests` | 28 |
| `lib L13_namespace` | 622 |
| `l07_source_render` / `l08` / `l12` surface | 77 / 88 / 91 |
