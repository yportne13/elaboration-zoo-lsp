# A 稿：L13 性能版（twin）性能现状与剩余优化空间

> 任务：`task-1`（owner `perf-hotpath`）。产出范围仅本文件。
> 分析轮日期：2026-09-27。主线当时正在改 `src/L13_namespace/mod.rs`、
> `legacy_tests.rs`、`src/prelude/hdl/*.typort`、`docs/hdl-*.md`、
> `src/L13_namespace/hdl_*_tests.rs`，本稿全程只读。

## 0. 证据分层与口径声明（先读这一节，否则下面每个数字都会读错）

本稿的每个数字只有三种来源，正文逐条标注：

- **[文档]**：引自仓库既有文档（附 `文件:行` 或小节号与日期）。
- **[代码]**：我自己 `read`/`grep` 到的代码坐标（附 `文件:行`），用于交叉验证文档结论。
- **[推断]**：无直接数据，由代码结构或算术推出，给出推导过程与证伪条件。

**本轮我一项实测都没有做**（遵守 lead 的硬约束：不跑 `cargo`、不运行
`target/release/*.exe`；`perf-measure` 队友在做实测）。因此「我自己量到的数字」
= **0 项**；我的增量价值是：把已有文档结论逐条落到代码坐标、找出文档与代码不一致处、
给出可验证的量化结构与排序。凡我无法用代码或算术支撑的文档数字，一律留在 A5。

**两个已知的口径偏差，贯穿全稿：**

1. **bench 口径的时点偏差**：仓库里最新的全量矩阵是
   [bench-matrix-2026-09-20.md](../../bench-matrix-2026-09-20.md)（工作区 `e36b76b`），
   它在 twin 的 09-22 / 09-23 / 09-23b / 09-24 / 09-25 / 09-26 六轮优化**之前**。
   所以矩阵的 `fast`/`fast_ss` 列整体低估了今天的 twin；同时
   [perf-l13-round-2026-09-22.md](../../perf-l13-round-2026-09-22.md) §2.7 修掉了
   **参考版的 bench 口径测谎偏差**（参考版 `bench_check_nf_bounded` 漏 `force_memo_clear`，
   修复后 struct k=11 basic −19%、prelude-core −30%），即矩阵里 `basic` 列在
   这两个负载上偏慢。**结论：矩阵里任何 twin/ref 比值都不能直接当今天的结论用。**
2. **二进制 vs 源码 HEAD 偏差**：[l13-perf-replace-2026-09-27.md](../../l13-perf-replace-2026-09-27.md)
   §6 记录 `target/release/*.exe` 构建于 2026-09-26 19:47–19:56（≈ `804c4dd`，
   正好是摊平链轮的收尾提交），之后主线提交了 HDL 特性/文档
   （`d416c3c`/`3a08b88`/`ede8773`/`5d710ea`/`52ba09b`）且有 682 行未提交改动。
   **twin 内核未动，但 HDL prelude 变了** ⇒ 用现成二进制测出的 prime 段与
   绝对墙钟，与源码 HEAD 不是同一份输入。

---

## A1. 现状盘点：twin vs 参考版在各负载族

### A1.0 归属现状（决定"哪个引擎在跑"）

- LSP 默认走 twin（`Engine::lsp_default`，[文档] replace-09-27 §1.2，
  `src/lib.rs:255-260`）；通用构造 `Backend::new` 默认参考版
  （`Engine::from_env`，`src/lib.rs:276-281`）⇒ **`cargo test` 与 CLI `check`
  的默认引擎仍是参考版**（[代码] `src/bin/cli.rs:684-707` 显式
  `Engine::Reference`，[文档] replace §1.2）。
- 实例归属：`Backend::twin_can_own`（[代码] `src/lib.rs:1398-1402`）要求
  `engine==Twin` 且该文件**无 import**（`file_deps`）且**未声明 package**
  （`file_namespaces`）。语料内 30 个 `examples/` 文件里 **29 个 twin 接管**、
  唯一回落是 `18-utils`（`untrusted-error`）（[文档]
  [lsp-twin-wiring-2026-09.md](../../lsp-twin-wiring-2026-09.md):1745-1751）。

### A1.1 bench 口径（`l13bench`，basic = 参考版，fast_ss = twin 稳态）

[文档] [bench-matrix-2026-09-20.md](../../bench-matrix-2026-09-20.md) §3.2
（2026-09-20，工作区 `e36b76b`；`enum`/`gadt`/`moduletree` k=9，其余 k=11）：

| 负载 | basic (ms) | fast_ss (ms) | ref/twin | 今天还成立吗 |
|---|---|---|---|---|
| church | 5.763 | 0.949 | 6.1× | 量级成立；twin 侧 09-22/23 有改动 |
| natadd | 6.595 | 0.867 | 7.6× | 量级成立 |
| gadt | 0.430 | 0.225 | **1.9×** | 薄边际；绝对值亚毫秒 |
| strchain | 4537.050 | 8.739 | 519× | 参考版这一格是 O(n²) 病态，不代表 twin 好 |
| match | 0.215 | 0.172 | **1.2×** | 薄边际 |
| enum | 0.527 | 0.291 | **1.8×** | 薄边际 |
| struct | 7490.110 | 13.187 | 568× | **两侧都变了**：basic 被 09-22 §2.7 测谎修复拉快 ~19%，twin 09-23 又改过 |
| moduletree | 0.187 | 0.133 | **1.4×** | 薄边际；09-22 §1 报 moduletree twin +49.6% |
| prelude-core | 17.822 | 8.261 | 2.2× | **basic 被测谎修复拉快 ~30%** ⇒ 真实比值显著低于 2.2× |
| prelude-core-show | 19.772 | 8.888 | 2.2× | 同上 |
| prelude-hdl | 3073.083 | 1331.941 | 2.3× | twin 侧 09-23 §2 报 −11.1%（fast） |
| examples-hdl | 17.714 | 8.203 | 2.2× | twin 侧 09-22 §1 报 +2~9% |

**四个薄边际格（match 1.2× / moduletree 1.4× / enum 1.8× / gadt 1.9×）与
内存口径的"反转格"是同一批**：[文档]
[mem-l06l13-2026-09-21.md](../../mem-l06l13-2026-09-21.md) §5 三类形态之 3
给出 `match`/`enum`/`gadt`/`moduletree` 的 **bytes 比 0.21×–0.69×**（twin 比参考版
**更费内存**），原因是 twin 的固定成本（1MB 初始 chunk + `Machine` 1536B 里的 20+
张常驻表，[文档] 同文 §2.1/§2.2；[代码] `src/L13_namespace/bump_spine_iter/machine.rs:100-109`
的三档 `ReclaimOnClear` 阈值）。⇒ 这四个格的"打平"是**结构性的**：twin 的
启动/固定成本与小 Box 树参考版同量级，再优化空间在亚毫秒级，优先级应低。

### A1.2 LSP kick 口径（`bench_examples_per_file_by_engine`，30 个 examples）

时间线（全部 [文档]；口径有两次变化，我标注了）：

| 日期 | 事项 | 数字 | 出处 |
|---|---|---|---|
| 2026-09-23 | HDL 自检闸撤除（21 文件从参考版转 twin）；**闸撤除前**已实现成本 | 18,461 ms（0.93×） | wiring:1530-1536 |
| 2026-09-23 | **闸撤除后**：参考列 19,918 / twin 列 12,416 / 已实现成本 11,281 ms | **1.64×** | wiring:1530-1536 |
| 2026-09-24 | `declb_of` 多条目缓存修复后，全 30 示例总比 | **1.78×** | wiring:1648-1649 |
| 2026-09-24 | 30 文件 twin 稳态 kick 合计（叶子快路径 + SumDataV 惰性分配） | 10,598 → 10,048 ms（−5.2%） | round-23 §9.3 |
| 2026-09-25 | 同上，以 10,641 为新基线（`FORCE_PRIM_MEMO`） | 10,641 → **9,518 ms（−10.6%）** | round-23 §11.2 |
| 2026-09-26 | 摊平链轮（tree 宏 `this._res` / Phase-B 消重 / App 臂实参跳过）：3 个文件 | 01-basics 180→101、09-hierarchy 150→82、**20-misc 1878→906** | chain-09-26 §5 |
| 2026-09-26 | **30 文件总量** | **文档未复测** | —— |

[推断] 由 09-25 的 9,518 ms 减去摊平链轮三个已测文件的差
（−79 −68 −972 = −1,119 ms），当前 30 文件 twin 总量应落在
**≈8.3–8.5 s**；这只是算术外推，未复测，见 A5-1。

单点：

- **18-utils 0.74×（3.9 s，占 twin 总量约 39%）**：不是 twin 自身慢，而是
  `untrusted-error` 回落导致 **twin 跑一遍 + 参考版再跑一遍**，twin 段实测约 2.4 s
  （[文档] round-23 §9.5.1）。机制在代码里可见：[代码] `src/lib.rs:2338-2344`
  （`twin_elaborate` 返回 `false` → `elaborate_reference(.., None)` 重跑），
  分类器在 [代码] `src/lib.rs:1534-1562`。
- **adder_proof**：2026-09-23 曾是全语料唯一 twin 远慢的文件（0.34×），
  2026-09-24 修 `declb_of` 后 **1.88×**（[文档] wiring:1640-1649）。
- **HDL 主力文件 2.7–4.1×**（09-hierarchy 4.10×、05-bool 3.71×、03-bitwise 3.58×、
  13-adder-tree 3.47×）（[文档] wiring:1535-1536）。
- **不降反升的 3 个文件**：adder_proof +2.8%、theorem_proving +0.6%、
  typeclass_complex +2.2%，全是**不使用 HDL 模块路径的证明文件**——prim 结果缓存
  对它们无事可做，差异在噪声带（[文档] round-23 §11.2）。

### A1.3 三色分类（twin 更慢 / 打平 / 未验证）

**twin 仍然更慢（唯一一格）**

| 格 | 比值 | 根因状态 |
|---|---|---|
| LSP `18-utils` | 0.74× | **double-pay**（twin 跑完被信任闸否掉，参考版重跑）。twin 段本身约 2.4 s，比参考版快；见 A3-1 |

**打平（twin 领先 <2×，收益空间薄）**

| 格 | bench 比值 | 备注 |
|---|---|---|
| `match` k=11 | 1.2× | 亚毫秒；且内存反转（0.21×） |
| `moduletree` k=9 | 1.4× | 亚毫秒；内存反转 |
| `enum` k=9 | 1.8× | 亚毫秒；内存反转 |
| `gadt` k=9 | 1.9× | 亚毫秒；内存反转 |
| `prelude-core` / `prelude-core-show` | 2.2×（**虚高**） | basic 列 09-22 §2.7 被拉快 30%，真实边际更薄 |
| 证明类文件（adder_proof / theorem_proving / typeclass_complex） | 1.6–1.9× | prim 缓存无用武之地；[文档] wiring:1640-1649 + round-23 §11.2 |

**未验证（本轮无数据）**

| 项 | 缺什么 |
|---|---|
| bench 口径**全部 12 格**在今天 HEAD 上的比值 | 矩阵早于六轮优化（见 §0.1） |
| 摊平链轮后的 30 文件 LSP 总量与 1.78× 语料比 | 文档只有 3 个文件的数（见 §A1.2） |
| `prelude-hdl` 的 LSP kick 段（955→958 decls 的 prelude） | 主线正在改 prelude，且新二进制无对应 prelude |
| `wide_enum` k=4/6/9/11 | 只有 09-23b §2.1 的 bench 数（1,328.7 ms @k=11），没有 LSP 口径 |
| L10/L11/L12 等邻层 | 超出本稿范围，但矩阵里 L11/L12 的 `basic` 列是全流程 `run`（含 parse+pretty），[文档] mem-l06l13 §1 表注——**跨层比较时不要用** |
| `strchain`/`global` 的今日 twin 值 | 09-21 之后 twin 侧有改动（A2.6 指出文档归因与代码不一致） |

---

## A2. 成本模型：一个 LSP kick 的钱花在哪

### A2.1 模块 class 摊平链：一个 kick 内被求值几遍

**结论（[文档] chain-09-26 §4/§6，[代码] 交叉验证）：今天剩 3 遍。**

| 遍 | 存在理由 | 代码坐标 |
|---|---|---|
| ① Phase-A 检查 | class 体每个 item 的 check/infer 必须跑（否则拿不到字段类型、算不出 `PrecheckedItems`） | [代码] `machine.rs:4456`（Class 臂）、`:4460`（phase A 起点）、`:4545-4591`（逐 item `quote`/`export`/指针导入表登记） |
| ② Phase-B `create` 检查实跑 | `expand_class_decls` 生成 struct/create/impl/tree 后**逐个当普通 decl 再 `infer_after_prefix` 一遍** | [代码] `machine.rs:4592-4627`（`expand_class_decls` → `for dd in decls { infer_after_prefix }`） |
| ③ 用户 `X.create` 调用 | 用户源码里的调用点必须求值 | [文档] chain-09-26 §1 a3（"用户 create 调用 12.3%"） |

历史形态与已消掉的 3 遍（顺序倒推）：

- **6 遍 → 4 遍（[文档] chain-09-26 §4）**：一次
  `println(moduleTreeVL(X.create.tree))` 曾跑 6 遍 = tyck 期 4（Obj 臂接收者 eval ×1 +
  App 臂逐层实参 eval ×2 的 create 链 + 1 tree 链）+ println nf 期 2（必要）。
  修法：`binder_occurs` 深度感知扫描——余定义域不引用 binder 就不为类型检查
  eval 实参（[代码] `machine.rs:58-84` 定义，`:2457-2458` 与 `:3278-3279` 两个 App 臂调用）。
- **Phase-B 弃结果 eval 双跑（[文档] chain-09-26 §3）**：twin `check` 的 `Raw::Tm` 臂曾有一句
  弃结果的 `let _ = self.eval(.., tm)`（参考版 `39b5d79` 引入的），而外层 Let 臂立即对
  同一 tm 同 env 再 eval 一遍。已删，理由与副作用幂等论证逐条写在
  [代码] `machine.rs:1618-1632`。
- **tree 宏改造（[文档] chain-09-26 §2）**：`def tree: ModuleTree = this._res`——读 create 时
  捕获的模块树，不再整链重放。代码里在四处：
  [代码] `src/prelude/hdl/hdl-macros.typort:177`（简版）与 `:590`/`:626`/`:660`（另三种形态）。

**每遍的定价（[文档] chain-09-26 §1，宏级 stub 因果 A/B，25 个 examples/hdl，逐 decl 合计）**：

| 变体 | 内容 | 合计 | 差值归因 |
|---|---|---|---|
| a0 | HEAD 基线 | 7172 ms | —— |
| a1 | + `moduleTreeVL`/`allModulesVL` 体 stub | 6990 ms | Verilog 生成仅 2.5% |
| a2 | + 三臂 `def tree` 体 stub（tree 链全消） | 4535 ms | **tree 侧 34.2%**（大头在 class 声明内部的 tree def 检查期求值） |
| a3 | + 顶层 `X.create.tree` 调用点换空树 | 3655 ms | **用户 create 调用 12.3%** |

即：**08-26 之前，两次额外求值的可测部分合计 46.5%**，保守下界（Phase-B
create-def 检查期重求值未含）。落地三项后剩余 3 遍的成本结构仍是
"单条模块 class 声明吃掉 kick 的 68-85%"（[文档] round-23 §9.1.3，21-crossclock
i=2 = 1.9–3.1 s / 2.8 s kick，363–484 MB arena）。

**长期方案已裁决不做**（[文档] chain-09-26 §6）：把 ModuleTree 下沉 Rust prim 只降
每遍单价 ~6-18%（中心 ~10%），**消不掉遍数**，12-18 人天不划算。三个触发器二选一：
自检阶段 2 立项，或 `string_to_global_type` meta 家族/三明治红线再次咬人。

### A2.2 arena 每 kick ~850 MB 中间分配

[文档] round-23 §9.5.3（2026-09-24，20-misc/24-verilog 实测）：
**每 kick 涨到 908 MB → 压实回 181 MB**，`compact_resident` 因此从 0.1 ms 涨到
**150-190 ms**；且"调大 `TYPORT_TWIN_BUMP_BUDGET_MB` 不改善墙钟（2.85 s vs 2.86 s）"
⇒ **压实本身不是主要成本，真正的量是每 kick 的 ~850 MB 中间值分配**。

同族数据点（[文档] wiring:1660-1670，adder_proof 修复前）：hdl prelude 下
单次 kick 的 bump chunk 容量达 **3842 MB**（core 1016 MB），其中
`vec_adder_correct` 一条声明就分配 **2055 MB**（core 449 MB），而 force 计数逐位相同
（1,734,362）——**分配次数相同、每次分配更大**，真身是 `declb_of` 单条目缓存
100% 抖动导致的每调用 O(D=1416) 整表重建（该文件 27,837 次重建 ≈ 1.7 GB/kick）。
这条**已修**（A3-2），所以"每 kick 850 MB"这个数**必须重测**（A5-2）。

按代码可以定位中间分配的来源（[代码]）：

| 来源 | 代码坐标 | 量级 |
|---|---|---|
| spine 链纯 prim 结果（`string_concat` 每次 2 次 bump 分配：`alloc_layout` + `alloc(XCell::Lit)`） | `prim.rs:499-517` | [文档] round-23 §10.1：21-crossclock 3.32M 次 spine 链/kick，`string_concat` 2.79M（84%），≈84 MB/kick |
| `declb_of` 存根表重建（**已修**：`DECLB_CACHE_ENTRIES = 4` FIFO） | `force.rs:236-251`、`:597` | 1.7 GB/kick → 现在应为 O(1) 次 |
| `PatternDetail::Con` 子 Vec 移进 bump 后永不 Drop（**未修**） | [文档] round-23b §5 残留尾巴 | wide11 2.36 MB/轮、match 4.6 KB/轮 |
| 压实期 `Copier` 的 15 张 memo 表每次新建（**未修**） | `compact.rs:33-77`、`:593` | [文档] round-23b §5（B）"机会在 Copier 15 张 memo 表跨压实复用" |

### A2.3 spine 链：2.79M 次 force / 33× 重入，及其残余成本

[文档] round-23 §10.1（2026-09-25，21-crossclock 单 kick，force 入口按 tag 细分）：

| 桶 | 调用数 | 占比 |
|---|---|---|
| 纯 WHNF 叶快路径 | 11,895,020 | 74.1% |
| **叶 → `force_inner`（tag-2 spine 链）** | **3,319,196** | **20.7%** |
| 复合（SumCase/Call/Obj，memo 覆盖） | 830,934 | 5.2% |

其中 99.95% 是 `HK_DECL` 头（3,318,363/3,319,196）；按名 Top：
`string_concat` 2,792,202（84%）、`nat_to_dec` 383,620、`str_eq` 77,928、`nat_add` 64,269
——全部在 `prim_is_pure` 白名单内（[代码] `force.rs:442-456`）；
**只有 99,476 个不同链 → 33× 重入**（最大单链 16,915 次）。

**§11 的 `FORCE_PRIM_MEMO` 已落地**（[代码] `force.rs:702-720`）：在 `HK_DECL` 臂
**实参 force 之后**按 `(pid_code, 已 force 实参打包字列)` 查内容键表，命中直接返回。
收益 [文档] round-23 §11.2：30 文件 10,641→9,518 ms（−10.6%），20-misc −24.2%、
21-crossclock −22.9%。两次判负的坑（按下标当键 / 入口早退跳过实参 force）已固化成
[代码] 注释 `force.rs:505-521`。

**残余成本（[代码] 结构确定，量级待测）**：即使 memo 全命中，每次进入
`HK_DECL` 臂仍要付：

1. `args.clear()` + `collect_args` + `args.reverse()`（复用主栈，无分配，[代码] `force.rs:686-688`）；
2. **逐实参 `force` 一遍**（语义必需，§10.3 的红线，[代码] `force.rs:699-701`）；
3. **键构造 `collect::<Vec<u64>>()` 每次调用一次堆分配**（[代码] `force.rs:711-715`）；
4. `FxHashMap<(u8, Vec<u64>), V>` 的一次哈希（哈希的是 Vec 内容）。

第 3 条是**当前唯一明显可零成本消除的分配**：按 09-25 口径 3.32M 次/kick、
2.79M 次属于 `string_concat`，每次一次 `Vec<u64>`（2 元素 = 16 B 载荷）。
按 20-50 ns/次估 ≈ **56-140 ms / 2.8 s kick（2-5%）**，且这**不受 memo 命中率影响**
（键必须先构造才能查表）。**注意**：3.32M 这个数是摊平链轮（09-26）之前测的，
tree 链改造后需要重测（A5-3）。

### A2.4 `compact_resident` 150-190 ms 的内容分解

调用点：`observe_user` 入口，用户段 arena 增量 > 预算时（[代码] `entry.rs:1147-1171`），
预算默认 `RESIDENT_BUMP_LIMIT = 512 << 20`（[代码] `entry.rs:799`）。对
20-misc/24-verilog 这类文件**每 kick 触发一次**。

`compact_resident`（[代码] `entry.rs:1059-1107`）做四件事：

1. `compact_state(cxt, cap_hint)`——`Copier` 从旧 arena 深拷可达状态到新 arena
   （[代码] `compact.rs:593`、`:33-77`；[文档] round-23b §5（B）实测 ~41 MB/次拷贝、
   每次 prime 32 次就地压实、1.28 GB 流量换 −1.99 GB 常驻）；
2. `force_memo_clear()` + `conv.memo`/`scratch1`/`scratch2` 归还 + `ren.reset()` +
   `ns_method_cache = None`（[代码] `entry.rs:1084-1091`）⇒ **跨压实所有 memo 变冷**；
3. **重建 `Resident` 检查点：把 7 张 owned 表 + `metas` 整个深克隆一遍**
   （[代码] `entry.rs:1092-1106`）；
4. 调用方接着 `defs.truncate` / `spine.stack.reclaim` / 观察表 clear+reclaim
   （[代码] `entry.rs:1179-1192`）。

[文档] round-23 §9.5.3 的 `restore(clones)` 计时区间是 `kick_t0 → restore_done`
（[代码] `entry.rs:1142-1144` 起、`:1204` 止、`:1385-1395` 打印），**包含**上面第 1-3 步
与 `clone_cxt`，所以"0.1 ms → 150-190 ms"这个变化量主体就是压实。

**我自己的代码级发现（见 A4 #2）**：第 3 步的深克隆**没有任何生产消费者**。
`Resident` 的 7 张表 + `metas` 的**唯一读点**是 `TYPORT_KICK_PROBE` 门控的自检断言块
（[代码] `entry.rs:1311-1384`），`r.metas` 连断言都没读（我 grep 过 `entry.rs` 里所有
`r.<field>` 读点：`cap_hint`/`cxt`/`defs_len`/`base_keys`/`base_bytes` 在
`:1064-1208`，其余全在 `:1313-1383` 的 probe 块内）。kick 末的恢复已改为
journal 撤销（[代码] `entry.rs:1300-1305`），`Resident` 的那份快照在
[代码] `entry.rs:777-779` 的注释（"每 kick 恢复"）里还留着旧设计的说法。

### A2.5 观察面成本（三个口径必须分开读）

| 口径 | 结论 | 出处 |
|---|---|---|
| **bench**（`L13BENCH_NOBSERVE=1` 消融） | prelude-core **39-41%**、prelude-hdl **19.0%**、wide_enum k=6/9 **54-59%**、k=11 15-21% | [文档] round-23b §3 |
| **bench 的 prelude 段** | 是**假象**：`prime_resident` 显式 `observe=false`（[代码] `entry.rs:903`），装载期 push 被总闸挡掉（[代码] `observe.rs:36-38`、`:85-87`、`:111-113`） | [文档] round-22 §3.1 |
| **LSP 用户段**（`TYPORT_TWIN_NO_USER_OBSERVE`） | 20-misc 2807 vs 2827 ms、18-utils 6258 vs 6226 ms ⇒ **噪声内** | [文档] round-23 §9.1.2，开关在 [代码] `entry.rs:1132-1134` |
| **单文件 proof 形态** | adder_proof **~216 ms/kick**（关 `machine.observe` 对照，修复前口径） | [文档] wiring:1550 |

**结构（为什么两个口径不矛盾）**：push 期就渲染定稿是**跨引擎契约**
（[文档] `src/L13_namespace/README.md:251-256`）：`push_hover` 走
`quote → types_names_list → export → pretty_tm`（[代码] `observe.rs:26-45`）——
每次 push 一次整值 quote + 一棵 `Rc<CTm>` 导出树 + 一个 `String`。
条目数与渲染量成正比，所以：

- examples 语料（小文件、观察条目少）⇒ 噪声内；
- adder_proof 这类"声明少但类型巨大"的 proof 文件 ⇒ 每 kick 十几到几十万条 ×
  quote+export+pretty（[文档] round-23 §5：hover_table struct 24605 条/轮、
  strchain 16382 条/轮，bench 口径）。

已有两个局部洞：`push_hover_cached` 在 `typ_pretty_final` 时直推缓存串
（[代码] `observe.rs:63-68`）、`push_ctor_hover` 的 `ctor_hover_memo`
（[代码] `observe.rs:88-98`，[文档] README §3.2 实测每 Con 模式 ~0.5 µs）。
**没有洞的是 def/局部变量的普通 `push_hover` 路径**，那才是延迟渲染的兑现面。

### A2.6 一项文档与代码的不一致（影响 A4 排序）

[文档] [mem-l06l13-2026-09-21.md](../../mem-l06l13-2026-09-21.md) §3.3(a) 与
[mem-l13-opt-2026-09-21.md](../../mem-l13-opt-2026-09-21.md) §3.5 都称
"**L13 的 `string_concat` prim 仍是堆 `String`**，churn 8.87 MB/轮"，
并把"arena 化"列为待做项。**代码里不是这样**：

- twin：`PrimId::StringConcat` 直接 `bump.alloc_layout` 写 arena，再
  `bump.alloc(XCell::Lit(s))`（[代码] `bump_spine_iter/prim.rs:499-517`）——**零堆分配**；
- 参考版：`format!("{x}{}", b.data)`（[代码] `src/L13_namespace/cxt.rs:329-337`）——**每 concat 一个堆 String**。

而 [文档] mem-l06l13 §3.3(c) 又把同一组数字（86,696 allocs / 8.87 MB）归因给
"decl 表与索引的每轮重建"。(a) 与 (c) 不可能同时为真。结合代码，**L13 twin 的
strchain churn 应记在 (c)（decl 表/后缀索引/观察表重建）名下**，(a) 的 L13 行是错的
（或原本说的就是参考版列）。⇒ 影响：mem 文档"strchain/global arena 化可省
26% 分配器滞留"的收益估计对 **L13 twin 不成立**（对它成立的是参考版与 L06-L08）。

---

## A3. 单点异常逐项根因状态

### A3-1 `18-utils` 的 untrusted-error double-pay —— **未修；根因已换过一次基线**

- **症状**：twin 段 ~2.4 s + 参考版回落段 ⇒ 合计 3.9 s、0.74×（[文档] round-23 §9.5.1）。
- **机制（[代码] 已核实）**：`twin_elaborate` 跑完、诊断被信任闸否掉后返回 `false`，
  `elaborate_with` 紧接着 `elaborate_reference(uri, text, version, None)` **重解析+重跑**：
  [代码] `src/lib.rs:2338-2344`；闸的判据在 [代码] `src/lib.rs:1534-1562`
  （只信 `can't unify…` 与"确实未定义的名字"，其余一律 `untrusted-error`）。
- **历史定位（两个阶段，务必分开读）**：
  1. 2026-09-11：twin 用户段 `fresh_meta` **+289 次（1.37×）**，多出的 46 个 trait 洞中
     `LetNamed` 那条在 `mv >= m` 扫描里递归求解失败（[文档] wiring:589-613，
     逐 decl 计数表在 `:593-602`）。当时结论：**结构性、非单点补丁**。
  2. 2026-09-14：查出真因之一是 **`tm_refs_bn` 索引换算式写反**（`depth + i == bind_idx`
     应为 `ix == bind_idx + depth`），导致复用门恒真、tree/create 方法体整链重推；
     修后 18-utils 用户段 net meta 982→**680**（参考版 733，twin 反而更少），
     代价是 twin +15%/+30%（[文档] wiring:983-1048）。**该修复在代码里**
     （[代码] `machine.rs:4932-4965` 的 `go()` 用 `i + d`；注释 `:4941-4942` 明说
     "18-utils 隐参分叉的根因"）。
  3. **但假 `solve trait failed: LetNamed` 仍在** ⇒ 18-utils 继续回落
     （[文档] wiring:1041-1045：分叉机制需按新基线重新定位，`solve_multi_trait_ref`
     的 `mv >= m` 索引扫描对 meta 编号敏感）。
- **状态：未修**。下一步是**逐 decl 的 `insert_go`/`fresh_meta` 调用计数对照**
  （两版同一 decl 的计数差即定位点）——[文档] 的处置建议是"单独立项、保持现状"
  （correct but not accelerated）。详见 replace-09-27 §5.2 的 R2（3-5 人天）。

### A3-2 `adder_proof` 类证明负载 —— **已修（2026-09-24）**

- 根因：`declb_of` 的 decl 存根表缓存**只有单条目**，在 Match/Match 密集的证明上
  被多个 decl 表实例交替访问打成 100% 抖动；键是 `(decl 表地址, len)`，
  Match/Match unify、quote、rename 交替用多个 COW `Rc<Decls>` 实例，
  `Rc::make_mut` 重分配即换地址。计数：44,757 次调用 / **27,837 次重建** /
  2,100 万条目/kick ≈ **1.7 GB/kick**，参考版同窗口 0 次
  （[文档] wiring:1667-1674；[代码] `force.rs:236-251` 的注释把同一组数字固化）。
- 修复：`RefCell<Option<..>>` → `RefCell<Vec<..>>`，`DECLB_CACHE_ENTRIES = 4` FIFO
  （[代码] `force.rs:250`、`:597`；轮界由 `force_memo_clear()` 清，`:410-417`）。
- 结果：hdl prelude 1534→**287 ms**、core 485→**280 ms**，与参考版比从 0.34× 变
  **1.86×**，对 prelude 规模的敏感度 3.16×→1.02×（[文档] wiring:1640-1649）。
- 顺带证伪的四条（**别再重走**）：decl 表 `Rc::make_mut` 深拷贝（37 次 × ~30 µs ≈ 1 ms）、
  `trait_metas` 全表扫描（LSP kick 口径只 193 次调用）、实例候选全表扫描
  （`idx_calls`/`fullscan_calls` 两 prelude 完全相同）、`FORCE_MEMO` 表大小
  （[文档] wiring:1587-1599、:1699-1703）。

### A3-3 大文件（20-misc / 24-verilog-practice）—— **未修，根因定性到"每 kick 中间分配 + 每 kick 压实"**

- 现状：摊平链轮后 20-misc 906 ms（从 1878 ms），但 [文档] 明确
  "调大 `TYPORT_TWIN_BUMP_BUDGET_MB` 不改善墙钟（2.85 vs 2.86 s）"⇒ 压实不是主因，
  ~850 MB/kick 的中间值才是（round-23 §9.5.3）。
- 代码侧可确认的机制：单条模块 class 声明 68-85% 的 kick（A2.1）、
  spine 链 3.32M 次/kick 的 prim 结果分配（A2.3）、压实每 kick 一次
  （`RESIDENT_BUMP_LIMIT=512MB` 被 908 MB 越过，A2.4）。
- **状态：未修，且没有比"降每遍单价"更近的路**——chain-09-26 §6 已裁决
  ModuleTree 下沉不做（消不掉遍数）。可动的只有 A2.4 #3 与 A2.3 #3 这两处
  "结构性白付"。

### A3-4 match 密集负载 —— **分层状态：值层已证伪、编译层已修、残留是数据结构**

| 层 | 状态 | 证据 |
|---|---|---|
| 值层 `eval_aux` 宽表分派扫描（曾以为是 wide_enum 主兑现路径） | **证伪** | 只占 k=11 的 **0.4-1.4%**（k=9 2.6-8.6%）；per-node `MatchIdx` 实现完整落地后 A/B 仅 −0.2~3.4%，**未达 <3% 门槛，回退归档**（[文档] round-23b §3/§4.1） |
| 编译期 `covers` 覆盖检查 O(n³) 名字扫描 | **已修（09-23b §2.1）** | wide_enum k=11 −83.5~84.8%（12,112→1,993 ms）；窄表（构造子 <16）不建表走原口径（[代码] `compiler.rs:545-551`、`:835-892`） |
| `PatternDetail::Con` 子 Vec 进 bump 后永不 Drop | **未修** | wide11 **2.36 MB/轮**、match 4.6 KB/轮；A 方案设计已存档，预估 1-2 天（[文档] round-23b §5 残留尾巴） |
| `PatternDetail` ~128 B/臂 的 SoA 化 | **未做** | [文档] round-23 §7.2 列为同族结构项 |
| 窄表 match 的 ~0.15 ms 地板 | **解释清楚，不动** | harness（`prime_round` + 非 match decl elaboration）+ 语义必需（体检查/特化方程）（[文档] README §5） |

---

## A4. 机会清单（按 预期收益 × 置信度 ÷ 工作量 排序）

排序原则：**先补判据，再做低风险结构性项，最后才是引擎级改动**。
每一项都给出"需要什么证据才能判定真伪"与"已被证伪的相邻尝试"。

### #1 重跑基线：bench 矩阵 + 30 文件 LSP kick（含逐文件归属）

- **内容**：以当前 HEAD（`target_l13perf` 隔离构建）重跑 `l13bench --workload all`、
  `--workload wide_enum`、`bench_examples_per_file_by_engine`，并输出逐文件
  `归属引擎 / fallback class / kick 墙钟`。
- **预期收益**：不直接加速，但**是 A4 其余每项的判据**——今天所有 twin/ref 比值都建立在
  早于六轮优化的矩阵上（§0.1），且 09-26 摊平链轮后没有总量。
- **置信度**：高（方法已在 [文档] round-23 §0 定稿：同源码树、同窗口交错 A/B、min-of-5）。
- **工作量**：0.5-1 人天（`perf-measure` 队友正在做，本项与其合并）。
- **判定证据**：能复现三个已知结论即判据可信——29/30 归属、18-utils 0.74×、
  1.78× 语料比（[文档] replace §5.2 的 R0 退出判据同款）。
- **已证伪的邻居**：跨窗口绝对对比（±10% 假信号，[文档] round-23 §0）；
  "多流并行下先测性能再验证"的顺序（round-23 §10.4）。

### #2 压实路径的两处"白付"（零语义风险）

- **2a（新发现，[代码] 实证）**：`Resident` 检查点每次 prime/压实深克隆 7 张 owned 表
  + `metas`（`entry.rs:1019-1033`、`1092-1106`），**唯一读点是 `TYPORT_KICK_PROBE`
  断言块**（`entry.rs:1311-1384`；`r.metas` 无任何读点）。改法：把快照改成
  probe 门控的惰性构建，或直接在 `cfg(debug_assertions)`/env 下才克隆。
- **2b（[文档] 已有）**：`Copier` 15 张 memo 表跨压实复用（每次压实新建、从 0 长起）——
  [文档] round-23b §5（B）/§7 第 3 项。
- **预期收益**：大文件每 kick 的 `compact_resident` 段（150-190 ms，占 20-misc 906 ms 的
  16-21%）里砍掉可量化的一块；2a 的量级 = 每次压实 × (7 张表深拷贝 + N_meta × 40 B)，
  表规模参考 [文档] mem-l13-opt §1.2（`Machine` 20+ 张常驻表，`tstate.solver` 桶型表
  在 prelude-hdl 下是万条级）。
- **置信度**：2a 结构确定（**中高**），量级未测；2b 中。
- **工作量**：2a 0.5 人天；2b 0.5-1 人天；两者同族可一起做。
- **判定证据**：`TYPORT_KICK_PROBE` 的 `restore(clones)` 与 `compact` 行前后对比
  （`entry.rs:1385-1395`、`:1068-1075` 已有现成探针），加 20-misc/24-verilog 的
  kick 墙钟 A/B；**必须同时跑 `twin_engine_tests`**（`TYPORT_KICK_PROBE` 断言是
  "漏埋写点"的回归网，不能因为省克隆把断言一并删掉——正确做法是断言下改成按需克隆）。
- **已证伪的邻居**：`TYPORT_TWIN_BUMP_BUDGET_MB` 调大（2.85 vs 2.86 s，无效）；
  `Copier::casesmap` 切片去重（零命中，[文档] round-23b §4.4）；
  "压实导致局部性变差"（[文档] wiring:1701）。

### #3 `FORCE_PRIM_MEMO` 键构造零分配化

- **内容**：`force.rs:711-715` 每次进 `HK_DECL` 臂都 `collect::<Vec<u64>>()` 建键。
  改法二选一：(i) TLS 复用键缓冲 + hashbrown `raw_entry`/`Equivalent` 借用查表；
  (ii) 把 `(pid_code, args)` 折叠成 u64 内容哈希 + 命中后二次校验。
- **预期收益**：09-25 口径 ≈3.32M 次/kick（`string_concat` 2.79M），
  [推断] ≈56-140 ms / 2.8 s kick（2-5%），**与 memo 命中率无关**
  （键必须先建）。对 20-misc/21-crossclock 型文件最明显。
- **置信度**：结构确定（高），量级中（3.32M 是摊平链轮之前测的，**必须重测**）。
- **工作量**：0.5 人天。
- **判定证据**：`l06l13mem` 分配计数（确定性口径，跨窗口可比）先证"每次调用一次分配"
  消失；再 `21-crossclock`/`20-misc` 同窗交错 A/B（min-of-2）。
- **已证伪的邻居（**红线**）**：§10 两次判负——按 spine 下标当键（槽位复用→错命中）、
  在 `force` 入口按链内容当键（跳过实参 force→少报 HDL001）。
  **任何改动都不得把实参 force 移出**（[代码] `force.rs:505-521` 的注释是硬约束）；
  `prim_is_pure` 只声明"结果只依赖实参"，不是"可跳过"许可证。

### #4 18-utils double-pay 消除（= replace §5.2 的 R2）

- **内容**：逐 decl 对照两版 `insert_go`/`fresh_meta` 调用点计数，把 twin 用户段
  多出的隐参创建对齐；对齐后全语料 0 `untrusted-error`，信任闸退化为恒信任。
- **预期收益**：18-utils 从 0.74× 变"twin 单跑"⇒ 语料 twin 时间砍掉 ~2.4 s；
  按 [推断] 当前总量 ≈8.4 s 计 **−25~28%**，且彻底消掉"跑两遍"这一最坏形状。
  这是 A4 里**单项收益最大**的。
- **置信度**：中（根因已换过一次基线：`tm_refs_bn` 修好后 twin 的 meta 总数
  反而更少（680 vs 733），分叉机制需按新基线重新定位）。
- **工作量**：3-5 人天（[文档] replace §5.2 的 R2 估计）。
- **判定证据**：18-utils 的 twin 段逐 decl `fresh_meta` 计数差 + `LetNamed` 求解失败
  消失（`last_kick_metas_created` 已在 [代码] `entry.rs:1298-1299` 暴露）。
- **已证伪的邻居**：`trait_metas` 全表扫描、实例候选全表扫描、`bn_refs` 单点补丁
  （已落地但没消掉症状，[文档] wiring:1041-1045）；"孪生多注册 ~20 条 trait meta"
  这个 09-11 的前提已被 09-14 的数据推翻。

### #5 观察面按请求延迟渲染（只对观察条目密集的文件）

- **内容**：`push_hover` 现在是 push 期 `quote → export → pretty` 定稿
  （[代码] `observe.rs:26-45`，契约见 README §3.1）；改成 push 期只存
  `(span, 值/decl 键)`，hover/inlay 命中时再渲染；`(path,offset)` 有序索引
  （[文档] round-23b §7 第 1 项、round-23 §7.6）。
- **预期收益**：分形态——adder_proof 型 proof 文件 ~216 ms/kick
  （[文档] wiring:1550，修复前口径）；examples 小文件**噪声内**
  （[文档] round-23 §9.1.2）⇒ 不要按 pcore 的 39-41% 上账（那是 bench 假象，A2.5）。
- **置信度**：中（收益面窄但真实；实现要动 `twin_tables` 快照从 owned String 变惰性，
  跨轮语义要重新论证）。
- **工作量**：2-4 人天（LSP 消费侧改造）。
- **判定证据**：先量**逐文件的 hover/inlay 条目数与渲染字节**
  （`TYPORT_TWIN_NO_USER_OBSERVE` 已有开关，[代码] `entry.rs:1132-1134`），
  条目数 × 单条渲染成本 = 上界；再对 top-3 文件做 A/B。
- **已证伪的邻居**："观察面是 LSP 大项"（examples 口径下噪声内）；
  `probe_accessible` 轮内缓存（命中率仅 5-6%）；
  `trait_wrap` 二次正规化（实测 ~0.5 ms/轮，真身是命中后的 `infer_expr($method x)`）。

### #6（备选）宽表残留：`PatternDetail::Con` 子 Vec 不进 bump

- 预期收益：wide11 **2.36 MB/轮** 泄漏清零（[文档] round-23b §5）；对 wide_enum
  k=11（修 covers 后 fast 1,328.7 ms）的墙钟收益待估，主要是内存与分配卫生。
- 置信度：中高（根因已栈级定位，A 方案设计已存档）；工作量 1-2 人天。
- 判定证据：`l06l13mem --workload wide_enum` 分配计数 + 泄漏探针（round-23b §2.2 的手法）。
- 已证伪邻居：per-node `MatchIdx`（<3% 门槛，归档）。

### #7（备选）基础设施：内核 tick 补点

- 内容：`compiler.rs` 覆盖循环 / `eval_aux` 入口 / `force.rs` `vapp1`+force-miss /
  `machine.rs` quote / `tm_size`（[文档] round-23b §3 优先级表）。
- 价值：今天 `Compiler::compile` 的 10 s 级区间整体被"上一个 tick 点"（eval 站点 91.8%）
  吸收；adder_proof 的定位链已证明**栈采样 + PDB 符号化**才是可靠归因工具
  （tick 口径的 self% 曾误导，[文档] wiring:1658-1662）。
- 工作量：1-2 人天；收益间接（让 #2/#3/#5 的量级可测）。

### 已经证伪、不要再做的清单（省下重走成本）

| 尝试 | 判决 | 出处 |
|---|---|---|
| spine 链 memo 第 1 版（按下标当键）/ 第 2 版（入口按链内容当键） | **两次判负，已撤销** | round-23 §10.2 |
| `trait_wrap` 二次正规化 | 证伪（~0.5 ms/轮） | round-23 §4、round-22 §3.2-1 |
| `probe_accessible` (Sum,ctor) 轮内缓存 | 证伪（命中率 5-6%，消融 \|Δ\|≤1.5%） | round-23 §4 |
| 嵌套 unify 共享 `conv.memo` | 证伪（八负载 \|Δ\|≤1%） | round-23 §4 |
| `eval_aux` 宽表 constr_idx 逐调用重建 | 证伪（we11 +9.1%、match k=12 +16~24%） | round-23 §4 |
| `MatchIdx` per-node 分派索引 | −0.2~3.4%，未达门槛，归档 | round-23b §3/§4.1 |
| size-32 草稿栈复用（三种形态） | 零收益（0% / −0.02%） | round-23b §4.3 |
| `Copier::casesmap` 切片去重 | 零命中 | round-23b §4.4 |
| `declb_of` 单条目 / `Rc::make_mut` 深拷 / `trait_metas` 全表扫描 / 实例全表扫描 | 已修或已证伪为成本 | wiring:1587-1599 |
| `TYPORT_TWIN_BUMP_BUDGET_MB` 调大 | 无效（2.85 vs 2.86 s） | round-23 §9.5.3 |
| ModuleTree 下沉 Rust prim | **现在不做**（只降单价 6-18%，消不掉遍数，12-18 人天） | chain-09-26 §6 |
| 参考版侧的移植项（后缀倒排索引等） | 与本稿目标（twin 取代参考版）**方向相反**，除非参考版要留作判据性能基线 | round-23 §7.3 |

---

## A5. 我没能验证的（诚实清单）

1. **零实测**：本轮没有运行任何二进制（约束所致），所以**没有任何一个数字是我自己量到的**。
   §A1.2 的"当前 30 文件总量 ≈8.3-8.5 s"、§A2.3 的"键构造 56-140 ms"都是 [推断]，
   证伪方式分别是重跑 sweep、以及 `l06l13mem` 分配计数 + 21-crossclock A/B。
2. **"每 kick ~850 MB 中间分配"是否还成立**：这个数是 2026-09-24（`declb_of` 修复前）
   在 20-misc/24-verilog 上测的，而同一轮修复消掉了 1.7 GB/kick 的重建
   （wiring:1667-1670）。修复后的 arena 增量**没有任何文档记录**。
3. **`FORCE_PRIM_MEMO` 命中率与摊平链轮后的 spine 链计数**：3.32M/2.79M/33× 全是
   2026-09-25 的数；`def tree = this._res`（09-26）把 tree 链整条去掉后，这些数
   必须重测才能给 #3 定级。
4. **`Resident` 七表深拷贝的量级**（A4 #2a）：我只证明了"没有生产读点"（结构），
   没有量过它占 `compact_resident` 的多少。表规模只能从
   [文档] mem-l13-opt §1.2 的"20+ 张常驻表"与 `Machine` 1536 B 间接推。
5. **`prelude-hdl`（955→958 decls）与主线新 HDL prelude 的 twin 成本**：主线正在改
   `src/prelude/hdl/*.typort`，且现成二进制是 09-26 19:56 之前的 prelude。
   prime 段与 kick 段的绝对墙钟都不可比。
6. **`fast` 列的 wide_enum / traitchain / struct 在 LSP 口径下的对应物**：
   wide_enum 只有 bench 数（1,328.7 ms @k=11），traitchain 的 L13 格在矩阵里缺失
   （L10 k=9 才有）。
7. **`strchain`/`global` 的 twin 侧今日 churn**：A2.6 指出文档把 L13 的
   string_concat 归因写错了（twin 已 arena 化，参考版才是堆 String），
   所以"L13 strchain churn 8.87 MB/轮"到底现在是多少、由 decl 表还是别的构成，
   我没有 l06l13mem 数据可查。
8. **`18-utils` 的 twin 段 2.4 s 的内部构成**：只有总量与回落机制，
   没有逐 decl 分解（`TYPORT_KICK_DECLTIME` 能出，但需要跑）。
9. **`observations` 的 per-file 条目数 × 单条渲染成本**（A4 #5 的判据）：
   只有 struct 24605 / strchain 16382（bench 口径，round-23 §5），
   没有 adder_proof 的 LSP 口径条目数。
10. **主线未提交改动对 twin 的影响**：682 行未提交改动里 `mod.rs`/`legacy_tests.rs`
    可能触及孪生入口的调用面（我只对 `bump_spine_iter/` 做了完整读码），
    未逐行核对；若 `mod.rs` 里的参考版 `bench_check_nf_bounded` 或
    `def_needs_replay` 有动，本稿的 bench 段结论需要复核。

---

## 最值得先做的 3-5 条性能项

1. **重跑基线（bench 矩阵 + 30 文件 LSP kick + 逐文件归属/fallback class）**。
   0.5-1 人天，与 `perf-measure` 合并。**不做这一步，下面每一步的收益都无法判定**——
   现有矩阵早于六轮优化，且 09-26 摊平链轮后 30 文件总量没有数字。
2. **压实路径的两处白付：`Resident` 七表+`metas` 快照改 probe 门控惰性克隆
   （`entry.rs:1019-1033`/`1092-1106`，唯一读点在 `:1311-1384`）+ `Copier` 15 张
   memo 表跨压实复用**。0.5-1.5 人天，零语义风险，命中大文件每 kick 的
   150-190 ms 压实段；判据用现成探针 `TYPORT_KICK_PROBE` + `twin_engine_tests`。
3. **`FORCE_PRIM_MEMO` 键构造零分配化（`force.rs:711-715`）**。
   0.5 人天，[推断] 单文件 2-5%，且**与 memo 命中率无关**；红线是实参 force 一步都不能少
   （§10 两次判负的教训）。先重测 09-26 后的 spine 链计数再定级。
4. **18-utils double-pay 消除（逐 decl `fresh_meta`/`insert_go` 计数对照）**。
   3-5 人天，**单项收益最大**：[推断] 语料 twin 时间 −25%，并消掉"跑两遍"形状；
   风险是根因基线已换过一次（twin 的 meta 总数现在比参考版少）。
5. **观察面按请求延迟渲染（限观察条目密集的 proof 文件）**。2-4 人天。
   examples 小文件已证噪声内，不要按 pcore 的 39-41% 上账；先量逐文件条目数再动手。

> 排序理由：1 是判据，2/3 是"结构性白付、低风险、可立刻验证"，4 是收益最大但最重，
> 5 收益面窄需先证。全部完成后，twin 在 LSP 单文件口径的主要剩余项将收敛到
> **摊平链的 3 遍（已裁决不动）+ spine 链的实参 force（语义必需）**，
> 即"每遍更便宜"的路已走到边际——这与 chain-09-26 §6 的裁决一致。
