# L01_nbe — 归一化求值（NBE）：19 种实现的对比与基准

纯 lambda 演算（`Term`，de Bruijn 索引）的正常化（eval + quote），在 19 种
表示/策略变体下实现，回答：**项和值的表示方式对求值性能有多大影响？**
基准工作负载固定（丘奇数加法 `church_pair(n)`），每个变体先断言结果等于
`church(2n)`，再计时（`l01bench`）。

## 变体一览（变体名即文件名，见 `src/L01_nbe/`）

公共设施（非变体）：`term.rs`（项/编码/丘奇数）、`persistent_list.rs`
（`ListArena` 下标 arena 链表）、`bench.rs`（基准）。

| 变体 | 项表示 | 环境 | 求值策略 | 备注 |
|---|---|---|---|---|
| `naive` | `Box<Term>` | Rc 链表 | 递归 | 基线 |
| `rc_value` | `Box<Term>` | Rc 链表 | 递归 | 值带 Rc 骨架 |
| `rc_term` | `Rc<TermRc>` | Rc 链表 | 递归 | 项也共享 |
| `bytes_env_list` | 前缀字节码 | Rc 链表 | 递归 | 项扁平化 |
| `bytes_env_arena` | 前缀字节码 | `ListArena` | 递归 | 环境免分配 |
| `bytes_env_arena_tm` | 字节码 + 体共享 arena | `ListArena` | 递归 | 闭包体免拷贝 |
| `bytes_flat_value` | 前缀字节码 | `ListArena` | 递归 | 值也扁平（O(n²)，别用） |
| `rpn_owned` | 后缀字节码（自持） | Rc 链表 | 递归 | RPN 镜像 |
| `ast_env_arena` | `Box<Term>` | `ListArena` | 递归 | AST + 免分配环境 |
| `bump_arena` | bump 引用树 | bump 引用链表 | 递归 | 结果 Box 输出 |
| `bump_tree` | bump 引用树 | bump 引用链表 | 递归 | 结果也 bump，全程零 malloc |
| `env_slice` | bump 引用树 | bump 数组切片 | 递归 | nth O(1)，深索引友好 |
| `compiled` | 指令数组 `&[Ins]` | bump 引用链表 | 递归解释 | 项编译为指令 |
| `cek` | `Box<Term>` | Rc 链表 | CEK kont 栈 | 最简栈安全 |
| `cek_bump` | bump 引用树 | bump 引用链表 | CEK kont 栈 | 栈安全 + bump |
| `bump_iter` | bump 引用树 | bump 引用链表 | 双栈迭代 | 速度 + 深度（迭代版基线） |
| `bump_spine` | bump 引用树 | bump 引用链表 + spine 栈 | 递归 + 流式 quote | 值打包 8B、中性扁平化、右链自底向上 |
| `bump_spine_iter` | bump 引用树 | bump 引用链表 + spine 栈 | 双栈 + 流式 quote | 推荐：spine 系的迭代版，速度 + 深度 |
| `bump_spine_rpn` | bump 引用树 | bump 引用链表 + spine 栈 | 递归 + 流式写字节 | quote 直出 RPN 字节流（输出体积 ~2.4× 小） |

## 怎么跑

```text
cargo build --release --bin l01bench
./target/release/l01bench                   # 默认 1000→4000，每变体 5 轮
./target/release/l01bench --max-church 8000 --rounds 7
./target/release/l01bench --only bump_iter,cek --max-church 512000   # 深度无上限演示
```

- 规模从 1000 起翻倍到 `--max-church`；`--only` 逗号分隔多值过滤变体。
- 口径：预热 1 次 + `--rounds` 轮，只计 `normalize`（入参编码/import 在计时
  外），arena 变体跨轮次复用（稳态）；输出最小 / 中位时间（毫秒），`*` 标
  本轮最快。
- n > 8000 时只有迭代变体（`cek`/`cek_bump`/`bump_iter`/
  `bump_spine_iter`）出赛——其余变体
  的构造/求值/比较全链路是递归，在此规模栈溢出；大 n 段用迭代构造 + 迭代
  比较（`bench.rs` 的 `bench_cek_deep`）。
- 基准挂载 mimalloc（与生产二进制一致）——Windows 默认堆在小分配密集负载
  上慢约 4 倍。

## 实测结果

机器：Windows x64（release profile：LTO + codegen-units=1 + mimalloc）。

n = 4000（min ms / med ms / 相对 bump_spine_iter）：

| 变体 | min | med | 相对 |
|---|---|---|---|
| `bump_spine_iter` | 0.068 | 0.069 | 1.00× |
| `bump_spine_rpn` | 0.082 | 0.084 | 1.21× |
| `bump_spine` | 0.087 | 0.093 | 1.28× |
| `compiled` | 0.172 | 0.208 | 2.53× |
| `cek_bump` | 0.178 | 0.179 | 2.62× |
| `env_slice` | 0.179 | 0.185 | 2.63× |
| `bump_iter` | 0.181 | 0.183 | 2.66× |
| `bump_tree` | 0.204 | 0.207 | 3.00× |
| `bump_arena` | 0.277 | 0.278 | 4.07× |
| `bytes_env_arena_tm` | 0.430 | 0.482 | 6.32× |
| `bytes_env_arena` | 0.439 | 0.478 | 6.46× |
| `ast_env_arena` | 0.600 | 0.740 | 8.82× |
| `bytes_env_list` | 0.627 | 0.679 | 9.22× |
| `rc_term` | 0.698 | 0.712 | 10.3× |
| `rc_value` | 0.740 | 0.754 | 10.9× |
| `naive` | 0.743 | 0.767 | 10.9× |
| `rpn_owned` | 0.784 | 0.822 | 11.5× |
| `cek` | 1.482 | 1.491 | 21.8× |
| `bytes_flat_value` | 76.5 | 77.5 | 1125× |

n = 8000（min ms / 相对 bump_spine_iter）：

| 变体 | min | 相对 |
|---|---|---|
| `bump_spine_iter` | 0.141 | 1.00× |
| `bump_spine_rpn` | 0.196 | 1.39× |
| `bump_spine` | 0.201 | 1.43× |
| `bump_tree` | 0.349 | 2.48× |
| `compiled` | 0.354 | 2.51× |
| `env_slice` | 0.357 | 2.53× |
| `cek_bump` | 0.358 | 2.54× |
| `bump_iter` | 0.359 | 2.55× |
| `bump_arena` | 0.542 | 3.85× |
| `bytes_env_arena_tm` | 0.934 | 6.62× |
| `bytes_env_arena` | 0.999 | 7.09× |
| `bytes_env_list` | 1.298 | 9.21× |
| `ast_env_arena` | 1.311 | 9.30× |
| `rc_term` | 1.389 | 9.85× |
| `rpn_owned` | 1.505 | 10.7× |
| `rc_value` | 1.508 | 10.7× |
| `naive` | 1.523 | 10.8× |
| `cek` | 2.958 | 21.0× |
| `bytes_flat_value` | 314.3 | 2228× |

spine 系的提速来源（消融，n = 4000，单变量关闭流式 quote，见
`bump_spine`）：

```text
bump_tree（24B 值枚举 + 逐节点 bump 中性 + 树式 quote）   0.206 ms
+ 值打包 8B + 中性压扁平 spine 栈（quote 仍逐节点递归）   0.160 ms   （-22%）
+ 流式右链 quote（自底向上扫栈 + Idx 节点共享）           0.088 ms   （再 -45%）
+ 迭代化（bump_spine_iter：双栈 eval + 任务栈 quote）     0.071 ms   （再 -19%）
```

表示打包是均匀的常数缩减；大头在 quote 一侧——树式 quote 对右嵌套链
（`f (f (f x))`，church 数正态形的形状）是**依赖式指针追逐**（每层一次
不可预取的 load，n ≥ 8000 时中性树超出 L2 更痛），流式化后变成对连续
spine 栈的顺序扫描 + 顺序自底向上分配，内存访问全部可预取。迭代化反而
更快是任务栈条目少（流式链不逐层占任务）+ 机器栈帧免除的合计。

**输出编码轴是中性结果**（`bump_spine_rpn`）：quote 直出 RPN 字节流
（每层 ~10B 顺序追加 + tag 批量 resize + 模式块成摞拷贝）与建结果树
（每层 24B bump 分配）速度持平、互有胜负——两者都是顺序写，每层的固定
开销（容量检查 vs 指针推进）同阶；收益只剩输出体积 ~2.4× 小。下游若
接受字节流形态，选它；否则不必。

深度无上限（大 n，min ms；递归变体在此规模已栈溢出；`cek` 列为
128MB 大栈线程跑出——bump 系三列 4MB 栈即可复验，`L01_STACK_MB=4`）：

| n | `cek` | `cek_bump` | `bump_iter` | `bump_spine_iter` |
|---|---|---|---|---|
| 16000 | 6.47 | 0.85 | 0.99 | 0.27 |
| 32000 | 13.60 | 2.24 | 1.73 | 0.67 |
| 64000 | 31.79 | 4.26 | 3.61 | 1.27 |
| 128000 | 70.01 | 8.44 | 6.14 | 2.75 |
| 256000 | 169.71 | 17.38 | 16.42 | 10.90 |
| 512000 | 335.89 | 27.08 | 37.50 | 24.57 |

大 n 段 `bump_spine_iter` 保持领先（64k 时 ~3×、128k 时 ~2.5×；512k
时 `cek_bump` 靠低分配量追近到 1.1×）。修复 `quote_bump_iter` 的递归
eval 后，`cek_bump`/`bump_iter` 大 n 段自身也快了 2.6-3.2×（512k 时
87.8→27.1 / 97.6→37.5）——深递归的机器栈帧（冷栈页 + 缓存不友好）
本身就是慢的，迭代化一举两得。

## 怎么选（结论）

- **默认推荐：`bump_spine_iter`**。速度与深度兼得：小 n 段全场最快
  （n = 4000 比 `bump_tree` 快 ~3×、比 naive 快 ~11×），大 n 段领先
  （64k ~3×、512k 仍第一），求值/quote 深度均不受进程栈限（4MB 栈跑
  51 万）。
- **栈限内的极限速度：`bump_spine`**。递归版，n ≤ 2000 时与迭代版互有
  胜负；深度受进程栈限（~1.6 万）。
- `bump_spine_rpn`：spine 系 + 扁平输出——速度与树输出持平，输出体积
  ~2.4× 小；下游接受字节流时选它。
- `cek_bump` / `bump_iter`：spine 系出现前的迭代答案（CEK kont 栈 vs
  双栈推土机，等价），现为对照保留。
- `cek`：最简的栈安全实现（慢 ~22×），适合教学/对照。
- `env_slice`：de Bruijn 索引大的负载（nth O(1)）值得一试；教堂数基准的
  索引 ≤ 2，测不出差异。
- `bytes_flat_value`：值是整段 memcpy + 拼接，O(n²) 退化（8000 时 0.32s），
  不要用于生产。
- 其余变体（字节码、Rc、指令数组等）为对照/教学保留。

## 已知限制

- spine 系变体（`bump_spine`/`bump_spine_iter`/`bump_spine_rpn`）的
  spine 栈是普通 `Vec`（mimalloc 分配），预保留 4096 槽；超长中性链仍会
  触发倍增扩容（一次顺序 memcpy，占比小）；跨轮不复用。
- ~~51 万+ 规模的线性栈消耗点尚未定位~~ **已定位（两处，2026-08）**：
  ① `quote_bump_iter` 的 `EvalThenQ` 曾调用**递归** `bump_arena::eval`——
  quote 循环本身迭代，但每次强制闭包体都对深链递归 eval（"采样不在
  quote 主循环"说的就是这个），已改调 `bump_iter::eval`（迭代），
  `cek_bump`/`bump_iter` 现在 **4MB 栈**即可跑 51 万（`L01_STACK_MB=4`
  可复验）；② `cek` 的 `Value` 派生 `Clone`/`Drop` 递归——`Idx` 查表
  克隆环境里的 `Clo` 会深拷贝 `Box<Term>` 闭包体、深中性链析构同理
  （藏在派生胶水里，采样看不见）——教学变体保留原样，靠大栈线程兜底。
- 大 n 段的 `check`/输入树用 `mem::forget` 泄漏（百万层深 Box 树的递归
  析构会爆栈；bench 进程一次性，退出即回收）。
- bump 生命周期贯穿单个 `Bump`：求值期间的值/结果不能跨调用保存（对 NBE
  即用即弃的形态够用）。
- 结果树的可比较形式（`Term`）在 bump 之外（`export` 转回时才分配）；
  spine 系的流式 quote 会把链上重复的变量 `Idx` 节点共享成同一节点
  （结果从树变 DAG）——结构比较与 `export` 逐出现访问，语义不变。