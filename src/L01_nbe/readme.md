# L01_nbe — 归一化求值（NBE）：17 种实现的对比与基准

纯 lambda 演算（`Term`，de Bruijn 索引）的正常化（eval + quote），在 17 种
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
| `bump_iter` | bump 引用树 | bump 引用链表 | 双栈迭代 | 推荐：速度 + 深度 |
| `bump_spine` | bump 引用树 | bump 引用链表 + spine 栈 | 递归 + 流式 quote | 速度之王：值打包 8B、中性扁平化、右链自底向上 |

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
- n > 8000 时只有迭代变体（`cek`/`cek_bump`/`bump_iter`）出赛——其余变体
  的构造/求值/比较全链路是递归，在此规模栈溢出；大 n 段用迭代构造 + 迭代
  比较（`bench.rs` 的 `bench_cek_deep`）。
- 基准挂载 mimalloc（与生产二进制一致）——Windows 默认堆在小分配密集负载
  上慢约 4 倍。

## 实测结果

机器：Windows x64（release profile：LTO + codegen-units=1 + mimalloc）。

n = 4000（min ms / med ms / 相对 bump_spine）：

| 变体 | min | med | 相对 |
|---|---|---|---|
| `bump_spine` | 0.086 | 0.088 | 1.00× |
| `compiled` | 0.176 | 0.189 | 2.05× |
| `env_slice` | 0.210 | 0.215 | 2.44× |
| `bump_tree` | 0.212 | 0.213 | 2.47× |
| `bump_iter` | 0.214 | 0.218 | 2.49× |
| `cek_bump` | 0.218 | 0.222 | 2.53× |
| `bump_arena` | 0.283 | 0.293 | 3.29× |
| `bytes_env_arena` | 0.469 | 0.481 | 5.45× |
| `bytes_env_arena_tm` | 0.485 | 0.601 | 5.64× |
| `ast_env_arena` | 0.582 | 0.692 | 6.77× |
| `bytes_env_list` | 0.660 | 0.731 | 7.67× |
| `rc_term` | 0.697 | 0.715 | 8.10× |
| `rpn_owned` | 0.725 | 0.812 | 8.43× |
| `rc_value` | 0.738 | 0.754 | 8.58× |
| `naive` | 0.739 | 0.772 | 8.59× |
| `cek` | 1.485 | 1.507 | 17.3× |
| `bytes_flat_value` | 76.6 | 78.5 | 890× |

n = 8000（min ms / 相对 bump_spine）：

| 变体 | min | 相对 |
|---|---|---|
| `bump_spine` | 0.201 | 1.00× |
| `compiled` | 0.340 | 1.69× |
| `env_slice` | 0.357 | 1.78× |
| `bump_tree` | 0.360 | 1.79× |
| `bump_iter` | 0.432 | 2.15× |
| `cek_bump` | 0.440 | 2.19× |
| `bump_arena` | 0.558 | 2.78× |
| `bytes_env_arena_tm` | 1.078 | 5.36× |
| `bytes_env_arena` | 1.101 | 5.48× |
| `ast_env_arena` | 1.324 | 6.59× |
| `rc_term` | 1.408 | 7.00× |
| `bytes_env_list` | 1.495 | 7.44× |
| `naive` | 1.505 | 7.49× |
| `rc_value` | 1.512 | 7.52× |
| `rpn_owned` | 1.685 | 8.38× |
| `cek` | 2.948 | 14.7× |
| `bytes_flat_value` | 310.0 | 1542× |

`bump_spine` 的提速来源（消融，n = 4000，单变量关闭流式 quote）：

```text
bump_tree（24B 值枚举 + 逐节点 bump 中性 + 树式 quote）   0.201 ms
+ 值打包 8B + 中性压扁平 spine 栈（quote 仍逐节点递归）   0.160 ms   （-20%）
+ 流式右链 quote（自底向上扫栈 + Idx 节点共享）           0.086 ms   （再 -46%）
```

表示打包是均匀的常数缩减；大头在 quote 一侧——树式 quote 对右嵌套链
（`f (f (f x))`，church 数正态形的形状）是**依赖式指针追逐**（每层一次
不可预取的 load，n ≥ 8000 时中性树超出 L2 更痛），流式化后变成对连续
spine 栈的顺序扫描 + 顺序自底向上分配，内存访问全部可预取。

深度无上限（大 n，min ms；递归变体在此规模已栈溢出）：

| n | `cek` | `cek_bump` | `bump_iter` |
|---|---|---|---|
| 8000 | 2.919 | 0.331 | 0.325 |
| 16000 | 5.94 | 0.96 | 0.93 |
| 32000 | 12.10 | 1.62 | 2.42 |
| 64000 | 25.61 | 3.60 | 6.70 |
| 128000 | 60.03 | 8.82 | 17.4 |
| 256000 | 124.34 | 32.04 | 25.6 |
| 512000 | 252.20 | 67.34 | 63.4 |

## 怎么选（结论）

- **极限速度：`bump_spine`**。值打包 + 中性扁平化 + 流式右链 quote，
  比 `bump_tree` 快 ~2.5×、比 naive 快 ~8.6×；深度受进程栈限（与
  `bump_tree` 同级，~1.6 万）。
- **默认推荐：`bump_iter`**。速度 ≈ 递归 `bump_tree` 的 1.2×（显式栈的
  固定成本），但求值深度不受进程栈限——n = 51 万（church 一百万位加法）
  线性可跑；代码是 `bump_tree` 递归的贴身改造（双栈推土机），比 CEK
  形态直观。`bump_spine` 的打包值/扁平 spine/流式 quote 尚未移植到
  迭代版——这是大 n 场景最直接的后续提速点。
- **栈安全且要快：`cek_bump`**，与 `bump_iter` 等价（CEK kont 栈形态），
  按口味二选一。
- `cek`：最简的栈安全实现（慢 ~15×），适合教学/对照。
- `env_slice`：de Bruijn 索引大的负载（nth O(1)）值得一试；教堂数基准的
  索引 ≤ 2，测不出差异。
- `bytes_flat_value`：值是整段 memcpy + 拼接，O(n²) 退化（8000 时 0.31s），
  不要用于生产。
- 其余变体（字节码、Rc、指令数组等）为对照/教学保留。

## 已知限制

- `bump_spine` 的 spine 栈是普通 `Vec`（mimalloc 分配），预保留 4096 槽；
  超长中性链仍会触发倍增扩容（一次顺序 memcpy，占比小）；跨轮不复用。
- 51 万+ 规模的线性栈消耗点尚未定位（栈指针采样证明不在 quote 主循环）；
  `l01bench` 用大栈线程跑大规模，默认 1MB 主线程栈下 25.6 万可稳定通过。
- 大 n 段的 `check`/输入树用 `mem::forget` 泄漏（百万层深 Box 树的递归
  析构会爆栈；bench 进程一次性，退出即回收）。
- bump 生命周期贯穿单个 `Bump`：求值期间的值/结果不能跨调用保存（对 NBE
  即用即弃的形态够用）。
- 结果树的可比较形式（`Term`）在 bump 之外（`export` 转回时才分配）；
  `bump_spine` 的流式 quote 会把链上重复的变量 `Idx` 节点共享成同一节点
  （结果从树变 DAG）——结构比较与 `export` 逐出现访问，语义不变。