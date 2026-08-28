# L01_nbe — 归一化求值（NBE）：16 种实现的对比与基准

纯 lambda 演算（`Term`，de Bruijn 索引）的正常化（eval + quote），在 16 种
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

n = 4000（min ms / med ms / 相对 bump_tree）：

| 变体 | min | med | 相对 |
|---|---|---|---|
| `bump_tree` | 0.153 | 0.166 | 1.00× |
| `bump_iter` | 0.155 | 0.162 | 1.01× |
| `cek_bump` | 0.158 | 0.162 | 1.03× |
| `compiled` | 0.171 | 0.202 | 1.12× |
| `env_slice` | 0.185 | 0.190 | 1.21× |
| `bump_arena` | 0.225 | 0.230 | 1.47× |
| `bytes_env_arena` | 0.490 | 0.519 | 3.2× |
| `bytes_env_arena_tm` | 0.543 | 0.553 | 3.6× |
| `ast_env_arena` | 0.572 | 0.699 | 3.7× |
| `bytes_env_list` | 0.585 | 0.658 | 3.8× |
| `rpn_owned` | 0.656 | 0.712 | 4.3× |
| `rc_term` | 0.711 | 0.729 | 4.6× |
| `rc_value` | 0.732 | 0.761 | 4.8× |
| `naive` | 0.744 | 0.756 | 4.9× |
| `cek` | 1.501 | 1.507 | 9.8× |
| `bytes_flat_value` | 76.1 | 79.6 | 497× |

n = 8000（min ms / 相对 bump_tree）：

| 变体 | min | 相对 |
|---|---|---|
| `bump_tree` | 0.276 | 1.00× |
| `bump_iter` | 0.325 | 1.18× |
| `cek_bump` | 0.331 | 1.20× |
| `compiled` | 0.350 | 1.26× |
| `env_slice` | ~0.35 | 1.27×（与 bump_tree 统计持平） |
| `bump_arena` | 0.434 | 1.57× |
| `bytes_env_arena` | 1.038 | 3.8× |
| `bytes_env_arena_tm` | 1.210 | 4.4× |
| `ast_env_arena` | 1.275 | 4.6× |
| `rc_term` | 1.450 | 5.3× |
| `rpn_owned` | 1.484 | 5.4× |
| `naive` | 1.518 | 5.5× |
| `rc_value` | 1.522 | 5.5× |
| `bytes_env_list` | 1.523 | 5.5× |
| `cek` | 2.919 | 10.6× |
| `bytes_flat_value` | 313.6 | 1134× |

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

- **默认推荐：`bump_iter`**。速度 ≈ 递归最快的 `bump_tree` 的 1.2×（显式
  栈的固定成本），但求值深度不受进程栈限——n = 51 万（church 一百万位
  加法）线性可跑；代码是 `bump_tree` 递归的贴身改造（双栈推土机），比
  CEK 形态直观。
- **极限速度：`bump_tree`**。全程零 malloc（结果树也 bump），基准最快；
  深度受进程栈限（~1.6 万）。
- `cek_bump` 与 `bump_iter` 等价（CEK kont 栈形态），按口味二选一。
- `cek`：最简的栈安全实现（慢 ~10×），适合教学/对照。
- `env_slice`：de Bruijn 索引大的负载（nth O(1)）值得一试；教堂数基准的
  索引 ≤ 2，测不出差异。
- `bytes_flat_value`：值是整段 memcpy + 拼接，O(n²) 退化（8000 时 0.31s），
  不要用于生产。
- 其余变体（字节码、Rc、指令数组等）为对照/教学保留。

## 已知限制

- 51 万+ 规模的线性栈消耗点尚未定位（栈指针采样证明不在 quote 主循环）；
  `l01bench` 用大栈线程跑大规模，默认 1MB 主线程栈下 25.6 万可稳定通过。
- 大 n 段的 `check`/输入树用 `mem::forget` 泄漏（百万层深 Box 树的递归
  析构会爆栈；bench 进程一次性，退出即回收）。
- bump 生命周期贯穿单个 `Bump`：求值期间的值/结果不能跨调用保存（对 NBE
  即用即弃的形态够用）。
- 结果树的可比较形式（`Term`）在 bump 之外（`export` 转回时才分配）。