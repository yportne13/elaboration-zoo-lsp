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
| `bump_spine_iter` | 0.039 | 0.039 | 1.00× |
| `bump_spine_rpn` | 0.085 | 0.088 | 2.18× |
| `bump_spine` | 0.086 | 0.090 | 2.21× |
| `compiled` | 0.169 | 0.177 | 4.33× |
| `cek_bump` | 0.179 | 0.182 | 4.59× |
| `bump_iter` | 0.179 | 0.180 | 4.59× |
| `bump_tree` | 0.197 | 0.204 | 5.05× |
| `env_slice` | 0.208 | 0.214 | 5.33× |
| `bump_arena` | 0.267 | 0.269 | 6.85× |
| `bytes_env_arena_tm` | 0.440 | 0.461 | 11.3× |
| `bytes_env_arena` | 0.454 | 0.485 | 11.6× |
| `ast_env_arena` | 0.606 | 0.774 | 15.5× |
| `bytes_env_list` | 0.646 | 0.762 | 16.6× |
| `rc_term` | 0.696 | 0.715 | 17.8× |
| `rpn_owned` | 0.724 | 0.742 | 18.6× |
| `naive` | 0.743 | 0.749 | 19.1× |
| `rc_value` | 0.749 | 0.766 | 19.2× |
| `cek` | 1.480 | 1.495 | 37.9× |
| `bytes_flat_value` | 77.5 | 79.9 | 1988× |

n = 8000（min ms / 相对 bump_spine_iter）：

| 变体 | min | 相对 |
|---|---|---|
| `bump_spine_iter` | 0.079 | 1.00× |
| `bump_spine_rpn` | 0.191 | 2.42× |
| `bump_spine` | 0.196 | 2.48× |
| `compiled` | 0.347 | 4.39× |
| `cek_bump` | 0.355 | 4.49× |
| `bump_iter` | 0.355 | 4.49× |
| `bump_tree` | 0.359 | 4.54× |
| `env_slice` | 0.409 | 5.18× |
| `bump_arena` | 0.535 | 6.77× |
| `bytes_env_arena` | 0.943 | 11.9× |
| `bytes_env_arena_tm` | 0.948 | 12.0× |
| `ast_env_arena` | 1.287 | 16.3× |
| `bytes_env_list` | 1.299 | 16.4× |
| `rc_term` | 1.422 | 18.0× |
| `naive` | 1.509 | 19.1× |
| `rpn_owned` | 1.522 | 19.3× |
| `rc_value` | 1.550 | 19.6× |
| `cek` | 2.971 | 37.6× |
| `bytes_flat_value` | 310.4 | 3929× |

spine 系的提速来源（消融，n = 4000，单变量关闭流式 quote，见
`bump_spine`）：

```text
bump_tree（24B 值枚举 + 逐节点 bump 中性 + 树式 quote）   0.197 ms
+ 值打包 8B + 中性压扁平 spine 栈（quote 仍逐节点递归）   0.160 ms   （-19%）
+ 流式右链 quote（自底向上扫栈 + Idx 节点共享）           0.086 ms   （再 -46%）
+ 迭代化（双栈 eval + 任务栈 quote）                     0.068 ms   （再 -21%）
+ eval 右链快速路径（头值直进 vals，ChainWrap 收拢）      0.039 ms   （再 -43%）
```

拆账（n = 8000，quote 内部计时）：总时间 ~78% 在 quote 强制闭包的
eval 里（church_pair 顶层 eval 只做 O(λ) 步直接出闭包）——所以第四轮
的 eval 快速路径收益最大：右链（`App(变量头, ·)` 连续嵌套）不走通用
三推（每层 3 work 弹压 + 2 vals 弹压），头值下降时直接 `nth` 压 vals，
base 求值后 `ChainWrap` 一次收拢，整条链不占 work 栈。表示打包是均匀
的常数缩减；流式 quote 消除树式 readback 的依赖式指针追逐（n ≥ 8000
中性树超出 L2 时尤痛）。

**输出编码轴是中性结果**（`bump_spine_rpn`）：quote 直出 RPN 字节流
（每层 ~10B 顺序追加 + tag 批量 resize + 模式块成摞拷贝）与建结果树
（每层 24B bump 分配）速度持平、互有胜负——两者都是顺序写，每层的固定
开销（容量检查 vs 指针推进）同阶；收益只剩输出体积 ~2.4× 小。下游若
接受字节流形态，选它；否则不必。

深度无上限（大 n，min ms；递归变体在此规模已栈溢出；`cek` 列为
128MB 大栈线程跑出——bump 系三列 4MB 栈即可复验，`L01_STACK_MB=4`）：

| n | `cek` | `cek_bump` | `bump_iter` | `bump_spine_iter` |
|---|---|---|---|---|
| 16000 | 6.47 | 0.79 | 1.07 | 0.16 |
| 32000 | 13.60 | 1.65 | 1.74 | 0.50 |
| 64000 | 31.79 | 4.08 | 3.27 | 0.87 |
| 128000 | 70.01 | 8.83 | 6.31 | 1.68 |
| 256000 | 169.71 | 17.23 | 15.66 | 9.48 |
| 512000 | 335.89 | 36.61 | 27.66 | 15.04 |

大 n 段 `bump_spine_iter` 对旧迭代双雄领先 1.8-5×（64k 时 4-5×，
512k 时 1.8-2.4×）。修复 `quote_bump_iter` 的递归 eval 后，`cek_bump`/
`bump_iter` 大 n 段自身也快了 2.6-3.2×（512k 时 87.8→36.6 /
97.6→27.7）——深递归的机器栈帧（冷栈页 + 缓存不友好）本身就是慢的，
迭代化一举两得。

## 怎么选（结论）

- **默认推荐：`bump_spine_iter`**。速度与深度兼得：小 n 段全场最快
  （n = 4000 比 `bump_tree` 快 ~5×、比 naive 快 ~19×），大 n 段领先
  （64k 4-5×、512k 1.8×），求值/quote 深度均不受进程栈限（4MB 栈跑
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