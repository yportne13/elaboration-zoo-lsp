# L01_nbe — 归一化求值（NBE）：22 种实现的对比与基准

纯 lambda 演算（`Term`，de Bruijn 索引）的正常化（eval + quote），在 22 种
表示/策略变体下实现，回答：**项和值的表示方式对求值性能有多大影响？**
基准负载两族（`--workload`）：丘奇数加法 `church_pair(n)`（默认，线性）
与复制强制 `dup_pair`/`dup_deep`（开记忆化轴），每个变体先断言结果正确
再计时（`l01bench`）。

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
| `bump_spine_iter` | bump 引用树 | bump 引用链表 + spine 栈 | 双栈 + 流式 quote | 速度 + 深度（一次性口径的推荐） |
| `bump_spine_slim` | bump 引用树 | bump 引用链表 + spine 栈 | 双栈 + 流式 quote | 条目 16B + quote 期连续性推断（实测否决） |
| `bump_spine_memo` | bump 引用树 | bump 引用链表 + spine 栈 | 双栈 + 流式 quote + memo | quote 记忆化：值×level → 共享子树（dup 轴） |
| `bump_spine_rpn` | bump 引用树 | bump 引用链表 + spine 栈 | 递归 + 流式写字节 | quote 直出 RPN 字节流（输出体积 ~2.4× 小） |
| `native_clo` | 原生闭包树（bump `&dyn Fn`） | bump 引用链表 + spine 栈 | 原生调用 + 流式 quote | β=间接调用（封轴实验，实测否决） |

另有两个**测量口径行**（非独立变体，实现在对应变体文件里）：`bump_spine_iter_ss`
与 `bump_spine_slim_ss`——`Machine`（spine/vals 跨调用复用）配合同一
`Bump` 的 `reset()`，即稳态近零分配口径，与 `bytes_*` 变体跨轮复用
`ListArena` 同口径。

## 怎么跑

```text
cargo build --release --bin l01bench
./target/release/l01bench                   # 默认 1000→4000，每变体 5 轮
./target/release/l01bench --max-church 8000 --rounds 7
./target/release/l01bench --only bump_iter,cek --max-church 512000   # 深度无上限演示
./target/release/l01bench --workload dup --only bump_spine_iter,bump_spine_memo  # 复制强制轴
```

- 规模从 1000 起翻倍到 `--max-church`；`--only` 逗号分隔多值过滤变体。
- 口径：预热 1 次 + `--rounds` 轮，只计 `normalize`（入参编码/import 在计时
  外），arena 变体跨轮次复用（稳态）；输出最小 / 中位时间（毫秒），`*` 标
  本轮最快。
- n > 8000 时只有迭代变体（`cek`/`cek_bump`/`bump_iter`/
  `bump_spine_iter`/`bump_spine_slim`，及稳态行 `bump_spine_iter_ss`）
  出赛——其余变体的构造/求值/比较全链路是递归，在此规模栈溢出；大 n
  段用迭代构造 + 迭代比较（`bench.rs` 的 `bench_cek_deep`）。
- `_ss` 后缀是稳态口径测量行（`Machine` + `Bump::reset`，见变体一览），
  与同名变体的算法完全一致，只是栈跨轮复用。
- 基准挂载 mimalloc（与生产二进制一致）——Windows 默认堆在小分配密集负载
  上慢约 4 倍。

## 实测结果

机器：Windows x64（release profile：LTO + codegen-units=1 + mimalloc）。

n = 4000（min ms / med ms / 相对 bump_spine_iter_ss）：

| 变体 | min | med | 相对 |
|---|---|---|---|
| `bump_spine_iter_ss` | 0.030 | 0.030 | 1.00× |
| `bump_spine_iter` | 0.036 | 0.038 | 1.20× |
| `bump_spine_memo` | 0.039 | 0.039 | 1.30× |
| `bump_spine_slim_ss` | 0.040 | 0.041 | 1.33× |
| `bump_spine_slim` | 0.044 | 0.045 | 1.47× |
| `bump_spine_rpn` | 0.083 | 0.086 | 2.77× |
| `native_clo` | 0.084 | 0.101 | 2.80× |
| `bump_spine` | 0.091 | 0.128 | 3.03× |
| `cek_bump` | 0.183 | 0.191 | 6.10× |
| `bump_iter` | 0.183 | 0.200 | 6.10× |
| `compiled` | 0.184 | 0.195 | 6.13× |
| `bump_tree` | 0.214 | 0.218 | 7.13× |
| `env_slice` | 0.220 | 0.251 | 7.33× |
| `bump_arena` | 0.282 | 0.284 | 9.40× |
| `bytes_env_arena_tm` | 0.473 | 0.560 | 15.8× |
| `bytes_env_arena` | 0.494 | 0.523 | 16.5× |
| `ast_env_arena` | 0.595 | 0.902 | 19.8× |
| `bytes_env_list` | 0.672 | 0.732 | 22.4× |
| `rc_term` | 0.702 | 0.731 | 23.4× |
| `rpn_owned` | 0.730 | 0.773 | 24.3× |
| `rc_value` | 0.769 | 0.777 | 25.6× |
| `naive` | 0.772 | 0.775 | 25.7× |
| `cek` | 1.509 | 1.521 | 50.3× |
| `bytes_flat_value` | 76.4 | 77.1 | 2547× |

n = 8000（min ms / 相对 bump_spine_iter_ss）：

| 变体 | min | 相对 |
|---|---|---|
| `bump_spine_iter_ss` | 0.059 | 1.00× |
| `bump_spine_iter` | 0.076 | 1.29× |
| `bump_spine_slim_ss` | 0.077 | 1.31× |
| `bump_spine_memo` | 0.079 | 1.34× |
| `bump_spine_slim` | 0.089 | 1.51× |
| `native_clo` | 0.184 | 3.12× |
| `bump_spine_rpn` | 0.200 | 3.39× |
| `bump_spine` | 0.206 | 3.49× |
| `compiled` | 0.349 | 5.92× |
| `bump_iter` | 0.363 | 6.15× |
| `cek_bump` | 0.365 | 6.19× |
| `bump_tree` | 0.365 | 6.19× |
| `env_slice` | 0.415 | 7.03× |
| `bump_arena` | 0.545 | 9.24× |
| `bytes_env_arena` | 0.933 | 15.8× |
| `bytes_env_arena_tm` | 1.098 | 18.6× |
| `ast_env_arena` | 1.181 | 20.0× |
| `bytes_env_list` | 1.378 | 23.4× |
| `rc_term` | 1.456 | 24.7× |
| `rpn_owned` | 1.474 | 25.0× |
| `rc_value` | 1.559 | 26.4× |
| `naive` | 1.564 | 26.5× |
| `cek` | 3.009 | 51.0× |
| `bytes_flat_value` | 310.4 | 5254× |

spine 系的提速来源（消融，n = 4000，单变量关闭流式 quote，见
`bump_spine`）：

```text
bump_tree（24B 值枚举 + 逐节点 bump 中性 + 树式 quote）   0.197 ms
+ 值打包 8B + 中性压扁平 spine 栈（quote 仍逐节点递归）   0.160 ms   （-19%）
+ 流式右链 quote（自底向上扫栈 + Idx 节点共享）           0.086 ms   （再 -46%）
+ 迭代化（双栈 eval + 任务栈 quote）                     0.068 ms   （再 -21%）
+ eval 右链快速路径（头值直进 vals，ChainWrap 收拢）      0.039 ms   （再 -43%）
+ Machine 稳态复用（spine/vals 跨调用，Bump::reset 保池） 0.030 ms   （再 -17%）
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

**第十二轮的三个实测（2026-08，n = 4000，基线 `bump_spine_iter` 0.036 ms）**：

- **条目瘦身被否决**（`bump_spine_slim`，0.044 ms，慢 22%）：spine 条目
  从 24B（带 `len`/`base` 记账）瘦到 16B、连续性改由 quote 期沿 `a`
  下行推断（`entry[i].a == v_spine(i-1)` 即连续）——**push 期记账比
  quote 期推断便宜**。下行推断每条目多一次 load + 循环开销（且在
  Vec 索引的边界检查里），只换回 push 期省下的一次前驱读取；16B 的
  缓存密度收益在 L2 放得下的规模（n ≤ 8000）显现不出来。大 n 段
  （≥ 32k，spine 超出缓存）密度开始回本——256k 时 slim 反超 iter
  （5.99 vs 7.53）——但两者都远输稳态复用。
- **原生闭包轴被封顶**（`native_clo`，0.084 ms，慢 2.8×）：项编译为
  原生 Rust 闭包树（`&'a dyn Fn` 装在 bump 里，β = 一次间接调用）。
  它比 `compiled`（指令数组解释，0.184）快 ~2.2×——证明"编译"方向
  本身有油水；但败给指针树解释 2.8×：dyn 调用不可内联、每 β 三次
  bump 分配（闭包体 + Clo 单元 + EnvCons，解释版两次）、最关键的是
  **没有右链快速路径可特化**——解释器能把 church 链的每层机器开销
  摊到一次 `nth` + 一次 store，原生闭包必须逐层走完整的 apply 分发。
  结论：在 Rust 里，"编译为原生闭包"不敌"解释 + 形状特化"。
- **稳态复用是新赢点**（`bump_spine_iter_ss`，0.030 ms，快 17%）：
  `Machine` 跨调用复用两个无生命周期的大栈（spine ~2n 条、vals ~n 个，
  本负载仅有的两个大缓冲；带生命周期的小栈恒浅，每调用新建），配
  同一 `Bump` 的 `reset()`（保池）。省掉的是每轮 spine 的 mimalloc
  分配 + 倍增拷贝（n=4000 时 4096→8192 一次拷 96KB）与 vals 的对数
  次倍增。规模越大收益越大：8000 快 22%，512k 快 **3.3×**（20.6→6.2，
  省的是每轮 24MB spine 的分配/倍增/缺页）。这是**口径**而非算法
  改进——但 LSP 一类长驻进程本来就该这么用。

## 重复求值轴（`--workload dup`，第十三轮）

`church_pair` 是刻意选的线性负载：每个闭包恰好被 quote 强制一次，
共享/记忆化无从收益。**为什么 call-by-need 在 NbE 里几乎无处可用**：
NbE 的 CBV 只急切到 WHNF——`Lam` 求值是 O(1) 闭包创建，经典"丢弃
参数"浪费（`(λx. y) BIG`）几乎免费；真正的重复在 **readback**：同一个
闭包/中性值经 λ-binder 复制（`(λx. pair x x) BIG`）后，quote 会对它
**多次完整强制**（每次都是 body 重走 + 结果树重建）。

负载族（`term.rs` 的 `dup_pair`/`dup_deep`）：

```text
dup_pair(n) = (λx. pair x x) (add (ch n) (ch n))     正态形 λf. f C C
             —— C = church(2n) 被强制 2 次
dup_deep(n) = (λx. pair x x) ((λy. pair y y) (add …))  λf. f (λf. f C C) (λf. f C C)
             —— C 被强制 4 次
```

`bump_spine_memo` 用 **quote 记忆化**对付它（readback 侧的 call-by-need
对偶，Lean 式 whnf 缓存的 quote 版）：memo 键 = 值的打包字 × quote
level（闭包指针与 spine 句柄全局唯一；spine 只增不改，同一值在同一
level 的 quote 结果只依赖该键）。实现是任务栈里一个 LIFO 屏障任务
（`MemoStore`）：`Q(v, level)` 未命中时把屏障压到最深处，栈纪律保证
v 的整棵子任务跑完后屏障弹出、done 栈顶恰是完整结果——入表放回；
命中则直接复用**共享子树**（结果从树变 DAG，与 ChainRun 的 Idx 共享
同性质）。

实测（n = 4000 / 8000，min ms）：

| 负载 | `bump_spine_iter` | `bump_spine_memo` | 分离度 |
|---|---|---|---|
| church_pair 4000（线性，中性验证） | 0.036 | 0.039 | 哈希税 +8% |
| church_pair 8000（线性） | 0.073 | 0.079 | 哈希税 +8% |
| dup_pair 4000（强制 ×2） | 0.072 | 0.040 | **1.8×** |
| dup_deep 4000（强制 ×4） | 0.145 | 0.040 | **3.6×** |
| dup_pair 8000（强制 ×2） | 0.146 | 0.079 | **1.8×** |
| dup_deep 8000（强制 ×4） | 0.289 | 0.079 | **3.7×** |

两个要点：**复制被完全塌缩**——memo 后 `dup_pair` ≈ `dup_deep` ≈ 单次
强制的成本（0.040/0.079，与 church_pair 同阶），收益随复制层数指数
增长（2^k，受哈希税恒定）；**线性负载的代价只有 3-8%**（`Q` 的调用
次数是 O(λ 层)，链节点走 ChainRun 不经过 memo）。何时开：负载里同一
值被多次 quote（elaborator 的 conversion checking、let-共享展开）就该
开；纯线性负载付小税。

深度无上限（大 n，min ms，同一轮实测；递归变体在此规模已栈溢出；
`cek` 列为 128MB 大栈线程跑出——bump 系各列 4MB 栈即可复验，
`L01_STACK_MB=4`）：

| n | `cek` | `cek_bump` | `bump_iter` | `bump_spine_iter` | `bump_spine_slim` | `bump_spine_iter_ss` |
|---|---|---|---|---|---|---|
| 16000 | 6.18 | 0.83 | 1.00 | 0.17 | 0.20 | 0.12 |
| 32000 | 12.75 | 1.72 | 2.02 | 0.40 | 0.37 | 0.24 |
| 64000 | 26.30 | 3.68 | 3.65 | 1.04 | 0.78 | 0.55 |
| 128000 | 58.51 | 8.47 | 6.54 | 1.72 | 1.60 | 1.26 |
| 256000 | 122.82 | 17.49 | 12.77 | 7.53 | 5.99 | 2.86 |
| 512000 | 245.70 | 39.91 | 27.71 | 20.62 | 16.16 | 6.18 |

大 n 段 `bump_spine_iter` 对旧迭代双雄领先 1.5-6×（64k 时 3.5-6×，
512k 时 1.4-1.9×）；稳态复用（`_ss`）再拉开一截——512k 时 6.18 ms，
对 `cek_bump`/`bump_iter` 领先 6.5×/4.5×，比一次性口径的自己快 3.3×。
`bump_spine_slim` 的 16B 条目在 spine 超出缓存的规模（≥ 64k）开始
反超 24B 版（256k 时 5.99 vs 7.53），但仍远输稳态复用——密度是
二级效应，复用才是一级效应。修复 `quote_bump_iter` 的递归 eval 后，
`cek_bump`/`bump_iter` 大 n 段自身也快了 2.6-3.2×——深递归的机器
栈帧（冷栈页 + 缓存不友好）本身就是慢的，迭代化一举两得。

## 怎么选（结论）

- **默认推荐：`bump_spine_iter`，长驻进程用它的 `Machine` 稳态口径**。
  速度与深度兼得：一次性口径小 n 段全场最快（n = 4000 比 `bump_tree`
  快 ~6×、比 naive 快 ~21×），大 n 段领先；稳态复用（`_ss`）再快
  17%-3.3×（512k 时 6.2 ms，比 naive 快 ~56×），求值/quote 深度均
  不受进程栈限（4MB 栈跑 51 万）。LSP 一类跨请求复用机器的形态，
  稳态才是真实成本。
- **栈限内的极限速度：`bump_spine`**。递归版，n ≤ 2000 时与迭代版互有
  胜负；深度受进程栈限（~1.6 万）。
- `bump_spine_rpn`：spine 系 + 扁平输出——速度与树输出持平，输出体积
  ~2.4× 小；下游接受字节流时选它。
- `native_clo` / `bump_spine_slim` / `compiled`：三条被实测否决的轴
  （原生闭包编译 / 条目瘦身 / 指令数组），为对照保留——否决理由见
  上方"第十二轮的三个实测"。
- **`bump_spine_memo`：负载含重复强制时开**（同一值被多次 quote——
  elaborator 的 conversion checking、let-共享展开的常态）。线性负载付
  3-8% 哈希税；复制强制负载收益 1.8×（×2）/3.6×（×4），随复制层数
  指数增长，复制被塌缩为单次强制（见"重复求值轴"）。
- `cek_bump` / `bump_iter`：spine 系出现前的迭代答案（CEK kont 栈 vs
  双栈推土机，等价），现为对照保留。
- `cek`：最简的栈安全实现（慢 ~50×），适合教学/对照。
- `env_slice`：de Bruijn 索引大的负载（nth O(1)）值得一试；教堂数基准的
  索引 ≤ 2，测不出差异。
- `bytes_flat_value`：值是整段 memcpy + 拼接，O(n²) 退化（8000 时 0.32s），
  不要用于生产。
- 其余变体（字节码、Rc 等）为对照/教学保留。

## 已知限制

- spine 系变体（`bump_spine`/`bump_spine_iter`/`bump_spine_rpn`/
  `bump_spine_slim`）一次性口径的 spine 栈是普通 `Vec`（mimalloc 分配），
  预保留 4096 槽；超长中性链仍会触发倍增扩容（一次顺序 memcpy）。
  **稳态口径（`_ss` 行）已消除此项**：`Machine` 跨调用复用 spine/vals，
  配 `Bump::reset` 保池；大 n 段收益 1.4-3.3×（512k 时 20.6→6.2 ms）。
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
  spine 系的流式 quote 会把链上重复的变量 `Idx` 节点共享成同一节点，
  `bump_spine_memo` 进一步把重复 quote 的整棵子树共享（结果从树变
  DAG）——结构比较与 `export` 逐出现访问，语义不变。