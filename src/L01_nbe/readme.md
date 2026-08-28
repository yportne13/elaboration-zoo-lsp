# L01_nbe — NBE 表示层实验的整理与基准

本模块把 `L01a_fast` 时代散落的 `nbe_closure*.rs` 实验按「表示轴」整理为 8 个
变体（见 `mod.rs` 的对照表），再加一个求值策略变体 `cek`，用统一的基准回答当初
那个问题：**项和值的表示方式对求值性能有多大影响？**

## 跑法（独立二进制，不依赖 typort / lib 其余各层）

```text
cargo build --release --bin l01bench
./target/release/l01bench                  # 默认 1000→4000，每变体 5 轮
./target/release/l01bench --max-church 8000 --rounds 7
./target/release/l01bench --only cek --max-church 131072   # 单独测 cek 大 n
```

规模从 1000 起翻倍到 `--max-church`。每个变体先断言 `normalize(church_pair(n))`
等于 `church(2n)`（所有变体在 1000…8000 上全部通过），再计时：预热 1 次 +
`--rounds` 轮，只计 `normalize`（入参编码在计时外），arena 变体跨轮复用 arena
（稳态）。输出每轮的最小 / 中位时间（毫秒），`*` 标本轮最快。

> n > 8000 时**只有 `cek`** 出赛：其余变体的构造/求值/比较全链路都是递归，
> 在此规模直接栈溢出（`bench.rs` 的 `bench_cek_deep` 用迭代构造 + 迭代比较，
> `cek` 则 eval/quote/解码全迭代）。基准挂载了与生产二进制相同的 mimalloc
> 分配器——Windows 默认堆在这个小分配密集负载上要慢约 4 倍。

## 实测结果

机器：Windows x64（release profile：LTO + codegen-units=1 + mimalloc）。

n = 4000（5 轮，2026-08-28）：

| 变体 | min ms | med ms | 相对 bytes_env_arena |
|---|---|---|---|
| **bytes_env_arena_tm** | 0.546 | 0.567 | 1.00× |
| **bytes_env_arena** | 0.492 | 0.544 | 0.90× |
| bytes_env_list | 0.638 | 0.806 | 1.30× |
| rpn_owned | 0.686 | 0.730 | 1.39× |
| naive | 0.729 | 0.743 | 1.48× |
| rc_value | 0.743 | 0.776 | 1.51× |
| rc_term | 0.851 | 0.860 | 1.73× |
| cek | 1.572 | 1.585 | 3.19× |
| bytes_flat_value | 77.2 | 78.9 | 157× |

n = 8000（7 轮，2026-08-28）：

| 变体 | min ms | 相对 bytes_env_arena |
|---|---|---|
| **bytes_env_arena** | 1.053 | 1.00× |
| **bytes_env_arena_tm** | 1.109 | 1.05× |
| bytes_env_list | 1.470 | 1.40× |
| naive | 1.536 | 1.46× |
| rc_value | 1.568 | 1.49× |
| rpn_owned | 1.612 | 1.53× |
| rc_term | 1.716 | 1.63× |
| cek | 3.161 | 3.00× |
| bytes_flat_value | 313.2 | 297× |

cek 大 n（5 轮；其余变体此时已栈溢出，无数据）：

| n | cek min ms | 扩展 |
|---|---|---|
| 8000 | 3.17 | — |
| 16000 | 5.94 | 1.9× |
| 32000 | 12.46 | 2.1× |
| 64000 | 25.37 | 2.0× |
| 128000 | 54.87 | 2.2× |
| 256000 | 113.5 | 2.1× |

## 结论（当初 readme 的「nbe_closure2 seems faster」基本正确，且更精确）

1. **字节码 + arena 环境（`bytes_env_arena`）是赢家**：比基线 `naive` 快
   ~1.5×，比 `bytes_env_list`（同样的字节码但环境用 `Rc` 链表）快 ~1.3×。
   `bytes_env_arena` 与 `bytes_env_arena_tm` 互有胜负（差距 ~5-10%，在噪声内）：
   把闭包体也搬进 arena 并没有带来可测收益——`prepend` 消除分配才是大头。

2. **项从 AST 换成字节码就有 ~1.5×，环境从 `Rc` 链表换成 arena 再有 ~1.2×**；
   值的 `Box` → `Rc` 无收益（rc_value 反而偏慢，原子计数 > 拷贝），
   项再套 `Rc`（rc_term）也只拉平。

3. **`bytes_flat_value` 是陷阱**：值整段 memcpy + `App` 字节拼接导致
   O(n²) 退化——4000 时 77ms、8000 时 313ms（冠军的 300 倍）。扁平化
   省掉的间接性远偿不上拷贝量，规模一大就崩。

4. **`cek` 是最慢的常规变体（~3×），但它是唯一不爆栈的**：求值深度不受进程
   栈限——n = 26 万（church 52 万位加法）依然线性扩展、正确性断言通过，而
   其他变体在 16000 就连输入都构造不出来。取舍很清晰：**有限深度内要速度用
   `bytes_env_arena`，要深度无上限用 `cek`**（如把它做成 L02+ 的求值内核，
   免去栈溢出补丁）。

5. 其他变体在 8000 时与 `naive` 拉开到 ~1.5×，说明收益随规模略微扩大，
   但量级已定：**表示层能买到的加速封顶在 ~2×**，想更快得换算法
   （如 defunctionalization / 展开求值），这是 L02+ 的事。