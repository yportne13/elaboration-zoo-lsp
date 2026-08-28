# L01_nbe — NBE 表示层实验的整理与基准

本模块把 `L01a_fast` 时代散落的 `nbe_closure*.rs` 实验按「表示轴」整理为 8 个
变体（见 `mod.rs` 的对照表），并用统一的基准回答当初那个问题：**项和值的表示
方式对求值性能有多大影响？**

## 跑法

```text
cargo build --release
./target/release/typort bench                # 默认 1000→4000，每变体 5 轮
./target/release/typort bench --max-church 8000 --rounds 7
```

规模从 1000 起翻倍到 `--max-church`。每个变体先断言 `normalize(church_pair(n))`
等于 `church(2n)`（所有变体在 1000…8000 上全部通过），再计时：预热 1 次 +
`--rounds` 轮，只计 `normalize`（入参编码在计时外），arena 变体跨轮复用 arena
（稳态）。输出每轮的最小 / 中位时间（毫秒），`*` 标本轮最快。

## 实测结果

机器：Windows x64（release profile：LTO + codegen-units=1）。

n = 4000（5 轮，2026-08-28）：

| 变体 | min ms | med ms | 相对 bytes_env_arena |
|---|---|---|---|
| **bytes_env_arena** | 0.501 | 0.534 | 1.00× |
| **bytes_env_arena_tm** | 0.476 | 0.491 | 0.95× |
| bytes_env_list | 0.599 | 0.632 | 1.20× |
| rpn_owned | 0.704 | 0.715 | 1.40× |
| rc_term | 0.770 | 0.774 | 1.54× |
| naive | 0.777 | 0.784 | 1.55× |
| rc_value | 0.790 | 0.799 | 1.58× |
| bytes_flat_value | 77.5 | 78.4 | 155× |

n = 8000（7 轮，2026-08-28）：

| 变体 | min ms | 相对 bytes_env_arena |
|---|---|---|
| **bytes_env_arena** | 1.026 | 1.00× |
| **bytes_env_arena_tm** | 1.120 | 1.09× |
| bytes_env_list | 1.338 | 1.30× |
| rc_term | 1.549 | 1.51× |
| naive | 1.560 | 1.52× |
| rpn_owned | 1.579 | 1.54× |
| rc_value | 1.608 | 1.57× |
| bytes_flat_value | 312.8 | 305× |

## 结论（当初 readme 的「nbe_closure2 seems faster」基本正确，且更精确）

1. **字节码 + arena 环境（`bytes_env_arena`）是赢家**：比基线 `naive` 快
   ~1.5×，比 `bytes_env_list`（同样的字节码但环境用 `Rc` 链表）快 ~1.3×。
   `bytes_env_arena` 与 `bytes_env_arena_tm` 互有胜负（差距 ~5-10%，在噪声内）：
   把闭包体也搬进 arena 并没有带来可测收益——`prepend` 消除分配才是大头。

2. **项从 AST 换成字节码就有 ~1.5×，环境从 `Rc` 链表换成 arena 再有 ~1.2×**；
   值的 `Box` → `Rc` 无收益（rc_value 反而最慢，原子计数 > 拷贝），
   项再套 `Rc`（rc_term）也只拉平。

3. **`bytes_flat_value` 是陷阱**：值整段 memcpy + `App` 字节拼接导致
   O(n²) 退化——4000 时 77ms、8000 时 313ms（冠军的 300 倍）。扁平化
   省掉的间接性远偿不上拷贝量，规模一大就崩。

4. 其他变体在 8000 时与 `naive` 拉开到 ~1.5×，说明收益随规模略微扩大，
   但量级已定：**表示层能买到的加速封顶在 ~2×**，想更快得换算法
   （如 defunctionalization / 展开求值），这是 L02+ 的事。