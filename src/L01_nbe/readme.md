# L01_nbe — NBE 表示层实验的整理与基准

本模块把 `L01a_fast` 时代散落的 `nbe_closure*.rs` 实验按「表示轴」整理为 8 个
变体，加上求值策略变体 `cek`（CEK 机）与两轮 arena 探索的产物
`ast_env_arena` / `bump_arena`（共 11 个，见 `mod.rs` 的对照表），用统一的
基准回答当初那个问题：**项和值的表示方式对求值性能有多大影响？**

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

| 变体 | min ms | med ms | 相对 bump_arena |
|---|---|---|---|
| **bump_arena** | 0.219 | 0.229 | 1.00× |
| bytes_env_arena | 0.487 | 0.515 | 2.2× |
| bytes_env_arena_tm | 0.489 | 0.500 | 2.2× |
| bytes_env_list | 0.571 | 0.646 | 2.6× |
| ast_env_arena | 0.578 | 0.669 | 2.6× |
| rpn_owned | 0.640 | 0.675 | 2.9× |
| rc_term | 0.699 | 0.713 | 3.2× |
| naive | 0.724 | 0.734 | 3.3× |
| rc_value | 0.737 | 0.756 | 3.4× |
| cek | 1.489 | 1.492 | 6.8× |
| bytes_flat_value | 76.7 | 77.3 | 350× |

n = 8000（7 轮，2026-08-28）：

| 变体 | min ms | 相对 bump_arena |
|---|---|---|
| **bump_arena** | 0.437 | 1.00× |
| bytes_env_arena | 1.044 | 2.4× |
| bytes_env_arena_tm | 1.164 | 2.7× |
| bytes_env_list | 1.282 | 2.9× |
| ast_env_arena | 1.260 | 2.9× |
| rpn_owned | 1.419 | 3.2× |
| rc_term | 1.442 | 3.3× |
| naive | 1.506 | 3.4× |
| rc_value | 1.556 | 3.6× |
| cek | 2.991 | 6.8× |
| bytes_flat_value | 308.8 | 707× |

cek 大 n（5 轮；其余变体此时已栈溢出，无数据）：

| n | cek min ms | 扩展 |
|---|---|---|
| 8000 | 3.17 | — |
| 16000 | 5.94 | 1.9× |
| 32000 | 12.46 | 2.1× |
| 64000 | 25.37 | 2.0× |
| 128000 | 54.87 | 2.2× |
| 256000 | 113.5 | 2.1× |

## 结论（各轮探索的累积结论）

1. **`bump_arena` 是当前绝对赢家**（Rc 家族 → arena 家族的第二轮探索）：项/值/环境
   全部 bump 分配 + 引用式结构，比旧冠军 `bytes_env_arena` 快 **2.2–2.4×**、
   比基线 `naive` 快 **3.3–3.4×**（8000 时 0.437ms vs naive 1.506ms）。bump
   分配只是指针推进（无计数、无析构、无 malloc），引用直访比字节码解析 +
   下标查表还便宜。代价：生命周期贯穿单个 `Bump`，求值结果之外不能跨调用
   保存值（对 NBE 求值即用即弃的形态完全够用）。

2. **arena 环境的收益独立于项表示**：`ast_env_arena`（AST + `ListArena`）比
   `naive` 快 ~1.25×，与字节码侧的 `bytes_env_list → bytes_env_arena`（~1.2×）
   一致——换掉 `Rc` 链表是稳定的 ~1.2×，项表示的字节码化再给 ~1.2×。

3. **项从 AST 换成字节码 ~1.5×，环境从 `Rc` 链表换成 arena 再 ~1.2×**；值的
   `Box` → `Rc` 无收益（rc_value 反而偏慢，原子计数 > 拷贝），项再套 `Rc`
   （rc_term）也只拉平——这些在 bump_arena 面前都已被吸收。

4. **`bytes_flat_value` 是陷阱**：值整段 memcpy + `App` 字节拼接导致 O(n²)
   退化——4000 时 77ms、8000 时 309ms（bump_arena 的 350–700 倍）。扁平化
   省掉的间接性远偿不上拷贝量，规模一大就崩。

5. **`cek` 是最慢的常规变体（~6.8×），但它是唯一不爆栈的**：求值深度不受进程
   栈限——n = 26 万（church 52 万位加法）依然线性扩展、正确性断言通过，而
   其他变体在 16000 就连输入都构造不出来。取舍清晰：**有限深度要速度用
   `bump_arena`，要深度无上限用 `cek`**——若把二者结合（bump 分配 + 迭代
   求值）就是下一轮探索的自然方向。