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

| 变体 | min ms | med ms | 相对 bump_tree |
|---|---|---|---|
| **bump_tree** | 0.153 | 0.166 | 1.00× |
| bump_arena | 0.225 | 0.230 | 1.47× |
| bytes_env_arena | 0.490 | 0.519 | 3.2× |
| bytes_env_arena_tm | 0.543 | 0.553 | 3.6× |
| ast_env_arena | 0.572 | 0.699 | 3.7× |
| bytes_env_list | 0.585 | 0.658 | 3.8× |
| rpn_owned | 0.656 | 0.712 | 4.3× |
| rc_term | 0.711 | 0.729 | 4.6× |
| rc_value | 0.732 | 0.761 | 4.8× |
| naive | 0.744 | 0.756 | 4.9× |
| cek | 1.501 | 1.507 | 9.8× |
| bytes_flat_value | 76.1 | 79.6 | 497× |

n = 8000（7 轮，2026-08-28）：

| 变体 | min ms | 相对 bump_tree |
|---|---|---|
| **bump_tree** | 0.276 | 1.00× |
| bump_arena | 0.454 | 1.65× |
| bytes_env_arena | 1.038 | 3.8× |
| bytes_env_arena_tm | 1.210 | 4.4× |
| ast_env_arena | 1.275 | 4.6× |
| rc_term | 1.450 | 5.3× |
| rpn_owned | 1.484 | 5.4× |
| naive | 1.518 | 5.5× |
| rc_value | 1.522 | 5.5× |
| bytes_env_list | 1.523 | 5.5× |
| cek | 3.006 | 10.9× |
| bytes_flat_value | 307.5 | 1114× |

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

1. **`bump_tree` 是当前绝对赢家**（第三轮探索：分配全 bump + 结果树也 bump）：
   项/值/环境/**结果**全部 bump 分配（零 Rust 堆分配），n=8000 时 0.276ms——
   比第二轮冠军 `bump_arena` 快 1.65×、比基线 `naive` 快 **5.5×**。三轮的
   收益分解：bump 分配（vs mimalloc malloc）~3.4×，结果树 bump 化（省掉
   quote 阶段每节点一次 `Box::new`，测出占 bump_arena 的 30%）~1.4×，
   bump chunk 预分配 `Bump::with_capacity` ~1.1×。

2. **本轮试过的三个"优化"全被实测否决**（教训如下）：
   - quote 改引用签名（消 `Bv::clone`）：慢 2.4×——浅拷贝本身便宜，引用
     间接反而破坏内联；
   - `#[inline(always)]`：慢 ~1.1×——热函数体膨胀破坏指令缓存；
   - **迭代 quote（显式任务栈）**：慢 ~1.3×——Vec 栈的边界检查与容量管理
     比机器栈帧贵，与 `cek` 的 kont 栈同一条教训：**在这台机器上，硬件栈
     就是最快的栈**。
   分段计时还确认了结构事实：`eval` 对 church_pair 只做 O(λ) 步（直接出
   闭包），重活全在 quote 的 Clo 重入展开。

3. **arena 环境的收益独立于项表示**：`ast_env_arena`（AST + `ListArena`）
   比 `naive` 快 ~1.25×，与字节码侧 `bytes_env_list → bytes_env_arena`
   （~1.2×）一致——换掉 `Rc` 链表是稳定的 ~1.2×，项表示的字节码化再给 ~1.2×。

4. **`bytes_flat_value` 是陷阱**：值整段 memcpy + `App` 字节拼接导致 O(n²)
   退化——8000 时 308ms（bump_tree 的 1100 倍）。扁平化省掉的间接性远偿
   不上拷贝量。

5. **`cek` 仍是最慢的常规变体（~11×），但它是唯一不爆栈的**：求值深度不受
   进程栈限（n = 26 万依然线性）。取舍：**有限深度要速度用 `bump_tree`，
   要深度无上限用 `cek`**；"bump 分配 + CEK 迭代求值"的结合仍是开放方向
   （预期速度与深度兼得，但喷显式栈开销已有两次前科）。

6. 未验证的提速候选（留给以后）：手写裸 bump 分配器（省 bumpalo 的 chunk
   检查，预期 +10%）；指令数组求值（项压平成连续内存的 `&[Ins]`，去指针
   追逐，预期与 bump 相当或略快）；hash-consing 共享子树（对高度重复的
   结构有效）。