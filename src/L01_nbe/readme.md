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
| bump_iter | 0.155 | 0.162 | 1.01× |
| cek_bump | 0.158 | 0.162 | 1.03× |
| bump_arena | 0.225 | 0.230 | 1.47× |
| bytes_env_arena | 0.490 | 0.519 | 3.2× |
| bytes_env_arena_tm | 0.543 | 0.553 | 3.6× |
| ast_env_arena | 0.572 | 0.699 | 3.7× |
| bytes_env_list | 0.585 | 0.658 | 3.8× |
| rpn_owned | 0.656 | 0.712 | 4.3× |
| rc_term | 0.711 | 0.729 | 4.6× |
| rc_value | 0.732 | 0.761 | 4.8× |
| naive | 0.744 | 0.756 | 4.9× |
| compiled | 0.171 | 0.202 | 1.12× |
| cek | 1.501 | 1.507 | 9.8× |
| bytes_flat_value | 76.1 | 79.6 | 497× |

n = 8000（7 轮，2026-08-28）：

| 变体 | min ms | 相对 bump_tree |
|---|---|---|
| **bump_tree** | 0.276 | 1.00× |
| bump_iter | 0.325 | 1.18× |
| cek_bump | 0.331 | 1.20× |
| bump_arena | 0.434 | 1.57× |
| bytes_env_arena | 1.038 | 3.8× |
| bytes_env_arena_tm | 1.210 | 4.4× |
| ast_env_arena | 1.275 | 4.6× |
| rc_term | 1.450 | 5.3× |
| rpn_owned | 1.484 | 5.4× |
| naive | 1.518 | 5.5× |
| rc_value | 1.522 | 5.5× |
| bytes_env_list | 1.523 | 5.5× |
| compiled | 0.350 | 1.26× |
| cek_bump | 0.331 | 1.20× |
| cek | 2.919 | 10.6× |
| bytes_flat_value | 313.6 | 1134× |

cek 大 n（5 轮；其余变体此时已栈溢出，无数据）：

| n | cek min ms | 扩展 |
|---|---|---|
| n | cek ms | cek_bump ms | bump_iter ms |
|---|---|---|---|
| 8000 | 2.919 | 0.331 | 0.325 |
| 16000 | 5.94 | 0.96 | ~1.0 |
| 32000 | 12.10 | 1.62 | ~1.6 |
| 64000 | 25.61 | 3.60 | ~3.5 |
| 128000 | 60.03 | 8.82 | ~9 |
| 256000 | 124.34 | 32.04 | 25.6 |
| 512000 | 252.20 | 67.34 | 63.4 |

## 结论（各轮探索的累积结论）

1. **`bump_tree` 是当前绝对赢家**（第三轮探索：分配全 bump + 结果树也 bump）：
   项/值/环境/**结果**全部 bump 分配（零 Rust 堆分配），n=8000 时 0.276ms——
   比第二轮冠军 `bump_arena` 快 1.65×、比基线 `naive` 快 **5.5×**。三轮的
   收益分解：bump 分配（vs mimalloc malloc）~3.4×，结果树 bump 化（省掉
   quote 阶段每节点一次 `Box::new`，测出占 bump_arena 的 30%）~1.4×，
   bump chunk 预分配 `Bump::with_capacity` ~1.1×。

2. **第四轮探索：两个"经典提速方向"也被实测否决**（累积教训）：
   - **指令数组求值（`compiled`，项编译成连续 `&[Ins]`）**：慢 1.1–1.3×——
     现代 CPU 的指针追逐在 cache 内几乎免费，数组索引 + 宽枚举分派反而更
     贵；劣势还随规模扩大。字节码解析（`bytes_env_list`）与指令数组在
     同一量级，都打不过 bump 引用树。
   - **手写裸 bump（`RawBump`，去 bumpalo 的 chunk 检查）**：慢 ~1.3× 且
     容量管理脆弱——bumpalo release 的快路径已近"指针 + 检查"，手写版
     引入的间接反而更贵。已被移除。
   至此"分配方式（bump）→ 表示（引用式）→ 项访问（树 vs 数组）"三条轴
   都探到底：**瓶颈已不在这些层面**，bump_tree 的每节点 ~17ns 就是这台
   机器上"解释式 NBE"的实用下限。

3. **第三轮的三个微优化也被否决**：
   - quote 改引用签名（消 `Bv::clone`）：慢 2.4×——浅拷贝本身便宜，引用
     间接反而破坏内联；
   - `#[inline(always)]`：慢 ~1.1×——热函数体膨胀破坏指令缓存；
   - **迭代 quote（显式任务栈）**：慢 ~1.3×——Vec 栈的边界检查与容量管理
     比机器栈帧贵，与 `cek` 的 kont 栈同一条教训：**在这台机器上，硬件栈
     就是最快的栈**。
   分段计时还确认了结构事实：`eval` 对 church_pair 只做 O(λ) 步（直接出
   闭包），重活全在 quote 的 Clo 重入展开。

4. **arena 环境的收益独立于项表示**：`ast_env_arena`（AST + `ListArena`）
   比 `naive` 快 ~1.25×，与字节码侧 `bytes_env_list → bytes_env_arena`
   （~1.2×）一致——换掉 `Rc` 链表是稳定的 ~1.2×，项表示的字节码化再给 ~1.2×。

5. **`bytes_flat_value` 是陷阱**：值整段 memcpy + `App` 字节拼接导致 O(n²)
   退化——8000 时 308ms（bump_tree 的 1100 倍）。扁平化省掉的间接性远偿
   不上拷贝量。

6. **`cek` 是最慢的常规变体（~11×）**——这个"慢"已被第五、六轮解决："栈安全
   不是只有 cek 一种做法，**bump_tree 递归可以直接改造**。两条等价路线：
   - `cek_bump`（CEK 通用 kont 栈：`Fun`/`Arg` 两条 continuation）；
   - `bump_iter`（双栈推土机：`work` 栈（待求值项 + `Apply` 标记）+
     `vals` 值栈，β 归约零额外条目——bump_tree 递归的更贴身改造）。
   实测两者性能**相同**（8000 时 0.325 / 0.331ms，慢 `bump_tree` ~17%，
   大 n 512000 时 63 / 67ms）——**显式栈的 ~17% 开销与 kont 形态无关**，
   换来的都是深度不受进程栈限。这就是栈安全方向的最终答案：显式栈的
   代价从 `cek` 的 ~11× 压缩到 ~1.2×。
   （注意：51 万+规模的线性栈消耗点尚未定位——栈指针采样证明不在 quote
   主循环；l01bench 用大栈线程跑大规模，默认 1MB 栈下 25.6 万可稳定通过。）

7. 还没试过的候选中，唯一可能再往下的路子是算法层的形态融合（在展开的
   同时直接生成结果的紧凑编码，跳过值树的中间形态）——但那已经脱离
   "表示层"的范畴，属于 L02+ 求值内核的设计题了。