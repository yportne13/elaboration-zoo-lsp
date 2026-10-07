# L01 热点静态审计与候选优化清单（task-2）

范围：**生产推荐路径** `bump_spine_iter`（一次性口径）+ `bump_spine_iter_ss`
（`Machine` 稳态口径），对照 `bump_spine`（递归，非右链形状更快）。
方法：纯静态走查 + 行号锚定；**本文件不含任何计时**，所有"预期量级"都是待
`00-baseline.md` 噪声界校准的假设。

> 引用口径提醒：readme 中的所有数字来源是 **Windows x64**（LTO +
> codegen-units=1 + mimalloc），本机是 aarch64 big.LITTLE，**不能**当作本机
> 事实；本文件只在"机制方向"上引用它们，量级一律标"待判定"。
>
> 本机计时统一口径（与 task-1 对齐）：`taskset -c 7`（单个 Cortex-X2）+
> 独占（`docs/perf-l01/.benchlock`）+ min-of-N≥7；低于 `00-baseline.md`
> 噪声界的差异判"未判定"。命令中 `./target/release/l01bench` 为 release 构建。

---

## 0. 结论摘要

**Top-3（按 预期收益 × 置信度 / 风险）**

1. **C1 `W::ApplyKnown` 回移 + `ChainWrap(0)` 消除**（L02 已有原型，L01 未回移）：
   右链下钻遇 β 岔路时函数值已在手，直接 β，省掉 `Apply` 三推里的一次
   `nth` 重查 + 一次 `W::Apply` 分发；`heads==0` 时不再压/弹空转的
   `ChainWrap`。**语义零风险、改动 ~15 行**；预期量级高度依赖负载的 β 岔路
   密度——L01 现有 `church_pair` 上大概率 < 噪声（见 C1 的证伪设计），
   guest/真实 elaborator 形状上可能 3–10%。
2. **C2 一次性口径的自适应预保留（spine/vals）**：`Spine` 常量预留 4096 槽、
   `vals` 从 0 起倍增（`bump_spine_iter.rs:354-364`）。n=4000 时 spine 需
   8000 槽 → 一次 `realloc`+96KB memcpy，n=8000 两次；`vals` 十几次倍增。
   预保留 = 一次机会把"一次性口径 vs `_ss`"的差距（Windows x64 记 17% @4000）
   收回一部分。预期 5–15% @4000，随 n 增大；零语义风险。
3. **C4 `QJob`/`ChainRun` 瘦身**：`QJob` 最大变体 `ChainRun` 让枚举到 56B
   （实测 `size_of`），而混合链每层要 push/pop 一个完整 `ChainRun` + 一个 `Q`
   ≈80B 任务栈流量。这正是推荐路径在**非右链形状**（parigot/exponential）
   输给递归版 ~2× 的机制之一（Windows x64 记 1.9–2.0×）。预期 0–10%，只对
   非右链形状有感。

**最可能被证伪的一条：C1 的 `ApplyKnown` 部分。** 因为 L01 现有负载的 β 岔路
次数是 O(1)（论证见 C1）：`church_pair` 的 2n 层链头全是 quote 期绑定的
**Level 值**（`bump_spine_iter.rs:177` 把 λ-binder 绑成 `v_lvl(level)`），
根本落不到 `v_tag(vf)==1` 分支。所以必须先做"岔路计数"再谈 A/B（设计见 C1）。

**不建议实验（预期收益≈0，已给出机制级论证）**：C9 恒假守卫、C10 打包字位宽、
C14 `#[inline]`。这三条写清楚比"试了再说"更有价值。

---

## 1. 候选优化清单

排序 = 预期收益 × 置信度 / 风险。每条都给"本机判定命令"与"证伪条件"。
`--only` 的变体名必须与 bench 注册名一致（guest 表见
`src/L01_nbe/bench.rs:135-148`）。

### C1 `W::ApplyKnown` 回移 + `ChainWrap(0)` 消除（高优先，零语义风险）

- **机制**：右链下钻遇到变量头解析出闭包（β 岔路）时，L01 现在推
  `W::Apply` + `W::Tm(f, env)`（`bump_spine_iter.rs:87-90`），随后
  `W::Apply`（`:108-119`）再把 `Tm(f)` 弹回来重新 `nth(env, i)`、再走一次
  `v_tag(vf)` 分发。而函数值 `vf` 在岔路点就已经在寄存器里。L02 的
  `W::ApplyKnown(vf)`（`src/L02_tyck/bump_spine_iter.rs:211` 定义、
  `:276` 压栈、`:309-314` 执行）直接用它做 β：省 1 次 `nth`（2 次依赖 load）、
  省 1 对 `work` push/pop（24B 枚举）、省 1 次 jump-table 分发。
  同时 L01 在 `:77`/`:87`/`:99` **无条件**压 `W::ChainWrap(heads)`，而
  `ChainWrap(0)`（`:120-127`）会 `vals.pop` 出 base 再 `vals.push` 回去，
  纯空转；L02 三处都改成 `if heads > 0`（`:261`/`:274`/`:286-288`）。
- **落点**：`src/L01_nbe/bump_spine_iter.rs:35-40`（`W` 加变体，仍 24B）、
  `:85-92`（岔路改 `ApplyKnown`）、`:77`/`:87`/`:99`（`if heads > 0`）、
  `:108-119`（新增 `ApplyKnown` 臂）。对照实现：
  `src/L02_tyck/bump_spine_iter.rs:211`/`:309-314`。
- **预期量级**：**待判定**。每个岔路省 ~10-20 条指令。L01 现有
  `church_pair` 的岔路次数 ≈ 2/次 normalize（见下），预期 **≈0**；
  guest/真实 elaborator 里"变量头绑定到未饱和闭包"的应用链有多热**未知**。
- **实现难度**：低（~15 行，拷贝 L02 形态；`W` 大小实测 24B 不变，不增栈流量）。
- **改变语义/输出形状**：否。β 归约顺序、spine 入栈次序、结果树完全一致
  （L01 单测 `chain_beta_fork`/`chain_mixed_heads`/`interleaved_chains_fallback`
  + `guest_shapes_ok` 应全绿）。
- **是否需改 L01 源码**：**是**（影子副本；主树冻结）。
- **本机判定命令**（三段分开看，因为岔路只在特定形状触发）：
  ```bash
  # ① 线性右链：预期看不到差异（岔路 O(1)）
  ./target/release/l01bench --workload church --only bump_spine_iter \
      --max-church 8000 --rounds 7
  # ② 复制强制：quote 侧多次强制，岔路次数随复制层数增加
  ./target/release/l01bench --workload dup --only bump_spine_iter \
      --max-church 8000 --rounds 7
  # ③ guest 三形状：parigot/exponential 求值期共享闭包，岔路最可能变热
  ./target/release/l01bench --workload guest --only bump_spine_iter --rounds 7
  ```
  A 版取主树构建的二进制，B 版取影子副本（`CARGO_TARGET_DIR=/tmp/l01-exp/target`）
  的二进制，**同一时段交替执行 A B A B…**，取各自 min。
- **证伪条件（两层，先廉价后正式）**：
  1. **先计数（零计时成本，优先做）**：在影子副本给 `:85` 的岔路分支与
     `:120` 的 `ChainWrap(k)` 各挂一个 `static AtomicUsize`，跑
     `--only bump_spine_iter --max-church 8000` 与 `--workload guest`，
     打印计数。`church_pair` 若岔路 ≈ 个位数、`ChainWrap(0)` 也只出现个位数，
     则**该负载上必然无差异**，直接判"优化无效（对本负载）"，不必 A/B。
  2. **A/B**：只有当计数显示岔路/空 ChainWrap 达到 10^5 量级（对应
     ≥0.1–1ms 的可省工作量）才值得跑；若 A/B 的 min 比落在
     `00-baseline.md` 噪声界内 → 判无差异。
- **如何区分"优化无效"与"负载不触发"**：用一个**能触发岔路的合成形状**。
  机制上，岔路要求钻取到的链头变量绑定到一个**未饱和的闭包**（不是
  quote 期的 Level）。最小构造：
  ```
  clo_chain(k) = (λh. λx. h (h … (h x))) (λy. y)
  ```
  eval 阶段把 `h` 绑成 `Clo(λy.y)`，quote 强制闭包体时 `h` 是闭包而非
  Level，于是 `k` 层每层都走 `:85` 的岔路（对照论证：`church_pair` 走同一
  位置的 `v_tag(vf)==0` 快路径，因为 `:177` 把 binder 绑成 `v_lvl`）。
  建议在影子 bench 里加 `clo_chain(k)`，`k = 32000/128000`。**若 C1 在
  `clo_chain` 上也无差异 → 机制本身无收益（真判死）；若 `clo_chain` 有差异
  而三个现成负载没有 → 结论应写成"对 L01 现有负载无效，对 elaborator 形状
  待 L02+ 侧量"。**
- **备注**：`docs/review-continuity/a1-r1.md:45` 把这条登记为"未下沉"，
  `:80` 给出的理由是"改 L01 变体会作废其基准叙事"——即**有机制但从未在 L01
  负载上量过**。若 C1 落地，必须作为**新变体文件**（如
  `bump_spine_iter_ak.rs`）而不是原地改 `bump_spine_iter`，否则 readme 的
  消融表/基线与既有数字全部作废。

### C2 一次性口径的自适应预保留（spine + vals）

- **机制**：`bump_spine_iter::normalize_imported`（`:353-365`）里
  `Spine` 常量 `Vec::with_capacity(4096)`，`vals` 直接 `Vec::new()`。
  右链负载的 spine 条目数 = 输出 App 数 ≈ 2n：n=4000 需要 8000 槽 →
  4096→8192 一次 realloc + 96KB memcpy；n=8000 两次。`vals` 从 0 起倍增
  （右链一次收 n 个链头，n=4000 时 ~11 次分配 + 累计拷贝）。
  这些都在计时窗口内（bench 的 `Instant::now()` 在 import 之后、
  `normalize_imported` 之前，`bench.rs:638-643`）。
- **落点**：`src/L01_nbe/bump_spine_iter.rs:354`（spine 容量）与 `:364`
  （vals `Vec::new()`）；对称位置 `bump_spine.rs:205`。
  实现：① 入口加容量 hint（`import_iter` 在计时外，可顺手返回 App 计数
  ——`bump_arena.rs:57-89`）；或 ② 保守放大常量；或 ③ 分段 spine
  （块数组，免 realloc，但索引要 div/mod，不推荐）。
- **预期量级**：**假设** 5–15% @n=4000（一次性口径），随 n 增大而增大；
  n≤1000 时可能因多预留 96KB 反而略慢（首次触碰页）。Windows x64 上
  一次性 vs `_ss` 的差距是 17%（4000）/22%（8000）/3.3×（512k），其中分配、
  倍增拷贝、首次触碰页是主要成分（readme 第 368-370 行）；`_ss` 行同时也
  少了 `Bump` 每轮重建，故不能把差额全算给预保留。
- **实现难度**：低（① 需要 API 小改；② 一行）。
- **改变语义/输出形状**：否（纯容量）。
- **是否需改 L01 源码**：**是**。
- **本机判定**：
  ```bash
  # 零改动敏感性探针：spine 的 realloc 阈值在 2n=4096/8192，即 n=2048/4096。
  # 看 bump_spine_iter 的"每元素耗时"在 n=2000→4000→8000 是否跳变。
  ./target/release/l01bench --workload church \
      --only bump_spine_iter,bump_spine_iter_ss --max-church 8000 --rounds 7
  # 正式 A/B（影子副本改容量）：
  ./target/release/l01bench --workload church --only bump_spine_iter \
      --max-church 64000 --rounds 5     # 大 n 段效果应更明显
  ```
  大 n 段（>8000）走 `bench_cek_deep`，`--only bump_spine_iter` 仍出赛
  （`bench.rs:1067`）。
- **证伪条件**：影子 A/B 在 n=4000 **与** n=32000/64000 都落在噪声界内 →
  预保留不是瓶颈，判死。若小 n 变慢且大 n 不变 → 只保留"大 n 专用 hint"，
  否则整条放弃。

### C3 SoA spine（第三条轴：分离 `f` / `a` / `len` / `base` 数组）

- **机制**：`bump_spine` 的 `Entry` 是 24B AoS（`f,a,len,base`，
  `bump_spine.rs:88-94`）。quote 的 `ChainRun` 内层**只读 `f`**
  （`bump_spine_iter.rs:261`），却按 24B/条 拉整条缓存行；右链在大 n 时
  spine 超 L2，扫描读放大 3×。`bump_spine_slim` 走的是"砍到 16B AoS +
  quote 期沿 `a` 下行推断连续性"，readme（Windows x64）实测在 n≤8000
  慢 17–22%、在 256k 反超 24B 版（5.99 vs 7.53）——说明**密度收益真实存在，
  但被推断开销吃掉了小 n 段**。SoA 是第三条路：保留 push 期 `len`/`base`
  记账（不付推断税），只把 `f` 单独成数组，让 ChainRun 扫描 8B/条。
- **落点**：`src/L01_nbe/bump_spine.rs:88-99`（`Entry`/`Spine` 拆分）、
  `:104-116`（push 变 4 次 push）、`bump_spine_iter.rs:184-196`（Q 的
  `f[h]`/`len[h]`/`base[h]`/`a[base]` 取用）、`:261`（ChainRun 只碰 `f[]`）、
  `:120-127`（ChainWrap）。**应新建变体文件**（如 `bump_spine_iter_soa.rs`）。
- **预期量级**：n≤8000 **可能负**（push 从 1 条 store 流变 4 条、4 次容量检查，
  AoS 24B×2n=192KB 在 A710 512KB L2 内不需要密度）；n≥64k **0 – +20%**
  （ChainRun 读字节数降 3×，但每层还要写 24B 结果节点，是写带宽主导，
  读的节省会被摊薄）。
- **实现难度**：中（新变体 + 所有 `Entry` 访问点改写；索引/容量检查要小心）。
- **改变语义/输出形状**：否（只改内存布局）。
- **是否需改 L01 源码**：**是**（新变体文件，影子副本）。
- **本机判定**：
  ```bash
  # 小 n（预期负收益，验证"是否真的负"）
  ./target/release/l01bench --workload church --only bump_spine_iter_soa \
      --max-church 8000 --rounds 7
  # 大 n（唯一可能回本处；作为新变体需在影子 bench 注册）
  ./target/release/l01bench --workload church --only bump_spine_iter_soa \
      --max-church 256000 --rounds 5
  # 以现存 slim 为密度上界的参照
  ./target/release/l01bench --workload church \
      --only bump_spine_iter,bump_spine_slim --max-church 256000 --rounds 5
  ```
- **证伪条件**：n=8000 回归 > 噪声界（预计 -5% 以上）**且** n=256k 的
  相对 `bump_spine_iter` 收益 ≤ 噪声界 → 判死（"密度在 L2 放得下的规模
  是二级效应"再次成立，且 SoA 的 push 变贵）。若 256k 只有 SoA 快而 slim
  不快 → 说明推断税确实是 slim 的问题，SoA 路线成立。

### C4 `QJob` / `ChainRun` 瘦身（非右链形状的任务栈流量）

- **机制**：`QJob` 实测 `size_of` = **56B**（最大变体 `ChainRun` 有 6 个字段：
  `level,next,end,f0,idx_node,prev`）。混合链（链头不全是同一 Level，
  例如 `f (g (h x))`）每层都落到 `:267-305` 的 `_` 臂：push 一个完整
  `ChainRun`（56B）+ push `Q`（24B）→ 再 pop `Q`、pop `ChainRun`，每层
  ≈80B 任务栈搬运 + 两次 56B 枚举按值移动。这正是推荐路径在
  **非右链形状**（parigot/exponential，readme 记递归版快 1.9–2.0×）落后的
  机制之一：church 纯右链走 `:263-266` 共享 `idx_node` 的快路径，
  **完全不碰任务栈**，所以 `church_pair` 测不出这一项。
- **落点**：`src/L01_nbe/bump_spine_iter.rs:136-155`（`QJob` 定义）、
  `:246-309`（`ChainRun` 臂）。方案：把链状态挪到独立的
  `Vec<ChainState>` 侧栈，`QJob::ChainRun(handle)` 缩回 24B；或把
  `ChainRun` 状态放在 quote 主循环的局部变量 + 侧栈里，避免每层重推全部字段。
- **预期量级**：church ≈0；混合链/非右链 0–10%；guest 峰值（parigot n=10、
  exponential n=20，结果 2^20 节点）最可能显形。
- **实现难度**：中（要保证嵌套 ChainRun 的续跑语义，`prev/next/end` 不丢）。
- **改变语义/输出形状**：否（栈纪律不变）。
- **是否需改 L01 源码**：**是**。
- **本机判定**：
  ```bash
  ./target/release/l01bench --workload guest \
      --only bump_spine_iter,bump_spine_iter_ss --rounds 7
  ./target/release/l01bench --workload church \
      --only bump_spine_iter --max-church 8000 --rounds 7   # 回归对照
  ```
- **证伪条件**：guest 三形状 min 均落噪声界内（且 church 无回归）→ 判死。
  注意 guest 的 parigot/exponential 有 `bump_spine_memo` 数量级优势
  （Windows x64 记 286×/517×），若生产默认开 memo，这条的**实际收益会趋近 0**
  ——开 memo 的路径由 memo 主导，不由任务栈主导。此点必须在实验报告里写明。

### C5 结果树 bump 分配的快路径（raw cursor arena）

- **机制**：结果树每个节点一次 `bump.alloc(Bt::App/Idx/Lam)`（`Bt` 实测 24B；
  调用点 `bump_spine_iter.rs:174,177,192,235,244,251,264`）。bumpalo 的
  `alloc` 每次都要取 chunk 游标、校验剩余空间、对齐、推进。输出密集的负载
  （`church_mul n=200` → n²=4 万节点；`exponential n=20` → 2^20≈100 万节点；
  Windows x64 记 0.317ms / 10.1ms）里，这是每节点固定开销。
- **落点**：同上全部 `bump.alloc` 热点；需要一次性的节点数上界 hint
  （与 C2 同一 API 改动：`import` 在计时外可以数节点/App 数）。
- **预期量级**：church_pair（4000 节点）≈0–3%；`church_mul`/`exponential`
  3–10%（假设 bumpalo 快路径 ≈2–3ns/次、总 10ns/节点量级）。
- **实现难度**：中高（要在 `Bump` 上安全地"预留一大块 + 裸游标"，
  引用生命周期仍需 `'a`；`unsafe` 面积大）。
- **改变语义/输出形状**：否。
- **是否需改 L01 源码**：**是**。
- **本机判定**：
  ```bash
  ./target/release/l01bench --workload guest --only bump_spine_iter --rounds 7
  ./target/release/l01bench --workload church --only bump_spine_iter \
      --max-church 8000 --rounds 7
  ```
- **证伪条件**：`church_mul 200` 与 `exponential 20` 的改善均 ≤ 噪声界 →
  bumpalo 快路径已被编译器内联得很好，判死。

### C6 `ChainWrap` 里消掉 `Spine::push` 的前驱 load（记账寄存器化）

- **机制**：`Spine::push`（`bump_spine.rs:104-116`）在 `a` 是 spine 句柄时
  要 `let prev = &self.stack[v_spine_of(a)]` 读前驱条目的 `len`/`base`。
  `ChainWrap`（`bump_spine_iter.rs:120-127`）连续 push 的每一条的前驱都是
  **本循环上一次刚写的**条目——`len`/`base` 完全可以留在寄存器里递增，
  却每层多做一次 L1 load + 一次索引计算。右链有 2n 层，等于 2n 次冗余 load。
  变体：右链下钻时链头先压 `vals`、`ChainWrap` 再弹回来（2n 次 Vec
  push/pop），也可考虑小数组暂存（链长 >阈值再落 `vals`）。
- **落点**：`bump_spine.rs:104-116`（加 `push_with(prev_len, prev_base)`
  或 `push_preceded`）、`bump_spine_iter.rs:120-127`。
- **预期量级**：1–4%（每层省 1 次 L1 load + 1 次下标计算；2n 层）。
- **实现难度**：低。
- **改变语义/输出形状**：否。
- **是否需改 L01 源码**：**是**。
- **本机判定**：
  ```bash
  ./target/release/l01bench --workload church --only bump_spine_iter \
      --max-church 64000 --rounds 7
  ```
- **证伪条件**：n=4000 与 64000 均落噪声界内 → 判死（load 太便宜）。

### C7 有界索引/边界检查消除（`get_unchecked` / `pop_unchecked`）

- **机制**：热路径上大量带检查的索引：`spine.stack[h]`（`:185`）、
  `spine.stack[base as usize]`（`:190`/`:196`）、`spine.stack[i]`（`:261`，
  ChainRun 每层一次）、`vals.pop().expect(...)`（`:109-110,122-123`）、
  `work.pop()`（`:62`，每步一次）。它们的"检查"是 1 个比较 + 1 个高度可预测
  的分支；在 A710/X2 上几乎免费，在 A510（顺序核）上稍贵。ChainRun 的
  `i<=end` 与 `end` 是否 `< len` 编译器无法证明，故每层保留一次边界比较。
- **落点**：`bump_spine_iter.rs:185,190,196,261,109,110,122,123`；
  `bump_spine.rs:104-116`。
- **预期量级**：**≈0–2%，不建议单独实验**（预测分支在 OoO 大核上不构成瓶颈；
  收益测量分辨率不够）。若与 C3/C4 一起改可顺手带上。
- **实现难度**：低但引入 `unsafe`（必须用不变量支撑 SAFETY 注释）。
- **改变语义**：越界从 panic 变 UB——对**受损输入**是语义变化；对 release
  基准路径（闭项、不变量成立）无变化。
- **是否需改 L01 源码**：**是**。

### C8 `env nth` 的重复查询缓存（右链下钻）

- **机制**：右链下钻每层都 `nth(env, *i)`（`:83-84`），而 `nth`
  （`bump_spine.rs:119-125`）沿 `EnvCons` 链走 `idx` 步（`Option` 每步一次
  `expect` 检查）再取 `.val`。church 链里每层的 `i` 与 `env` **完全相同**
  （都是 `Idx(1)` 对同一个 env），所以同一个值的 2 次依赖 load 被重复
  2n 次。一次 1-entry 缓存 `(env_ptr, i) -> vf` 即可在链内命中。
- **落点**：`bump_spine_iter.rs:73-95`（下钻循环内加缓存）；`nth` 本身
  `bump_spine.rs:119-125` 不动（深索引负载仍要它）。
- **预期量级**：0–5%（每层省 2 次 L1 load + 1 个可预测分支；对 A510 更友好）。
  深 de Bruijn 的 elaborator 项上可能更高，但 L01 的 church 索引 ≤2。
- **实现难度**：低。
- **改变语义/输出形状**：否。
- **是否需改 L01 源码**：**是**。
- **本机判定**：
  ```bash
  ./target/release/l01bench --workload church --only bump_spine_iter \
      --max-church 8000 --rounds 7
  ```
- **证伪条件**：落噪声界内 → 判死（env 头两级命中 L1，缓存不划算）。

### C9 每个迭代步的"恒假防御守卫"（`:214` / `:274`）——**明确判断：预期收益≈0，不建议实验**

同意 Lead 的初读，并补两条更强的论证：

1. **`:214`（Q 的二叉 fallback）根本不在任何内层循环**：它在 `QJob::Q(v,level)`
   的 `_` 臂里，只在"引一个中性值且不走连续右链"时执行。readme 与 memo 模块
   （`bump_spine_memo.rs:17-21`）都指出 church_pair 里 `Q` 的调用次数是
   **O(λ 层)**（链节点全走 `ChainRun`，不经过 `Q`），所以它每次 normalize
   只执行个位数次。
2. **`:274` 在 ChainRun 的内层 `loop` 里，但只在 `fi.0 != f0.0` 的 `_` 臂**：
   church 快路径 `:263-266`（`Some(n) if fi.0 == f0.0`）**永远不落 `_` 臂**；
   落 `_` 臂后代码立刻 `break` 并把状态交给新的 `ChainRun`（`:295-303`），
   所以它是"每层非同头链头一次"，不是"每层一次"。即使触发，代价只是对
   **已经 load 出来的** `fi`（`:261`）做一次 `and 3 / cmp / 预测不跳转`——
   相对同臂里 push 56B `ChainRun` + push `Q` 的开销，占比 ≤1–2%。

- **可否外提**：不能外提到循环外——`fi` 每层不同；能做的只有"改成
  `debug_assert!` + 依赖不变量"，但那是**语义决策**（不变量破坏时从"安全
  但慢的 fallback"变成 UB/错结果），收益换不来。L01 模块头
  （`bump_spine_iter.rs:15-19`）已论证守卫恒假，`bump_spine_slim`/
  `bump_spine_memo` 干脆不带守卫，但它们的实测差异来自连续性推断与哈希税，
  **无法**用来隔离守卫成本。
- **反例形状**：不存在——L01 的 eval 保证 spine 条目的 `f` 恒非闭包
  （β 岔路在压栈前先行归尽：`:85-92` 岔路分支不 push spine，`:108-119`
  `Apply` 闭包分支直接 β，`:120-127` `ChainWrap` 收到的链头来自 `:93` 的
  `vals.push(vf)`，而 `vf` 已在 `:85` 排除闭包）。所以该守卫在**所有可达
  执行**里都取假分支。
- **落点**：`bump_spine_iter.rs:214`、`:274`。
- **预期量级**：≈0（结构上不在热内层；即使在内层也只是 1 条预测分支）。
- **实现难度**：低；**风险**：删掉后若未来加 meta/惰性解会破健全性。
- **是否需改 L01 源码**：否（建议保留）。
- **结论**：**不列为实验项**。

### C10 打包字与 tag 位宽——**明确判断：预期收益≈0，不建议实验**

- **机制现状**：`V` = `u64`，低 2 位 tag（`00=Lvl`、`01=Clo`、`10=Spine`、
  `11` 空闲；`bump_spine.rs:33-68`）。解包全部是寄存器操作：
  `v_tag = v & 3`（1 条）、`v_clo_of = v & !3`（1 条）、
  `v_lvl_of/v_spine_of = v >> 2`（1 条）、构造 `v_lvl/v_spine = (x << 2) | tag`。
  代码里没有"重复解包"的热点：ChainRun 内层直接比较**打包字**
  `fi.0 == f0.0`（`:263`），不 tag 解包；`v_tag` 只在分发点用一次。
- **位宽**：3 个形态只需 2 位；L02 用 3 位是因为它有 5 个形态
  （`src/L02_tyck/bump_spine_iter.rs:8-9,71-99` 多出 `U`/`Pi`），**不是**
  性能原因。把 L01 扩到 3 位只会把 `<<2` 变 `<<3`，净收益 0；缩到 1 位
  放不下 3 个 tag。`11` 空闲也没有"多一个形态"的需求。
- **落点**：`bump_spine.rs:34-68`、`bump_spine_iter.rs:173`（分发）、`:85`。
- **预期量级**：≈0（无位宽余量可利用；解包次数已是最小）。
- **是否需改 L01 源码**：否。
- **结论**：**不列为实验项**。

### C11 编译期/构建选项（**环境轴，单独列**：优化的是构建而不是算法）

> 本节**不是**算法轴。任何结论都必须注明"换了构建配置"，且 `target-cpu`
> 会牺牲产物可移植性；本机 big.LITTLE（A510×4 + A710×3 + X2×1、governor=walt）
> 上还要说明绑定核。

- **现状**（`Cargo.toml` `[profile.release]`）：`lto = true`（fat LTO）、
  `codegen-units = 1`、`opt-level` 默认 3；release 已开 LTO/CGU=1；
  toolchain 固定 `1.98.1`（`rust-toolchain.toml`）。
- **可试项**：
  1. `RUSTFLAGS="-C target-cpu=native"`：对纯指针追逐 + 整数负载，主要影响
     调度与寻址模式；在 aarch64 上收益通常 0–5%，且 **big.LITTLE 下
     依赖实际运行核**（native 会按构建机探测）。判定：同一二进制分别用
     `taskset -c 7`（X2）与 `-c 0`（A510）看是否结论翻转。
  2. `panic = "abort"`：去掉 landing pad/展开表，代码更小（icache 友好），
     热路径无 panic 时预期 0–2%。
  3. PGO / BOLT：理论上对分支密集的解释器环收益最大（常见 5–15%），
     但需要采样构建，且**采样负载要覆盖 church/dup/guest 三形状**，
     否则会过拟合 `church_pair`。属重工程，建议排在算法项之后。
- **落点**：`Cargo.toml` `[profile.release]`、`rust-toolchain.toml`、
  `RUSTFLAGS`；源码 **0 行**。
- **预期量级**：`target-cpu=native` 0–5%；`panic=abort` 0–2%；PGO 5–15%（待判）。
- **改变语义/输出形状**：`panic=abort` 改变 panic 行为（LSP 进程崩溃策略），
  需产品侧确认；`target-cpu` 改变二进制兼容性。
- **是否需改 L01 源码**：否（改构建配置）。
- **本机判定**：
  ```bash
  RUSTFLAGS="-C target-cpu=native" cargo build --release --bin l01bench
  ./target/release/l01bench --workload church \
      --only bump_spine_iter,bump_spine_iter_ss --max-church 8000 --rounds 7
  ./target/release/l01bench --workload guest --only bump_spine_iter --rounds 7
  ```
  与基线二进制**交替**跑（A B A B…），不要只跑一轮。
- **证伪条件**：min 比 ≤ 噪声界 → 判无收益。注意：任何 build 轴结果都不能
  回写进"算法改进"结论。

### C12 结果输出侧成本（树 vs RPN vs export）——不在 l01bench 计时内，但真实负载会付

- **机制**：bench 只计 `normalize`；输出转换全在计时外：
  `bump_arena::export`（`bump_arena.rs:163-169`）是**递归 + 每节点一次
  `Box::new`**（Rust 堆分配，走 mimalloc）；大 n 段 bench 甚至用
  `mem::forget` 泄漏结果树来规避百万层 `Box` 树的递归析构
  （`bench.rs:985`、`:994`、`:1002`、`:1162`）——**析构成本被完全隐藏**。
  `bump_spine_rpn` 则直接写字节流（每层 ~10B 顺序追加 + App tag 批量
  `resize`，`bump_spine_rpn.rs:42-108`），readme 记"速度中性、体积 ~2.4× 小"。
- **真实 LSP 负载会付的成本**：拿到 `&Bt` 后要么 `export` 成 `Term`
  （1 malloc/节点）、要么做结构比较/遍历、要么转成别的表示。对
  `church_mul 200`（4 万节点）或 `exponential 20`（2^20 节点），
  `export` 的 malloc 次数=节点数，量级可能与 normalize 同阶；析构同理
  （若用 `Box` 树，还要一次递归 drop）。
- **落点**：`bump_arena.rs:163-169`（export）、`bump_spine_rpn.rs:42-120`
  （RPN 输出）、`bench.rs:505/520` 等（export 在计时外）。
- **预期量级**：**无法用现有 l01bench 判定**（不在计时窗口）；需要用
  "输出侧微基准"量：建议在影子 bench 加一个 `--export-cost` 模式，同轮
  分别计 `normalize` 与 `export(normalize)` 与析构，报告比值。
- **实现难度**：低（加计时口）/ 中（若改出迭代版 visitor API）。
- **改变语义/输出形状**：提供新 API，不改现有语义。
- **是否需改 L01 源码**：**是**（bench 或 API；若只加测量口则是 bench-only）。
- **判定命令（需先加输出侧计时口）**：
  ```bash
  ./target/release/l01bench --workload guest --only bump_spine_iter --rounds 7
  # 影子版加 --export-cost 后：
  ./target/release/l01bench --workload guest --only bump_spine_iter --export-cost --rounds 7
  ```
- **证伪条件**：`export` 时间 < normalize 的 10%（在目标规模上）→ 判定
  "输出侧不是瓶颈，不值得投入"，只保留 `bump_spine_rpn` 的体积优势说明。

### C13 非右链形状的混合递归 fast path（高收益 / 高风险，建议后置）

- **机制**：readme（Windows x64）实测递归版 `bump_spine` 在
  `parigot_add n=10` / `exponential n=20` 上比 `bump_spine_iter` 快
  1.9×/2.0×——递归调用直接返回值、没有 work/tasks 双栈的 push/pop + 判别
  分发。迭代化的代价是为"深度无上限"付的固定税。混合方案：入口带一个
  栈预算计数器，深度未超预算时走递归快速路径，超了回落到迭代路径
  （或反之：迭代外壳 + 递归内层）。
- **落点**：`bump_spine_iter.rs:51-131`（eval）与 `:159-313`（quote）。
  对照 `bump_spine.rs:128-152`/`:157-200`（递归版）。
- **预期量级**：**非右链形状最高 ~2×**（Windows x64 证据方向），
  右链形状 0；但**有共享的负载上 memo 才是答案**：readme 记
  `bump_spine_memo` 在 parigot_add n=10 是 0.207ms vs 非 memo 最快 59.2ms
  （286×）。所以这条只对"非右链且无重复强制"的形状有价值，生产收益面窄。
- **实现难度**：高（递归/迭代切换 + 栈预算 + 两套语义必须逐字等价）。
- **改变语义/输出形状**：否（深度受限时行为需与迭代版一致）。
- **是否需改 L01 源码**：**是**（建议新变体，别动推荐路径）。
- **本机判定**：
  ```bash
  ./target/release/l01bench --workload guest \
      --only bump_spine,bump_spine_iter,bump_spine_iter_ss --rounds 7
  ```
  先复现"递归快 ~2×"（Windows 结论在本机是否成立），再决定是否投入。
- **证伪条件**：本机 guest 上递归/迭代差距 ≤ 20% → 迭代税在本机不显著
  （A710 的 OoO 掩盖了栈操作），混合方案失去前提，判死并记录"本机特性"。

### C14 闭包/内联提示与 dispatch 形态——**预期≈0–2%，低优先**

- **机制现状**：热的小函数**已经**带 `#[inline]`：`nth`（`bump_spine.rs:119`）、
  `v_*`（`:37/41/45/49/53/57/65`）、`Spine::push`（`:103`）、
  `Spine::push` 解包等。`eval_iter`/`quote_iter`（`:51`/`:159`）**没有**
  内联标注——但它们体量大，LTO（fat）+ `codegen-units=1` 下 rustc 本来
  就会按启发式决定是否内联；`quote_iter` 里对 `eval_iter` 的重入
  （`:216/238/277`）若被强行内联会让 icache 膨胀。`match w` / `match job`
  是 jump table 分发，每个迭代步一次间接跳转（间接分支预测在现代大核上
  尚可，在 A510 上会贵）。
- **落点**：`bump_spine_iter.rs:51`/`:159`（是否加 `#[inline]`）、
  `:62-128`/`:171-311`（分发结构）。
- **预期量级**：≈0–2%；`#[inline(always)]` 甚至可能负收益（icache）。
- **是否需改 L01 源码**：是（若试）。
- **证伪条件**：A/B 落噪声界内 → 判死；不建议单独立项，最多随其他改动
  一起编译对比。

### C15 `Machine` 的小栈常驻（work/tasks/done）——预期≈0–1%

- **机制**：`Machine::normalize`（`bump_spine_iter.rs:334-348`）每次调用新建
  `work/tasks/done` 三个 `Vec::with_capacity(64)`（`:338`、`:342-344`），
  即每调用 3 次 malloc + 3 次 free；spine/vals 已常驻。源码注释
  （`:315-318`）解释了不常驻的原因：`struct Machine` 持有带 `'a` 的栈会与
  跨 `Bump::reset` 的借用冲突。
- **落点**：`bump_spine_iter.rs:319-348`。
- **预期量级**：大请求 ≈0；逐键小请求（LSP 高频小 normalize）0–1%。
- **实现难度**：中（要解决 `'a` 擦除，unsafe 或类型擦除）。
- **改变语义/输出形状**：否。
- **是否需改 L01 源码**：是。
- **证伪条件**：稳态口径 min 落噪声界内 → 判死（本负载 spine 主导）。

---

## 2. 热点路径逐段走查（行号锚定 + 每迭代工作量）

以下"每迭代"指**右链负载（church_pair）的每层链**：结果是 `church(2n)`，
eval 阶段在 quote 强制闭包体时处理 2n 层右链（`bump_spine_iter.rs:237-240`
的 `EvalQ` → `:51` 的 `eval_iter`）。

### 2.1 eval 双栈主循环（`bump_spine_iter.rs:62-131`）

| 段 | 行号 | 每迭代工作量 |
|---|---|---|
| `while let Some(w) = work.pop()` | `:62` | 1 次 Vec pop（len load + 检查 + 24B 枚举按值移出）+ 1 次 jump table 分发 |
| `W::Tm(Bt::Idx)` → `nth` | `:64` | 1 次 `Bt` tag load + env 走 `i` 步（每步 1 load + `expect` 分支）+ 1 次 vals push |
| `W::Tm(Bt::Lam)` | `:66` | 1 次 16B `CloCell` bump 分配 + vals push |
| `W::Tm(Bt::App)` 通用三推 | `:69` 起 | 3 次 work push + 2 次 vals pop（只在非右链形状） |

### 2.2 右链下钻（`:73-106`，church 每层走这条）

每层（head 是 Level 时）：

| 操作 | 行号 | 代价 |
|---|---|---|
| `match tm { Bt::App(f,a) }` | `:74-75` | 1 次 `Bt` 判别 load + f/a 两个指针 load；`import_iter` 前缀序使 `a` 指向下一个 App，**顺序访存**（预取友好） |
| `Bt::Idx(i)` 分支 | `:83` | 1 次判别 |
| `nth(env, i)` | `:84` | idx=1 时 2 次依赖 load（`.next`、`.val`）+ 分支 |
| `v_tag(vf) == 1` 快路径判定 | `:85` | 1 条 `and` + 1 条 `cmp` + 预测不跳转；**church 恒假** |
| `vals.push(vf); heads += 1` | `:93-94` | 1 次 Vec push（容量检查 + 8B store + len 更新） |
| `tm = a` | `:95` | 寄存器移动 |

→ 每层 ≈6–9 条指令 + 3–4 次 load，**零分配**。这条路径是 readme"eval 右链
快速路径（再 -43%）"的来源。

### 2.3 `ChainWrap`（`:120-127`）与 spine push（`bump_spine.rs:104-116`）

- `ChainWrap(k)`：1 次 `vals.pop`(base) + k 次 { `vals.pop` + `spine.push` } +
  1 次 `vals.push`。
- `spine.push` 每层：`stack.len` load；`v_tag(a)==2` 判定；若是链延续则
  `stack[idx]` 读前驱 `len/base`（24B 条目里 offset 16/20 两次 load）；
  写 24B `Entry`；返回 `v_spine(idx)`（1 条 shl+or）。
- **每层总代价**：~2 次 Vec 操作 + 1 次 24B load + 1 次 24B store + ~10 指令。
  注意：`ChainWrap(0)` 会 `pop` 出 base 再 `push` 回去，**纯空转**（C1）。

### 2.4 spine 只增不减语义

`Spine.stack` 从不弹出（`bump_spine.rs:96-99` 注释"槽位下标即句柄"），
所以 `Q`（`:183-187`）能安全地把 `Entry` 四个字段拷成标量后再触发
可能扩容的操作——这是源码里 `:182` 注释的风险点，任何新代码都不能在
持有 `&spine.stack[..]` 的同时 push。

### 2.5 quote 任务栈主循环（`:171-311`）

| 任务 | 行号 | 每迭代工作量 |
|---|---|---|
| `Q(v,level)` 分发 | `:171-173` | 1 次 Vec pop（**56B `QJob` 按值移出**）+ `v_tag` 1 次 and+2 cmp |
| tag 0（Level） | `:174` | 1 次 24B `Bt::Idx` bump 分配 + done push |
| tag 1（Clo） | `:175-180` | 1 次 16B `EnvCons` 分配 + 2 次 task push（`Lam1`/`EvalQ`） |
| tag 2（Spine）：拷字段 | `:183-187` | 1 次索引 + 24B load |
| 连续性判定 | `:188` | 1 次 u32 比较（`len>1 && base+len-1==h`） |
| 链头 `idx_node` | `:190-195` | `f0` load + （Level 头时）1 次 24B `Idx` 分配 |
| 派发 | `:197-205` | 2 次 task push（`ChainRun` 56B + `Q` 24B） |
| `Lam1`/`App1` | `:233-245` | 各 1 次 done pop + 1 次 24B `Bt` 分配 |
| `EvalQ` | `:237-240` | 1 次 **`eval_iter` 重入**（复用调用方 work/vals）+ 1 次 task push |

### 2.6 `ChainRun` 内层（`:246-309`，church 的主力）

每层（`fi.0 == f0.0` 快路径）：

| 操作 | 行号 | 代价 |
|---|---|---|
| `spine.stack[i].f` | `:261` | 1 次 24B 索引 + 8B load（AoS 下每层跨 24B，见 C3） |
| `fi.0 == f0.0` | `:263` | 1 次 64 位比较（**直接比打包字，不解包**） |
| `bump.alloc(Bt::App(n, prev))` | `:264` | bumpalo 快路径：chunk 游标 load/检查/推进 + 24B store（tag + 2 指针） |
| `i += 1` | `:265` | 寄存器 |
| 循环回边 | `:256` | 1 次 `i>end` 比较（可预测） |

→ 每层 ~10 条指令 + 1 次 8B load + 1 次 24B store。**这就是 quote 侧的主导
每层成本**；readme 记"流式右链再 -46%"正来自这里（相对逐节点递归的指针追逐）。

非共享链头（`fi.0 != f0.0`）落 `:267-305`：push 56B `ChainRun` +
push 24B `Q(fi)` → 后续 resume 时再 pop 两个 + 1 次 24B `App` 分配
（C4 的对象）。

### 2.7 结果树 bump 分配（C5）

全部结果节点分配点：`:174`（Idx）、`:177`（EnvCons，值环境不是结果树）、
`:192`（Idx 共享节点）、`:235`（Lam）、`:244`（App1）、`:251`（App，ChainRun
resume）、`:264`（App，ChainRun 快路径）。`Bt` 实测 `size_of` = **24B**；
`CloCell`/`EnvCons` = 16B。

### 2.8 `ChainWrap` / `Idx` 共享

- `ChainWrap`（`:120-127`）：收拢右链头，见 2.3。
- `Idx` 共享：`Q` 在 `:191-194` 为 `f0`（Level 头）只分配**一个**
  `Bt::Idx` 节点，`ChainRun` 在 `:263` 用打包字相等把 2n 层全部接到同一
  指针上——readme"Idx 节点共享"即此。它把 quote 侧分配从 2n+1 降到 n+2
  （结果仍是树，只是子树共享）。
- `Machine`（`:319-348`）跨调用复用 spine/vals：稳态口径省的是每轮
  spine 分配 + 倍增拷贝 + 页触碰（readme Windows x64：4000/8000 快 17%/22%，
  512k 快 3.3×）。残余成本：3 次小栈 malloc（C15）、`spine.stack.clear()`
  （1 条 store）。

### 2.9 `env nth`（`bump_spine.rs:119-125`）

`for _ in 0..idx { env = env.next }` → `idx` 次 load + `idx` 次 `expect`
（None 检查分支），最后 1 次 `.val` load。church 索引 ≤2 → 2–3 次 L1 load。
深索引负载应换 `env_slice`（readme 记 nth O(1)，但 church 测不出差异）。

### 2.10 V 打包字编解码（`bump_spine.rs:33-68`）

`v_tag` = `and #3`；`v_lvl/v_spine` = `shl #2 | tag`；`v_lvl_of/v_spine_of`
= `shr #2`；`v_clo` = `or #1`；`v_clo_of` = `and #!3`。全部单条寄存器指令，
`#[inline]`。**不是瓶颈**（C10）。

---

## 3. 已经封顶、别再试的轴

| 轴 | 依据（一句话） |
|---|---|
| `bump_spine_slim`（条目 24B→16B + quote 期连续性推断） | push 期记账（一次前驱 load）比 quote 期逐条下行推断便宜：Windows x64 实测 n≤8000 慢 17–22%，仅 n≥256k 因缓存密度反超，且仍远输 `_ss` 稳态复用（readme:166-175、242-258）。 |
| `native_clo`（项编译为原生 `&dyn Fn` 闭包树） | dyn 调用不可内联、每 β 3 次 bump 分配、**无法特化右链快速路径**：Windows x64 实测败给指针树解释 2.8×（readme:176-183）。 |
| `compiled`（项编译为定长 `&[Ins]` 数组解释） | 只替换项访问一层，中性应用分配变量已修正后仍比 `bump_tree` 慢 2× 量级（Windows x64 复测 0.220/0.428ms）：数组下标访问不敌指针树 + 形状特化（readme:138-141、`compiled.rs:1-13`）。 |
| `bump_spine_memo_inline`（memo 槽内联进值 cell，去哈希表） | 单槽只能留最后一次 `(值,level)`，parigot 的多 level 重复强制导致抖动→指数级变慢（n=10 慢 186×）：**哈希表同时保留多 level 条目是收益来源**（readme:309-330）。 |
| `bytes_flat_value`（值也压成扁平字节） | 值是整段 memcpy + 拼接，O(n²) 退化（Windows x64 n=8000 0.32s，2547×），不要用于生产（readme:24、104、360-361）。 |
| 输出编码轴（`bump_spine_rpn` 树 vs RPN） | 两类输出都是顺序写、每层固定开销同阶，速度中性（Windows x64 互有胜负）；收益只剩体积 ~2.4× 小，不是速度轴（readme:160-164）。 |
| `env_slice`（数组切片环境，nth O(1)） | church 基准索引 ≤2，nth 不是瓶颈；只有深 de Bruijn 索引负载值得试（readme:29、358-359）。 |

---

## 4. 行号抽查（验收项）

写完对以下 8 条做了 `grep -n` / `read` 复核（命令与结果一致）：

| 引用 | 复核内容 |
|---|---|
| `bump_spine_iter.rs:62` | `while let Some(w) = work.pop() {` ✓ |
| `bump_spine_iter.rs:64` | `W::Tm(Bt::Idx(i), env) => vals.push(nth(env, *i)),` ✓ |
| `bump_spine_iter.rs:85` | `if v_tag(vf) == 1 {`（β 岔路）✓ |
| `bump_spine_iter.rs:111` | `if v_tag(vf) == 1 {`（`W::Apply`）✓ |
| `bump_spine_iter.rs:214` | `if v_tag(ef) == 1 {`（恒假守卫①）✓ |
| `bump_spine_iter.rs:274` | `if v_tag(fi) == 1 {`（恒假守卫②）✓ |
| `bump_spine.rs:104` / `:109` / `:120` | `Spine::push` / `let prev = &self.stack[...]` / `nth` ✓ |
| `bump_spine.rs:205` | 一次性口径 `Vec::with_capacity(4096)` ✓ |
| `src/L02_tyck/bump_spine_iter.rs:211/276/309-314` | `ApplyKnown` 定义/压栈/执行 ✓ |

尺寸复核（独立 `rustc` 小程序，非 L01 源码）：`Bt`=24B、`W`=24B、
`Entry`=24B、`Entry16`=16B、`QJob`=56B。

---

## 5. 未覆盖 / 待后续

- `bump_spine_memo` 作为**生产默认**的税/收益边界（readme 已给方向：线性
  负载 +3–8% 哈希税，共享负载数量级收益）不在本审计的候选内——它是
  选型开关而不是新优化。
- 本机 aarch64 上"递归 vs 迭代"的真实差距（C13 的前提）必须由
  `00-baseline.md` 先给数；Windows x64 的 1.9–2.0× 不能外推。
- 所有候选的实验编排（影子副本、A/B 交替、噪声界套用）见 task-3 的
  `02-experiments.md`；`ApplyKnown` 已由 Lead 另派 `exp-ab`（task-4），
  本文件只提供判定设计。
