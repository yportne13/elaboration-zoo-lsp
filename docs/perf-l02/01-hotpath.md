# L02 热点静态审计与候选优化清单（task-7）

范围：**性能版主路径** `src/L02_tyck/bump_spine_iter.rs`（1715 行）+ 基准口径
`src/bin/l02bench.rs`（265 行），参考版 `src/L02_tyck/mod.rs` 只作对照。
方法：静态走查（`文件:行号` 锚定）+ **确定性分配计数**（`l02l05mem`）。
**本文件不含任何墙钟计时**：我没有跑 `l02bench`，没有取基准锁；只跑了
`l02l05mem --sizes` 与 `run_mem.sh`（k=9/11，分配计数是精确量、无噪声）。
所有"预期量级"都是待 task-6 基线 / task-8 消融 / task-9 A/B 校准的**假设**。

> **引用口径提醒**
> - `src/L02_tyck/readme.md` 的实测数字来源是 **Windows x64**（release，
>   LTO + codegen-units=1 + mimalloc，预热 1 次 + N 轮取 min）。**不能当作
>   本机事实**；本文件只在"机制方向"上引用，量级一律标"待判定"。
> - `docs/perf-l01/*` 的数字来源是**本机 aarch64/Termux，cpu7，med_of_min**，
>   但量的是 L01（`src/L01_nbe`）。L01 的结论**不自动迁移**到 L02——凡涉及
>   迁移处本文件都单独给机制差异与证伪条件。
> - 本机判定协议（task-6 harness `tools/perf-l02/run_bench.sh`）：`taskset -c 7`
>   + keep-alive + 独占锁 + **强制 `--only` 单实现隔离** + 整轮 N reps +
>   指标 `med_of_min`。噪声界（承接 L01 轮量化，task-6 将复测）：
>   **<5% 永不可判；5–20% 需 ≥21 reps/侧 + 同批空对照；≥20–25% 可判**。
>   7 reps/侧的空 A/B p95 假阳 14.6%（21 reps/侧 p95 中位 2.6%、最坏 14.8%）。
> - 确定性口径 `tools/perf-l02/run_mem.sh`（= `l02l05mem --chapter L02`）**不是
>   计时**，不进锁：分配次数/字节逐位可复现，用来给"分配/churn/容量"类候选
>   零噪声证据（也用来证伪：分配计数无变化 ⇒ 该候选不可能是分配轴的问题）。

---

## 0. 结论摘要

### 0.1 Top-3（按 预期收益 × 置信度 / 风险）

1. **C1 `W` 枚举瘦身 40B → 24B（`W::PiBody` 携带 Π 节点指针而非
   `(name, cod, env)`）**。实测 `W` = **40B**（`W::PiBody(&str, &Tm,
   Option<&EnvCons>)` = 32B payload + tag），而 L01 的 `W` 只有 24B；eval
   主循环每一步按值 pop 一个 40B 枚举，β 数 3n、右链下钻每层还要 push。
   改后 replica 实测 24B（每次 push/pop 省 16B 搬运）。L02 特有（Π 是 L02
   新增变体），改动 ~10 行、零语义风险、分配计数**不变**（纯栈流量）。
   预期 1–4%，必须在墙钟上看。
2. **C2 β/let 尾任务寄存器化（免 `work.push(W::Tm…))` + `pop` + jump-table
   分发）**。`:304`/`:313`（β）与 `:326`（let）三处 push 的任务在**下一轮
   循环必被弹出**（LIFO 无中间项），却写 40B 进 `work` 再读回 40B。church
   β=3n、conv 两侧各 3n β（readme:126-128，Windows x64 探针）
   ——这是两族负载的公共主项。预期 2–6%，低风险（严格 LIFO 等价）。
3. **C3 conv 判等记忆化条件化（哈希税/`Store` 屏障）**。`:686` 每个弹出的
   Pair 都做一次 `FxHashSet<(u64,u64)>` 查表，`:711/727/743/754/773` 每个
   复合对都压 40B `WItem::Store` 并在弹出时 insert（表扩容 = 逐调用分配）；
   **线性负载永不命中**却付全额税。头寸上界可由内建消融
   `L02_NO_CONV_MEMO=1` 零成本量出（readme:209-211 记 k=12 conv 0.833 vs
   0.807ms ≈ +3.2%，噪声内 ⇒ 头寸 ≤ ~3%）；能否回收要看阈值化后是否仍
   保留 conv_dup 的 1.4–1.6×。

**最可能被证伪的一条：C2**。机制上 `work` 是 L1 常驻的热 Vec，push/pop 是
2 次"store-forwarding 友好"的 40B 搬运 + 1 次高度可预测的容量/长度更新；
在 Cortex-X2 这类 OoO 大核上很可能被吸收到 <5%（永不可判档）。**先做 C1
（纯字节数）再看 C2 是否还有空间**——C1 落地后 C2 的每次 push 成本下降，
两条收益会互相蚕食，必须分别单独 A/B 再叠加。

### 0.2 L02 特有、L01 轮没覆盖过的候选

- **C1（`W::PiBody` 让 `W` 变 40B）**：L01 的 `W` 是 24B（无 Π）。
- **C3/C6/C7（conv 工作表：记忆化、位相等预筛、条目布局）**：L01 没有 conv。
- **C4（`Tm` = 48B）**：L02 的 `Let`/`Pi` 变体把枚举撑到 48B；L01 的 `Bt`
  只有 24B。结果树的每个节点都付 48B。
- **C5（conv 逐调用草稿的 160B×N 分配）**：L01 的 conv 不存在。
- **C9（`bench_check_nf` 计时窗内含 `tm_size`，而 `basic` 不含）**：L01 的
  bench 只计 `normalize`，没有这个口径不对称。

### 0.3 产品影响（如实）

`mod L02_tyck` 在 `src/lib.rs:36-37` 声明，带
`#[cfg_attr(not(test), allow(dead_code))]` → **非 test 构建里是死代码，无
调用点**。真实使用者只有两个基准 bin（`src/bin/l02bench.rs:53-61`、
`src/bin/l02l05mem.rs:147-148`）和三个黑盒测试
（`tests/l02_blackbox.rs:29-30`、`tests/l02_blackbox_v2.rs:29-30`、
`tests/l03_blackbox.rs:37-38`）。**本轮所有候选的产品收益都是 0**，价值在
"研究/基准产物"与"给 L03+ 的机制模板"（L03+ 的性能版是 L02 的继承体）。

---

## 1. 候选优化清单（C1–C13）

排序 = 预期收益 × 置信度 / 风险。`--only` 每次只允许一个实现（harness 强制）。
影子树统一 `/tmp/l02-exp`、二进制 `target/release/l02bench-exp`（task-9 的
约定）；A/B 必须**同批交错、≥21 reps/侧**，并同批跑一个空对照
（同二进制奇偶半分组，`-N 42 --tag nullab` + `tools/perf-l02/null_ab.py`）。

### C1 `W` 枚举 40B → 24B（`W::PiBody` 改携带 Π 节点指针）

- **机制**：`W` 最宽变体是 `PiBody(&'a str, &'a Tm, Option<&'a EnvCons>)`
  = 16+8+8 = 32B payload；加判别式/对齐后 **40B**（replica 实测，见 §6）。
  eval 主循环每步 `while let Some(w) = work.pop()` 按值搬出 40B；每次
  `work.push(W::…)` 存 40B。而 Π 节点本身就是 `Tm::Pi(name, dom, cod)`：
  `PiBody` 只需携带**节点指针 + env**（16B），arm 内再 `match` 取
  name/cod。改后 replica 实测 `W` = **24B**（与 `App`/`Lam` 的 push 同宽）。
  每次 push/pop 少 16B 的 store+load；三处 `W::Tm` push 与 `PiBody` 都受益。
- **落点**：定义 `bump_spine_iter.rs:217`；构造 `:245`
  (`work.push(W::PiBody(name, cod, env))`)；执行 `:328-331`。
- **预期量级**：**1–4%**（work 栈搬运量 ∝（β + 下钻 + ChainWrap）次数；
  L1 带宽不是瓶颈，所以上限不高）。L02 特有。
- **难度**：低（~10 行）。**语义**：不变（同一 Π 节点，同一求值顺序）。
  **需改源码**：是。
- **判定命令**（影子 A，主树基线 B，同批交错）：
  ```bash
  tools/perf-l02/run_bench.sh --only fast    -w church -k 15 -N 21 --bin target/release/l02bench-exp
  tools/perf-l02/run_bench.sh --only fast    -w conv   -k 15 -N 21 --bin target/release/l02bench-exp
  tools/perf-l02/run_bench.sh --only fast_ss -w church -k 15 -N 21 --bin target/release/l02bench-exp
  # 同批空对照（同一二进制、奇偶半分组）：
  tools/perf-l02/run_bench.sh --only fast -w church -k 15 -N 42 --tag nullab
  tools/perf-l02/null_ab.py 'docs/perf-l02/raw/*nullab*_rep*.txt'
  ```
  harness 每档都从 k=9 跑到 `--max-k`，判定只看 k=13/15（`--ks 13,15` 只过滤显示）。
- **证伪条件**：影子 A/B 的 |Δ(med_of_min)| ≤ 同批空对照 p95 → 判"未判定/
  无收益"；由于 `l02l05mem` 分配计数**预期零变化**（work Vec 的容量与次数
  不变），这条**只能靠墙钟**，没有确定性旁证——若 A/B 落噪声内就直接判死，
  不要靠"机制上应该更快"续命。
- **确定性验证**：`l02l05mem` 预期：`fast`/`fast_ss churn` 的 allocs/bytes
  **完全不变**（这是"证明它是纯栈流量"的对照，也是证伪路径）。
- **消融开关**：不适用。

### C2 β/let 尾任务寄存器化（免 work push/pop + 分发）

- **机制**：`W::Apply`（`:297-308`）、`W::ApplyKnown`（`:309-314`）、
  `W::LetBody`（`:323-327`）三处的最后一句都是
  `work.push(W::Tm(c.body, Some(node)))`，而循环下一轮**必然**先 pop 它
  （LIFO，臂内没有其它更晚的 push）。于是每次 β/let 多一次 40B store +
  40B load + 一次 jump-table 分发。用循环局部 `cur: Option<W>` 接管这三处
  即可（其它多推臂不变）。church β=3n、conv 两侧各 3n β（readme:126-128，
  Windows x64 探针）——两族的主项之一。
- **落点**：循环头 `:236`；三处 push `:304`/`:313`/`:326`。
- **预期量级**：**2–6%**（β 密度主导；conv 与 church 同量级）。
- **难度**：低（~25 行）。**语义**：不变（严格 LIFO 等价）。
  **需改源码**：是。
- **判定命令**：同 C1（church + conv，`--only fast` 与 `fast_ss` 各一遍）。
- **证伪条件**：A/B ≤ 空对照 p95 → 判死（"store-forwarding 吃掉搬运"，与
  L01 C15 小栈常驻同类现象）。或与 C1 叠加后增量 ≤ 地板 → 说明 C1 已把
  该路径的边际成本压到不可判。
- **确定性验证**：分配计数**预期完全不变**（无新分配、无容量变化）→
  确定性口径对本条无分辨率，属"必须墙钟"的候选。
- **消融开关**：不适用。

### C3 conv 判等记忆化条件化（空表短路 + 阈值化 `Store` 屏障）

- **机制**：三笔税。(a) `:686` 每个弹出的 `WItem::Pair` 都做一次
  `memo.contains(&(t.0,u.0))`：2 个 u64 的 FxHash + 表探测；(b)
  `:711/727/743/754/773` 每个复合对都压一个 40B `WItem::Store`，弹出时
  `:654-656` `memo.insert`，哈希表扩容走全局分配器；(c) `:649` 每次 conv
  调用新建表（首次 insert 分配）。线性负载（church/conv）下 `Store` 插入
  的对在**本轮内不会二次出现**，全是纯开销；只有 conv_dup（readme:203-211）
  的同一昂贵子对 3 次重现才需要它。条件化：只给"屏障子树 dispatch 数 ≥
  阈值"的对入表（阈值可用一次 dispatch 计数器在 `:654` 弹出时判定），并
  在 `memo.is_empty()` 时短路查表。
- **落点**：`:649`（表）、`:686`（查）、`:711/727/743/754/773`（压屏障）、
  `:654-656`（insert）。
- **预期量级**：**0–3%**，头寸被 `L02_NO_CONV_MEMO=1` 的消融差卡死
  （readme:209-211 记 k=12：conv 0.833 vs 消融 0.807ms ≈ +3.2%，噪声内）。
  **先跑消融，若 conv 上 ≤ 地板 → 本条直接判死**（没有可回收的税）。
- **难度**：中（阈值/延迟插入必须保持"合取屏障"语义：屏障弹出 ⇔ 其上方
  子比较全部成功入表）。**语义**：不变（只是少记/晚记）。
  **风险**：memo 漏记只影响速度、误记会影响正确性——必须过
  `cargo test --lib L02_tyck`（26 用例，含
  `conv_ablation_flags_agree_with_structural_path`）。
  **需改源码**：是。
- **零成本前置（内建开关）**：
  ```bash
  tools/perf-l02/run_bench.sh --only fast -w conv     -k 15 -N 21                     # 默认臂
  L02_NO_CONV_MEMO=1 tools/perf-l02/run_bench.sh --only fast -w conv     -k 15 -N 21  # 消融臂
  L02_NO_CONV_MEMO=1 tools/perf-l02/run_bench.sh --only fast -w conv_dup -k 15 -N 21
  ```
  两臂的差 = memo 的**总税**（查表 + 插入 + 扩容），是本候选的收益上界；
  conv_dup 上的负差（消融更慢）= 它保住的收益，条件化不能吃掉这部分。
- **判定/证伪**：影子 A/B ≤ 空对照 p95 → 判死；或 conv_dup 上出现回归
  > 地板（阈值把必要的记忆化挡掉了）→ 判死并回退。
- **确定性验证**：`l02l05mem` 的 `fast_ss churn` 里 160B 桶次数应下降
  （哈希表桶扩容减少）；若 churn **不变**，说明表就没扩容过，那么 (b)(c)
  两项收益≈0，只剩 (a) 的查表税（由消融给出上界）。
- **消融开关**：**这是唯一能被 `L02_NO_CONV_MEMO=1` 直接上界化的候选**，
  但它**不能**把"查表税"与"插入/扩容税"分开——要分开得看 `l02l05mem`
  的 alloc 计数，或影子副本里给 `Store`/`contains` 各挂计数器。

### C4 结果树节点瘦身：`Tm` 48B → 32B/24B（`Let`/`Pi` 载荷外置）

- **机制**：`bump.alloc(Tm::App(f,a))` 分配的是 `size_of::<Tm>()` =
  **48B**（`l02l05mem --sizes` 实测；最宽变体
  `Let(&str,&Tm,&Tm,&Tm)` = 40B payload + tag）。结果树里 App 节点只用到
  16B 载荷却占 48B：church nf = 2n+4 个节点（`l02bench.rs:160-165`），
  k=15（n=65536）结果树写 **6.3MB** bump 而非 3.1MB(32B)/1.6MB(24B)，
  `tm_size` 又要读一遍（§2.10）。readme:126-128 的探针记 bump 分配
  ~250B/输出节点（Windows x64），48→24 约占其中 10%。做法：`Let` 改存
  `&'a LetCell<'a>`，`Lam`/`Pi` 若要压到 24B 也各改存单元指针
  （App 变体 16B payload → 24B 枚举）。
- **落点**：定义 `:59-66`；构造/匹配点集中在 quote `:397,408,412,448,
  468,485,494,499,508,521,534`、`export:1136-1157`、`tm_size:1186-1204`。
- **预期量级**：**1–4%**，只作用于 **church/dup/dup_deep**（走 quote+nf）；
  conv/conv_dup 口径不 quote → 0。若改名每个节点还附带一次指针解引用，
  净收益要 A/B 才知。
- **难度**：中（~30 处构造/匹配；`export`/`tm_size` 同步）。
  **语义**：不变（内存布局 + 生成树形状不变；`tm_size` 逐出现计数不变）。
  **需改源码**：是。
- **判定命令**：
  ```bash
  tools/perf-l02/run_bench.sh --only fast -w church   -k 15 -N 21 --bin target/release/l02bench-exp
  tools/perf-l02/run_bench.sh --only fast -w dup_deep -k 15 -N 21 --bin target/release/l02bench-exp
  # 回归对照（应无差别）：conv 不 quote
  tools/perf-l02/run_bench.sh --only fast -w conv -k 15 -N 21 --bin target/release/l02bench-exp
  ```
- **确定性验证（强）**：
  ```bash
  ./target/release/l02l05mem --sizes            # 确认 Tm=48（改后 32/24）
  WORKLOADS=church K=15 ROUNDS=3 tools/perf-l02/run_mem.sh
  ```
  预期方向：`fast(one-shot)` 的 **arena chunk 总字节下降**（省 ≈ 24B × 节点数，
  k=15 约 3MB，跨 chunk 才能看见）；分配**次数不变**（bump 不经过全局
  分配器）。若 k=15 的 arena 字节无变化 → 候选无实际写入节省，判死。
- **证伪条件**：A/B ≤ 地板，或确定性 arena 字节不变。
- **消融开关**：不适用。

### C5 conv 逐调用草稿的内联化（hybrid 栈，避免"常驻缓冲膨胀"）

- **机制**：每次 `conv` 调用新建 `Vec<WItem>`（`:650`）、`Vec<W>`
  （`:916`）与 `FxHashSet`（`:649`）；首次 push 各触发一次分配
  （`WItem` 40B×4 = **160B**、`W` 40B×4 = 160B、hashbrown 桶）。确定性实测
  （我跑，k=9/11）：`fast_ss churn` = **176–290 allocs/轮**，其中 160B 桶
  156–274 次（k=11 church churn 199 allocs/162KB，160B×176）——**逐调用
  草稿是线性负载稳态 churn 的主体**。真实 LSP 场景 conv 调用数 ∝ check 数，
  这条会线性放大。
- **与已封顶轴的区别**：把栈**常驻**到 `Machine` 在 L02 实测 +4~13% 退化
  （`:826-837` 注释：church +6~13%、conv +4~10%、dup_deep +5~13%），
  **不要重试**。本条的机制不同：**栈内内联存储**（前 N 项放固定数组，
  深了才 spill 到 Vec），既不留"被历史最深调用撑大"的常驻缓冲，也免除
  浅调用的一次分配。可选实现：自写 `[MaybeUninit<WItem>; 8]` + spill Vec
  （引入 `smallvec` 会改 `Cargo.toml`，属环境轴混杂，不建议）。
- **落点**：`:649-650`、`:916`；`Machine::conv :909-924`。
- **预期量级**：**bench 规模 <1%**（churn ~200 allocs × ~25ns ≈ 5µs，
  对 k=13 的 0.85ms/1.5ms 是 0.3–0.6%）；**小 k / 高频小 check 1–3%**。
  无产品调用点 → 研究价值为主。
- **难度**：中。**语义**：不变。**需改源码**：是。
- **判定命令**：
  ```bash
  tools/perf-l02/run_bench.sh --only fast_ss -w conv -k 13 -N 21 --bin target/release/l02bench-exp
  tools/perf-l02/run_bench.sh --only fast_ss -w conv -k 9  -N 21 --bin target/release/l02bench-exp   # 小 k 更敏感
  ```
- **确定性验证（强）**：`WORKLOADS=conv K=11 ROUNDS=3 tools/perf-l02/run_mem.sh`
  → 预期 `fast_ss churn` 的 **160B 桶计数降到 0**（或只剩首次扩容）；
  allocs 总量预期降 150–250/轮。若 160B 桶不降 → 说明 160B 不是草稿
  （归因错误），本条判死。
- **证伪条件**：churn 桶计数不降，或墙钟 ≤ 地板。
- **消融开关**：不适用。

### C6 `Pair` 入栈前的位相等预筛（push-site bit-eq）

- **机制**：位相等检查在 `:683`，即**先把 40B `WItem` 从栈里 pop 出来**
  才比较。有两处 push 点可以先比打包字、相等就不入栈：`(2,2)` 内联环里
  `:785` 的 `Pair(l,f1,f2)` 与 `:796` 的 `Pair(l,a1,a2)`（`biteq` 开启时
  已经先比过 `f1.0!=f2.0` / `a1.0!=a2.0`，实际已在点上——**只有 `(0,0)`
  之外的臂没做**），以及各 `(1,*)`/`(4,4)` 臂压的 `Pair(l+1, vt, vu)`
  （vt/vu 是新 eval 出来的值，位相等概率低）。真正可做的是：`(4,4)` 的
  dom 对与 `(1,1)` 的子对在**压栈前**比一次，命中就省掉 pop+dispatch+
  memo 查询。
- **落点**：`:713`、`:729`、`:745`、`:757`、`:785`、`:796`。
- **预期量级**：**0–1%**（能命中的场景少：新 eval 的值打包字不同）；
  列出来是因为它是**唯一一类能被 `L02_NO_BITEQ=1` 上界化的改动**——
  任何"新增位相等剪枝"的收益上界 = 消融差（readme:91-98 记 conv k=13
  1.5→3.5ms ≈ **2×**，即全部位相等剪枝之和；单条远小于它）。
- **难度**：低。**语义**：不变（位相等只是加速，见 readme:266-269 教训 3）。
  **需改源码**：是。
- **判定/证伪**：
  ```bash
  L02_NO_BITEQ=1 tools/perf-l02/run_bench.sh --only fast -w conv -k 15 -N 21  # 上界
  tools/perf-l02/run_bench.sh --only fast -w conv -k 15 -N 21 --bin target/release/l02bench-exp
  ```
  A/B ≤ 空对照 p95 → 判死。
- **确定性验证**：分配计数不变（除非与 `Store` 数量相关——命中位相等会
  少压一个 `Store` 屏障，可看 `l02l05mem` churn 的微小变化，但**不能**
  作为主证据）。
- **消融开关**：**可用 `L02_NO_BITEQ=1` 给上界**，但注意它**同时**关掉
  `:683` 的逐对剪枝与 `:769-801` 内联环里的两处剪枝（`:784`/`:789`/`:795`）
  ——测出的是**三者之和**，无法归因到本候选。

### C7 conv 工作表条目 `WItem` 40B → 32B（或 `Pair`/`Store` 分栈）

- **机制**：`WItem` 最宽变体 `EvalCod2`（4 指针 + u32 = 36B payload）→
  **40B**（replica 实测）。每次 `Pair`/`Store` push/pop 搬 40B。改
  `EvalCod2(&'a EvalCod2State<'a>)`（bump 单元）后最宽变体是
  `Pair(u32,u64,u64)` = 24B → `WItem` 32B；或 pairs/stores 两条并行栈。
- **落点**：定义 `:608-627`；push 点 `:651,678,713,729,745,757,773,785,796`。
- **预期量级**：**0–1%**。readme:127-128 的"每元素 worksheet 往返"是**加
  内联环之前**的画像；加环之后每条链基本 1 次 dispatch（§2.3），条目数
  远小于 β 数，布局收益被摊薄。**低优先**。
- **难度**：中。**语义**：不变。**需改源码**：是。
- **判定/证伪**：`run_bench.sh --only fast -w conv -k 15 -N 21`（+conv_dup）；
  ≤ 地板判死。
- **确定性验证**：分配计数不变（栈容量变化只在很深时影响 Vec 扩容）——
  若 `l02l05mem` churn 不变且墙钟不可判，直接判死。
- **消融开关**：不适用。
- **注**：`QJob` 实测 48B（L01 轮记 56B 是 L01 形态），其瘦身属 **L01 C4
  已列的同一条轴**，本清单**不重复立项**（见 §3）。

### C8 一次性口径的 spine/vals 容量 + `fast_ss` chunk churn（诊断优先）

- **机制（a，`fast` 专属）**：`Machine::new` 把 `Spine` 预置
  `Vec::with_capacity(4096)`（`:850`，96KB）、`vals` 4096×8B（`:851`）。
  `l02bench` 的 `fast` 口径里 `Tycker::new()` 在**计时窗外**
  （`l02bench.rs:203-204`），所以只有**扩容**在窗内：church spine 条目
  ≈ n，k=15（n=65536）要 4096→8192→…→65536 共 4 次 realloc + 累计
  ~1.4MB memcpy；k=13 两次。把初值提到 16384（384KB，仍在窗外）可把
  k≤13 的扩容全部移出窗。**张力说明**：readme:140-141 实测否决的是
  **2^18（6MB）** 那一点，理由是"顺序 memcpy 便宜 + 不值得常备 6MB"；
  4096→16384 是曲线上的另一个点，且 L01 轮在本机实测 4096→16384 得
  `church_pair` −7.4%/−10.3%（`docs/perf-l01-optimization-2026-10-06.md`
  §3 第 2 行，本机、med_of_min、已复核）。**但 Lead 已明确：不要把 L01
  结论外推到 L02**——所以本条必须先拿确定性计数确认 L02 上确实有可省
  的扩容，再谈 A/B。
- **机制（b，`fast_ss` 专属）**：`Bump::reset` **只保留 current（最后、
  最大）chunk**，其余 dealloc（bumpalo-3.20.3 `src/lib.rs:1073-1113`）；
  新 chunk 按 2× 增长（同文件 `:2020-2024`）。稳态每轮：若该轮 bump 用量
  > 保留 chunk，就要在**计时窗内**重新 malloc 整条 2×/4×… chunk 链。这
  正是 readme:43-48 "`fast_ss` 跨轮持有大 bump 池 → 页被淘汰 → 大 k min
  被高估" 的机制层来源；readme:85-89 又记 `fast_ss` 在 L02 无 L01 式收益。
- **落点**：`:850-851`（容量）；`Tycker::new:1221-1226`；`bench_nf_impl`
  首行 `:1281`（`bump.reset()` 在窗内）。
- **预期量级**：`fast` 上 **0–3%**（视 k；扩容字节 ~1.4MB @k=15），
  `fast_ss` 上 **0**（容量跨轮保留）。产品影响 0（无调用点）。
- **难度**：低（改一个常量）。**语义**：不变。**需改源码**：是。
- **判定命令**：
  ```bash
  # 确定性门（先做）：看扩容次数/字节与 chunk churn
  WORKLOADS=church,conv K=15 ROUNDS=3 tools/perf-l02/run_mem.sh   # 看 fast 直方图与 fast_ss churn 的 arena 列
  ./target/release/l02l05mem --chapter L02 --workload church --k 15 --rounds 3 --no-basic
  # 只有确定性门通过才做墙钟：
  tools/perf-l02/run_bench.sh --only fast -w church -k 15 -N 21 --bin target/release/l02bench-exp
  ```
- **证伪条件**：确定性口径显示 `fast` 的 ≥4288B 分配（含 96KB/192KB/384KB
  spine 扩容）次数/字节可忽略（< 窗的 0.5% 量级），或 `fast_ss churn` 的
  `arena 0×` 在 k=15 仍成立（无 chunk churn）→ 判死。墙钟 A/B ≤ 地板同样判死。
- **确定性验证（强）**：**预期** `fast` 直方图里 ≥4288B 桶的计数减少
  1–4 次、字节减少对应容量；`fast_ss churn` 的 `arena N×` 若 k=15 出现
  N>0，则 (b) 有真实 churn（且给出了字节数），否则 (b) 机制不存在。
- **消融开关**：不适用。
- **⚠️ 与 task-9 通用优先级的冲突**：task-9 描述把"容量/预保留"列为
  零风险优先项，但 L02 的 readme 先验是**中性/负**（readme:85-89,
  140-141）。`tools/perf-l02/run_mem.sh` 是零成本裁决者：**确定性计数
  说没油水就不要开 A/B**。

### C9 `bench_check_nf` 计时窗内含 `tm_size`（测量卫生，不是优化）

- **机制**：`bench_nf_impl`（`:1280-1292`）的顺序是 `reset` → `infer` →
  `eval` → `quote_maybe` → **`tm_size`**，全部落在 `l02bench` 的
  `Instant::now()` 窗口内（`l02bench.rs:188-196/204-210/227-229`）。
  `tm_size`（`:1183-1207`）对结果树做**第二次完整遍历**：每节点 1 次
  Vec pop + match + 0–3 次 push。church nf = 2n+4 节点，k=15 ≈ 131k 节点
  ≈ 按 4–8 cycles/节点静态估 0.17–0.35ms（对照 readme 的 Windows x64
  church k=15 fast 3.3ms → **5–10%**，待本机测）。
- **口径不对称（重要）**：`basic` 走 `mod.rs:646-651` 的
  `bench_check_nf`，它只 `infer + nf + mem::forget`，**不含 `tm_size`**；
  而 `fast/fast_ss/fast_memo` 都含。→ readme 的 `basic/fast ≈ 13×`
  （church）与跨口径比较都被这一项偏置（fast 被加税 ⇒ 倍率被**低估**）。
- **候选（二选一，都属 bench/测量修正）**：① quote 里顺便计数（改源码，
  ChainRun 快路径要加计数）；② 把 `tm_size` 移出计时窗（改 `l02bench`，
  正确性跑里仍保留节点数断言）。**生产路径零收益**。
- **预期**：把 church/dup 族的计时窗缩短数个百分点、跨负载可比性变好；
  **不得计入任何优化收益**。
- **判定命令（先量化，需影子 bench 在 `:1288` 前后打点，或在窗外单独
  重复 `tm_size` N 次）**：若 `tm_size` < 窗的 2% → 只作文档注记，不改。
- **证伪条件**：`tm_size` 占比 <2%。
- **确定性验证**：不适用（这是墙钟口径问题）。
- **消融开关**：不适用。

### C10 elaboration：`Raw::U`/`Raw::Var` 的 check 特殊化 —— **预期≈0，不建议实验**

- **机制**：`check` 的 fall-through（`:964-977`）对每个节点先 `infer` 再
  `conv`；`Raw::U` 在 `a` 是 U 时可写成显式分支直接 `Ok(Tm::U)`，
  `Raw::Var` 在推断类型与期望位相等时也可省 conv（每次 conv 还附 2 次
  原子读 `:911-912`、建 Vec/HashSet）。church/conv 源里 `U`/`Var` 出现
  **O(k)** 次，而工作量是 2^(k+1) → 占比 <0.1%；readme:125-128 的探针也
  表明 elaborate 相不是热点（church ~7%、conv ~0.5%）。
- **落点**：`:964-977`；对照 readme 的参考语义 `mod.rs:276-289`。
- **预期**：bench **≈0**；真实大源上是 O(节点数) 的常数因子，但 elaborate
  相本身在整体里极小。**不列为实验项**。
- **确定性验证（若仍想看方向）**：`l02l05mem` 的 `fast_ss churn` 会少
  ~（省下的 conv 调用数 × 320B）——但**分配计数减少 ≠ 墙钟收益**（见 C5
  与 `:826-837` 的常驻缓冲反例）。
- **消融开关**：`L02_NO_CONV_MEMO`/`NO_BITEQ` 不适用。

### C11 elaboration 深名字/深环境查找（线性 `types` 链 + `nth`）—— **预期≈0，已裁决不下沉**

- **机制**：`infer(Raw::Var)`（`:990-1004`）逐 `TCons` 比较
  `tc.name == x.data`（`SmolStr`→`&str` 比较：长度 + memcmp）；`nth`
  （`:156-161`）沿 `EnvCons` 链走 idx 步。最内层引用 O(1)，**最老名字
  O(#binders)**；现有负载的引用都落在链头附近（readme:328-330），
  church k=15 下总计 ~O(k²)≈100 次比较 ≈ 几百 ns，占不了 3.3ms 的 0.1%。
- **落点**：`:990-1004`、`:156-161`；参考 readme:325-341「环境机制的低层
  朴素形态（刻意，下沉评估已裁决）」。
- **预期**：现有负载 **≈0**。**不立项**；重启条件 = readme:338-341
  明写的"l02bench 新增 chain 负载 / 出现链式引用形态"。
- **确定性验证**：无（不是分配轴）。
- **消融开关**：不适用。

### C12 parse / 源构造（`*_src` + parser + `with_pos`）—— **对 l02bench 恒为 0**

- **事实（读 `l02bench.rs` 确认）**：每个 k 的流程是
  `src = church_src(k)`（`:146-152`）→ `parser(&src,0)`（`:154`）→ 正确性
  断言（`:166-175`），**全部在** `fast_ss`/`fast`/`fast_memo`/`basic` 四次
  `Instant::now()`（`:189`/`:204`/`:227`/`:239`）**之前**。即 **parse 与源
  构造不在任何计时窗内**，优化它对 l02bench 数字的影响严格为 0。
- **量化它的占比意义（确定性计数）**：我实测 k=11 各负载 `parse` 行 =
  **296–477 allocs / 47–84KB**（church 296/46824B；conv 458/61416B；
  conv_dup 477/83688B），相对同负载 `fast` 的 1.5–4.7MB 是 2–5% 的分配
  足迹——但**不计时**。真实 LSP 端到端里 parse 是每次击键都付的唯一相，
  所以它是"bench 之外"的成本；readme:165-168 已实测 SmolStr 让 parse 慢
  15–29%（Windows x64，2 万行标识符密集源 29.4→34.2ms），readme:170-172
  留了 `Rc<str>` 未实测备选。
- **落点**：`l02bench.rs:146-175`；`church_src` 等 `:1336-1430`；
  `parser/mod.rs:11-20,146-163,256-265`；`parser/lex.rs:180-200`。
- **预期**：对 l02bench **0**；对真实输入是"每次输入必付的固定相"。
  **不建议为 bench 立项**；要碰就先在**窗外**建 parse 微基准（或直接用
  `l02l05mem` 的 `parse` 行做确定性对照）。
- **确定性验证（强）**：`l02l05mem` 的 `parse` 行：任何 parse/源构造改动，
  allocs/bytes 必须**逐位可复现地**变化；这是零噪声证据。
- **消融开关**：不适用。

### C13 conv eta 展开的句柄复用 —— **预期≈0，不建议单独立项**

- **机制**：`(1,_)`/`(_,1)` 两臂每次 `spine.push(u, v_lvl(l))`
  （`:725`、`:741`）都新建一条 `Entry`；spine 只增不减，若同一
  `(中和值, level)` 在一次 conv 内被 eta 展开多次，会得到不同句柄 →
  后续位相等永不命中。可加"conv 内 `(u.0,l) -> 句柄` 小缓存"复用。
- **落点**：`:715-746`。
- **预期**：**≈0**。重复子对的场景已由 `memo` 覆盖（readme:203-211）；
  线性负载的 eta 次数是 O(λ 层)（readme:193）。而且**新增句柄共享是
  健全性敏感改动**（句柄是 memo 键）——必须过
  `conv_ablation_flags_agree_with_structural_path`（`:1643-1714`）与
  readme:276-283 教训 5 的"枚举全部等价来源"检查。**不列实验项**。
- **消融开关**：`L02_NO_BITEQ=1` 可观察其边界（关掉后句柄不同也不再被
  剪枝，但这不构成收益证据）。

### 候选速览

| # | 候选 | 落点 | 预期 | 改语义 | 改源码 | 确定性(l02l05mem) | 消融开关 |
|---|---|---|---|---|---|---|---|
| C1 | `W` 40B→24B | `:217,245,328` | 1–4% | 否 | 是 | 无变化 | — |
| C2 | β/let 尾任务寄存器化 | `:236,304,313,326` | 2–6% | 否 | 是 | 无变化 | — |
| C3 | conv memo 条件化 | `:649,686,711-773` | 0–3% | 否 | 是 | churn 160B 桶↓ | ✅ NO_CONV_MEMO 上界 |
| C4 | `Tm` 48B→32/24B | `:59-66` + quote/export | 1–4%(nf 族) | 否 | 是 | arena 字节↓ | — |
| C5 | conv 草稿内联化 | `:649-650,916` | <1%（小 k 1–3%） | 否 | 是 | churn 160B 桶→0 | — |
| C6 | push-site 位相等预筛 | `:713…796` | 0–1% | 否 | 是 | 微 | ⚠️ NO_BITEQ 只给三者之和 |
| C7 | `WItem` 40B→32B | `:608-627` | 0–1% | 否 | 是 | 无变化 | — |
| C8 | spine 容量 + chunk churn | `:850-851,1281` | fast 0–3%/ss 0 | 否 | 是 | ✅ 计数字节 | — |
| C9 | `tm_size` 出窗 | `:1280-1292` | 窗 2–10% 的测量偏置 | 否 | 是(bench) | — | — |
| C10 | check 特殊化 | `:964-977` | ≈0 | 否 | 是 | churn↓但无墙钟义 | — |
| C11 | 深名字/环境 | `:156-161,990-1004` | ≈0 | 否 | 是 | — | — |
| C12 | parse/源构造 | `l02bench:146-175` | 对 bench 0 | 否 | 是 | ✅ parse 行 | — |
| C13 | eta 句柄复用 | `:715-746` | ≈0 | 否 | 是 | — | ⚠️ NO_BITEQ 不单独 |

---

## 2. 热点路径逐段走查（行号锚定 + 每迭代工作量）

### 2.1 计时窗边界与口径差异

| 事项 | 位置 | 说明 |
|---|---|---|
| 计时窗 | `l02bench.rs:189-196`(fast_ss)/`204-210`(fast)/`227-229`(fast_memo)/`239-245`(basic) | 窗口只包住被调函数体；`Tycker::new()` 在窗外（`:203`/`:226`） |
| 窗外内容 | `:146-175` | `*_src` 构造、`parser`、正确性断言全在窗外 → **parse 候选对 bench 恒 0**（C12） |
| 窗内第一件事 | `bump_spine_iter.rs:1281-1282` | `bump.reset()` + `machine.clear_round()`（`spine.stack.clear()`） |
| `fast` 窗内 | `:1284-1289` | infer → eval → quote → **tm_size** |
| `basic` 口径 | `mod.rs:646-660` | infer + nf（引用版）+ `mem::forget`；**不含 tm_size**（C9 的不对称来源） |
| 单位 | `l02bench.rs:195/260` | `as_micros()`，打印时 `/1000` → 毫秒、微秒精度 |
| 聚合 | `l02bench.rs:86-89,197` | 进程内 `min` + `median`；跨进程由 harness 取 `med_of_min` |

### 2.2 elaboration 主循环（check/infer，`bump_spine_iter.rs:934-1108`）

| 段 | 行号 | 每迭代（每源节点）工作量 |
|---|---|---|
| `check(SrcPos)` | `:936-940` | 复制 `Cxt`（4 字）+ 1 次递归；**每个 Raw 节点都被 `with_pos` 包一层**（`parser/mod.rs:146-163`） |
| `check(Lam)` under Π | `:942-952` | `alloc_str`（名字拷进 bump）+ `alloc(EnvCons)`(16B) + `eval(p.body)` 配 fresh env + 递归 check + `alloc(Tm::Lam)`(48B) |
| `check(Let)` | `:954-962` | `check(ty, U)`→可能 1 次 conv；`eval(ty)`；`check(val, va)`；`eval(val)`；`alloc_str`；`check(body)`；`alloc(Tm::Let)`(48B) |
| `check` fall-through | `:964-977` | 1 次 `infer` + 1 次 `conv`（含 2 次原子读 `:911-912` + 每次新建 Vec/HashSet）+ `alloc` |
| `infer(Var)` | `:990-1004` | 沿 `TCons` 链线性扫描，每项 1 次 `&str` 比较（长度+memcmp）+ `alloc(Tm::Var)`(48B) |
| `infer(App)` | `:1008-1030` | 递归 `infer(f)` + `check(arg)` + `eval(arg)` + `eval(cod)` with fresh `EnvCons` + `alloc(Tm::App)` |
| `infer(Pi)` | `:1037-1043` | `check(dom,U)` + `eval(dom)` + `alloc_str` + bind + `check(cod,U)` + `alloc(Tm::Pi)`(48B) |
| `infer(Let)` | `:1045-1053` | 同 check(Let)，但 body 走 `infer` |
| `Cxt::bind/define` | `:1081-1098` | 每次 **2 个 bump 分配**：`EnvCons`(16B) + `TCons`(32B)；`Cxt` 本身 Copy（4 字） |

密度：elaborate 相只占整体极小（readme:125-128 探针给 quote 相
**~93%**、conv 相 **~99.5%**，其余为 elaborate 与顶层 eval 等的补数），
所以这一节的候选（C10/C11）预期都很低。

### 2.3 conv 工作表循环与位相等剪枝（`:638-820`）

| 段 | 行号 | 每迭代工作量 |
|---|---|---|
| 循环头 | `:652-653` | `stack.pop()` 按值搬出 **40B**（实测 `WItem`=40B）+ match |
| `Store` 弹出 | `:654-657` | 1 次 `FxHashSet::insert((u64,u64))`（可能桶扩容 = 分配） |
| `EvalCod2` 弹出 | `:658-680` | 2 次 `eval_iter`（各 clear work/vals + `alloc(EnvCons)`16B）+ 压 1 个 `Pair` |
| 位相等 | `:683` | 1 次 64 位比较（+ 可预测不跳转） |
| 记忆化查表 | `:686` | FxHash 两个 u64 + 1 次表探测（**每个 Pair 都付**，C3） |
| `(1,1)` | `:691-714` | 2 次 eval + `alloc(EnvCons)`×2 + （memo 时）压 40B Store + 压 Pair |
| `(1,_)`/`(_,1)` | `:715-746` | 1 次 eval + 1 次 `spine.push`（新 Entry 24B，只增不减）+ Store + Pair |
| `(4,4)` Π | `:750-758` | 压 Store + `EvalCod2`（惰性：dom 先比，dom 不等则 cod 的 eval 整个省掉）+ Pair |
| `(2,2)` 内联环 | `:769-801` | 每层：2 次 24B 条目读（f,a）、1 次打包字比较、`v_tag(a)==2`×2、句柄比较；**只有 f 不位相等才压 Pair**；两侧 `.a` 仍是 spine 且句柄不同则继续下钻——加环后一条链基本 **1 次 dispatch**（readme:111-115 记再 1.1–1.2×） |
| `(3,3)`/`(0,0)` | `:803-813` | U/U 空臂；变量比较 level（`v_lvl_of` 各 1 次移位） |

位相等总贡献：readme:91-98 记 conv k=13 关闭后 1.5→3.5ms ≈ **2×**、
k=15 6.7→14.2ms；且该开关**同时**关掉 `:683` 与内联环 `:784/789/795`
两处（见 §4）。

### 2.4 quote 任务栈与 `ChainRun`（`:380-584`）

| 段 | 行号 | 每迭代工作量 |
|---|---|---|
| 循环头 | `:394-395` | `tasks.pop()` 按值搬出 **48B**（实测 `QJob`=48B）+ match |
| `Q` tag0 Lvl | `:397` | 1 次 `alloc(Tm::Var)`(48B) + done push |
| `Q` tag1 Clo | `:398-411` | （memo 时）查表；`alloc(EnvCons)`16B + `Lam1` + `EvalQ` 两次 push |
| `Q` tag2 Spine | `:430-490` | 查表 + 24B 条目字段拷贝（`:440-443`）+ 连续性判定（`:444`）+ `base` 两次条目读（`:446,452`）+ `ChainRun`+`Q` 两次 push |
| 二叉 fallback | `:462-489` | 恒假守卫（`:473`，结构上不可达）+ `App1/Q/Q` 三次 push；**只在非连续链** |
| `Q` tag3 U / tag4 Pi | `:412`/`:413-428` | 1 次 `alloc(Tm::U)`；Pi 是 `EvalQ`+`Pi1`+`Q` 三次 push + 1 次 EnvCons |
| `ChainRun` 内层 | `:526-536` | 每层：`spine.stack[i].f`（24B 跨步里读 8B）+ 打包字比较 + `alloc(Tm::App)`(48B) + store + `i>end`；**这是 quote 侧主导每层成本** |
| `ChainRun` 非平凡头 | `:537-576` | 压 48B `ChainRun` + 24B `Q`（续跑）；church 快路径（`fi.0==f0.0`）不落这里 |
| `EvalQ` | `:501-504` | 1 次 `eval_iter` 重入（复用 work/vals）+ `Q` push |
| `Lam1/Pi1/App1/MemoStore` | `:492-515` | 各 1 次 done pop + 1 次 `Bump::alloc`（48B）或表 insert |

探针画像（readme:125-128，Windows x64，k=17）：church 总时 **~93% 在
quote 相**，β=3n、spine push=n、`nth` 链步数 ≈11n、bump 分配约
**250B/输出节点**。

### 2.5 eval 双栈与 β 岔路（`:225-336`）

| 段 | 行号 | 每迭代工作量 |
|---|---|---|
| 循环头 | `:236` | `work.pop()` 按值搬出 **40B `W`**（C1）+ jump-table 分发 |
| `Var` | `:238` | `nth`（idx 次链步）+ vals push |
| `Lam` | `:239-242` | `alloc(CloCell)` **32B** + vals push |
| `U` | `:243` | vals push |
| `Pi` | `:244-247` | push `W::PiBody`(40B) + push `W::Tm(dom)` |
| `Let` | `:248-251` | push `W::LetBody` + push `W::Tm(t)`（类型槽不求值） |
| `App` 下钻 | `:252-296` | 每层：`Tm::App` 判别 + `Tm::Var` 头 → `nth` + `v_tag==1` 判 + vals push + `heads++`；闭包头 → `ChainWrap`(若 heads>0)+`ApplyKnown`+`Tm(a)` 三推（`:270-279`）；复合头 → 通用三推（`:284-293`） |
| `Apply` | `:297-308` | vals pop×2 + `alloc(EnvCons)`16B + `work.push`（C2） |
| `ApplyKnown` | `:309-314` | vals pop + `alloc(EnvCons)`16B + `work.push`（C2，免 `Tm(f)` 重查环境，readme:104-110 记 1.24–1.48× church） |
| `ChainWrap(k)` | `:315-322` | 1 次 vals pop(base) + k×(`vals.pop`+`spine.push`)+1 次 push；**heads==0 不压**（readme:109-110） |
| `LetBody` | `:323-327` | vals pop + `alloc(EnvCons)`16B + `work.push`（C2） |
| `PiBody` | `:328-332` | vals pop + `alloc(PiCell)` **40B** + vals push |

### 2.6 `Spine::push` 记账（`:188-199`）

每次 push：`stack.len()` load；`v_tag(a)==2` 判定；若延续则读前驱 `Entry`
的 `len`/`base`（24B 条目里 offset 16/20 两次 L1 load）；写 24B `Entry`；
返回 `(idx<<3)|2`。`ChainWrap` 连续 push 时前驱是**本循环刚写的**条目 →
每层一次冗余 L1 load（L01 C6 已列，见 §3）。`Entry` = 24B 实测。

### 2.7 `env nth` 与名字表示（`:156-161`、`:990-1004`）

`nth` = idx 次 `next` load + `expect` 分支 + 1 次 `.val` load；church 引用
落在头附近（idx 0–3），readme 探针记 `nth` 链步数 ≈11n（Windows x64，
k=17）——即**每 β 平均约 2–3 步**。名字：热路径（eval/quote/conv）中
`&str` 只作为 `CloCell.name`/`PiCell.name` 的胖指针随单元搬迁，**零字符串
操作**（readme:160-161）；字符串比较只出现在 elaboration 的
`tc.name == x.data`（C11）。

### 2.8 parser 与源构造（`parser/mod.rs`、`parser/lex.rs`、`*_src`）

- `with_pos`（`parser/mod.rs:146-163`）给每个产生式包一层
  `Raw::SrcPos`（`Box::new`）：每个源节点多一次堆分配 + check/infer 多一层
  递归帧；`p_spine`（`:184-194`）左折叠建 App 树；`p_raw`（`:256-265`）
  四路 `or` 带回溯。
- `*_src`（`bump_spine_iter.rs:1336-1430`）用 `s += &format!(…)` 逐 let
  拼接（O(k²) 字节拷贝，k≤21 无所谓）。
- **这些全部在 `l02bench` 计时窗之外（§2.1）**；确定性成本见 C12。

### 2.9 `Tycker` 稳态、`Bump::reset` 与 `fast_ss` 残余分配

- `Tycker::new`（`:1221-1226`）：`Bump::with_capacity(1<<20)`（1MB chunk）
  + `Machine::new`（`:848-854`：spine 96KB + vals 32KB）。`l02bench` 里在
  窗外；`l02l05mem` 的 `fast` 计数里**在窗内**（`l02l05mem.rs:383-390`）
  ——两个口径不可混读。
- `bump.reset()`（窗内，`:1281`）：bumpalo 语义 = 保留 current（最后、
  最大）chunk、dealloc 其余（bumpalo-3.20.3 `src/lib.rs:1073-1113`）；
  新 chunk = 2× 前一块（`:2020-2024`）。
- `machine.clear_round()`（`:856-861`）：`spine.stack.clear()`（O(1)、保容量）。
- 稳态残余（我实测，确定性，k=9/11）：`fast_ss churn` = **176–290
  allocs/轮、41–163KB/轮**，`其中 arena 0×`（k≤11 时保留 chunk 够用）；
  保留 chunk = 1.00MB（k=9）/2.01MB（conv_dup k=11，首轮 chunk 链
  [1.00, 2.01]MB）；churn 的主体是 **160B 桶 ×156–274**（逐 conv 调用的
  `Vec<WItem>`/`Vec<W>` 首分配）。
- readme:85-89：`fast_ss` 在 L02 未复现 L01 的稳态收益（elaboration 里
  bump 分配占大头）；readme:43-48：全量跑时 `fast_ss` 的大 bump 池页被
  淘汰、大 k min 被高估（conv_dup k=15 全量 21ms vs `--only fast_ss` 12ms）。
  → 容量/复用类候选（C8(b)）的先验是**中性偏负**，必须先用确定性计数
  确认 churn 存在。

### 2.10 结果/节点计数 `bench_check_nf`（`:1270-1292`）

`bench_nf_impl` = `reset`（`:1281`）+ `clear_round`（`:1282`）+ `infer`
（`:1284`）+ `eval`（`:1287`）+ `quote_maybe`（`:1288`）+ `tm_size`（`:1289`）。
`tm_size`（`:1183-1207`）是**窗内第二次全树遍历**（每节点 1 pop + match
+ push），且 `basic` 口径不含它（C9）。`l02bench` 的节点数断言
（`:160-169`）在窗外另跑一次。

### 2.11 我实测的确定性分配快照（`l02l05mem`，k=9/11，`--no-basic`）

| 负载 | parse | fast(一次性) | fast_ss churn/轮 | churn arena |
|---|---|---|---|---|
| church k=9 | 264 / 44.0KB | 179 / 1.19MB | 176 / 60.1KB | 0× |
| church k=11 | 296 / 46.8KB | 203 / 1.54MB | 199 / 162.8KB | 0× |
| conv k=9 | 426 / 58.6KB | 257 / 1.23MB | 254 / 41.8KB | 0× |
| conv k=11 | 458 / 61.4KB | 280 / 1.82MB | 275 / 46.3KB | 0× |
| conv_dup k=9 | 444 / 60.4KB | 273 / 1.43MB | 269 / 45.1KB | 0× |
| conv_dup k=11 | 477 / 83.7KB | 297 / 4.71MB（2 chunk [1.00,2.01]） | 290 / 49.6KB | 0× |
| dup k=9 | 310 / 48.5KB | 207 / 1.25MB | 204 / 65.2KB | 0× |
| dup_deep k=9 | 417 / 60.1KB | 273 / 1.46MB | 269 / 76.1KB | 0× |

命令（可复现，逐位一致；我把 raw 写到 `/tmp/l02mem` 以免占用 task-6 的
`docs/perf-l02/raw`）：

```bash
RAW_DIR=/tmp/l02mem WORKLOADS=church,conv,conv_dup,dup,dup_deep K=9 ROUNDS=1 NO_BASIC=1 tools/perf-l02/run_mem.sh
RAW_DIR=/tmp/l02mem WORKLOADS=church,conv,conv_dup K=11 ROUNDS=2 NO_BASIC=1 tools/perf-l02/run_mem.sh
./target/release/l02l05mem --sizes
```

> **读表警告（工具口径）**：`l02l05mem.rs:48-49,63-68` 的直方图只有 320
> 个桶，**≥4288B 的请求全部挤进最后一个桶**，打印的 `size 4288` 与
> `bytes = count×4288` 是**下界标签**（96KB/192KB 的 spine 扩容也在里面）。
> 另外 `realloc` 记的是**新容量**（`:122-126`），`Tycker::new` 在 `fast`
> 计数内（`:384`）而 `l02bench` 的 `fast` 窗口外（`l02bench.rs:203`）。
> 用这些数字做判定时不要把桶标签当精确尺寸。

---

## 3. 已经封顶、别再试的轴

| 轴 | 一句话依据（来源） |
|---|---|
| 左折叠应用树下钻 + 实参缓冲 | readme:132-135 实测**略负**（church 15.2–16.3 vs 14.1–15.0ms，Windows x64） |
| `ApplyKnown2`/`ChainWrapVal`（实参/base 连值携带） | readme:136-137 两负载中性偏负（work 变体变宽抵消弹压） |
| `nth` 小下标展开（0..3 unroll） | readme:138-139 **变慢**（17.0ms），编译器对短循环已够好 |
| spine 预分配 **2^18** | readme:140-141 中性 + 不值得常备 6MB（**注意**：C8 谈的是 4096→16384 另一点，且 L01 外推被 Lead 禁止——先过确定性门） |
| `-C target-cpu=native` | readme:142-143 church 略快、conv 略慢、均在噪声内，且牺牲可移植性 |
| eval 侧 β(clo,arg) 结果记忆化 | readme:144-152 否决且经住复验（昂贵 β 的键在任意负载不重复；每次 β 换一次哈希 ~8–10ns 对标 β ~14ns） |
| 名字表示（String→SmolStr）对性能版 | readme:154-172：性能版 eval/quote/conv **全程零字符串操作**（这条对以后所有"名字"类优化同样适用）；parse 在窗外 |
| 小栈/判等表**常驻** `Machine` | `bump_spine_iter.rs:826-837` 注释：L02 实测普遍变慢（church +6~13%、conv +4~10%、dup_deep +5~13%，fast/fast_ss 两口径、k=11..13 同向）；机制=常驻缓冲被历史最深调用撑大后踩冷地址段。**L03+ 才是分界线正侧，别往回灌** |
| `fast_ss` 的 L01 式稳态收益 | readme:85-89：L02 两口径速度相当（bump 分配占大头）；容量/复用先验中性偏负 |
| L03 式 name_map（O(1) 名字解析）与 defs 平坦区 | readme:325-341 刻意不下沉、已裁决；重启条件 = l02bench 出现 chain 类链式引用负载 |
| 恒假回灌守卫 | L01 轮判死（L01 `01-hotpath.md` C9 + `perf-l01-optimization-2026-10-06.md` §3 第 5 行）；L02 的同类守卫在 `:473`/`:545`，结构上不可达（源码注释 `:463-472` 已给论证） |
| 打包字 tag 位宽 | L01 轮判死；L02 用 3 位是**因为 5 个形态**（readme:289-291、`:8-9`），不是性能原因 |
| `#[inline]` 提示 / dispatch 形态 | L01 轮判死（LTO + CGU=1 自行决定，预期≈0–2%，icache 风险） |
| `ChainRun` 判据外提 | L01 轮实测**零效果**（4 个规模全 0.00%，LLVM 本就 unswitch）；L02 同类结构见 `:532-533` |
| `Entry` SoA / 边界检查消除 | L01 C3/C7 已列：SoA 在小 n 可能负、边界检查 ≈0–2% 不单独实验；L02 的 `Entry` 同宽 24B（实测）。**不重复立项**，可作为 C1/C4 落地的顺带项 |
| `QJob` 瘦身（48B→） | L01 C4 同一条轴（L01 记 56B，L02 实测 48B）。**不重复立项** |
| 输出侧 `export`+`pretty`（真实 LSP 必付） | 不在 l02bench 计时窗内（`:1289` 只到 `tm_size`；`run_impl` 里才 `quote_str`→`export`→`pretty`）；L01 C12 已说明其真实成本。**要量必须另开口径** |

---

## 4. 内建消融开关可用性（`L02_NO_BITEQ` / `L02_NO_CONV_MEMO`）

两开关都是 `static LazyLock<AtomicBool>`（`:591-596` / `:600-605`），
**环境变量只读一次并缓存**，入口每次只做一次 `Relaxed` load
（`:911-912`）→ 没有逐调用 `env::var` 开销，task-8 的消融 A/B 是同二进制、
只差代码路径，干净。

| 候选 | 能否被开关验证 | 说明 |
|---|---|---|
| C3 conv memo 条件化 | ✅ `L02_NO_CONV_MEMO=1` | 给出 memo **总税**的上界（查表+插入+扩容混在一起）；conv 无命中 ⇒ 差=纯税；conv_dup ⇒ 差=税−保住的收益 |
| C6 push-site 位相等预筛 | ⚠️ 部分 | `L02_NO_BITEQ=1` **同时**关掉 `:683` 的逐对剪枝与 `:769-801` 内联环的两处剪枝 ⇒ 只能得到**三者之和**（readme:91-98、:111-115），无法归因到单条 |
| C13 eta 句柄复用 | ⚠️ 间接 | 句柄共享后位相等才会命中；`NO_BITEQ` 关掉后收益归零，但"关掉后变慢"不等于"共享就有收益" |
| C1/C2/C4/C5/C7/C8 | ❌ | 与 conv 剪枝无关；开关测不出 |
| C9（tm_size 口径） | ❌ | 两个开关都不改变窗口边界 |
| C10/C11/C12 | ❌ | elaboration/parse 侧，两开关都不触及 |

**这两开关测不出什么（明确写出）**：

1. **无法分离 `NO_BITEQ` 内部两处剪枝**（逐对 `:683` vs 内联环 `:784/789/795`）
   ——要分离只能在影子副本里各挂一个分支（或临时把 `biteq` 拆成两个参数），
   本文件不支持把"总差"当成"某一条"的收益。
2. **无法分离 `NO_CONV_MEMO` 内部三笔**（查表税 / `Store` 压弹 / 表扩容分配）
   ——要分离用 `l02l05mem` 的 churn 计数（扩容）或影子计数器（次数）。
3. **对 quote/eval/Spine 布局类候选完全无分辨率**（C1、C2、C4、C7）。
4. **实际只影响 `fast`/`fast_ss`**：conv/conv_dup 族不出 `fast_memo`
   （`l02bench.rs:216` 只在 nf 负载注册）；`basic` 走 `mod.rs:135-171` 的
   递归 conv（无剪枝、无记忆化），开关对它无意义。
5. **不改计时窗**：`reset`/`clear_round`/`tm_size`/`parse`（窗外）都不受
   开关影响，所以 C8/C9/C12 不能借它们判定。

---

## 5. 编译期/构建轴（**环境轴，不是算法轴**）

现状（`Cargo.toml:178-181`）：`[profile.release] lto = true`、
`codegen-units = 1`、`opt-level` 默认 3；toolchain 固定 `1.98.1`
（`rust-toolchain.toml`）；bin 用 mimalloc（`l02bench.rs:42-43`）。

可试项（任何结论必须注明"换了构建配置"，且**不得**写进算法收益）：

1. `RUSTFLAGS="-C target-cpu=native"`：readme:142-143 已实测（Windows x64）
   church 略快、conv 略慢、噪声内且牺牲可移植性 → **先验否决**；本机
   big.LITTLE 下还必须说明绑定核（cpu7/X2），否则核间差异会冒充收益。
2. `panic = "abort"`：去 landing pad/展开表，热路径无 panic 时预期 0–2%；
   改变 panic 行为（长驻/服务形态需产品侧确认）。
3. PGO/BOLT：理论上对解释器环收益最大（常见 5–15%），但采样负载必须覆盖
   church/conv/conv_dup/dup 四形状（否则过拟合 church），属重工程，排在
   算法项之后。
4. `lto = "thin"`：与 `codegen-units=1` 组合下大概率中性偏负；不建议。
5. 编译时间轴（`cargo build` 的墙钟）与运行期性能是**两个轴**，本轮
    benchmark 不测；若 L02 要并入 L03+ 的构建矩阵，单独记。

本机判定：与基线二进制**交替**跑（harness `--bin` 指向新构建），同批
空对照作地板；`target-cpu` 结论必须**同核**（`--cpu 7`）复测。

---

## 6. 自证：行号抽查、尺寸、确定性计数

**行号抽查（≥5 条，已用 read/grep 复核，命令与结果一致）**：

| 引用 | 复核内容 |
|---|---|
| `bump_spine_iter.rs:217` | `PiBody(&'a str, &'a Tm<'a>, Option<&'a EnvCons<'a>>),` ✓ |
| `bump_spine_iter.rs:245` | `work.push(W::PiBody(name, cod, env));` ✓ |
| `bump_spine_iter.rs:304` / `:313` | `work.push(W::Tm(c.body, Some(node)));`（Apply / ApplyKnown）✓ |
| `bump_spine_iter.rs:326` | `work.push(W::Tm(u, Some(node)));`（LetBody）✓ |
| `bump_spine_iter.rs:686` | `if memo_on && memo.contains(&(t.0, u.0)) {` ✓ |
| `bump_spine_iter.rs:711/727/743/754/773` | 5 处 `stack.push(WItem::Store((t.0, u.0)));`（各带 `if memo_on` 守卫）✓ |
| `bump_spine_iter.rs:850` | `spine: Spine { stack: Vec::with_capacity(4096) },` ✓ |
| `bump_spine_iter.rs:531` | `let fi = spine.stack[i].f;`（ChainRun 每层）✓ |
| `bump_spine_iter.rs:1281-1289` | `bump.reset()`/`clear_round`/`infer`/`eval`/`quote_maybe`/`tm_size` 全在 `bench_nf_impl` 内 ✓ |
| `l02bench.rs:203-204` | `let mut tycker = Tycker::new();` 在 `Instant::now()` **之前**（fast 窗外的证据）✓ |
| `l02bench.rs:146-175` | `*_src`/`parser`/正确性断言全在计时窗外 ✓ |
| `mod.rs:646-651` | `basic` 的 `bench_check_nf` 无 `tm_size` ✓ |

**尺寸（两个来源）**：

- `./target/release/l02l05mem --sizes`（真实 pub(crate) 类型 + 同构副本；
  副本法在 L03/L04/L05 上已交叉验证 `real == replica`）：
  `L02 Tm=48 CloCell=32 PiCell=40 EnvCons=16 Entry=24 TCons=32`，`V=8`。
- 私有热枚举的独立 `rustc` replica 探针（`/tmp/l02sz/sz.rs`，不碰仓库源码）：
  `W=40`、`W(PiBody 改指针)=24`、`QJob=48`、`WItem=40`、`&str=16`。
  这与 `l02l05mem --sizes` 的方法同族，但私有类型没有第二来源交叉验证
  ——**task-9 若要依赖 `W=40`，建议先在影子副本里 `size_of` 复核一次**。

**确定性计数**：§2.11 的 k=9/11 两批，raw 在 `/tmp/l02mem/`（临时；
命令可逐位复现）。这些数字与墙钟无关，但足以对"分配/churn/容量"类候选
做**零噪声**判定。

---

## 7. 未覆盖 / 交给 task-8、task-9

- **task-8（消融）**：`L02_NO_BITEQ` 的"总差"需要拆成 `:683` 与内联环
  两处才能用于候选归因；`L02_NO_CONV_MEMO` 的差要在 conv（纯税）与
  conv_dup（税−收益）上分别读——本文件只给判定设计。
- **task-9（A/B）**：优先级建议 **C1 → C2 → C3(先消融门) → C4**；
  C5/C6/C7/C8 先过确定性门再谈墙钟；C10–C13 不建议立项。所有 A/B 需
  同批空对照 + ≥21 reps/侧，并做 A/A'（影子树同源未改重建）量化跨树混杂
  （L01 轮实测 ≤3%，L02 需自测）。
- **未审计**：`show_val`/`display_error`/`pretty_tm`/`export` 的错误与
  输出路径（不在 l02bench 热窗）；`tests/l02_blackbox*` 的测试耗时；
  L03+ 继承体（它们各自有自己的 readme 与候选面）。
- **待 task-6 基线校准**：本文件全部"预期量级"都是机制假设；一旦
  `docs/perf-l02/00-baseline.md` 给出本机 `med_of_min` 矩阵与噪声界，
  应回到每条候选的"证伪条件"把可判/不可判重新标注。
