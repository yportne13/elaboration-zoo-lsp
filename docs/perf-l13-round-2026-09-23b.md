# L13 性能/内存深挖第三轮（2026-09-23 当日加场）

同日前两轮之后的加场轮：九路子 agent 两阶段并行——S1–S6 六路分析
（基准矩阵 / 采样归因 / 内存深挖 / 热路径读码 / 历史考古 / 优化实现），
S7–S8 两路在独立 worktree 落地两项已被归因证明的大机会（S3/S4 的
读码与剖析产物直接作为 S7/S8 的任务书）。口径沿用 09-23 §0 纪律：
共享机器多流并行下时间一律同窗交错 A/B 取 min，跨窗绝对值只作量级
参照；l06l13mem 分配计数为确定性硬口径。**九路全程未提交、未污染
主树**；未落地补丁归档 `docs/wip/l13-perf-round3/`。

## 1. 基线复测（S1，HEAD 9dbf99f）

全部可比时间指标落入 09-23 基线 ±7% 带（多数 ±4%）；nf 互检零新发散
（examples-hdl 6/6 `NF-DIVERGE 0/0` 为已知两版一致失败标签）。内存
硬口径逐字节复现：struct one-shot **107,629 allocs / 18.16MB**、natadd
fast_ss churn **0.35MB**、arena 新 chunk **0**。已知特征仍在：
wide_enum 宽度轴 ≈**n^2.33**（k=9→k=11：515.9ms→12,990ms）、参考版
struct ≈**n^1.81**（k=13 basic 1508ms；fast 保持 ~线性，k=13 时 58ms）。

## 2. 落地项（3 项）

### 2.1 覆盖检查索引化：宽表 O(n³) 名字扫描 → O(n) 查表（compiler.rs）

S2 用微基准 + 消融 + n^2.80 缩放把 wide_enum k=11 的 12.2s 钉死在
match 编译期 `covers` 覆盖检查：第 j 臂恰覆盖第 j 个构造子 ⇒ 每个
match fn ≈ Σᵢi²/2 = **n³/6 次短字符串比较**（n=2048 微基准实测
1.43e9 次、精确吻合；单次 1.4-2.4ns），3 个 fn = n³/2 ≈ 9.7-10.7s
（占 70-84%）。S8 落地 `CtorIndex`（名→下标 `FxHashMap`，
**每 match 编译一次**的 O(n) 构建）+ 一次 `covered: Vec<bool>` 预算；
窄表（构造子 <16，struct/church/strchain/prelude-*）不建表、走原线性
口径零额外分配。`covers` 原函数保留为参考口径（等价性基准）。

- 同窗交错 A/B（base=HEAD，min）：wide_enum **k=11 −83.5~84.8%**
  （12,112→1,993ms）、k=9 −37.9~42.2%、k=4/6 中性；
- 哨兵中性：struct +0.3% / church +1.3% / strchain −4.6% /
  prelude-core −3.6% / prelude-hdl +1.0%（fast 列）；
- 内存逐位不变（l06l13mem 四负载逐字节相同）；门禁全绿、nf 全标签一致；
- 主树冒烟（收编后）：wide_enum **k=11 fast 1,328.7ms**（会话初
  12,990ms，−89.8%）、k=9 203.2ms；struct 12.84ms / church 1.19ms /
  prelude-core 8.20ms 与基线持平。参考版 basic 列不动（其 covers 是
  另一份实现，仍为 n³——参考版作对照基准，本轮有意不动）。

### 2.2 参考版 `Tm::Drop`/`Val::Drop` 漏字段修复：27 处所有权字段（mod.rs）

S3 四链闭合（逐点栈 / 精确算术 / observe 消融 / OS 峰值）定位：
`drain_tm` 迭代析构把 `Tm::Sum.cases`（`Rc<Vec<Span<SmolStr>>>`）等
被 `_` 吞掉的所有权字段随壳一起 `mem::forget` ⇒ `RcBox` + 缓冲永不
释放。**`Val::drop` 内还有一份逐字拷贝的 `drain_tm`（S3 未报，S7 审出）
同病**。S7 按既有 ptr::read 模式补 `release_owned`，共 27 处
（Tm::drop 10 + Val 的 drain_tm 拷贝 10 + drain_val 7）。

修复前后每轮泄漏（探针，稳态）：

| 负载 | 修复前 | 修复后 | 降幅 |
|---|---|---|---|
| struct | 493,480 B | **0 B** | −100% |
| church | 4,920 B | **0 B** | −100% |
| match | 16,008 B | 4,608 B | −71.2% |
| wide4 / wide6 | 9.96MB / 35.2MB | 16.9KB / 72.2KB | −99.8% |
| **wide11** | **2,707,640,152 B** | **2,357,760 B** | **−99.91%** |

OS 峰值（`PeakWorkingSet64`）：wide11 r2 **5,210.8MB → 71.8MB**；
wide6 r8 368.9MB → 69.4MB 且不再随轮数爬升。时间中性偏正（重负载
−1~−3.5%，其余 |Δ|≤1.6%）。门禁 406/14/1 全绿、nf 逐标签一致、
l06l13mem 分配计数逐字节相同（只改释放侧）。

### 2.3 `l06l13mem` TRACE≤32 重入死锁修复（bin）

`trace_big` 首句 `trace_exact()` 的 `OnceLock::get_or_init` 闭包内
`std::env::var` 在分配器路径上首次执行（Windows 上自分配 UTF-16 缓冲
≥ 低阈值）⇒ 重入 `bump_sz` → `OnceLock` 同线程重入自旋 ⇒ size-32
官方口径直接挂死（实测 base：exit=124、零输出）。修法：三个 trace
环境变量提为原子量、`init_trace()` 里先读完再落值（此时分配器路径
不追踪，无重入链）。修复后 `TRACE_MIN=32` 正常打印 32B 精确桶；
无 trace 变量时输出与 base 逐字节相同。bin-only，不影响门禁目标。

## 3. 关键归因纠正（与落地项同等价值）

- **backlog #2"宽表分派扫描是 we11 主兑现路径"证伪**：值层
  `eval_aux` 分派只占 k=11 的 **0.4-1.4%**（k=9 2.6-8.6%）；与 09-23
  轮"逐调用重建索引 +9.1% 恶化"自洽——被索引的扫描本身太小。真身在
  同文件的编译期覆盖检查（见 §2.1）。S6 已把 per-node `MatchIdx`
  实现完整落地并验证（门禁绿、内存中性），但 A/B 仅 −0.2~3.4%、
  默认口径 ≤1.4%，**未达 <3% 门槛，按纪律回退归档**。
- **"16k 链 def 逐条 elaborate/注册"证伪**：k=4/k=6 全量消融实测
  21.6-38.6ms，是常数项，占 k=11 的 **0.2-0.3%**。
- **观察面是可测大项**（`L13BENCH_NOBSERVE` 运行时消融，两二进制互检）：
  prelude-core **39-41%**、prelude-hdl **19.0%**、wide_enum k=6/9
  **54-59%**、k=11 15-21%（k=11 上观察面经 L2 污染放大 n³ 扫描）。
  → backlog #6（LSP 侧延迟渲染）的最强定量依据。
- **tick 结构缺口（backlog #5 的定量化）**：内核仅 5 个 tick 点
  （machine eval/unify/check/infer_expr/后缀回退），compiler.rs /
  eval.rs / force.rs 零 tick ⇒ 本次 10s 级 `Compiler::compile` 区间
  整体被"上一个 tick 点"（eval 站点 91.8%）吸收。S2 给出补点优先级：
  ① `compiler.rs` 覆盖循环 + walk_pat 每臂 ② `eval_aux` 入口/第一遍
  出口 ③ `force.rs` vapp1/force-miss ④ `machine.rs` quote ⑤ tm_size。

## 4. 证伪与归档（4 项，补丁+数据在 `docs/wip/l13-perf-round3/`）

1. **MatchIdx per-node 分派索引**（backlog #2 原样）：实现健全、门禁
   绿、内存中性，收益 −0.2~3.4%（<3% 门槛）→ 回退归档。
   低噪声窗（NOBSERVE）8 行中 7 行 cand 全部样本低于 base，符号一致
   ——"效应为真、幅度不足"，非噪声误判。
2. **App 臂 Raw 双深克隆惰性化**（machine.rs `infer_expr`/`infer_expr_pm`）：
   prelude-core fast **+3.1%** / fast_ss −1.7%，符号不一致 → 回退归档
   （patch 存 `p4a-item1-app-clone-lazy.patch`，建议静窗重跑再定）。
3. **size-32 草稿栈复用**（quote/force/eval CallAsm/export）：帧内复用
   形态 0%、LIFO TLS 池形态 −0.02%，**均零收益**（S3 的逐点归因在
   l06l13mem 口径下不复现——8269 个 size-32 首块另有出处）。回退；
   下轮建议先移植 `l07whoalloc` 的分配点回溯再定池化目标。
4. **compact 期 cases 切片去重**（`Copier::casesmap`）：实现语义中性、
   门禁绿，但实测**零命中**（cases 切片在两条路径都按节点新分配，
   一份切片天然单引用者）→ 不落地存档，作"防退化护栏"备查。

## 5. 内存归因收口（S3 三项未决 + S7 落地）

- **size-32 之谜（A）**：三个独立站点（`quote.rs` 3 处嵌套
  `&mut Vec::new()` 草稿栈、`force.rs` splice 传参、`eval.rs` CallAsm
  臂 3 栈、`entry.rs` export `done`）的 8B 元素 Vec 首块（cap 4×8B=32B），
  **churn 非泄漏**（live 恒 0）；church 占每轮分配次数 **86.6%**、natadd
  77%、struct 3.9%。`docs §5` 的"struct 8269 个/one-shot"实为 church
  的数（本轮更正）。
- **压实画像（B）**：每次 prime **32 次**就地压实（30 文件边界 + 1 收尾
  + 1 次 decl 级 384MB 阈值触发）；~41MB/次拷贝、1.28GB 流量换
  **−1.99GB 常驻**（97.3MB vs 2,083MB live）；cap=1.125×live+1MB；
  单 decl churn 最大 +202MB（文件边界拦不住）。**档位不动**；
  机会在 `Copier` 15 张 memo 表跨压实复用。
- **压实切片去重（E）**：见 §4.4。
- **残留尾巴**：修 §2.2 后唯一残留泄漏 = `PatternDetail::Con` 的子
  `Vec`（384B/臂，`walk_pat`→`compiler.pats`→`alloc_slice_fill_iter`
  移进 bump 后永不 Drop）：wide11 **2.36MB/轮**、match 4.6KB/轮。
  栈级证据与 A 方案设计（孪生自有 `XPatDetail<'a>`）已存档，建议
  单独立项（预估 1-2 天）。
- 两项小项结论：`TRAIT_METAS_SNAP_POOL` 的 Err 路径已正确归还（S4
  的 panic 丢缓冲描述不成立，无需修）；`suffix_memo` Neg 条目整 Vec
  克隆低优先备查。

## 6. 门禁与主树验证（收编后复跑）

- `bash tools/gate_l13.sh`：**lib 406 / parity 14 / into_probe 1 全绿
  fail=0**（251s，含 5m15s release 重链）；
- `l13bench --workload all --max-k 11` 孪生 nf 互检与基线**逐标签一致**；
- 内存硬口径：struct 107,629 allocs / 18.16MB、church 9,576 /
  3.88MB 逐字节不变；
- 主树冒烟：见 §2.1 末。

## 7. Backlog（更新，按收益×置信度）

1. **观察面按请求类型延迟渲染**（LSP 侧；pcore 39-41% / phdl 19% 的
   生产级杠杆；挂钩点：observe.rs 渲染推迟到命中时 + (path,offset)
   有序索引）。
2. **`PatternDetail` 子模式树不再进 bump**（残留泄漏清零，wide11
   2.36MB/轮；A 方案设计已存档）。
3. **`Copier` 15 张 memo 表跨压实复用**（每次压实新建、从 0 长起）。
4. **内核 tick 补点**（§3 优先级表；先补 compiler.rs 覆盖循环与
   eval_aux，把 10s 级区间从 eval 站点拆出）。
5. **solve_trait_ref Phase-2 结果缓存**（09-23 §7.1 存档不变；设计
   草图已由 S4 补全：键+六守卫+三挂钩）。
6. size-32 分配点回溯归因（先移植 `l07whoalloc` 再定池化目标）。
7. 参考版自身 covers 仍 n³（basic 列 12.2s）——若参考版需退出对照
   基准角色再动。
8. 长尾（两轮未接）：双根压实、strchain/global arena 化、
   `TWIN_DECLB_CACHE` 地址键同款审计、known-bugs Bug1（文件末尾声明
   静默丢弃）。

## 8. 复现

```bash
# 时间基准 + 孪生互检
./target/release/l13bench.exe --workload all --rounds 5 --max-k 11
./target/release/l13bench.exe --workload wide_enum --max-k 11 --rounds 3
# 内存硬口径
./target/release/l06l13mem.exe --chapter L13 --workload struct,strchain,church,natadd --k 11 --rounds 3 --no-basic
# 观察面消融（运行时开关）
L13BENCH_NOBSERVE=1 ./target/release/l13bench.exe --workload wide_enum --max-k 11 --rounds 2
# 门禁
bash tools/gate_l13.sh && GATE_FULL=1 bash tools/gate_l13.sh
# 采样归因
bash tools/attr_l13.sh prelude-hdl --rounds 3
```

未落地补丁与证伪数据：`docs/wip/l13-perf-round3/`（4 个 patch + README）。
