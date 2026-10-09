# prelude 第 3 轮（2026-10-09）独立验证

> 由 **verifier**（task-26）独立撰写。所有数字实测，标注口径与 DUT 指纹（`size + mtime + sha256`）。
> **状态：进行中** —— **§2（交付物 1：`NF-DIVERGE` 期望范式裁决）已完成**；§3–§4（交付物 2/3 的落盘项复算与轮次终稿）等各项**真的落盘后**再补。
> 第 1/2 轮文档：`docs/prelude-round-2026-10b.md`（645dc3bd）、`docs/prelude-round-2-2026-10-08.md`。

## 0. 本轮 DUT 指纹（「名字会骗人」：一律记 size + mtime + sha256）

| 用途 | 路径 | mtime | size | sha256 |
|---|---|---|---|---|
| 引擎侧主 DUT（l13bench 口径） | `target/prelude_scratch/lead_w16_l13bench.exe` | 2026-10-08 23:00:19 | 9,283,072 B | `790BB801972A7EBA091B1688B9E4959557F5D7A00642AAD333A0767C573D1EFE` |
| 参考版 DUT（typort 口径，第 2 轮冻结） | `target/prelude_scratch/lead_w16_typort.exe` | 2026-10-08 22:48:10 | 19,999,232 B | `9844617DFA0FBBBB47E6FE9F701F4147A7B70387CFFEA74506F578E147C33152` |
| (K) 修前 | `target/prelude_scratch/hdl_c_bin/typort_kbefore.exe` | 2026-10-09 02:21:14 | 20,004,864 B | `A14E4B41D32030D8674C3CAF7A10B43D4DC4F424D4333EFBF147837A9A7AE795` |
| (K) K1（**有回归，已回滚**） | `target/prelude_scratch/hdl_c_bin/typort_kafter.exe` | 2026-10-09 02:25:55 | 20,013,568 B | `3EFB530F0EE18905A922F175F1EB5FE71431913FF4E36A23233646F1D92897D4` |
| (K) K2（**最终**） | `target/prelude_scratch/hdl_c_bin/typort_kafter2.exe` | 2026-10-09 02:41:30 | 20,015,616 B | `FB36CABBCDD41267DB5DEB0CAE5D608CCCADF87A7BA021A8B95603BA1853D025` |
| (M) **修前基线**（= `e0bc4fec` 干净树 build） | `target/prelude_scratch/r3_base_typort.exe` | 2026-10-08 23:34:33 | 19,999,232 B | `F51E7A4B3735058BE9A3ADB303A86D856ADF3AB7C78D6FB8D632400252F947D9` |
| (M) **中间冻结副本**（task-30 后 / **task-29 前**，非最终） | `target/prelude_scratch/verify3/bin/typort_w3mid.exe` | 2026-10-09 03:26:49 | 20,028,928 B | `36E909FAEC653EB960C9A7A7859AA68B22ED60031A2ED99FB923C8424F59AF58` |

- `r3_base_typort.exe` 与 `lead_w16_typort.exe` **同 size（19,999,232 B）但 hash 不同**（`F51E7A4B…` vs `9844617D…`）⇒ **再次印证「size 不能当身份」**（第 2 轮 §6.9 的同类现象）。
- `typort_w3mid.exe` 是我在 **03:26:49** 从当时的 `target/debug/typort.exe` **抓取并冻结**的副本（task-29 落地前）⇒ 只用于 (M) 的字面量边界复算；**(K)/task-29 的最终复算等 Lead 发最终二进制**。

- 前三份的 sha256 我**自己算过**并与 Lead/owner 给的 `A14E4B41…` / `FB36CABB…` **逐位一致**。
- 以上都是**冻结的 `cargo build` 产物**；**本轮全程未用 `target/debug/*`**（可能被 owner 窗口的 build / `cargo test` 覆盖，见第 2 轮 §6.9）。
- 本轮**不跑 cargo**（避免与 owner 抢锁）；不动 `src/**`、`tools/**`。代码行号一律标注 `HEAD e0bc4fec`。

## 1. 方法（沿用第 1/2 轮纪律 + 本轮新增）

1. **判定器先用必失败样本校准**：本轮用故意写错的证明 `s04`（`Eq (a*100 + x) (a + a + x) := rfl`）校准 —— 它稳定给出 `NF-DIVERGE 0/0`（**两版同败**标签），
   证明我的判读能把「两版同败」与「单侧偏离」分开，不会把 0/0 读成「有分歧」。
2. **冻结副本记 `size+mtime+sha256`**；不用 `target/debug/*`（第 2 轮 §6.9 已实测 test 产物与 build 产物**结论都会不同**）。
3. **新增工具口径：`L13BENCH_NF_DUMP=1`** —— `l13bench` 默认只在「尺寸分歧且两版都跑通」时补一次 pretty 对比；
   置该变量后**尺寸一致时也打印两版 pretty 串**。**本次定位的关键**：不看 pretty 就无法知道「哪一侧留了 redex」。
4. **`--only` 不能隔离引擎**（`nf_parity` 无条件跑两版，`src/bin/l13bench.rs:251-256`）⇒ 本轮全部**不带 `--only`**。
5. **单次异常读数复测两次**（本轮 `s07`/`s08` 各跑 2 次，报错文本逐字节一致）。
6. **探针全部自写**，放 `target/prelude_scratch/verify3/nfdiv/**`（**41 个 `.typort`**，输出 43 份在 `.../out/`）。
   （我发给 Lead 的首条裁决消息里写的「34 个」是当时已跑完的数量；随后又补了 `g01`–`g05` 与 `s07`/`s08`，故最终为 **41** 个。）

## 2. 交付物 1 · (I)② `e18`/`e19` 的 `NF-DIVERGE` **期望范式裁决**（完成）

### 2.1 事实与契约

- 事实：`e18`（`def z_f(a: Nat, x: Nat): Nat = a * 100 + x + 5`，**def-only**）与 `e19`（同体 primop 形）两版都终止（~3.5s），
  但 `NF-DIVERGE basic=413 fast=222`；pretty 在**第 13 字符**起不同：basic 613 字符（`a => x => {a + {a + …}} + x + 5`）vs fast 27 字符（`a => x => {a * 100} + x + 5`）。
  我在本轮**复现 ≥2 次**（`b06`/`b10` 是 `e18`/`e19` 的逐字副本：`413/222`、`@13`、`613c/27c`）。
- 契约（`src/prelude/core/nat.typort:38-43` + `docs/nat-primops-plan.md` §3/§6）：
  `nat_mul` **对第二个参数递归**；prim 必须「精确复刻旧定义的可归约性」；**`x * succ d ⇒ x + (x * d)` 与 `x * Nat(k>0) ⇒ x + (x * (k-1))` 已实现**（§6 明写，`legacy_tests::test_prove_term_pure` 依赖它）。
  ⇒ `a * 100`（rigid `a` × 具体 100）**是 redex，必须归约**；`nat_add` 的归约性**只看第 2 个实参**（§3 nat_add 表 + 「x 是否具体不影响 add 的归约性」）。

### 2.2 机理：孪生 `quote` 不 force「卡住应用里 prim 从未检查的那个实参」

`(a * 100) + x`：外层 `nat_add` 的**第 2 实参是裸 rigid 变量 `x`** ⇒ prim 判 `y` 非具体、非 succ 链 ⇒ **返回 `None`（卡住）**，
**第 1 实参 `a * 100` 从未被 force**。于是：

- **参考版（已确认，我独立读过）**：`quote_inner` 入口即 `force`（`mod.rs:3627-3629`）；`quote_sp`（`mod.rs:3600-3611`）对**每个** spine 项递归 `quote_inner`（`:3608`）
  ⇒ 卡住 `Val::Decl` 的**每个实参都先 force 再引** ⇒ 输出展开链（**范式，无 redex**）。
- **孪生侧落点：⚠️ 运行时待确认**（owner 逐行复核 + 我的独立抽读；行号按 `HEAD e0bc4fec`）：
  - **不是** `quote.rs:149-169`（那段 `QJob::Q` 确实先 `force`）—— **我最初的推断落点错了**，此处更正。
  - **候选缺口 =「连续右链」路径**：`quote.rs:370-393` 的连续右链分支 + `QJob::ChainRun`（**`518-591`**）。
    该路径只对 **base 槽**的实参下 `Q(base_v)`（`:393`），以及 `_` 分支里的 `Q(applied)`（`:575`）/`Q(fi)`（`:585`）；
    **`next..=end` 各槽自身的实参 `spine.stack[i].a` 全程没有 `Q`（既不 force 也不 quote）**；
    `idx_node` 快路径（**`543-547`**）直接 `Tm::App(n, prev, icit)` 拼接，**整段不碰 `Q`**。
  - `:178 XCell::Decl{name} => Tm::Decl(name)` **无实参**，**不是**跳过点。
  - ⇒ **行为面（§2.3–§2.5）是实测、不受影响**；但**代码落点需运行时确认**：
    task-29 判据 1 已改为「**先运行时确认落点再落盘**」——手段二选一：打印 `(a + 0) + x` 的孪生 quoted `Tm`，
    或给 `ChainRun` 加「槽实参从未被 Q」的计数（env 门控，默认关、零输出）。
    **若确认后形状未变 ⇒ 我的机理推断有误，需重新定位**（判据 2 会自动暴露）。

⇒ **basic 是期望范式；fast 偏离**（其输出**含 redex，按定义不是范式**）。

### 2.3 bisect（14 档，`b01`–`b14`，def-only；`--with-prelude core --rounds 1` + `NF_DUMP=1`）

| 档 | 形状 | 结果 | 备注 |
|---|---|---|---|
| b01 | `a * 100`（2 参、无尾） | **nf=399 一致**，pretty 603c 相同 | 两版**都**展开 mul ⇒ mul 本身不是问题 |
| b02 | `a * 100 + 5`（1 参） | **一致** nf=408 / 602c | 外层 add 的 y 具体 ⇒ 强制了第 1 实参 |
| b04 | `a * 100 + 5`（2 参） | **一致** nf=409 / 607c | 同上 |
| b11 | `x + a * 100 + 5`（mul 在后） | **一致** nf=413 / 613c | 同上 |
| b12 | `(a * 100) + (x + 5)` | **一致** nf=413 / 613c | y 是 add 应用 ⇒ 被 force ⇒ 顺带归约 |
| b13 | `a + x + 5`（无 mul） | **一致** nf=17 / 19c | 无 redex |
| b14 | `a * x + x + 5`（mul 双 rigid） | **一致** nf=21 / 25c | 无 redex（卡住即范式） |
| **b05** | **`(a * 100) + x`** | **DIVERGE 403/212**，@13，**b609c / f23c** | **mul 系的最小触发形状**（更小的无 mul 版本见 §2.4 `g01`） |
| b03 | `a * 100 + a + 5`（1 参，尾用同变量） | **DIVERGE 412/221**，@8，b608c / f22c | 尾是裸 rigid ⇒ 同机制 |
| **b06** | **`a * 100 + x + 5`（= e18 逐字）** | **DIVERGE 413/222**，@13，b613c / f27c | 复现 |
| b07 | `a * 100 + x + x` | **DIVERGE 407/216**，@14，b615c / f29c | 同机制 |
| b08 | `a * 2 + x + 5` | **DIVERGE 21/26**，@13，b25c / f25c | **小系数也分歧**（长度相同、内容不同） |
| b09 | `a * 1 + x + 5` | **DIVERGE 17/24**，@10，b19c / f25c | 系数 1 |
| **b10** | **`nat_add (nat_add (nat_mul a 100) x) 5`（= e19 逐字）** | **DIVERGE 413/222**，@13，b613c / f27c | 复现（primop 形同机制） |

### 2.4 与 `nat_mul` **无关**（5 档对照，`g01`–`g05`）——决定性

```
g01  (a + 0) + x        DIVERGE  7/12   basic: a => x => a + x        fast: a => x => {a + 0} + x
g02  (a * 0) + x        DIVERGE  8/12   basic: a => x => 0 + x        fast: a => x => {a * 0} + x
g03  (nat_add a 0) + x  DIVERGE  7/12   basic: a => x => a + x        fast: a => x => {a + 0} + x
g04  (a * 1) + x        DIVERGE  7/14   basic: a => x => a + x        fast: a => x => {a * 1} + x
g05  x + (a + 0)        nf=7 一致，pretty 15c 相同（redex 在**被检查的 y 位** ⇒ 被 force）
```
⇒ 触发条件 = **redex 位于「卡住 prim 应用未被检查的实参」位置**；`{a + 0}`、`{a * 0}`、`{a * 1}`、`{a * 100}` 都是 redex。
⇒ **第 2 轮那条「源自既有的 `nat_mul` 归约形态差异」的归因被推翻**（见 §2.9）。

### 2.5 用户可见后果（比 nf 假警报更硬）：**同一输入的报错文本不同**（各复测 2 次，逐字节一致）

探针 `s07`（`def z_eq(a: Nat, x: Nat): Eq (a * 1 + x) (a + a + x) = rfl`，故意写错）：
```
TWIN : can't unify | expected: Eq[Nat]({a * 1} + x, {a + a} + x) | find: Eq[Nat](a + x, a + x)
BASIC: can't unify | expected: Eq[Nat](a + x,     {a + a} + x) | find: Eq[Nat](a + x, a + x)
```
探针 `s08`（`Eq (a + 0 + x) (a + a + x)`）：TWIN `expected: …({a + 0} + x, …)` vs BASIC `expected: …(a + x, …)`。
- `find:` 侧**两版相同**（走了 unify/force）⇒ 分歧只在**渲染 `expected:` 时的归一化程度**。
- **注意代价面**：对齐到参考版意味着 `expected:` 可能打印 613 字符的展开链（第 2 轮实测），所以「对齐」不是纯粹无痛的 —— 见 §2.8 方案 B。
- 覆盖缺口：`l13_fast_parity` 的口径是「Err 判定 + 归一化正文一致」，但**现有套件没有覆盖「redex 落在卡住 prim 未被检查的实参」这个形状**（否则该文本差异早应报红）。

### 2.6 什么**没有**分歧（避免过度定性）

| 探针 | 内容 | 结果 |
|---|---|---|
| `s01` | `Eq (a * 100 + x) (a + (a * 99) + x) := rfl`（需要把 mul 展开才成立） | **两版都通过** nf=1211 |
| `s02` | `Eq (a * 2 + x) (a + a + x) := rfl` | 一致 nf=35 |
| `s03` | `Eq (a * 100 + x) (a * 100 + x) := rfl` | 一致 nf=1211 |
| `s05` | `Eq (a * 100) (a + (a * 99)) := rfl` | 一致 nf=1198 |
| `s06` | `Eq (a * 100 + x + 5) (a + (a * 99) + x + 5) := rfl` | 一致 nf=1241 |
| `s04` | **假证明**（校准样本） | **两版同败** `DIVERGE 0/0` |
| `d11`/`e15`/`e17` | 带调用的同体形状 | 一致（nf=202 / 216 / 216） |

⇒ **归约规则与 Ok/Err 判定两版一致**（证明该过的都过、假证明都拒）；偏离**只在 quote/范式与 `expected:` 渲染**。

### 2.7 裁决 + 判据

- **裁决：参考版（basic）是期望范式；孪生（fast）是偏离侧。** 判据三条：
  1. **定义**：`nf` = 引出的**范式**（`bench_check_nf_bounded` → `quote` → `tm_size`/pretty）。fast 的输出含 redex `{a * k}`/`{a + 0}`/`{a * 0}`，**按定义不是范式**；
  2. **契约**：`nat_mul` 的部分展开与 `nat_add` 的 `y=0 ⇒ x` 都是**明文可归约**（`nat-primops-plan.md` §3/§6），且**与「谁被检查」无关**——`x*Nat(k>0)` 的可归约性不依赖第 1 实参；
  3. **同形兄弟**：redex 落在**被检查的 y 位**时两版一致（`g05`、`b02`、`b04`、`b11`、`b12`）⇒ 差异只由「未检查实参不 force」造成，不能归因到归约规则。
- **定性**：**孪生 quote/范式侧的不完全归一化**（用户可见于 `can't unify` 的 `expected:`），**不是归约规则差异、也不是 Ok/Err 分歧**。
- **影响面**：① `nf_parity` 对 def-only 文件产生**假 DIVERGE**（`e18`/`e19` 即此）；② 诊断文本差异。

### 2.8 行动项（**Lead 已采纳方案 A**，落成 task-29；判据如下）

- **方案 A（**已采纳**）**：孪生 `bump_spine_iter/quote.rs` 引「卡住应用」时对**每个 spine 实参**也走 force+quote（镜像参考版 `quote_inner`），使范式无 redex。
  语义零风险（只影响 quote），代价 = quote 期额外 force。**task-29 写域** = `bump_spine_iter/**` + `tests/twin_engine_tests.rs`，**排在 task-25 之后**（engine-quirks 同一 writer）。
  **task-29 验收判据（待落地后由我独立复算）**：
  1. **先运行时确认落点（新增，见 §2.2）**：打印 `(a + 0) + x` 的孪生 quoted `Tm`，**或**给 `ChainRun`（`quote.rs:518-591`）加「槽实参从未被 Q」计数（env 门控，默认关、零输出）；
     **确认缺口确在连续右链之后**再落盘（避免改错分支）；
  2. `(a + 0) + x` / `(a*0) + x` / `(a*1) + x` / `(a*100) + x` 四个 def-only 形状 `nf` 两版**逐位一致**；`e18`/`e19`/`m_e1` 的 DIVERGE 消失；`s07`/`s08` 报错文本两版**逐字节相同**；
  3. **性能护栏**：quote 期多 force 的代价必须给同窗口数值（≥3 形状，与参考版对比），病理级变慢要明说；
  4. **parity 回归钉**：`tests/twin_engine_tests.rs` 加一条（`(a + 0) + x`），**twin 计数 27 → 28 属合法基线移动**；
  5. 四套件 + `round2_engine_tests` + 形状矩阵全绿；红则 60 秒回滚，退到方案 B 的书面版本。

**task-29 已落地 ⇒ 判据 2/3 我的复算结果（DUT `lead_r3_l13bench.exe` `86FF1BCA…`，2026-10-09 04:18:30；详见 §3.3）**：

| 判据 | 我的实测 | 结论 |
|---|---|---|
| 2a 四形状 `nf` 两版一致 | `g01` `(a+0)+x` **nf=7**、`g02` `(a*0)+x` **8**、`g04` `(a*1)+x` **7**、`b05` `(a*100)+x` **403**（全部 `same`，无 DIVERGE） | ✅ |
| 2b `e18`/`e19`/`m_e1` DIVERGE 消失 | **三者均 `nf=413`、pretty `same 613c`**（原 `413/222`）✔ 与 owner「413/222 → 413」逐位一致 | ✅ |
| 2c `s07`/`s08` 报错文本逐字节相同 | twin 与 basic 的 `Some(...)` 载荷**完全相同**（均为 `expected: Eq[Nat](a + x, {a + a} + x)`，孪生的 `{a * 1} + x`/`{a + 0} + x` **已消失**） | ✅ |
| 2d 形状矩阵 | 我全量跑 19 档：**AGREE 18 / DIVERGE 0 / TIMEOUT 1（唯一 `e07`）**，逐档 nf 与 Lead 的更正表**逐位一致**（e18/e19 均 413） | ✅ |
| 2e `nfdiv` 41 探针 | **DIVERGE 仅 3 条**（`s04`/`s07`/`s08`），且**全部是 `DIVERGE 0/0` + `both-failed`**（我的必失败校准样本）⇒ **`0/0` 假象确认**；其余 38 条全部 `nf=` 一致 | ✅ |
| 3 性能护栏 | 静默窗口（无并发）：`e18` **3.55s**、`e19` **3.55s**、`m_e1` **3.54s**、`b05` 3.44s、`g01/g02/g04` 3.32–3.33s、参照 `e15` 3.33s、`e16` 3.34s、`r2zf` 3.56s；19 档矩阵每档 **3.3–3.5s** | ✅ **与 pre-task-29 同量级**（w16 时 e18 4.2s / e15 2.9s / r2zf 3.5s）⇒ **无可测回退**，病理级变慢**未出现** |

> **与 Lead 数字的差异**：**无**。唯一需要标注的是 Lead 转述的 owner 报告里「形状矩阵 17/19 一致」是**笔误**，最终应为 **AGREE 18 / DIVERGE 0 / TIMEOUT 1（e07）** —— 我全量复跑**逐档吻合**该更正。
- **方案 B（备选，仅当 A 回滚）**：正式登记为**已知偏差**（挂 `src/L13_namespace/README.md` §6-3「快版已知分叉家族 · Prim 求值时机差」），并**同时**：
  ① `nf_parity` 两侧先做完全归一化再比较（消掉假 DIVERGE）；② 为诊断文本差异加 curated 守卫（或明确「不比 `expected:` 的归约程度」）。
- **无论 A/B 都要补的回归用例**（低成本、正是现有套件的缺口）：**redex 落在卡住 prim 未被检查的实参**，最小形状 `def z_f(a: Nat, x: Nat): Nat = (a + 0) + x`（预期：两版 pretty 一致且 `a => x => a + x`）。
- 另建议：把 `L13BENCH_NF_DUMP=1` 写进 `l13bench` 的使用说明（本次定位完全依赖它）。

### 2.9 对第 2 轮记录的两处更正（**不改其已验证数字**，只加更正指向）

1. `docs/prelude-round-2-2026-10-08.md` §4.1 残留② 与 §7 (E) 行把该分歧归因为「源自既有的 `nat_mul` 归约形态差异」⇒ **更正为**：
   「**孪生 `quote` 不 force 卡住应用未被检查的实参** ⇒ 范式里留 redex（与 mul 无关：`(a + 0) + x` 同样分歧）」。
2. 同处把影响面写成「与 memo 无关」是对的（本裁决再次确认），但「两种孪生实现给出逐位相同的 `fast=222`」这一条的**解释**要改：
   逐位相同是因为两条实现都**没有 force 未检查实参**，而不是因为 `nat_mul` 形态差异。

## 3. 交付物 2 · 第 3 轮各项落盘的独立复算

| 项 | 内容 | 状态 |
|---|---|---|
| **(K)** | 发射器根治：emit 前后对照（`21-crossclock` + `when`+Cd 最小例） | ✅ **已落盘 + 我已独立复算**（§3.1） |
| (I)① | `e07_bigcoef`：l13bench / typort 两入口修前修后 + 栈溢出复现 | 待 owner 落盘（第 2 轮已实测：pre/post 均 TIMEOUT；typort 入口两版**栈溢出**） |
| (I)③ | 孪生跨轮不变量：核对 owner 断言 + **自写**跨轮命中探针 | 待落盘 |
| (J) | `rfl[Nat] 3`：定向文案 + 4 个绕法 PASS + 反例零误报 | 待落盘 |
| (L) | 参考模型对照表与逐项映射：抽样 ≥5 条（点名模块 + 复现命令 + 实测） | 待落盘 |

### 3.1 (K) 发射器根治（`hdl-verilog.typort` **+56/−1**）—— 我的独立复算

**DUT**：`typort_kbefore.exe`（`A14E4B41…`）↔ `typort_kafter.exe`（K1，`3EFB530F…`）↔ `typort_kafter2.exe`（K2，`FB36CABB…`）；见 §0。

**(a) 源码形状（我读 diff 核对）**：3 个 hunk —— 新增 `def hasMainClocked`（`+50` 行，含「为什么必须含 `memWrite`」的 WHY 注释）+ `when` MAIN 分支的 `+5` 行注释 +
**唯一一处语义改动**：`case true => hasRegAssign(e)` → **`hasMainClocked(e)`**（`−1/+1`）。契约注释明写：
`regAssign`/`memWrite` = isMain-only，`regAssignCd` 由 `cdEq` 匹配 ⇒ 主域谓词必须**接受 `regAssign` ∪ `memWrite`、拒绝 `regAssignCd`**。
另核实：其余四处 `hasRegAssign` 调用点**未改**；`hasClockLines`（`:1420`）**没有任何调用者** ⇒ 它唯一的用途 `collectClockLines` 确为 dead code。

**(b) 最小复现（`when` 体内显式 `regAssignCd`；我自跑 `typort check r3_hdlc/when_cd_repro2.typort`，逐模块取 `kWhenMacro` 段）**：

| DUT | `kWhenMacro` 里的 clocked 块 | `always @(` | `r2 <= a;` | 判读 |
|---|---|---|---|---|
| `kbefore` | **2 个**：`always @(posedge clk)` **+** `always @(posedge clk2 or posedge rst2)` | **2** | **2** | **双驱动**（同一个 cd2 寄存器被主域块与 cd2 块各写一次）= (K) 缺陷 |
| `kafter`（K1） | 1 个：`always @(posedge clk2 or posedge rst2)` | **1** | **1** | 双驱动消失 ✓ |
| `kafter2`（K2） | 同上（1 个） | **1** | **1** | ✓ |

⇒ 与 Lead/owner 的「`r2 <= a;` 2 → 1、`always @(` 2 → 1」**逐项一致**（我的 `r2 <=` 原始计数含复位分支的 `r2 <= 0;`，故为 3 → 2）。

**(c) K1 回归（被 emit 对照抓住，我独立复现）**：`typort emit examples/hdl/21-crossclock.typort --top ccFifo`

| DUT | stdout len | `_d_mem[` 行数 | `_d_mem[_d_wrPtr[1:0]] <= pushData;` | 与 kbefore 逐字节相同 |
|---|---|---|---|---|
| `kbefore` | 1,597 | **2** | **在** | — |
| `kafter`（K1） | 1,461 | **1** | **消失** ⇒ 存储器永不写入 | **否** |
| `kafter2`（K2） | 1,597 | **2** | **在** | **是（identical=True）** |

⇒ **K1 确实造成真实回归**（`memWrite` 属主域、位于 `when` 内；只认 `regAssign` 的谓词把整个 when 路由到「没有任何 clocked 块」）⇒ **60 秒回滚是对的**；
K2（`hasMainClocked` = `regAssign` ∪ `memWrite`）**同时**修掉双驱动并**恢复 21-crossclock 逐字节相同**。

**(d) 顺带在 (b) 的输出里独立看到 hdl-c 的「附带发现 1」**：`kWhenMacro` 模块**没有任何主域 clocked 内容**，但端口表里**仍有 `input wire clk`**，且该 `clk` 在模块体里**从未被使用** ⇒ 「主域 clk 端口被合成」这一条**我用自己的读数复现**（见 §5-3、§7）。
**(e) 顺带确认「附带发现 2」**：`kNatural`（自然写法 `when en { r2 := a }`，`r2` 是 cd2 寄存器）在 **三个二进制上都是** `always @(*) ... r2 = a;`（**组合**驱动）⇒ 自然写法**不产生 `regAssignCd`**，与 (K) 改动无关（见 §5-4、§7）。
**(f) 未做**：L3 逐模块不退化需 hdl-a 的 L3 结果（第 2 轮口径 51/51）；我**未**独立跑 L3（避免与 owner 抢资源）。

### 3.2 (M)/task-30 入口栈预算对齐（`src/bin/cli.rs` **+30/−4**）—— 我的独立复算

**问题**：`typort check`（CLI 主线程，`.cargo/config.toml` 的 `/STACK:67108864` = **64 MiB** 保留）与 `l13bench`（worker，`L13_STACK_MB` 缺省 **256 MiB**，`bin/l13bench.rs:108-113`）**栈预算不同** ⇒ 同一大字面量在两个入口结局不同。
**落盘**：CLI 调度整体移进 worker 线程，`stack_size = TYPORT_STACK_MB`（**缺省 1024 MiB**；`0/非法 ⇒ 缺省`），`run(cli)` 抽出；注释诚实写明「**只抬高天花板、不消除 O(n) 递归**」，深度护栏仍是 `NAT_LITERAL_ELAB_LIMIT`。

**我的独立读数（全部我自跑；每个读数一个新鲜进程，把 stdout/stderr 原文存 `verify3/m_lit/**`）**

| DUT | 探针 | 结果 | 秒 |
|---|---|---|---|
| `r3_base_typort.exe`（**pre-M**，`F51E7A4B…`） | `lit_10000` | **STACK OVERFLOW ×2**（`thread 'main' … has overflowed its stack`） | 82.3 / 91.5 |
| 同上 | `lit_100000` | **STACK OVERFLOW** | 86.5 |
| `lead_w16_l13bench.exe`（`790BB801…`） | `lit_10000` | **PASS `nf=20002`** | 3.5 / 3.7 |
| 同上 | `lit_100000` | **STACK OVERFLOW ×3** | ~90（cap 90s；崩溃文本在场） |
| **`typort_w3mid.exe`**（**task-30 后**） | `lit_10000` | **PASS `note: 10000`** | 55.0 |
| 同上 | `lit_100000` | **PASS `note: 100000`**（**原崩溃**） | 72.1 |
| 同上 | `lit_100001` | **可诊断**：3 条错误，**末条 = guard 原文**「integer literal 100001 exceeds the Nat literal elaboration limit 100000: …」 | 57.9 |
| 同上 | `lit_1000000` | **可诊断**：同上（末条 = guard 原文） | 60.6 |
| 同上 | `lit_via_mul`（`nat_mul 1000 1000`） | **PASS `note: 1000000`** | 62.4 |

**三条结论**
1. **修前基线确实崩**：`typort check`（64 MiB）在 **10000 与 100000 都爆栈**（各 ≥1 次，10000 复测 2/2）；`l13bench`（256 MiB）在 **10000 PASS、100000 爆栈 ×3**。⇒ **入口不对称是既有事实**，与 `parse/mod.rs:49-56` 的三行双入口表**逐格吻合**。
2. **修后（缺省、无 env）**：10000/100000 **都 PASS 且给出 `note:`**；100001/1e6 **快速可诊断**（guard 文案在场）；`nat_mul` 绕法 PASS。⇒ 落盘目标达成。
3. **我的读数与 `parser/mod.rs:49-56` 的官方口径表以及 Lead 的 Step 1 数字一致**（我 55/72.1s vs Lead 77.6/67.1s；同量级、只差窗口负载）。**没有改变阈值**：`NAT_LITERAL_ELAB_LIMIT = 100_000` 保持（我实测 100000 可用、100001 被拒）。

**为什么「10000 在 64 MiB 崩、256 MiB 过」而「100000 两边都崩」**：字面量在 elaboration 期被展开成 n 层 unary 链（`parser/mod.rs:45-47`），下游遍历按 n 层递归 ⇒ 需要 ≈ c·n 的栈。10000 需 20002 节点、100000 需 200002 节点；**
64 MiB 两者都不够、256 MiB 只够前者、1024 MiB 两者都够** ⇒ 这个「栈需求 ∝ n」的模型**同时解释我上面全部 9 个读数**（唯一不解释的是 hdl-a 早期那个 `4C8C60BD` 2.5s PASS —— 那是**另一个中间态二进制**，我在冻结的 `790BB801…` 上**复现不出**，与 Lead 的 Step 0 一致）。

**影响面**：`tools/spinalhdl-verify/verify.py` 用 `typort check` 跑每个 L3 用例 ⇒ 修前任何含 ≈≥10000 字面量的用例都会崩 harness；**当前 5 个用例无大字面量，51/51 不受影响**，但「雷已拆」。公平记录：这只是**抬高天花板**（1024 MiB 是保留量、RSS 随实用增长），**e07 的爆栈属另一族**（参考版 `quote_sp` 非尾递归，§7-1），本轮**未混谈**。

**（M）的诚实边界**：我抓的是 **task-29 落地前**的中间冻结副本；task-29 会改孪生 quote，但**不触碰 CLI 栈预算** ⇒ 上述 9 个读数在最终二进制上**预期不变**；等 Lead 发最终二进制我再复跑 10000/100000/100001 三点确认。

## 4. 行为变更证据等级表（**(K) 已入表**；其余等落盘 + Lead 收官门禁）

| 变更 | 组 | 风险 | 证据等级 |
|---|---|---|---|
| **(K) 发射器 `when` 主域门控根治**（`hdl-verilog.typort` +56/−1：新 `hasMainClocked` = `regAssign` ∪ `memWrite`，`regAssignCd` 交 `cdEq`；唯一语义行 `hasRegAssign(e)` → `hasMainClocked(e)`） | hdl-c | 中（改 `when` 的域归属判据 ⇒ 影响发射产物） | **owner 门禁 `eq_w2r3`（fail=0）+ 我的独立 emit/复现复算（§3.1）**：① 最小复现 `when`+`regAssignCd` 由 **2 个 clocked 块 → 1 个**（`always @(` 2→1、`r2 <= a;` 2→1）；② **K1 真回归被抓住**：`21-crossclock` 的 `_d_mem[…wrPtr…] <= pushData;` **消失**（len 1597→1461）⇒ 回滚正确；③ **K2 恢复逐字节相同**（`identical=True`，len 1597）；④ 附带发现 1 我在输出里直接看到（多余的 `input wire clk`），附带发现 2 三版一致（自然写法走组合） |
| **(M) CLI 入口栈预算对齐**（`src/bin/cli.rs` +30/−4：CLI 调度进 worker，`TYPORT_STACK_MB` 缺省 **1024 MiB**） | engine-quirks | 中（改入口调度；**不改**阈值、不改 RTL/引擎语义） | **owner 门禁 `eq_w3`（fail=0）+ 我的独立 A/B（§3.2）**：pre-M `typort check` 在 10000/100000 **都爆栈**（10000 复测 2/2）；`l13bench` 10000 PASS nf=20002 / 100000 **爆栈 ×3**；post（中间冻结副本）10000/100000 **PASS + `note:`**、100001/1e6 **可诊断且 guard 文案在场**、`nat_mul` 绕法 PASS。**诚实边界**：只抬高天花板，不消除 O(n) 递归；e07 属另一族（§7-1） |
| 第 3 轮其余项 **(I)②/(I)③/(J)** | engine-quirks / hdl-c | 中 | **(I)② = task-29 孪生 quote 归一化**（我的复算 §3.3：四形状 `nf` 逐位一致、`e18`/`e19` 由 `413/222` → **一致 413**、19 档矩阵 **AGREE 18 / DIVERGE 0 / TIMEOUT 1（e07）**、`s07`/`s08` 报错文本两版逐字节相同、性能 e18 3.55s/e19 3.55s 无回退；**（I)③ 跨轮不变量** owner 已落盘（`PRIM_STUCK_STALE=0`）；**(J) formB 通用臂** 我的 7 探针 §3.4（混排恰好 1 条且点名、窄臂保留、formA 未变、10 形态零误报）。**(I)① e07 未落盘**（判定 (b) 键不稳定 + 规模在 `string_concat`；爆栈属参考版 `quote_sp` 族 ⇒ §7-1） |
| **收官门禁/覆盖率/L3** | Lead | — | `lead_r3` **fail=0**：lib **612/0**、parity **15/0**、twin **28/0**、hdl042 **2/0**；额外套件 round2 10/0、emit 12/0、macro_goto 9/0、parser_error 107/0、verilog_compat(lib) 25/0、hdl_fsm(lib) 17/0、hdl_stream_fix(lib) 11/0、prelude_hdl_c(lib) 10/0；`typort doc --min-coverage 60 --deny-warnings` **EXIT=0**、顶层 **1195/1195 = 100%**；L3 **51/51** 且与 w16/r3_base **零漂移**；CLI 钉定稿（`-RequireSha256 79B05E31…` ⇒ `HDL038=2`、无 036/037/039） |

### 3.3 (task-29) 孪生 quote 归一化落地 —— 我的独立复算

**DUT**：`lead_r3_l13bench.exe`（04:18:30 / 9,293,824 B / `86FF1BCAF96F8548E929B540F9C03E5F9E9BF623ECDCDC49430D929CE3BB1A69`）；工具 = 我自己的 `verify3/run_nfparity.ps1`（`L13BENCH_DIAG=1` + `L13BENCH_NF_DUMP=1`，**不带 `--only`**）；原文存 `verify3/t29/**`。

**(a) 判据 2（四形状 + `e18`/`e19`/`m_e1` + 报错文本）**：见 §2.8 的表 —— **全部通过**；`e18`/`e19`/`m_e1` = `nf=413`、`same 613c`；`s07`/`s08` 的 twin/basic `Some(...)` 载荷**逐字节相同**。

**(b) 判据 2d（19 档形状矩阵，我全量跑）**：**AGREE 18 / DIVERGE 0 / TIMEOUT 1（`e07`）**，逐档 nf：e01 252 / e02 246 / e03 250 / e04 242 / e05 12 / e06 10 / e08 252 / e09 252 / e10 12 / e11 10 / e12 252 / e13 108 / e14 22 / e15 216 / e16 22 / e17 216 / **e18 413** / **e19 413**；每档 **3.3–3.5s**。
⇒ 与 Lead 的更正表**逐位一致**（修前：16 一致 + e18/e19 `413/222` + e07 TIMEOUT）。

**(c) 判据 2e（`nfdiv` 41 探针）**：`DIVERGE` 只剩 **3 条**（`s04_rfl_false`、`s07_fail_mul1`、`s08_fail_add0`），且**三条都是 `DIVERGE 0/0` + `both-failed`**（我在第 2 轮设的必失败校准样本）⇒ **「0/0 假象」确认**；其余 **38 条**全部 `nf=` 一致。

**(d) 判据 3（性能护栏，静默窗口）**：`e18` **3.55s**、`e19` **3.55s**、`m_e1` **3.54s**、`b05` 3.44s、`g01` 3.32s、`g02` 3.33s、`g04` 3.33s、参照 `e15` 3.33s / `e16` 3.34s / `r2zf` 3.56s、19 档矩阵 3.3–3.5s/档。
⇒ 与 pre-task-29（w16：e18 4.2s、e15 2.9s、r2zf 3.5s）**同量级，无可测回退**。

**(e) 判据 4/5 由 Lead 门禁覆盖**：`twin_engine_tests` **28/0**（27 → 28 合法移动）、lib **612/0**、parity 15/0、hdl042 2/0（§8）。

**(f) 未做/边界**：`e07` **仍 TIMEOUT**（19 档里唯一；我的 cap 60.1s）——属**另一族**（参考版 `quote_sp` 非尾递归，§7-1），task-29 **不涉及**；`typort check` 崩的也是参考版（`cli.rs:710`），故 (M) 的栈对齐**不解除** e07（§3.2 已注明）。

### 3.4 (task-27 第二步) formB 通用臂 —— 我的独立复算（**自写探针 7 个**）

**DUT**：`lead_r3_typort.exe`（`79B05E31…`）；探针 `verify3/g1step2/mm1–mm7`；原文 `verify3/g1step2/out/**`。

| 探针（我的） | 形状 | 期望 | 我的实测 |
|---|---|---|---|
| `mm1_fb_mixed_typo` | **formB** 同一模块含 `Bool`/`UInt[7]`/`Bits[7]`/`SInt[7]` + **`Broken`**（我的拼写错名） | **恰好 1 条 HDV004 且点名 `Broken`**；合法端口 0 警告 | **HDV004=1**：`HDV004 [Broken] bad: this port type is not accepted - …`；**合法端口警告 = 0** ✅ |
| `mm2_fb_boolean` | formB `= Boolean` | 保留窄臂专门文案 | `HDV004 [Boolean] sel: \`Boolean\` is \`Bool\`'s defining type name - …` ✅ |
| `mm3_fb_uint_nowidth` | formB `= UInt`（**漏位宽**） | 通用臂捕获（中性文案） | `HDV004 [UInt] u: this port type is not accepted - …` ✅ |
| `mm4_fb_legal` | formB 全合法 | **HDV004=0** 且模块 elaborate | HDV004=0、模块正常打印 ✅ |
| `mm5_fa_boolean` | **formA**（header）两个 `= Boolean` | 窄臂逐端口告警 | **HDV004=2**（`[Boolean] sel` + `[Boolean] y`）✅ 与 formA 整调用匹配一致 |
| `mm6_fa_typo` | **formA** header `= Nope` | **无 HDV004**，仍 `expected def` | HDV004=0；诊断 = `error name not in scope: mmFormATypo` + **`error: expected \`def\`, found identifier`** ✅ |
| `mm7_matrix10` | **10 形态合法矩阵**（formB ×9 + 参数化 + `inout`） | **HDV004=0**，10/10 elaborate | **HDV004=0、10/10 模块打印** ✅ |

⇒ **task-27 第二步的四条判据我全部独立复算通过**（混排恰好 1 条且点名、窄臂文案保留、中性文案 + 响亮失败、formA 未变、10 形态零误报）。

**（我的自查，入 §5-14）**：`mm7` 首版有 **2/10 形态**因**我的探针语法**失败（`mx8[8].create.tree` 应为 `mx8.create[8].tree`；formA 带 body 赋值的写法非法）⇒ 修正后 **10/10**。这**不是** HDV004 误报（首版 HDV004 同样是 0），但说明「矩阵通过」必须**同时**核对模块是否真的 elaborate（我首版只数了 HDV004，差点漏掉 2 个失败形态）。

## 5. 缺陷清单（含自查事故）

1. **【本轮裁决发现】孪生 `quote` 不完全归一化**：`(a * k) + rigid`、`(a + 0) + rigid`、`(a * 0) + rigid` 等形状在孪生侧范式里留 redex；
   后果 = `nf_parity` 假 DIVERGE + `expected:` 诊断文本差异（§2.2–§2.5）。**归约语义两版一致**（§2.6）。
   **处置：Lead 已采纳方案 A ⇒ task-29**（`bump_spine_iter/**` + `tests/twin_engine_tests.rs`，排在 task-25 之后），判据见 §2.8。
2. **【覆盖缺口】`l13_fast_parity` / `twin_engine_tests` 未覆盖该形状**（§2.5）⇒ task-29 判据 3 已把它列为回归钉（twin 27 → 28 属合法基线移动）。
3. **【方法】`--only` 不能隔离引擎**（第 2 轮 §6.10 已登记，本轮再次作为口径约束执行）。
4. **【方法】`L13BENCH_NF_DUMP=1` 是定位此类分歧的必要工具**：默认口径只在尺寸分歧时补 pretty，
   而**尺寸一致但内容不同**的形状（如 `b08` 25c/25c）只能靠强制 dump 发现 ⇒ 建议把它写进使用说明。
5. **【自查】我的首条裁决消息把探针数写成「34」**（当时确为 34，随后补到 41）⇒ 已在本文件 §1-6 更正；
   教训：**报数前先重数**（同一类错误在第 2 轮 §6.6-5 已出现过一次）。
6. **【自查 · 工具】BOM-less `.ps1` 里写非 ASCII ⇒ PS 5.1 按 ANSI 读 ⇒ 脚本解析失败**：我第一版
   `verify3/run_nfparity.ps1` 用中文正则去匹配 l13bench 的中文输出行，PS 5.1 读成乱码后报
   `Unexpected token 'same'`（与第 2 轮 §6.12 的 `Set-Content` 事故**同源**：PS 的默认编码假设）。
   修法：**辅助脚本一律纯 ASCII**，只靠 ASCII 可见结构提取（`basic (\d+) / fast (\d+)`、`[NF]` 前缀、首个数字=字符下标）；
   产物文件用 `[System.IO.File]::WriteAllText(..., UTF8Encoding($false))` 写，避免 BOM。
   （这与 `run_probe2.ps1` 头注「ASCII only」是同一条纪律。）
7. **【自查 · 分析】我的代码落点推断错了（owner 逐行复核更正）**：我首版 §2.2 断言缺口在 `quote.rs:149-169`（即 `QJob::Q` 先 `force` 的那段）；
   owner 逐行复核指出**那段确实先 force**，真正候选是**连续右链**（`370-393` + `QJob::ChainRun` `518-591`：`next..=end` 各槽实参全程没有 `Q`，`idx_node` 快路径也不碰 `Q`）；
   我随后独立抽读了 `mod.rs:3600-3611`、`quote.rs:360-409`、`515-594`、`cli.rs:703-710`，**确认 owner 的更正成立**。
   **教训**：「行为实测 + 单点代码阅读」**不足以定落点** —— 必须**运行时确认**（打印 quoted `Tm` / 加 env 门控计数），或沿调用链读到**分支终点**。
   已把「先运行时确认落点」写进 task-29 判据 1（§2.8）。
8. **【发现 · (K) 附带 1】主域 `input wire clk` 仍被合成**（hdl-c 报；**我在 §3.1(d) 的输出里直接看到**）：
   `moduleDefVLPlain` 的 `has_seq` 用 **main+extras 合并后**的 `clocked` 串判空 ⇒ 只要模块里有**任何额外 cd 块**，就会补一个**没人用的主域 `clk` 端口**
   （实测：`kWhenMacro` 端口表有 `clk`，模块体内从未使用）。这是「主域/额外域混淆」的**另一半**；其回归钉**刻意不断言端口**。
   ⇒ 第 4 轮：改判空口径（按域分别判）+ 补「多余端口」断言（§7-2）。
9. **【发现 · (K) 附带 2】`when { cdReg := x }` 自然写法不产生 `regAssignCd`**（hdl-c 报；**我三版实测一致**）：
   `hdl-core` 的 `pickAssign` 只造普通 `regAssign`、**从不查信号自身的时钟域** ⇒ cd 寄存器在 `when` 里被当普通 reg 走**组合**驱动
   （实测输出：`always @(*) begin if (en) begin r2 = a; end end`）⇒ **用户面语义缺口**，与 (K) 改动无关。我判为**第 4 轮优先项**（§7-3）。
10. **【记录】(K) 新 def 命名偏离任务原文**：落地名是 **`hasMainClocked`**（不是任务描述的 `hasMainRegAssign`），理由 = **必须含 `memWrite`** 才能镜像 `collectClockLinesCd` 直接臂表的 isMain-only 集合；
    Lead 已裁定保留。我把该理由与 WHY 注释一并记在 §3.1(a)。
11. **【发现 · (M)】** **`typort check` 与 `l13bench` 的栈预算不同 ⇒ 同输入不同结局**：CLI 主线程 64 MiB（`.cargo/config.toml` 的 `/STACK:67108864`）vs l13bench worker 缺省 256 MiB；
    实测：10000 在 typort 崩、在 bench 过；100000 两边都崩（§3.2）。**这是既有现象**（pre-M 基线同样如此），**不是 window 1 回归**。
    影响面 = L3 harness（`verify.py` 走 `typort check`）的「未爆的雷」；task-30 已拆（缺省 1024 MiB）。
12. **【自查 · 测量】我的批量脚本用 `-like '10000*'` 匹配档名 ⇒ `'100000_a'` 也被匹配**，导致我第一轮 4 个「100000」读数其实全跑的是 `lit_10000`（我**在读原始输出时发现**：`-- lit_10000.typort` 而不是 `lit_100000`）。
    修正后重跑得 **100000 爆栈 ×3**（§3.2）。**教训**：批量脚本必须**打印实际处理的文件名**（我后来加了 `analyzed=` 列），且**summary 行不能替代原文核对**。
13. **【观察 · 诊断质量】guard 文案不是第一条错误**：`lit_100001`/`lit_1000000` 的输出里，guard 原文是**第 3 条**，前面还有 `find unsolved meta with type Nat` 与 `name not in scope`（§3.2 原文）。
    ⇒ 用户先看到的是 meta 错误、真因在最后。建议第 4 轮把 guard 消息提到**第一条**（或抑制前两条噪声）——低风险、纯诊断。（我第一版 summary 只抓了「第一条 error」，因此**差点把 guard 判为缺失**，已用原文纠正。）

## 6. 未完成项与理由

1. 交付物 2 中 **(K)/(I)②(task-29)/(J)(formB)/(M) 均已完成**（落盘 + 我的独立复算 §3.1–§3.4）；**(I)①（e07 机理）与 (I)③（跨轮不变量）由 owner 在第 3 轮收口**：e07 判定「键不稳定 + 规模在 prelude 文本构建」且**爆栈属参考版 `quote_sp` 非尾递归族**（未落盘，转 §7-1 第 4 轮）；跨轮不变量已落盘（`PRIM_STUCK_STALE` 实测 0）。
2. 第 2 轮 §4.1 残留②的**更正指向已加**（见 §2.9 与第 2 轮文档 §4.1 ③ 的「第 3 轮更正」块）；**其已验证数字一律未改**。
3. ~~task-29 的落地复算待落盘后执行~~（**已完成**，见 §3.3：5 条判据全过 + 性能无回退；门禁套件我不跑 cargo，数字以 Lead `lead_r3` 为准）。
4. 残留（**如实记录，不得写成「已修」**）：`e07_bigcoef` 仍 TIMEOUT（`lead_r3` 矩阵 19 档里唯一；属参考版 `quote_sp` 族，第 4 轮 §7-1）；`nfdiv` 41 探针里剩 3 条 `DIVERGE 0/0`（必失败校准样本的**假象标签**，两版一致失败）。

## 7. 第 4 轮候选（本轮已产出部分）

1. **（e07 爆栈的唯一可落地方向）参考版 `quote_sp` 非尾递归**（owner 离线给出，与我的 (I)① 实测**同向**）：
   `quote_sp`（`mod.rs:3600-3611`）的递归调用嵌在 `Tm::App(...)` 构造里 ⇒ **深度 = 单条 spine 长度**，且**下降段不 force**；
   这与 e07 实测「最后 ~22s 内 `force_inner`/prim 计数**全为 0**、随后 `thread 'main' has overflowed its stack`」**自洽**
   （第 2 轮 §4.1 ① 表 9：窗口 11 时间驱动在挂死末段无增量 ⇒ 爆点已不在 force/prim，而在 quote 的链式递归）。
   ⇒ 方向 = **`quote_sp` 迭代化**（显式栈，镜像孪生 `ChainRun`）**或**给上游链加上界。
   **重要边界**：`typort check` 崩的是**参考版** —— `src/bin/cli.rs:710` 显式 `Backend::new_with_engine(..., Engine::Reference)`（注释写明 `check` 是纯参考管线）
   ⇒ **task-29（修孪生 quote）预期不缓解 e07**；e07 需要单独立项（参考版侧）。
2. **主域 `input wire clk` 被合成（§5-8）**：`moduleDefVLPlain` 的 `has_seq` 用 main+extras **合并后**的 clocked 串判空 ⇒ 有任何额外 cd 块就补一个没人用的主域 clk 端口。
   方向：按域分别判空（main 与 extras 各判各的）+ 给回归钉加「端口集合」断言（现在刻意不断言端口）。**风险低、用户可见（多余端口）。**
3. **（优先）`when { cdReg := x }` 不产生 `regAssignCd`（§5-9）**：`hdl-core` 的 `pickAssign` 不查信号自身时钟域 ⇒ cd 寄存器在 `when` 内被当普通 reg 走组合驱动
   （`always @(*) ... r2 = a;`）⇒ **用户写法与语义不符**。方向：`pickAssign` 侧按信号 cd 选择 `regAssign`/`regAssignCd`（`hdl-core`，双引擎同构），
   并补「when + cd 寄存器自然写法」的 emit 回归钉。**我判为本轮最高价值的第 4 轮项。**
4. **（已升级为第 3 轮交付项）** 孪生 quote 对卡住应用实参补 force = **task-29（方案 A）**；其落地后的独立复算见 §6-3。
5. **（加固项，若 task-29 落地则降级）** `nf_parity` 在比较前对两侧做**完全归一化**：即便 task-29 修好当前形状，
   该口径也能让 oracle 对**未来**的「尺寸一致但 pretty 不同」免疫 —— 建议作为加固，而不是替代 task-29。
6. **`nf_parity` 假警报家族清理**：把「尺寸一致但 pretty 不同」的形状做成清单（本轮已给出 **7 个 DIVERGE 形状**：`b03`/`b05`/`b06`/`b07`/`b08`/`b09`/`b10`，外加 `g01`–`g04` 四个同机制形状），逐条判定「归约缺陷 / 合法形态差」。
7. **若方案 A 回滚**：退到方案 B 的书面版本（登记已知偏差 + oracle 归一化 + 诊断文本口径明确化），并保留 `s07`/`s08` 作为文本差异的守卫样本。
8. **其余第 3 轮落盘项**（e07 / 跨轮不变量 / rfl / 参考模型）的独立复算与终稿，见 §3。
9. **（小项，纯诊断）guard 文案排序**：把 `integer literal … exceeds the Nat literal elaboration limit …` 提到**第一条**（现在排第 3，前有 `find unsolved meta` 与 `name not in scope`），
   避免用户先看到无关错误（§5-13）。**阈值保持 100000**（(M) 明确未收紧）。
10. **（记录，非新的第 4 轮项）入口栈预算已对齐**：`typort check` 缺省 1024 MiB ⇒ **L3 harness 的雷已拆**（§3.2）；
    仍是「抬高天花板」而非消除 O(n) 递归 ⇒ 若将来出现 **>100000 或深递归**的新输入族，仍要按 §7-1 的思路（迭代化）处理。
11. **（文档卫生）** hdl-a 的 README 里关于大字面量/栈的警告已**过时**（(M) 落地后 10000/100000 都 PASS）⇒ 由 hdl-a 更新（Lead 已安排）；本文件以 §3.2 的实测为准。

## 8. 门禁 / 基线（**累积**；数字以 Lead 收官门禁为准）

| 时点 | 门禁 | lib | parity | twin | hdl042 | 汇总 |
|---|---|---|---|---|---|---|
| 第 2 轮收官 | `lead_w16` | 609 / 0 | 15 / 0 | 27 / 0 | 2 / 0 | `fail=0`，`GATE_EXIT=0`，total 231.8s |
| **(K) 落地后** | `eq_w2r3`（owner 门禁） | **610 / 0**（609 + 1 新钉 `when_with_only_cd_assign_is_emitted_once`） | 15 / 0 | 27 / 0 | 2 / 0 | `gate_l13[eq_w2r3]` **fail=0** |
| **(M) 落地后（中间点）** | `eq_w3`（owner 门禁） | **610 / 0** | 15 / 0 | 27 / 0 | 2 / 0 | **`gate_l13[eq_w3]: total 310.1s, fail=0`** |
| **(task-29 + formB 都落地后 = 收官**） | `lead_r3`（**Lead 权威门禁**） | **612 / 0** | 15 / 0 | **28 / 0** | 2 / 0 | **`gate_l13[lead_r3]: total 303.8s, fail=0`**，`GATE_EXIT=0`，`NOT RUN: none (all four suites ran)` |

- **收官树 4 条原始 `test result:`（Lead 亲跑，`lead_r3`，最终二进制 `lead_r3_*`）**
  - `lib`：`test result: ok. 612 passed; 0 failed; 6 ignored; 0 measured; 361 filtered out; finished in 135.97s`
  - `parity`：`ok. 15 passed; 0 failed; 0 ignored; 0 measured; 618 filtered out; finished in 0.05s`
  - `twin`：`ok. 28 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 132.38s`（27 → **28** 合法基线移动，来自 §3.3 的诊断 parity 钉）
  - `hdl042`：`ok. 2 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 26.63s`
- **收官额外套件（Lead 亲跑）**：`round2_engine_tests` **10/0**、`emit_tests` **12/0**、`macro_goto_tests` **9/0**、`parser_error_tests` **107/0**、`verilog_compat_tests`（lib filter）**25/0**、`hdl_fsm_tests`（lib filter）**17/0**、`hdl_stream_fix_tests`（lib filter）**11/0**、`prelude_hdl_c_tests`（lib filter）**10/0**。
- **doc 覆盖（Lead 亲跑，冻结副本 `79B05E31…`）**：`typort doc … --min-coverage 60 --deny-warnings` → **EXIT=0**，`1195 items (1195/1194 documented, 100%), 2 packages`，即**顶层维持 100%**（比第 2 轮 1194 多 1 = `hasMainClocked` 的 `///`）。
- **L3 仿真（hdl-a，最终 DUT `79B05E31…`）**：**51 passed / 0 failed / 51 total**，exit 0、660.8s、MISMATCH=0；与 w16（`9844617D`）和 r3_base（`F51E7A4B`）**零漂移**（逐模块判定一致 + 归一化全文 diff 为空）⇒ 本轮四处改动（孪生 quote / CLI 栈 / 发射器主域判据 / 端口诊断）在 51 个 L3 模块上**零行为漂移**。
- **(M) 中间点额外套件（owner 读数）**：`round2_engine_tests` **10/0**（+1 字面量边界钉）；形状矩阵（当时）**18/19**（`e07` 同状态；`e18`/`e19` 归 task-29）。
- **(K) 额外套件（owner 读数）**：`prelude_hdl_c_tests` **9/0**、`emit_tests` **12/0**、`macro_goto_tests` **9/0**、`verilog_compat_tests`（lib filter）**25/0**、`hdl_fsm_tests` **17/0**、`hdl_stream_fix_tests` **11/0**。
- **基线移动**：**lib 609 → 610（(K) 的 1 条新钉）→ 611（task-29 的 lib 内 parity 钉）→ 612（formB 通用臂的 1 条新钉）**；`twin 27 → 28`（task-29 的诊断 parity 钉）⇒ 第 2 轮 §9 的 `609/0` 是**本轮前**基线，不冲突；**收官请用 `lead_r3` 的 612/28**。
- **我的独立复算落点（verifier）**：(K) emit 对照 §3.1、(M) 字面量边界 A/B §3.2、(task-29) 5 条判据 + 性能护栏 §3.3、(formB) 7 探针矩阵 §3.4 —— **均已完成**；门禁套件本身按纪律**我不跑 cargo**，数字以 Lead 收官门禁为准（`lead_r3`）。
- ~~待补~~（已补齐）：task-29 的 `eq_w*` 行、`twin 27 → 28` 的合法基线移动、以及 `nf_parity` 四形状/`e18`/`e19`/`s07`/`s08` 的独立复算（见 §3.3(a)–(d)：**全部通过**；`e18`/`e19` 由 `413/222` 变为**两版一致 413**，19 档矩阵 **AGREE 18 / DIVERGE 0 / TIMEOUT 1（`e07`）**）。
