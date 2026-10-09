# prelude 第 2 轮（2026-10-08）独立验证

> 由 verifier（task-12）独立撰写。所有数字实测，标注口径、二进制 mtime、`git rev-parse HEAD`。
> 未实测项标 `【待补】` / `【owner 报告，未独立复核】`。
> 第 1 轮轮次文档：`docs/prelude-round-2026-10b.md`（已入库 645dc3bd）。

- 第 2 轮起点：`HEAD 645dc3bd`（第 1 轮封版）
- 冻结副本：`target/prelude_scratch/verify2/bin/{typort_r2.exe(13:56:32), l13bench_r2.exe(13:56:33), typort_r2b.exe(14:07:08)}`
- 本轮修复任务：(E) task-8 3 项算术链不收敛、(F) task-9 HDL039 误报+whenBegin Cd、(G1) task-10 module 宏诊断、(H) task-11/13 工具入库
- 我的判定器：`verify2/run_probe2.ps1`（硬超时 + 内存上限 + ZERO-OUTPUT/NO-OUTPUT/INCONCLUSIVE）

---

## 1. 验证方法（沿用第 1 轮纪律 + 本轮新增）

1. **判定器先用必失败样本校准**。本轮实测：我新建的 `run_probe2.ps1` **首版在 l13bench 模式下把必失败样本判成 `PASS-NODIAG`**——又一次假 PASS（l13bench 的失败行走 stdout 且标记是中文）。按码点匹配「首个失败」后修正；现在必失败=`DECL-FAIL`、必过=`PASS`（见 §5.1）。
2. **单次 TIMEOUT 不构成证据**：无并发构建窗口 + 两种方式复测。本轮 `f4` 一次 90.3s TIMEOUT，复测 82s 正常返回 ⇒ 是**预算不足**而非不收敛（§4.2）。
3. **冻结副本既保证可比也冻结 prelude 快照**：跨 owner 落盘节奏复算时必须同一二进制内同时包含被验证项（第 1 轮教训）。
4. **读数带 mtime + HEAD**。
5. **新增（本轮）**：**量词要匹配诊断形态，不能只 grep 记号**。我的 F 探针注释里含字面 `HDL039`，首轮统计把注释当告警（`HDL039=1`）；改成 `warning:.*HDL039` 后才是真读数（§4.2）。同理 `[r2probe]` 类引擎调试输出会污染 stderr（§6.1）。
6. **新增（终稿）**：**验证「新增诊断文案」三步法**（§4.6 实践）：① 同一条 grep 先在**改动前**冻结副本上跑，必须**零命中**（否则量词自证）；
   ② 正例必须同时看到**新文案 ∧ 原错误**（防止「新文案吃掉了原有更精确的错误」）；③ 反例集必须包含**同形态的合法兄弟**（`c2` 声明冒号 / `c3` 方括号 binder / `c4` verilog `w[7:4]` / `c7` 类型位 Pi binder），
   且对既有诊断夹具做**逐行 diff**（不是只比计数）。本轮 10 个既有夹具逐行 identical、10 个自写探针中 6 个零命中、4 个命中（2 个真 ascription + 2 个 annotated-lambda，后者暴露文案不准确）。
7. **新增（终稿）**：**「计数驱动」会漏事件，长时挂死要用「时间驱动」采样**（窗口 10 → 11，§4.1 ① 表 8/9）：计数驱动在挂死进程里可能永远等不到那次打印（实测三条 force 臂 22s 内 <100k 次），
   改成每 ~2s 一行后立刻得到线性增长曲线与两个爆点站点。

---

## 2. 零漂移回归：第 1 轮全部夹具在新树上重跑（268 项读数逐项相同）

工具：`verify2/diff_readings.py`（解析 `note:`/`error:` + 源码片段，比较读数与 error 表达式集合）。
复现：`run_probe2.ps1 -Exe verify2/bin/typort_r2.exe -Mode check`，再对第 1 轮 `verify/*.after.txt` 做 diff。

```
v1_direction 25 / v2a_basic 44 / v3_nat 74 / v4_show 44 / v5_cross 54 / w_core2 14 / w_core3 2 / w_data 51
=> 8/8 ZERO-DRIFT，共 268 项读数与 error 集合全部一致
```

⇒ 第 2 轮在飞改动**无语义漂移**。（本轮 owner 落盘后应再跑一次；见 §8。）

---

## 3. 仿真 A/B：第 1 轮 FIFO 修复升级为**真仿真背书**；并更正第 1 轮「无 verilator」的错误结论

### 3.1 更正
第 1 轮我在 `tools/spinalhdl-verify/verify.py` 里写「this machine has no verilator」，**是错的**。
本机 `C:\msys64\mingw64\bin` 有 `verilator_bin.exe`（**Verilator 4.024**）、`make.exe`、`g++.exe`；
`shutil.which("verilator")` 返回 `None` 是因为 **msys 把 `verilator` 装成无扩展名包装脚本，Windows 按 PATHEXT 匹配看不见**。
Lead 本轮最小修好三处（verilator 解析回退 `verilator_bin`；msys verilator 4.024 的 `-Mdir` 绝对路径坑；生成的 testbench 里反斜杠路径非法转义）后仿真跑通。

### 3.2 独立复现的 A/B（原始输出 `verify2/sim/ab_{after,before}.txt`）
命令：
```
$env:TYPORT="$PWD\target\debug\typort.exe";   python -X utf8 tools\spinalhdl-verify\verify.py tools\spinalhdl-verify\cases\v_dualclock.typort
$env:TYPORT="$PWD\target\release\typort.exe"; python -X utf8 tools\spinalhdl-verify\verify.py tools\spinalhdl-verify\cases\v_dualclock.typort
```
| 侧 | 二进制 | 结果 |
|---|---|---|
| AFTER | `target/debug/typort.exe`（mtime 14:07:08，HEAD 645dc3bd） | `[OK] vPulseCC` / `[OK] vFifoCC` → **2 passed, 0 failed, exit 0** |
| BEFORE | `target/release/typort.exe`（mtime **2026-09-29 03:49:29**，早于第 1 轮全部修复） | `[OK] vPulseCC`；vFifoCC **286 条 MISMATCH**（首条 `cycle 0: got 0 expected 1`）→ **1 passed, 1 failed, exit 1** |

⇒ 与 Lead 读数逐项一致（含 286 这个数）。**第 1 轮 `streamFifoCC` 修复的证据等级由「结构级 + emitted Verilog」升级为「真仿真背书」**：
Verilator 4.024 编译 RTL + 120 周期双引擎时钟锁步，参考模型是第 1 轮重写的**独立口径** `RefFifoCC`
（模 2^PW 占用差 + wrap 位 + 真非阻塞同步序，**不是**与 RTL 同构的循环验证）。
修前 286 条 MISMATCH 全部是「got 0 / expected 非 0」——即复位后 full/empty 同时为真、push 永不写、数据永不出现，与第 1 轮的静态分析完全吻合。

### 3.3 连带更新
第 1 轮文档里「PLRU / metaDiv / 大字面量护栏无仿真背书」的空缺：本轮仿真可用后，若这些项落在
`v_utils_*` / `v_misc_*` 用例覆盖面内即可一并升级 —— **以 hdl-a（task-13）的全用例集结果为准**（§8 待办）。

### 3.4 本机第一次真跑 L3：51 个模块 50 绿 1 红；红线经我裁决为 **(c) 参考模型陈旧**，不是实现缺陷

hdl-a 用冻结副本跑完 5 个 case 文件（51 模块）：`== 50 passed, 1 failed, 51 total ==`，
`v_utils_combinational 30/30 | v_utils_sequential 11/11 | v_stream_sequential 4/5 | v_misc_combinational 3/3 | v_dualclock 2/2`；
唯一红的是 **`vStreamM2s`**（`pop_valid`/`push_ready` 从 cycle 0 起不一致，56 条 MISMATCH）。
既有性：2026-09-29 的 release 二进制跑出**逐条相同**的 56 条 ⇒ 与第 2 轮改动无关。

**我的裁决：`(c)` 参考模型陈旧**（`RefStreamM2s` 仍编码 F1 修复前的错误公式），RTL 是对的。证据链：
1. **契约**：`docs/hdl-stream-fsm-design.md:38` 把 `input.ready := rValid || outReady` 标为 **F1「满/空条件写反」**，
   正确语义是 `ready = outReady || !rValid`（`Stream.scala:493-495`：空时随时收、满时等下游）；§4.2 的 S1 计划即「m2sPipe（修 F1）」。
2. **实现**：`hdl-stream.typort` 的 `streamM2sPipeUInt` 已是修正形式 `input.ready := outReady || !rValid`。
3. **参考模型**：`verify.py:434 RefStreamM2s` 仍写 `in_ready = self.rValid or inputs["pop_ready"]` —— 正是 F1 旧公式。
4. **模型级逐拍复现**（`python -X utf8 target/prelude_scratch/verify2/m2s_adjudication.py`，直接 import **真实** `RefStreamM2s`，
   另一侧是按 emitted Verilog 逐字转写的 DUT 模型）：

```
cycle  rst  pv  pr  | REF: prdy pval payl | DUT: prdy pval payl | mismatch
    0    1   0   0  |        0     0   00 |        1     0   00 | push_ready   <- 复位后空管：RTL ready=1(正确)，REF=0(F1 旧公式)
    1    1   0   0  |        0     0   00 |        1     0   00 | push_ready
    2    0   1   1  |        1     1   4d |        1     1   4d | -
    3    0   0   0  |        0     0   25 |        0     1   4d | pop_valid,pop_payload
    4    0   1   0  |        0     0   25 |        0     1   4d | pop_valid,pop_payload
   ...
total per-port mismatches (model-level) = 56      observed in the real Verilator run = 56
```
   与真仿真**同 cycle、同数值**（cycle 0 `got 1 expected 0`；cycle 3 `got 1 expected 0` + `got 4d expected 25`；…）；
   56/56 全部由这一条公式差异解释（payload 错位是「接受决策不同 ⇒ 锁存时刻不同」的下游后果）。
5. **结论**：**不是**「首次仿真发现的既有实现缺陷」，而是**首次仿真发现的既有参考模型陈旧**；`RefStreamM2s` 应按 F1 契约更新
   （**不动 RTL**），并复核其余 50 个模块的参考模型是否同样停留在旧语义 —— 已由 Lead 并入 task-13（hdl-a）。
   我不改 `verify.py`（本轮归 hdl-a），保持独立复核位置：它修完后我用同一脚本复算，确认 ref ↔ DUT 逐拍一致。

---

## 4. 四项修复的独立复算

### 4.1 (E) 3 项算术链不收敛 —— **目标形状端到端已修 + 两条残留**（本项**只写「目标形状已修 + 两条残留」**）

**证据来源**：owner 报告 `target/prelude_scratch/engine_quirks/task14_report.md` §10–§16、`window14_landing.md`、`window15_t2_marker.md`（窗口 4/7/8/9/10/11/14/15）；
回滚备份 `engine_quirks/{w8_stuck_memo_mod_rs,w9_arm_probe_mod_rs,t14_full_mod_rs,w11_timed_diag}.diff`；Lead 权威门禁 `lead_w16`；**我的独立复算见 ④**（冻结副本 A/B，两个入口）。

#### ① 11 行裁决表（9 条**证伪** + 窗口 14 **否决/回滚** + 窗口 15 **落盘**；跨窗口 4/7/8/9/10/11/14/15）

| # | 窗口 | 假设 | 实验 | 硬数据 | 裁决 |
|---|---|---|---|---|---|
| 1 | 4 | 「参考版缺孪生的 `FORCE_PRIM_MEMO`」→ 移植 prim memo | `task14_force_prim_memo.patch`（`+107/-3`，仅 `mod.rs`）落盘 → build → lib | lib **609 passed / 0 failed**（无副作用）但 `r2_zf`/`m_e1`/`e15` 三探针**仍 25–30s TIMEOUT** | **no-op**（移植对目标形状零收益）。旁证：孪生**原生**有 `FORCE_PRIM_MEMO` 却也 TIMEOUT ⇒ 分叉解释被推翻 |
| 2 | 4 | 判据 B「**重入环**」（`force(C)` 执行期间重入同一 `C`） | `MT14_INPROG=1`，in-progress 集合键 = Decl 节点指针 `Rc::as_ptr` | 三探针 **`reentry_lines = 0`**（全部 TIMEOUT） | **证伪**；把键换成「(prim 名, 实参指针) 的 FNV 摘要」后**仍 0** ⇒ 「重入环」表述**更正**为「同一批键被**顺序地、反复地** force」 |
| 3 | 4 | （隐含）「大量**不同**应用被展开」（→ 第 3 轮转 materialize 侧） | `MT14_KEYS=1`（键 = prim 名 + 原样实参指针） | `[mt14] forces=17000000 distinct_keys=117 max_repeat=6786837 key_overflow=0` | **推翻**：键只有 **117** 个，单键被 force **6,786,837** 次 ⇒ 是「**顺序重复**」而非「展开爆炸」 |
| 4 | 4 (S2) | 「去掉 force 不动点门槛的 memo 能修」 | `FORCE_PRIM_MEMO`（值含结果 + keepalive + `PRIM_VERSION` + epoch；taint/version 门；命中返回同一 `Rc`）→ build（18:06:18）→ 加 `MT14_MEMO=1` 计数（18:08:34） | 三探针**仍 TIMEOUT**；**`ins` 与 `skip_taint` 全程为 0**（周期打印一次都没触发） | **否决**：热键上 `prim_fn.0(...)` **返回 `None`（stuck）**，`if let Some(result)` 从未进入 ⇒ **memo 类修法（含孪生 `FORCE_PRIM_MEMO`）原理上不可能修该形状** |
| 5 | 7 | 「某个**调用方重试循环**」+「`Rc` 指针相等型定点比较永不收敛」 | `MT14_HOT`：最热键第 **1000** 次与第 **100,000** 次 force 各抓一次 `Backtrace::force_capture()`（两次同形） | 栈共 **436 帧**：内侧 **~415 层** `force_inner`(`mod.rs:2840`) ↔ `nat_add`(`cxt.rs:164`)，含 `nat_concrete`(`cxt.rs:139`)；栈底 **#419 `Infer::infer_in_place`(`elaboration.rs:1361`) ← #420 `bench_check_nf_bounded`(`mod.rs:4829`) ← #421 `l13bench::nf_parity`(`bin/l13bench.rs:252`) ← `bench_one`/`run`/`main`**，**无任何 loop/retry 帧** | **双双证伪**。根因 = **单次 decl elaboration 内的 ~415 层原生深递归重复下钻**，且这些键上 prim 结局是 **stuck(`None`)** ⇒ 缺的是「**stuck 结局**」的缓存（`FORCE_MEMO` 门 `mod.rs:2638-2642` 只覆盖 `SumCase\|Call\|Obj`，**`Val::Decl` 被刻意排除**，孪生 `FORCE_PRIM_MEMO` 也只缓存 `Some` ⇒ 同样失明） |
| 6 | 8 | 「缓存**零进展(stuck)结局**能修」 | Decl 臂零进展缓存（键 = prim 名 + **原样**实参指针；值 = 原样同一 `Rc` + keepalive + `PRIM_VERSION` + epoch；**仅 prim 返回 `None` 且 taint/版本未变时入表**）→ build（19:06:32，sha256 `8D646225…`） | **`e15`（primop + 调用）TIMEOUT 25s → PASS 2.9s**（basic 443ms / fast 227ms / fast_ss 226ms）；`r2_zf` **TIMEOUT 30.4s**、`m_e1` **TIMEOUT 30.2s** | **部分验证**：对 `Val::Decl` 头的卡住应用**有效**，但运算符形状仍挂 ⇒ 未过「三探针全 PASS」的 stop 规则 ⇒ **全量回滚** |
| 7 | 9 | 「窗口 8 失败是因为钩子只挂在 Decl 臂（**臂没覆盖**：运算符路径被 `Val::Call`/`Val::Obj` 包裹）」 | 把 `MT14_KEYS`/`MT14_HOT` 同口径挂到 `Val::Obj`(`mod.rs:2762`)、`Val::Call`(`2800`)、`Val::Decl`(`2857`) 三臂（build 19:13:19，sha256 `74FF5BF8…`） | `r2_zf`：`forces=15,000,000 distinct=5883 max=5,983,761`，top3 = `[decl:nat_add ×2, decl:nat_add 1,994,588]`；`e15`：`forces=15,000,000 distinct=5875 max=5,996,883`，top3 同为 `decl:nat_add` | **证伪**：`Call`/`Obj` **均未进 top3** ⇒ 运算符与 primop **同臂**（`decl:nat_add`），窗口 8 的原因不是臂覆盖。附带事实：键空间比窗口 4 所见更大（三臂合计 distinct **5883**，vs 窗口 4 单 Decl 臂 **117**）⇒ 两条待判别原因：**(i)** 插入门被 taint/`PRIM_VERSION` 变化挡掉；**(ii)** 键里原样实参指针**不稳定** ⇒ 系统性 miss |
| 8 | 10 | 「用 `MT14_MISS` **计数驱动**三分类能定位 miss 主因」 | 在窗口 8 的零进展缓存上加 `MT14_MISS`（lookup hit/absent/gate_ver/gate_epoch；insert ins_ok/skip_prog/skip_taint/skip_ver；键 distinct/max_rep）+ 臂级 `mt14_note`；build 19:27:22（`7FD8C652…`）/ 19:29:06（`FAFF5753…`）；`e15`/`r2_zf`，`--only basic`，20–25s 封顶 | `e15` **2.3s PASS** 但计数只到第一次打印（`forces=1`、`hit=absent=…=0`；臂级 `n=1 distinct=1 max=1 top=[call:cong=1]`，即 prelude 装载期那一次）；`r2_zf` **22.1s TIMEOUT**，同样 `forces=1` | **计数驱动漏测**（→ 该假设**无定论、被否**）：在有 memo 的构建上，三条 force 臂 22s 内访问 **<100k**（窗口 9 的 15M 是在**无 memo**构建上测的）⇒ 爆点**不在 force 臂上**；方法教训：**改时间驱动**。仍扎实的两条：① `e15` 有 memo 时 2.3s PASS（复现窗口 8）；② `r2_zf` 22s 挂死但耗时不在已插桩的三条 force 臂里 ⇒ **存在第二个独立爆点** |
| 9 | 11 | 「第二个爆点 = `cxt.rs` 的 `for _ in 0..k` 展开 / `succ^k` / `SumCase`/`force_chain` / `count_nat_forced`」 | `MT14_TIME=1` **时间驱动**（每 ~2s 一行；站点 = `cxt.rs` 的 `count_nat_forced`/`nat_concrete`/`nat_add` 入口/`nat_add` succ-inner/`nat_add` 展开循环/`nat_mul` 入口/`nat_mul` 展开循环 + `mod.rs` 的 `Val::SumCase` 臂）；build **19:36:06** sha256 `153C0DCB…`；`r2_zf` 与 `e15`，22s 封顶（**无 memo** 构建） | 两探针同形、线性增长：`r2_zf t=14s conc=34,383,683 add=15,629,134 add_step=1 add_unroll=156 mul=12 mul_unroll=6 sumcase=192` → `t=20s conc=49,319,042 add=22,417,935`；`e15 t=14s conc=35,267,207 add=16,030,742 mul=4 mul_unroll=2` | **第一爆点定位成功**：`nat_add` 入口（**`cxt.rs:161`**）稳定 **~1.12M 次/秒**、`nat_concrete`（**`cxt.rs:138`**）**~2.5M 次/秒**；**上述候选全部被反证排除**（`add_unroll=156`/`mul_unroll=6`/`mul=12`/`sumcase=192`/`count_nat_forced=0`/`add_step=1` 全程平坦）；按稳态换算 **15M ≈ 14s**，与窗口 8「`e15` 25s → 2.9s（−22s）」自洽 ⇒ **memo 确实有效**，`r2_zf` 剩余 ~22s 属**第二爆点**（**仍未定位到 file:line**） |
| 10 | 14 | 「孪生（Step T）：把**未 force 的卡住链句柄**存进 `FORCE_PRIM_MEMO` 也能修」 | 参考版 Step R（`mod.rs` 零进展 memo）+ 孪生 Step T 同时落盘 → gate `eq_w14` | `[twin FAILED (NO-TESTS) exit=-1073740791, 264.9s]`；首条失败 `memory allocation of 30064771072 bytes failed`（≈**28 GiB** 单次分配 ⇒ abort）；**隔离实验**：只回滚 Step T（保留 Step R）⇒ `twin_engine_tests 27 passed; 0 failed`（103.76s） | **否决 + 回滚（事实）**：OOM **由 Step T 引入**。窗口 14 的归因「spine 槽位同轮复用」**已被窗口 15 自行更正**（`spine.rs:39` 明写只增不减；槽位只在轮界 `clear_round` 的 `spine.stack.reclaim(...)` 回收，且与 `force_memo_clear()` 成对，见 `entry.rs` 907/908、1486/1487、1582/1583、1638/1639、1658/1659、1682/1683、1799/1800）⇒ **确切机理仍未钉死**（候选：未 force 的卡住链句柄被投入共享后某调用方按 WHNF 契约持续追加）。**参考版 Step R 保留** |
| 11 | 15 | 「孪生（Step T2）：表里**不存任何 arena 句柄**，只存『该应用在 (version, taint) 下已确认零进展』标记」 | `force.rs` +80/−1 落盘（键同 `FORCE_PRIM_MEMO`；值 `(PRIM_VERSION, FORCE_TAINT)`；命中 `return v` 即调用方当前链；仅 `None` 入表；轮界 `force_memo_clear()`）；`TYPORT_STUCK_PROBE=1` 验证身份稳定性 | `[T2] stuck_ins=123 stuck_hit=25002 stuck_tbl=119`（每轮；累积 246/50004/119、369/75006/119）⇒ hits/inserts ≈ **203×**、键集收敛 **119**（与参考版 117 同量级）；`e15` 对照 `ins=11 hit=15 tbl=7`；lib **609/0**、twin **27/0**（**无 abort/OOM**） | **落盘成功**（设计上绕开整类「句柄身份/保活」问题）⇒ `r2_zf` 两引擎 **2.5s、nf=449 一致** ⇒ **目标形状端到端解锁**（我的独立复算见 ④） |

#### ② 机理（终稿）

一次 decl elaboration **内部** ~415 层 `force_inner ↔ nat_add` 原生深递归（窗口 7 backtrace：**436 帧**，栈底是**单次** `Infer::infer_in_place`(`elaboration.rs:1361`)，**无 loop/retry 帧**）；
窗口 11 把第一爆点钉到 **`cxt.rs:161`（`nat_add` 入口，~1.12M 次/秒）+ `cxt.rs:138`（`nat_concrete`，~2.5M 次/秒）**；
键集**小**（Decl 单臂 117 个）但单键被 force **678 万次**；**热键上 prim 返回 `None`（stuck）**（`ins`/`skip_taint = 0）
⇒ 缺的不是「结果缓存」，而是「**stuck 结局的记忆**」，**只缓存 `Some` 的 memo 类修法原理上无效**（这也解释了孪生原生 `FORCE_PRIM_MEMO` 为何同样失明）。
⇒ 两条落地路径印证同一结论：参考版存「Decl 臂零进展结局」（Step R，`mod.rs`）；孪生存**句柄**会 OOM（窗口 14 Step T），
改成只存 **`(PRIM_VERSION, FORCE_TAINT)` 标记**（窗口 15 Step T2，`force.rs`）即成功 —— **要记的是「结论」，不是「值」**。

#### ③ 终稿状态：已修什么 / 残留什么（**措辞纪律：只写「目标形状已修 + 两条残留」**）

**目标形状端到端已修**：`a*100 + x*10 + 5`（具名 def + 调用）这一族**两引擎都终止且 `nf` 一致** ——
`r2_zf` pre TIMEOUT → post **3.5s / `nf=449`（两次同值）**（owner 2.5s；我第二次入口见 ④）；`e15` post **2.9s / `nf=216`**；矩阵 **16 档 nf 一致**（逐档见 ④）。
**残留 1 —— `e07_bigcoef`（`a*99999 + x*99998 + 5` + 调用）：两引擎仍一起 TIMEOUT**（我的 post 复测 **90.1s / 90.3s**，peakWS **0.42GB**；pre 侧 ×3 同值）；
窗口 15 在 60s 内**没有任何 `[T2]` 轮界输出** ⇒ 该轮从未结束；**机理未定位**（推测其卡住链**逐次增长** ⇒ 标记无法收敛，需要「增长中的链」的身份/上界策略）。
**残留 2 —— `e18`/`e19`（def-only 运算符 / primop）不再 TIMEOUT，但两引擎 `nf` 分歧**：`NF-DIVERGE basic=413 fast=222`
（basic：613 字符的 `{a + {a + …}}` 展开；fast：27 字符 `a => x => {a * 100} + x + 5`）。
**与 memo 无关的强证据**：窗口 14（缓存卡住链）与窗口 15（只存标记）两种**结构完全不同**的孪生实现给出**逐位相同的 `fast=222`**
⇒ 分歧源自两引擎**既有的 `nat_mul` 归约形态差异**，此前被双方 TIMEOUT 掩盖（**哪一侧是期望范式尚无裁决**）。
⇒ 准确表述 = **目标形状已修 + 两条残留**；`e07` 与 `e18/e19` 分别进入第 3 轮候选（§10-①/②）。

> **【第 3 轮更正 · 2026-10-09】** 上面「源自既有的 `nat_mul` 归约形态差异」这句**归因已被第 3 轮独立复算证伪**（完整证据链：`docs/prelude-round-3-2026-10-09.md` §2）。
> **正确机理** = **孪生 `quote` 不 force「卡住 prim 应用里 prim 从未检查的那个实参」**：`nat_add` 的归约性只看第 2 实参，当第 2 实参是**裸 rigid 变量**时 prim 直接返回 `None`（卡住），
> 第 1 实参**永不 force** ⇒ 它里面的 redex 原样留在孪生范式里；参考版 `quote_inner` 对每个访问到的值先 `force`，故把它归约掉。
> **与 mul 无关的对照形状同样分歧**：`(a + 0) + x`（DIVERGE 7/12）、`(a * 0) + x`（8/12）、`(a * 1) + x`（7/14）；且**同一输入的用户可见报错文本不同**
> （`can't unify` 的 `expected:`：孪生 `{a * 1} + x` vs 参考版 `a + x`；`s07`/`s08` 各复测 2 次逐字节一致）。
> **裁决：参考版（basic）是期望范式，孪生偏离** —— 范式里出现 redex 按定义就不是范式；Lead 已采纳**方案 A**（修孪生 `quote`，task-29）。
> **本文件全部实测数字（`413/222`、`613/27` 字符、4.2s、两种孪生实现 `fast=222` 逐位相同等）不变、仍然有效**；被替换的**只是归因**（以及「两种实现一致」的**解释**：两条实现都不 force 未检查实参）。

#### ④ 我的独立复算（verifier，2026-10-08 23:0x–23:3x，**两个入口**）

**DUT（全部冻结副本，hash 已核）**：pre = `verify2/bin/l13bench_r2.exe`（**13:56:33**，干净 HEAD）+ `verify2/bin/typort_r2_w5.exe`/`lead_w12_typort.exe`；
post = `target/prelude_scratch/lead_w16_l13bench.exe`（**mtime 23:00:19 / 9,283,072 B / sha256 `790BB801972A7EBA091B1688B9E4959557F5D7A00642AAD333A0767C573D1EFE`**，与共享 `target/debug/l13bench.exe` 字节相同，Lead 用 `cargo build --bin l13bench` 产出）
+ `lead_w16_typort.exe`（22:48:10 / 19,999,232 B / `9844617D…`）。

**(a) l13bench 口径**（`--file X --with-prelude core --rounds 1`，`L13BENCH_DIAG=1`；`nf=` 行 = `nf_parity` 两引擎一致，`NF-DIVERGE` = 两版都终止但范式不同）：

| 探针 | pre（13:56:33） | post（23:00:19） |
|---|---|---|
| `r2_zf`（`a*100 + x*10 + 5` + 调用） | **TIMEOUT ×3**（45.3s / 120.3s / 120.0s，peakWS 0.03GB） | **PASS ×2：3.5s / 3.5s，`nf=449` 两次同值** ✔ 与 owner 2.5s/449 一致 |
| `e15_primop_chain` | TIMEOUT 45.3s | **PASS 2.9s，`nf=216`** ✔ |
| `e07_bigcoef` | **TIMEOUT ×3**（45.0s / 120.2s / 120.0s，peakWS 0.42GB） | **TIMEOUT ×2**（90.1s / 90.3s，peakWS **0.42GB**）✔ 与 owner「>60s」一致 |
| `e18_defonly_ops` | TIMEOUT 45.3s | **终止 4.2s：`NF-DIVERGE basic=413 fast=222`** ✔ 逐位一致 |
| `e19_defonly_primop` | TIMEOUT 45.2s | **终止 4.2s：`NF-DIVERGE basic=413 fast=222`** ✔ 逐位一致 |

**矩阵 19 档（我两侧全量跑 —— 这是本项第一次真正的全量基线）**：

| 档 | pre | post | 档 | pre | post |
|---|---|---|---|---|---|
| e01 3term_lit | TIMEOUT | **nf=252** | e11 mulvar | PASS | nf=10 |
| e02 3term_var | TIMEOUT | **nf=246** | e12 fn_primop | TIMEOUT | **nf=252** |
| e03 4term | TIMEOUT | **nf=250** | e13 foldl_prod | TIMEOUT | **nf=108** |
| e04 2term | PASS | nf=242 | e14 foldl_nat | TIMEOUT | **nf=22** |
| e05 coef0 | PASS | nf=12 | e15 primop_chain | TIMEOUT | **nf=216** |
| e06 coef1 | PASS | nf=10 | e16 primop_addonly | PASS | nf=22 |
| e07 bigcoef | TIMEOUT | **TIMEOUT** | e17 ops_nomul3 | TIMEOUT | **nf=216** |
| e08 litonly | PASS | nf=252 | e18 defonly_ops | TIMEOUT | **NF-DIVERGE 413/222** |
| e09 lam_3term | TIMEOUT | **nf=252** | e19 defonly_primop | TIMEOUT | **NF-DIVERGE 413/222** |
| e10 add3 | PASS | nf=12 | | | |

⇒ **post：16 档两版 `nf` 一致 + 2 档「终止但分歧」+ 1 档 TIMEOUT**；**pre：7 PASS / 12 TIMEOUT**。
**新转「终止且 nf 一致」= 9 档**（e01/e02/e03/e09/e12/e13/e14/e15/e17）；**另 2 档（e18/e19）**由 TIMEOUT 转为「终止但分歧」；**`e07` 两版都 TIMEOUT**。
**零回归证据**：pre 已 PASS 的 **7 档**（e04/e05/e06/e08/e10/e11/e16）在 post 的 `nf` **逐档相同**（242/12/10/252/12/10/22）⇒ 引擎改动**没有**改变已收敛形状的范式。
与 owner 窗口 15 的矩阵**逐档同值**（我实得 e01 252 / e02 246 / e03 250 / e05 12 / e06 10 / e08 252 / e09 252 / e10 12 / e11 10 / e12 252 / e13 108 / e14 22 / e15 216 / e16 22 / e17 216 / e18 413·222 / e19 413·222 / e07 TIMEOUT）。

**(b) 孪生 `PRIM_STUCK` 标记复算（我独立设 `TYPORT_STUCK_PROBE=1` 复跑）**：stderr 原文 = `[T2] stuck_ins=0 hit=0 tbl=0` → `[T2] stuck_ins=123 stuck_hit=25002 stuck_tbl=119` → `246/50004/119` → `369/75006/119`
⇒ hits/inserts ≈ **203×**、键集收敛 **119**（与窗口 15 报告逐值一致）；**env 不设时 stderr = 0 字节、无 `[T2]` 行** ⇒ 新诊断**默认关、零输出**（同一次 stdout = `nf=449`）。

**(c) typort 第二入口**（`typort check X --max-infer-ms 20000`，**独立于 `nf_parity` 机制**；pre = `lead_w12_typort.exe`「改动前」/`typort_r2_w5.exe`，post = `lead_w16_typort.exe`）：

| 探针 | pre | post | 判读 |
|---|---|---|---|
| `r2_zf` | **TIMEOUT**（100s 封顶；原文只有 header + `parser` 行 ⇒ 卡在 elaboration） | **41.0s 正常返回，`note: 345`** ✔（`z_f 3 4` = 3·100+4·10+5） | 目标形状在**与 oracle 无关的入口**上也解开了 |
| `e15` | **TIMEOUT** 100.3s | 41.0s 正常返回（无诊断、无 println） | 同上 |
| `e18` / `e19` | **TIMEOUT** 100.1s / 100s | 40.0s / 40.0s 正常返回 | 同上 |
| `e07_bigcoef` | **68.3s 后 `thread 'main' has overflowed its stack`（栈溢出崩溃）** | **62.8s 后同样栈溢出崩溃** | ⚠️ **e07 的残留机理线索**：两版都在 elaboration 侧**爆栈**（不只是 l13bench 里的「慢」）⇒ 支持「卡住链**逐次增长**」的推断；**我的判定器把它记成 `INCONCLUSIVE`（无 note/error 行）——这是判定器缺陷**（崩溃 ≠ 无诊断），已按实测更正 |

⇒ 两入口结论一致：`r2_zf`/`e15`/`e18`/`e19` **pre 挂 → post 返回**；`e07` **两版都失败**（l13bench: TIMEOUT；typort: 栈溢出）。

**(d) 早期「分叉」口径更正史**：owner 曾报 `m_e1`（def-only）`--only fast` **4.4s PASS**、`a*100+x+5` + 调用 **4.6s PASS**；
我在安静窗口、同一 pre 冻结副本上把 `e18/e19`（def-only）与 `e17`（+调用）**都测成 TIMEOUT**（25s 封顶，40s 复测同）；
owner 后澄清 4.6s 读数来自 **14:32 的 `(B)` 实验构建**（带 `nat_concrete_forced`）、4.4s 来自更早 13:56:33 的**单次**读数 ⇒ 记为「**未复现 + 原读数属实验构建/未复测单次**」。
（这与 ⑤ 的更正是两件独立的事：`e18/e19` 确实 TIMEOUT，而 `e04/e05/e06/e08/e10/e11` 确实 PASS。）

#### ⑤ 我纠正的一条**基线错误**（本轮最有传导性的一次自查）

round-2 的 §4.1 曾写「**我测到的全部形状都 TIMEOUT，唯一的 PASS 是 `e16`**」——那是**过度概括**：当时我实际只实测了 `e15/e17/e18/e19` 四档（外加 `typort check` 的几条），
而 `e_shape/MANIFEST.txt` 里 `e04/e08/e10/e11` 本来就**写着预期 PASS**，我却把「已测的四档都挂」写成了「全部形状都挂」。
本轮我第一次把 **19 档全量**跑在 pre 副本上（上表 (a)），实得 **pre = 7 PASS / 12 TIMEOUT**。
**影响（已传导）**：owner 的窗口 14/15 报告引用了那句「基线（verifier 独立复算）：干净 HEAD 上除 `e16` 外全 TIMEOUT」
（`window14_landing.md` §形状矩阵、`window15_t2_marker.md` §5）——**该引用继承了我的错误**，故「16 档新转 PASS」「18/19 完成」这两句的**基线侧**应以本表为准；
准确说法 = **新转「终止且 nf 一致」9 档 + 新转「终止但分歧」2 档 + `e07` 两版都失败**（④ 已逐档列出）。
**教训（已入 §6.6-5）**：「我没测到的形状」不能写进结论；矩阵型结论**必须逐档列表**，并区分「已实测的档」与「设计存在的档」。

### 4.2 (F) HDL039 误报 —— **已用 hdl-b 的最小复现 + 两个冻结副本做出独立 A/B（修前误报在场 / 修后消失 / 正例保持）**

**① hdl-b 的最小复现**（不依赖 hdl-crossclock）：`target/prelude_scratch/hdl_b_hdl039_repro.typort`，
结构 `src`(cdA) → `s1`(cdB) → `s2`(cdB) 两条纯移位 = 2FF 链；末级 `s2` 有两个**合法**读者：
`q := s2`（组合输出）+ `cons <= mux(en, s2, cons)`（同域寄存器、无条件时钟赋值、RHS 直读末级）。
**正例**（必须仍报）：`hdl_check_graph_tests.rs:649-671` 的 `midRead`（读真中间级 `s1`），我已复刻为 `verify2/f_cases/f1_pos_mid_read.typort`。

**② 单变量 A/B（(F) 已落盘后复算）**：修前 = 我的 round-1 冻结副本 **11:47:26**；修后 = 冻结的当前构建
**15:59:36**（`verify2/bin/typort_r2_frozen.exe`）。（Lead 报的是 15:55:01；我实际冻结到的是 **15:59:36** ——
共享 exe 在 hdl-c 的窗口里又被重建过，按「先冻结」指令我用的是自己冻结时看到的 mtime。）

| 探针 | 修前 11:47:26 | 修后 15:59:36 |
|---|---|---|
| `hdl_b_hdl039_repro` | HDL038=1 / **HDL039=1**（`[t9MuxConsumer] s2`） | HDL038=1 / **HDL039=0** ✓ |
| `f1_pos_mid_read`（真中间级正例） | HDL039=1（`[midRead] s1`） | **HDL039=1** ✓ 未被过度抑制 |
| `examples/hdl/21-crossclock`（example 级） | HDL038=2 / **HDL039=1** | HDL038=2 / **HDL039=0** ✓；无 HDL036/037 |

原文（修前，example 21）：
```
warning: [hdl][warning] HDL039 [ccFifo] _d_wrPtrSync2: synchronizer mid-stage read: consumer bypasses the chain head
```
⇒ **结论**：误报**确认存在**、修后**消失**、真中间级正例**仍报**；且改动动 `srcs` 语义这一点在 **example 级**得到验证
（旗舰例子的 `ccFifo` 链末级 `_d_wrPtrSync2` 修前被误判为「中间级」，修后消失，两条 HDL038 保持不变）。
`examples/` 在工作树中**未被修改**（`git status -- examples/` 空）⇒ 这是纯二进制对照，无文件混淆。

**③ 【我先前的「测试盲区」假设已被**出处核查推翻**，据实更正】** 我最初用 **11:47:26** 副本在 example 21 上看到
`HDL039 [ccFifo] _d_wrPtrSync2`，而 `hdl_check_graph_tests.rs::examples_21_crossclock_expected_warnings`
断言 `!output.contains("HDL039")`（in-process `run_with_prelude`），于是我曾推测「测试是空断言 / CLI 与 in-process 不等价」。
**该推测不成立**——用**干净 HEAD 的冻结副本**（`verify2/bin/typort_r2.exe`，mtime **13:56:32**，round-2 开始时冻结、
当时 `git status` 干净、`HEAD 645dc3bd`）复测：

| 探针（干净 HEAD 645dc3bd，13:56:32） | 读数 |
|---|---|
| `examples/hdl/21-crossclock` | HDL038=2 / **HDL039=0** ⇒ **与 in-process 断言一致，无盲区** |
| `hdl_b_hdl039_repro` | HDL038=1 / **HDL039=1** ⇒ 该误报在**干净 HEAD 上真实存在**（(F) 修复正是冲它去的） |

⇒ 真正的解释是**二进制出处**：11:47:26 是**第 1 轮期间**的中间构建，其内嵌 prelude 与提交态 645dc3bd 不同。
HEAD 的 `hdl-crossclock.typort:347-357` 有对应注记：*「when 包裹 + Cd 赋值」会被主域与 outCd 域各发射一次，
导致 `_d_rdPtr` 的时钟赋值 RHS 就含 `_d_wrPtrSync2`，CDC 检查（hdl-check-graph…）* —— 并因此引入具名组合线
`_d_popGo`（`popGoE = create(... "_popGo")` → `rdNext = mux(popGo, rdPtr+1, rdPtr)`，作用在 **pop/读侧**）。
⇒ 11:47:26 那次 `_d_wrPtrSync2` 的 HDL039 属**中间态产物**，不能用来推断测试路径行为。
**教训（入 §6.6）**：**与测试断言做对照时，必须用「干净 HEAD 构建」的二进制**；中间构建的读数只能用于「修前/修后同源对照」。
（可选的加固：仍值得补一条 CLI 文本级钉，让 `typort check` 的 warning 集合也被断言 —— 但这不是「空断言」问题。）

**③ hdl-b 的修前读数与根因**（其 `hdl_b/task9_report.md`，mtime 15:01:49 二进制）与我的 11:47:26 读数一致；
根因：`chainNextOf` 缺「纯移位」判据 ⇒ `x <= mux(cond, r, x)` 被当作链级 ⇒ 真末级被升级为「中间级」⇒ 误报。
关键证据：被拒链级的 `srcs` **恰好是 `[r]`**（拒绝来自 **enable 分支**而非 srcs）；mux 消费者 `srcs=[cons,s2,en]`。
`ccFifo` 的 `_d_rdPtrSync1/2` 带 init（`newUIntRegInitNatNamed`）⇒ 链被截断；`_d_wrPtrSync1/2` 不带 init ⇒ 正常。

**④ 我自造夹具的局限（保留，作为方法论）**：`verify2/f_cases/` 的 `f2`/`f3`/`f4` 在**修前二进制上也不报 HDL039**
⇒ 我的形状没有命中该误报（触发需要「末级被 mux 驱动 **且** 末级另有合法读者 **且** 链级形态精确匹配」）。
「自造夹具不报」不等于「缺陷不存在」——**必须拿 owner 的最小复现做锚点**。
- 附带读数：`f4` 在 round-1 二进制 11.6s vs r2b 82s（同窗口有并发构建，不能据此断言性能回归；§8 待净窗口复测）。

### 4.3 (G1) module 宏端口诊断 —— **已落盘（窄设计 v6）**；我的独立复算待补
**最终形态（v6，hdl-c）**：**只**对字面 token `Boolean` 特化（5 条臂），**通用 `$ty` 臂全部删除**。
理由（hdl-c 实测）：通用臂会把**合法的 `= Bool` 端口**误报。

**Lead 独立复测的四条探针原文（我尚未独立复算，等级 = Lead 读数）**：
| 探针 | 读数 |
|---|---|
| `formA` / `formB`（`input x = Boolean`） | `HDV004 [Boolean] sel` + `name not in scope`（模块失败，但**可定位到端口类型**） |
| `typoA` / `typoB`（`input a = MyTypo`） | **无 HDV004** + `expected 'def', found identifier` + `not in scope`（**仍响亮失败** ✓） |

**我在 14:07:08 副本上的旧读数（落盘前，保留作对照）**：
| 用例 | round-1 语义 | 14:07:08 实测 |
|---|---|---|
| `g1_boolean_port`（`input x = Boolean`） | 无臂可匹配 | `expected 'def', found identifier` + `name not in scope: boolPort` ⇒ 旧行为 |
| `g2_mytypo`（`input a = MyTypo`） | 必须仍响亮失败 | 同上 ⇒ 仍响亮失败 ✓ |
| `g3_bool_pos`（`input sel = Bool`） | 应正常 | `note: module boolOk (` ⇒ 正常 ✓ |

- `g3` 首版我写成 `output y = UInt[1]; y := sel`，实测报 `cannot convert Bool to UInt[1]`——那是**我的探针类型错**，已修正为 `output y = Bool`。
- **两条已知限制（入 §6.7 与 §10）**：(i) `MyTypo` 这类**拼写错误类型名仍不可诊断**（仍只有 `expected 'def'`）；
  (ii) **formA 混合端口表未覆盖**（同表内既有合法 `= Bool` 又有 `= Boolean`）——通用臂会误报合法 `Bool` 端口，故本轮不做。
- **我的独立复算（冻结副本 `typort_r2_w5.exe`，sha256 `E69FEBA0…`，与 `hdl_a_sim/typort_w5.exe` 同源）**——与 Lead 读数**逐项一致**：
  | 探针 | 实测（w5） |
  |---|---|
  | `hdlc_t10_x1_formA` | **HDV004 ×2**（`[Boolean] sel` 与 `[Boolean] y`，报文含「`Boolean` is `Bool`'s defining type name - write `Bool`…」）+ `name not in scope: aliasA`（模块失败）；`expected 'def'` **0** |
  | `hdlc_t10_x1_formB` | HDV004 ×1（`[Boolean] sel`）+ `name not in scope: aliasB` |
  | `hdlc_t10_x1_typoA` | **HDV004=0** + `expected 'def', found identifier` + `name not in scope: typoA` |
  | `hdlc_t10_x1_typoB` | **HDV004=0** + `expected 'def', found identifier` + `name not in scope: typoB` |
  | 我的 `g1_boolean_port`（`input x = Boolean`） | HDV004 ×1（`[Boolean] x`）+ 模块未展开 ⇒ **旧行为已被新诊断取代** ✓ |
  | 我的 `g2_mytypo` | HDV004=0 + `expected 'def'` ⇒ **仍响亮失败但不可定位**（见 §6.7） |
  | 我的 `g3_bool_pos`（`input sel = Bool`） | `note: module boolOk (`、0 error、0 HDV004 ⇒ **正例未受影响** ✓ |
  ⇒ (G1) 结论：**v6 达成设计目标**（`Boolean` 端口给出可定位诊断；`Bool` 正例不受影响；`MyTypo` 保持响亮失败）。

### 4.4 (H) 工具对抗式验证 —— 见 §5

### 4.5 (F 附带) `DriveSrc.srcs` **pending 泄漏**：owner 有插桩证据；我**未能**用可观测探针独立复现

**owner 的机理与证据**（hdl-b task16 报告）：`scanStmtEx` 的 `memWrite`/`assertExpr`/`assertExprCd` 三个臂把读扫进
`pending` 却**从不清理**，`stmtAssign` 随后把整个 `pending` 当成本条 drive 的 `srcs`。插桩原文：
`r=rdSync1 x=rdSync2 shapes=[|"rdSync1","pushData","wrPtr","m",]`（纯移位被算成读了写数据/地址/mem）；
对照 `r=wrSync1 x=wrSync2 shapes=[|"wrSync1",]`。修法 = 三个臂末尾 `accClearPending(...)`。
影响面：污染 `headDriveSrcCount`/`headQualified` ⇒ **HDL037 误报**；`driveEdges`/`domRoundSrcs` ⇒ **幻影边/域传播**。

**我的独立复现尝试（失败，据实记录）**：
- 我自写的最小例子 `verify2/leak_cases/v_leak_min.typort`（`wrPtr`(主域) -Cd→ `ws1` → `ws2`(从域) 纯移位链 + 同域消费者 +
  链前一个条件 `memWrite`），在**修前 11:47:26** 与**修后 15:59:36** 上读数**完全相同**：
  `HDL036=0 HDL037=0 HDL038=1 HDL039=0`（`HDL038 [lkLeak] ws1`）。
- hdl-b 自己的 `hdl_b_fifo_like.typort` 在两侧也是 `HDL038=2 / HDL037=0`，同样**不显示 pre/post 差异**。
⇒ **我无法用可观测（告警）探针独立复现该泄漏的后果**；其证据目前只存在于**引擎插桩输出**（`srcs` 形状），
而按纪律我不改 `src/**`、无法自行插桩。**唯一可观测的同族后果**是 example 21 的 `HDL039 [ccFifo] _d_wrPtrSync2`
（§4.2 ③）：修前有、修后无 —— 但它与「判据缺纯移位」这一条修复同属一次改动，我**无法把两者分开归因**。
⇒ 结论记为：**pending 泄漏 = owner 级插桩证据，我未独立坐实其可观测后果**；建议 hdl-b 给一个**只靠告警文本即可判别**的
最小例子（例如能稳定产出 HDL037 的那个探针），我再复算。

**与 owner 声称的一处矛盾（留档，档源已固定）**：hdl-b 称「**带 `memWrite` → HDL037；去掉 `memWrite` → HDL038×2**」，
但我实测该文件（**同时含 `memWrite` 与 `memRead`/`popReg`**）在修前/修后**两侧都是 HDL038=2、HDL037=0**，与该声称不符。
档源指纹：`target/prelude_scratch/hdl_b_fifo_like.typort`，**mtime 15:46:17 / size 2848 / sha256 前 16 位 `5127AA4223CB1262`**；
内含 `memWrite`（:36）与 `regAssignCd(popReg, memRead(...))`（:41）。⇒ 请 hdl-b 明确其「带/不带 memWrite」两版各自的**文件名 + hash**，
否则「泄漏 ⇒ HDL037」这条缺少可判别的告警级最小复现。

### 4.6 (G2-land) task-18 的 `(e : T)` 定向文案 —— **我的独立 A/B 复算（自写探针 10 项）**

DUT：**改动后** `target/prelude_scratch/lead_w12_typort.exe`（20:41:25 / 19,941,376 B / sha256 `57906082…`）↔ **改动前** `verify2/bin/typort_r2_w5.exe`（18:11:10 / `E69FEBA0…`）。
探针目录 `verify2/g2land/`（全部我自写，未照抄 owner）；读数 `verify2/out/{pre_*,g2l_*,w12_*}.txt`；判定器 = `run_probe2.ps1 -Mode check`。
**判定器校准（纪律）**：先用同一条 grep（`type ascription`）在**改动前**副本上跑 —— `p1` 命中 **0**，改动后命中 **1** ⇒ 量词本身不会自证。
**新文案原文**（`p1` 原始输出）：
```
error: type ascription `(e : T)` is not supported by this language; bind it first and use the binder, e.g. `def z: T = e` then `z`
```

| 探针（我的） | 形状 | 改动前（w5） | 改动后（w12） | 判定 |
|---|---|---|---|---|
| `p1_ascription_pos` | `(left 9 : Either[Nat, Boolean]).left_to_option` | 3 条错误（`can't unify` + `expected ')'` + `expected newline`），**新文案 0** | **原 3 条一条不少** + 新文案 1（共 4 条）：`can't unify` 1、`expected ')'` 1、`expected newline` 1 | ✅ **新文案 ∧ 原错误共存**（任务判据） |
| `p3_ascription_simple` | `def n_bad: Nat = (9 : Nat)`（无方法应用） | 2 条错误，新文案 0 | 3 条错误，新文案 1 + `expected ')'` 1 | ✅ 诊断不依赖方法调用（第二个正例） |
| `p2_workaround` | `def z_ok: Either[Nat, Boolean] = left 9` → `.left_to_option` → `println …show` | `note: some 9`、0 error | **完全相同**：`note: some 9`、0 error | ✅ **绕法可用**（文本逐字节同） |
| `c2_decl_colon` | `def bar: Nat = 3` | 0 error（1 note） | 完全同 | ✅ **不误报** |
| `c3_bracket_binder` | `def id_len[len: Nat](…): …`（方括号 binder）+ `keep[T]` | 0 error（1 note） | 完全同 | ✅ **不误报** |
| `c4_verilog_range` | `module rng(input [7:0] w, …); assign y = w[7:4];`（**owner 第一版翻车的那类**） | 0 error、0 note（`infer 0.50s`，真解析） | **逐字节同** | ✅ **不误报** |
| `c5/c1` annotated lambda | `(y: Nat) => y`（def 体 / 实参位） | **已失败**：`expected ')' , found ':'` + `name not in scope: y`（4 / 6 条） | 同 + **新文案 1 / 2 条** | ⚠️ **不是「新引入的假阳性」（两侧都不接受该形态），但新文案在 binder 位置**给出「type ascription … bind it first」的**误导建议** ⇒ 记限制（见下） |
| `c6` 对照（我补） | `def lamU: Nat -> Nat = y => y` + `apply1 lamU`（**无标注** lambda = 本语言支持的 lambda 形态） | `note: 3`、0 error、新文案 0 | **逐字节同** | ✅ 界定「lambda 本身没问题，问题在**标注**形态」 |
| `c7` 对照（我补） | `def twice(f: (y: Nat) -> Nat, n: Nat)`（**类型位** 命名 Pi binder）+ `twice succ1 3` | `note: 5`、0 error、新文案 0 | **逐字节同** | ✅ 冒号在**类型位** binder 里**不触发** ⇒ 触发面 = 表达式位 `(...)` 内的冒号 |

**同时做的「无文本漂移」对照（改动前 vs 改动后，`verify2/**` 既有诊断夹具逐行 diff）**：

| 夹具 | 诊断行数（前 → 后） | 逐行 identical |
|---|---|---|
| `examples/hdl/24-verilog-practice.typort`（owner 第一版翻车处：曾多 3 条假阳性 + twin 25/2 红） | 11 → 11 | ✅ True |
| `examples/hdl/21-crossclock.typort` | 6 → 6 | ✅ True |
| `hdlc_t10_x1_formA` / `formB` | 4 → 4 / 3 → 3 | ✅ True |
| `hdlc_t10_x1_typoA` / `typoB` | 3 → 3 / 3 → 3 | ✅ True |
| 我的 `g1_boolean_port` / `g2_mytypo` / `g3_bool_pos` | 2 → 2 / 2 → 2 / 1 → 1 | ✅ True |
| (F) 正例 `f1_pos_mid_read` | 3 → 3 | ✅ True |
| 我的 `c2_decl_colon` / `c3_bracket_binder` / `c6_lambda_unannot` / `c7_pi_binder_type` | 1→1 / 1→1 / 1→1 / 1→1 | ✅ True |
| 我的 `c4_verilog_range` | 0 → 0（两版都无诊断；`infer≈0.50s` 证明真解析） | ✅ True |

⇒ **10 个既有夹具 + 5 个反例探针（共 15 个文件）：新增文案零命中、既有诊断文本逐行 identical**；唯一出现新文案的是 2 个真 ascription 正例（`p1`/`p3`）与 2 个 annotated-lambda 探针（`c1`/`c5`，见下）。
（原始读数：`verify2/out/{pre_*,w12_*,g2l_*}.txt`；对比脚本口径 = 只取 `^\s*(note|error|warning)` 行）

**逐条判定行**（`verify2/out/verdicts.txt`，w12 冻结副本，`-TimeoutSec 150`；`peakWS` 全部 0.31GB）：
```
[w12_ex24]      69.4s notes=10 errors=0 -> OK(notes=10)      [w12_g1]      48.0s notes=0 errors=1 -> ERRORS=1
[w12_ex21]      56.2s notes=4  errors=0 -> OK(notes=4)       [w12_g2]      47.4s notes=0 errors=2 -> ERRORS=2
[w12_t10A]      49.8s notes=1  errors=1 -> ERRORS=1          [w12_g3]      44.5s notes=1 errors=0 -> OK(notes=1)
[w12_t10B]      47.4s notes=1  errors=1 -> ERRORS=1          [w12_f1]      44.2s notes=1 errors=0 -> OK(notes=1)
[w12_t10typoA]  47.8s notes=1  errors=2 -> ERRORS=2          [w12_c6]      43.2s notes=1 errors=0 -> OK(notes=1)
[w12_t10typoB]  47.7s notes=1  errors=2 -> ERRORS=2          [w12_c7]      43.5s notes=1 errors=0 -> OK(notes=1)
[w12_c5]        47.5s notes=0  errors=5 -> ERRORS=5          [pre_c6]      43.3s notes=1 errors=0 -> OK(notes=1)
[g2l_p1]        43.2s notes=0  errors=4 -> ERRORS=4          [pre_c7]      43.3s notes=1 errors=0 -> OK(notes=1)
[g2l_p2]        42.9s notes=1  errors=0 -> OK(notes=1)        [g2l_c1]      43.2s notes=0 errors=8 -> ERRORS=8
[g2l_p3]        43.4s notes=0  errors=3 -> ERRORS=3           [g2l_c2]      43.3s notes=1 errors=0 -> OK(notes=1)
[g2l_c3]        43.0s notes=1  errors=0 -> OK(notes=1)        [g2l_c4]      43.9s notes=0 errors=0 -> INCONCLUSIVE(无诊断=符合预期)
```
（**作废读数**：同一批探针我第一次用 `-TimeoutSec 40`，`g2l_p1/p2/p3` 被判 `40.1s TIMEOUT` —— 那是预算伪影，不是挂死，已在下面「读数口径」说明。）
（`pre_*` 对应读数在 `verify2/out/pre_*.txt`：`pre_p1 ERRORS=3`、`pre_p2 OK(notes=1)`、`pre_p3 ERRORS=2`、`pre_c1 ERRORS=6`、`pre_c2/c3 OK(notes=1)`、`pre_c4 INCONCLUSIVE`、`pre_c5 ERRORS=4`、`pre_ex24 OK(notes=10)`、`pre_ex21 OK(notes=4)`。）

**读数口径与一处自查**：`typort check` 在本机冻结副本上单文件固定开销 **~43–50s**（`24-verilog-practice` 69.7s），
`--max-infer-ms 20000` **不**约束这个总时长；我第一批探针用 `-TimeoutSec 40` ⇒ 7 个探针全部被判 `TIMEOUT`（**假挂死**，不是证据），
改用 `-TimeoutSec 150` 后全部正常返回。⇒ 记入方法：**check 模式的超时阈值必须 ≥ 3× 观测总时长**，否则得到的是预算伪影。

#### 4.6.1 **(G2-final) task-23 修订后 —— 我的终稿复算（DUT = `lead_w16_typort.exe` `9844617D…`）**

**新文案（最终）**：
```
error: this language supports neither type ascription `(e : T)` nor an annotated lambda binder `(x: T) => ...`;
       bind it first instead, e.g. `def z: T = e`, or drop the annotation (`x => e`)
```
（单行原文；**一条文案覆盖两义** ⇒ 收口了 task-19 限制 ①。）

| 探针 | w12（修订前） | **w16（终稿）** | 判定 |
|---|---|---|---|
| `p1_ascription_pos`（真 ascription） | 4 条错误：`can't unify` + 新文案 + `expected ')'` + `expected newline` | **同 4 条**，仅新文案文字变长 | ✅ 新文案 **×1** ∧ 原错误**一条不少** |
| `p3_ascription_simple` | 3 条 | 3 条（新文案 ×1） | ✅ |
| `c5_lambda_body`（`(y: Nat) => y` def 体） | 新文案 ×1，4 条 | **新文案 ×1**，5 条 | ✅ 每处 ×1 |
| `c1_binder_colon`（`(y: Nat) => y` **实参位**） | **新文案 ×2**，8 条 | **新文案 ×1，7 条** | ✅ **重复已修**（task-19 限制 ①） |
| `c2` 声明冒号 / `c3` 方括号 binder / `c4` `w[7:4]` / `c6` 无标注 lambda / `c7` 类型位 Pi binder | 0 | **0** | ✅ |
| `c8_brace_range`（`{w[7:0], w[15:8]}`，**新反例**） | — | **0**（0 诊断） | ✅ |
| `c9_brace_colon`（`{3 : 4}`，**新反例**） | — | **0**（3 条其他错误，无新文案） | ✅ |
| `p2_workaround` | `note: some 9` | `note: some 9`（逐字节同） | ✅ 绕法仍可用 |

⇒ **7 类反例零命中**（`w[7:0]`/`w[7:4]`、`{a : b}`、`def bar: Nat = 3`、方括号 binder、类型位 Pi binder、无标注 lambda、大括号拼接）；正例 ×1；重复已去。
**Limitation 现状**：①「文案按 ascription 劝告」已修（文案明说两种都不支持，并给出两条替代写法）；② `tests/round2_engine_tests.rs` 已扩到 **7 例**并由 Lead 亲跑 **7/0**（仍**不在**门禁四条原始行内，见 §9）。**仍未做**：annotated-lambda 语法本身（`(y: Nat) => y` 仍报错，本轮只改文案）。

#### 4.6.2 限制与收尾（task-19 → task-24）
1. ~~**文案在 annotated-lambda 位置不准确**~~ → **已修（task-23）**：文案现同时声明两种都不支持（`c5`/`c1` 各 ×1），`c1` 的**重复两条已去**（8 → 7 行）。
2. ~~**`tests/round2_engine_tests.rs`（6 例）不在权威门禁四条原始行内**~~ → **部分收口**：已扩到 **7 例**并由 Lead 亲跑 **7/0**，且**列进了 Lead 的额外套件清单**；但它**仍不在** `gate_l13.ps1` 的四条原始行内 ⇒ 门禁本身仍不覆盖它（第 3 轮候选：把它并入 lib 或给门禁加第五条，§10-⑥）。

---

## 5. 工具对抗式验证（对 task-11/13 产物）

### 5.1 `tools/probe/run_probe.ps1`（我的独立复跑）
| 检查 | 命令 | 实测 |
|---|---|---|
| 判定器自校准 | `-Calibrate` | `fail_decl → DECL-FAIL OK (8.3s)` / `pass_decl → PASS OK (2.9s)` → `calibration OK -- judge discriminates`，**exit 0** |
| 必失败样本 | `-File verify/hang/mfail_calib.typort` | **exit 3**（非 PASS）✓ |
| 必过样本 | `-File verify/hang/m2_nat_fold.typort` | **exit 0** ✓ |

- 校准样本本体经我核对**不是空壳**：`tools/probe/calib/fail_decl.typort` 用未定义名（必须失败），`pass_decl.typort` 是 `1 + 2`（必须通过）⇒ 校准不是同义反复。
- 工具设计上已修掉第 1 轮两起事故：合并 stdout+stderr 读、按码点匹配中文标记、`NO-OUTPUT`/`EXTERNAL-KILL(exit=N)` 与 `JUDGE-BROKEN`(exit 4) 区分、`Resolve-Bin` 回退 `target/debug/deps/`。
- **我自己的判定器事故**：`verify2/run_probe2.ps1` 首版在 l13bench 模式下对必失败样本判 `PASS-NODIAG`（假 PASS）；校准后修正。**这说明「先校准」这条纪律必须对每个新判定器重做一遍，不能只对上一轮的判定器做。**

### 5.2 `tools/prelude_doc_cov.py`（独立复跑）
```
python -X utf8 tools\prelude_doc_cov.py target\prelude_scratch\verify2\doc\doc.json
=> core+data 156/156, hdl 1003/1003, show 35/35, TOTAL 1194/1194 = 100.0%（documented=1194 items=1194）
```
与 Lead 冻结时的 **1192/1192 = 100%** 同口径（差值 2 = 冻结后 owner 又新增的条目，hdl 1001 → 1003）⇒ **工具结论与我的手工复算一致**，且与我第 1 轮自写 `doc_cov.py` 的分桶一致。

### 5.3 `tools/gate_l13.ps1`（独立跑一次：**当前树是红的**）
命令：`powershell -ExecutionPolicy Bypass -File tools\gate_l13.ps1 -Label verifier_r2 -OutDir target\prelude_scratch\verify2\gate`
（HEAD 645dc3bd，工作树含在飞编辑；日志 `verify2/gate/gate_verifier_r2.txt`）
```
==> [lib] cargo test --lib L13_namespace::
test result: FAILED. 538 passed; 68 failed; 6 ignored; 0 measured; 361 filtered out; finished in 87.57s
```
- **68 个由绿转红**（538 + 68 = 606，测试总数未变）；第 2 轮起点是 606 passed / 0 failed。
- 失败家族：`calc_tests::*`（9 条在日志前 12 行内）、`cong_projection_tests::cong_lambda_add_zero_refl_unwraps` /
  `cong2_nat_add_e_rfl_nonreducing_expected`、`bare_ctor_member_tests::applied_and_concrete_receivers_still_show`；
  panic 落点 `calc_tests.rs:46/63/89/106/123/141/159/177/366`、`cong_projection_tests.rs:108/140`、
  `bare_ctor_member_tests.rs:27`。
- **归因（三方交叉，不是把它当失败）**：① Lead 的 prelude 装载冒烟 `typort check doc_measure.typort` exit 0 零 error
  ⇒ 不是全局装载坏；② 同时在飞的改动只有 `src/L13_namespace/{cxt.rs,elaboration.rs,unification.rs}`（task-8）、
  `hdl-*.typort`（hdl-b）、`tools/**`（hdl-a），而失败集中在 **`cong`+lambda 与宏/归约路径**
  （`cong_projection_tests` / `calc_tests`）⇒ 与 task-8 的写域吻合；③ 我的写域不碰引擎，且
  `prelude_stdlib_tests` 在 13:56 副本上仍 9 绿。⇒ 结论：**并行 in-flight 编辑导致的红树，属引擎侧**。
- **工具边界（建议 task-13 修）**：失败时 `Write-LogLines -Max 12` 只印前 12 条 FAILED，且**不印总数**
  ⇒ 读者会低估规模（我第一封报告就据此误报成 12）。权威数字只在 `test result` 行。
  建议 `[<suite> FAILED]` 行同时打印 `N failed / M passed`，或把 `-Max` 可配。

### 5.4 `tools/gate_l13.ps1` 的对抗式阅读（发现的边界洞）
脚本只用 **cargo 退出码**判 `fail=N`（`:200`）。**0 个测试也是 exit 0**：若某 suite 的测试被改名/过滤到 0 个
（例如 `parity` 的 `--skip L13_namespace::` 某天把全部用例滤掉），门禁会报 `fail=0` 而实际没有覆盖。
建议加**最小计数断言**（lib ≥ N、parity ≥ 15、twin ≥ 27、hdl042 ≥ 2），至少在 `$results.Count -eq 0` 时判失败
（脚本目前只在输出里提示 `(no 'test result' line in log)`，仍算 ok）。
**实测坐实**（干净窗口，cargo/rustc=0）：
```
cargo test --test hdl042_engine_tests -- --exact __no_such_test__
test result: ok. 0 passed; 0 failed; 0 ignored; 0 measured; 2 filtered out; finished in 0.00s
exit=0
```
⇒ **0 个测试时 cargo 退出码为 0**；`gate_l13.ps1` 只看退出码 ⇒ 该情形会报 `fail=0` 而**覆盖为 0**。
同一窗口我另测集成钉仍在绿：`cargo test --lib L13_namespace::prelude_stdlib_tests` → `ok. 9 passed; 0 failed`（exit 0）。

### 5.5 `tools/gate_l13.ps1` 的 `ExitCode` 假失败（我独立实测；第 3 个工具缺陷）
hdl-a 报「`Start-Process -PassThru` 在 PS 5.1 下 `ExitCode` 恒空 ⇒ `$null -ne 0` 为真 ⇒ 通过的套件被判失败」。
我用脚本 `verify2/ps51_exitcode_test{,2,3}.ps1` 独立复现（Windows PowerShell **5.1.19041.6456**）：
```
instant exit 0      finished=True ExitCode=[] isNull=True afterRefresh=[]
instant exit 3      finished=True ExitCode=[] isNull=True afterRefresh=[]
sleep ~2s exit 0    finished=True ExitCode=[] isNull=True afterRefresh=[]
sleep ~2s exit 3    finished=True ExitCode=[] isNull=True afterRefresh=[]
-Wait want=0        ExitCode=[0] isNull=False
-Wait want=3        ExitCode=[3] isNull=False
```
- 复现结论：`-PassThru` + 显式 `WaitForExit()` 时 **`ExitCode` 为空**（8/8 次，含 ~2s 的 child），
  而 `Start-Process -Wait` **正确**返回 0/3。`$null -ne 0` 在 PowerShell 里为 **True** ⇒ 该模式会把通过的套件判成失败。
- **但不是无条件发生**：`gate_l13.ps1` 自己那次 lib 运行打出的是 `[lib FAILED exit=101, 88.8s]`（长跑 child 有值）。
  ⇒ 结论应写成：**`ExitCode` 在该模式下不可靠（至少对快退出的 child 为空），不能作为唯一的 pass/fail 依据**；
  修法：`Start-Process -Wait`（已实测有效），或从已解析的 `test result:` 行判 fail，或校验 `ExitCode` 非 null 再比较。
- 这是本轮**第 3 个**「验收工具自身有缺陷」实例（前两个：`run_probe.ps1` 假 PASS、`gate_l13.ps1` 失败清单截断/0-tests 洞）。
  三条合起来构成「**验收工具必须被验收**」的强论据。

---

## 6. 缺陷清单

### 6.0 【本轮最有价值的方法论】红树归因：从「谁在飞」到**读原生断言文本**才算确证

本轮实测：`tools/gate_l13.ps1` 在 HEAD 645dc3bd + 未提交工作树上给出 **lib 538 passed / 68 failed**（§5.3），
第 2 轮起点是 606/0。**归因过程与最终根因（Lead 锁定 + 我的独立复核）**：

1. **先问「树上有谁在飞」**：`git status` 显示 `cxt.rs/elaboration.rs/unification.rs`（task-8）、`hdl-*.typort`（hdl-b/hdl-c）、`tools/**`（hdl-a）。
2. **三方交叉缩小范围**：① **prelude 装载冒烟** `typort check doc_measure.typort` exit 0 零 error ⇒ 不是全局装载坏；
   ② **差异体量/写域**；③ **失败家族形状**（`calc_tests` / `cong_projection_tests` / `bare_ctor_member_tests` 一片输出断言型测试）。
   → 我与 Lead 都据此先怀疑「引擎侧在飞编辑」——**这个推断是错的**（合理但未确证）。
3. **确证靠读原生断言文本**：engine-quirks 抓到
   `bare_ctor_member_tests.rs:27 raw: "[hdl][warning] HDV004 [module] \n[]\n[]\nnone\n"`，
   即断言左侧**多出一条 warning 行**。**根因**（hdl-c 给出完整链路）：hdl-c 往 `hdl-macros.typort` 加的端口类型诊断兜底臂
   **在 prelude 自身代码上误触发** → 产生 `[hdl][warning] HDV004 [module]`（module 槽位是 `module`、端口名空串）；
   而 **`run_with_prelude` 走 `clone_prelude_state(true)`（带 HDL）**，于是这条 warning 泄进**所有输出断言型测试**。
4. **更深的维护者知识（比「插桩留在树上」精确得多）**：Lead 在 `mod.rs:4365` 把 `CheckIssues`/`CheckIssuesSeen`
   补进 `clone_prelude_state` 的重置清单后，lib 从 **537/69 → 604/2**（67 条泄漏红全消）。真正的因果链是三者叠加：
   **`clone_prelude_state` 不重置 CheckIssues** ＋ **声明检查会求值 def body** ＋ **`report_check_issue` 只读字面量实参**
   （链路位置：`mod.rs:4365`、`cxt.rs:383-386`）。剩下的 2 条是 hdl-b 判据改动的**真实语义后果**
   （`examples_21` 的 HDL038 计数 2→1；`observe` 的 HDL HDL 示例 parity），与泄漏无关。
5. **教训（四条，全部入档）**：
   - **门禁红灯的默认解读应是「谁在飞」，而不是「本轮失败」**；但**归因必须走到「读原生断言文本」**，
     仅凭「失败家族形状 + 写域」会误判（本轮我与 Lead 都被形状误导过一次）。
   - **兼容性知识（下一位维护者必读）**：`run_with_prelude` **带 HDL** ⇒ **任何新增的 prelude 期 warning
     都会让输出断言型测试整片红**。本轮两次同类事故：第 1 轮 prelude 新增 `not_not` 与示例同名 → `redefine`；
     第 2 轮新增诊断 warning → 输出断言全红。
   - **树在飞时不要反复重跑门禁**（一次 3–5 min，结论必然反复），等 owner 明确通知回绿后再做对照。
   - **并发测量陷阱**：peer 占着同一个 `elaboration_zoo_lsp-*.exe` 时 `cargo test --lib` 会 `LNK1104`，
     `exit 101` **既不能证明也不能证伪**断言失败 —— 必须区分「链接错误」与「panic」。
   - **落盘前先验基线可编译**（hdl-b 的「基线守卫」本轮拦住了在不编译树上落盘）：
     共享树上落盘前先跑一次最小构建，否则会把「树本来就编译不过」误记成自己的失败。
   - **门禁对「编译失败 / 0 测试」显式报错是正面价值**：Lead 那次四套件跑在 task-14 patch 应用中的窗口，
     lib 606/0 而 parity/twin/hdl042 全 `NO TESTS EXECUTED`（`E0308 mismatched types` @ `mod.rs:2870/2889`）——
     新门禁**判成失败而不是静默通过**（正是 hdl-a 那条修复的价值）。该次 `fail=3` **不可引用**：
     它测的不是一致快照（同理，我们**没有干净的四套件基线**，等全树定案再跑）。

### 6.1 【缺陷 · 本轮已清】引擎里 7 处无条件调试输出 `[r2probe]`（**reopened→cleaned，实测 count=0**）

**发现时**（本轮早期）`grep r2probe src/` 命中 7 处：
```
elaboration.rs:1020  eprintln!("[r2probe] check n={n}");
elaboration.rs:2822  eprintln!("[r2probe] infer_expr n={n}");
cxt.rs:47            eprintln!("[r2probe] {} n={}", $label, n);        (宏，多处调用)
cxt.rs:230           eprintln!("[r2probe] backtrace at nat_add #5M:\n{}", Backtrace::force_capture());
cxt.rs:247           eprintln!("[r2probe] nat_add depth={d} x={x:?} y={y:?}");
unification.rs:622   eprintln!("[r2probe] solve_multi_trait n={n}");
unification.rs:992   eprintln!("[r2probe] unify n={n}");
```
**实测复算（我，2026-10-08 15:59 窗口）**：`grep -r r2probe src/**/*.rs` → **0 命中**（engine-quirks 已全部清理）。
**保留的流程建议（第 3 轮候选）**：引擎调试输出必须走**运行时门控**（如 `L13_DEBUG`），并在**封版前清零**——
否则任何按行解析 stdout/stderr 的工具（探针包装器合并两流判定）都会吃噪声；`Backtrace::force_capture!` 这类
一旦命中还会淹没日志并拖慢运行。
- 实测影响（发现时）：每次 `typort` / `l13bench` 运行都会向 stderr 打印 `[r2probe] ...`（我在 `tools/probe/run_probe.ps1`、`prelude_doc_cov.py` 的输出里都看到了 `[r2probe] unify n=0` 等行）。
- 风险：探针包装器**合并 stdout+stderr** 后判定，任何未来的「按行解析」都会吃到这些噪声；`cxt.rs:230` 的 `Backtrace::force_capture()` 一旦命中会打印整段回溯。

### 6.2 【缺陷 · 既有】`tools/gate_l13.ps1`：失败清单截断 + 缺最小计数断言 + `ExitCode` 假失败
1. 失败时 `Write-LogLines -Max 12` 只印 12 条 FAILED 且不印总数（§5.3）。
2. 只用退出码判 `fail=N`，**0 tests 也是 exit 0** ⇒ 覆盖为 0 仍报 `fail=0`（§5.4）。
3. `Start-Process -PassThru` + `WaitForExit()` 下 `ExitCode` 可为空 ⇒ `$null -ne 0` 为真 ⇒ **通过的套件被判失败**（§5.5，我独立实测 8/8）。

### 6.3 【第 1 轮遗留】(E) 3 项算术链不收敛 —— **目标形状端到端已修 + 两条残留**（完整证据链见 **§4.1**）
- 一句话状态：**11 行裁决表**（9 条假设证伪 + 窗口 14 孪生 Step T 否决/回滚 + 窗口 15 Step T2 落盘）；根因是**单次 decl elaboration 内 ~415 层 `force_inner ↔ nat_add` 原生深递归**（键仅 117 个、单键 678 万次、热键 prim 返回 `None`）⇒ 缺的是「**stuck 结局的记忆**」；落地后 `r2_zf` pre TIMEOUT → post **3.5s `nf=449` ×2**、矩阵 **16 档 nf 一致**（新转「终止且一致」**9 档**）。
- **两条残留**：① `e07_bigcoef` 两引擎仍失败（l13bench TIMEOUT；typort 侧**栈溢出崩溃**）；② `e18/e19` 终止但 **`NF-DIVERGE 413/222`**（与 memo 无关，源自既有 `nat_mul` 归约形态差异）。
- **我纠正的基线错误**：round-2 曾把「已测四档全挂」写成「全部形状都挂」，并被 owner 报告引用；本轮全量复算更正为 **pre 7 PASS / 12 TIMEOUT**（§4.1 ⑤、§6.6-5）。

### 6.4 【第 1 轮遗留】`streamFifoCC` 读指针双驱动：**已修复 + 本轮升级为仿真背书**（§3.2）
- **真正的根因（hdl-b 本轮给出完整证据链，第 3 轮候选）**：`when` 内只含 `regAssignCd` 时会被**主域与 Cd 域各发射一次**
  ⇒ 双驱动。链路：`hdl-core.typort:662-664 hasRegAssign` **同时接受 `regAssign` 与 `regAssignCd`** →
  `hdl-verilog.typort:1042 collectClockLinesCd` 用它做主域 when 归属。最小修法在 `hdl-verilog.typort`
  （加 `hasMainRegAssign` 镜像 `hasRegAssignCd`，替换主域分支），风险面 `:1063/:1109/:1265/:1298`。
  ⇒ **结论：第 1 轮的 3 处 per-site 修法（含 `_d_popGo` 具名组合线）是「绕过」而非「根治」**；
  `whenBegin` **不需要**新 Cd API，缺的是发射器的域归属判据。
- 仿真背书见 §3.2（修前 286 MISMATCH / 修后 2 passed）。

### 6.5 【本轮 · 裁决】`RefStreamM2s` 参考模型陈旧（F1 旧公式），RTL 正确（§3.4）
证据等级：模型级 + 真仿真交叉印证（56/56 逐条对齐）。属 task-13 条目，**不动 RTL**。

### 6.6 【工具/方法】我自己的**六起**测量/归因事故（全部入档）
1. `run_probe2.ps1` 首版 l13bench 模式假 PASS（§1.1 / §5.1）。
2. F 探针注释里含 `HDL039` 字面量 ⇒ 首轮统计把注释当告警；改用 `warning:.*HDL039` 才是真读数。
3. `g3` 首版把 `Bool` 赋给 `UInt[1]` 输出 ⇒ 报 `cannot convert`，被我误读为「Bool 端口不工作」。
4. **拿「中间构建」的读数去对照「提交态测试断言」** ⇒ 误判出「测试盲区 / 空断言」（§4.2 ③）。正确做法：
   与测试断言对照必须用**干净 HEAD 构建**的二进制；中间构建的读数只能用于「修前/修后同源对照」。
5. **【本轮新增 · 最有传导性的一次】把「已测的四档」写成「全部形状」**（§4.1 ⑤）：我实测了 `e15/e17/e18/e19` 四档全挂，
   就在 §4.1 写成「我测到的**全部形状**都 TIMEOUT，唯一 PASS 是 `e16`」，而**设计矩阵有 19 档、其中 `e04/e08/e10/e11` 本来就预期 PASS**（`e_shape/MANIFEST.txt` 写着）。
   后果**传导给了 owner**：`window14_landing.md` §形状矩阵 与 `window15_t2_marker.md` §5 都引用了「基线：干净 HEAD 上除 `e16` 外全 TIMEOUT」这句话。
   本轮我全量重跑 pre 副本得 **7 PASS / 12 TIMEOUT**，已在 §4.1 ④/⑤ 用逐档表更正。
   **教训**：矩阵型结论**必须逐档列表**，且必须区分「已实测的档」与「设计存在的档」；「未测」绝不能写成「全挂」。
6. **【终稿新增】判定器的 `INCONCLUSIVE` 可能是「崩溃」而不是「无诊断」**：`typort check e07_bigcoef` 在 pre/post 两侧都在 ~60–68s 后
   `thread 'main' has overflowed its stack`（**栈溢出崩溃**），而我的 `run_probe2.ps1` 只看 `note:`/`error:` 行 ⇒ 判成 `INCONCLUSIVE`（看似「跑完了、没诊断」）。
   **教训**：判定器必须同时记录**退出码/崩溃标记**（`overflowed its stack`、`memory allocation of`、`exit=-…`），否则「崩溃」会被读成「干净返回」。
   本轮 (E) 的 `e07` 残留结论即靠**读原文**才发现（§4.1 ④(c)）。

### 6.7 【本轮 · 已知限制】(G1) 窄设计 v6 的两条未覆盖面（→ §10）
1. **拼写错误的类型名仍不可诊断**：`input a = MyTypo` 仍只有 `expected 'def', found identifier` + `name not in scope`
   （无 `HDV004`）——**响亮失败**（好）但**不可定位**（差）。
2. **混合端口表未覆盖**：同一模块端口表里既有合法 `= Bool` 又有 `= Boolean` 时，`Boolean` 那一路仍得不到诊断。
   原因：补一条通用 `$ty` 兜底臂会把**合法的 `= Bool` 端口**误报（hdl-c 实测），故本轮只特化字面 token `Boolean`（5 条臂）。
   证据等级：**owner（hdl-c）实现 + Lead 四条探针复测**；我的独立复算（formA/formB/typoA/typoB + 我的 g1/g2/g3）待 task-10 二进制落盘后补。

### 6.8 【本轮 · 引擎/工具事实六条（hdl-c 挖掘）】证据等级：owner 报告 + Lead 部分复核
> 均为**跨轮维护者知识**，直接影响「怎么加 prelude 检查/怎么测 prelude」。我的独立复算按需随后补。
1. **`report_check_issue` 只读字面量实参**（`cxt.rs:383-386`）：经 **def 形参**传进去的诊断值恒为**空**。
   ⇒ 检查函数若把消息拼在形参里，报出来是空串。
2. **prelude 装载期的声明检查会求值 def body** ⇒ helper def 里的 `report_check_issue` 会污染 **cached `CheckIssues`**
   （而 `clone_prelude_state` 当时**不 reset**）⇒ 泄漏进**每一次** `run_with_prelude`。这就是本轮 67 条红的真机理；
   Lead 已在系统层（`mod.rs`）修复。**下一位维护者加 prelude 期 warning/check 时必须知道这一条。**
3. **转录器里出现空字符串实参 `""` 会让整次宏展开解析失败**（`expected '}', found 'let'`）——**新怪癖**。
4. **class body 的错误被 `declaration failed to elaborate` 吞掉** ⇒ 可定位的唯一信号只能是 `HDV004`。
5. **恢复式解析静默丢弃失败的 module decl** ⇒ `run_with_prelude` 会返回 `Ok("")`；
   ⇒ 测试必须用下游 `println(... .create ...)` 才能观测到「模块没展开」。
6. **`Copy-Item` 保留源 mtime** ⇒ cargo 跳过 lib 重编、`build.ps1` 仍报 OK，于是**二进制里是旧 prelude**
   （症状：新宏臂永不生效）。⇒ 重建流程里应**touch/重建产物**或以 hash 校验，而不是只看 mtime。

### 6.9 【本轮 · 工具现象】`cargo test` 的 `[[bin]]` **不是** `cargo build --bin` 的产物（hdl-a 发现并复测）
实测两个 artifact：**19,938,304 B / sha256 `E69FEBA0…`**（`cargo build --bin typort`）↔ **12,548,096 B / sha256 `5E57845A…`**
（`cargo test` 之后 `target/debug/typort.exe` 变成的那个）。
⇒ **纪律**：任何 `cargo test` / 门禁之后，**不得**把 `target/debug/typort.exe` 直接当 DUT（它可能是 test profile 的产物）；
要么用**冻结副本**，要么先重跑 `cargo build --bin typort`。
这**解释了我 11:47:26 那个 12.5 MB 副本的来源**（当时刚跑过测试）——即我 §4.2 ③ 的「中间构建出处」问题有一个更精确的机理：
**它不只是「中间态」，还可能是「test 产物 ≠ build 产物」**。两者都指向同一条纪律：**对照必须用「build 产物」的冻结副本**。
**本轮的第 3 次实例（终稿前复核）**：`target/debug/typort.exe` 已变成 **20:46:22 / 12,548,608 B / `AAC38623…`**，而权威冻结副本是 **20:41:25 / 19,941,376 B / `57906082…`** ⇒ 两者**同时存在、且都不是对方**。§9 的读数全部取自冻结副本。
**第 4 次实例 + 行为差异的硬证据（窗口 14，最重要的一条）**：owner 实测**同一矩阵**在 `cargo test` 产物里是 **0.3s / 17 PASS**，在 `cargo build` 产物里是 **2.1s / 16 PASS**
（`window14_landing.md` §Step R 读数，Lead 自己也复核过 `l13bench` 的 5,462,016 B test 产物 vs 9,283,072 B build 产物）。
⇒ 这不只是「size/hash 不同」，而是**结论会不同**（PASS 数 17 vs 16）。**本轮收官时 Lead 已用 `cargo build --bin l13bench` 把共享 exe 复原**（`790BB801…`，我的 (E) 复算即用它）。

### 6.10 【本轮 · 工具口径】**`--only basic|fast` 不能隔离引擎**（`nf_parity` 无条件跑两版）
`src/bin/l13bench.rs:251-256`、`461-466`：`nf_parity` **无条件**跑 basic 与 fast 两版并比较范式；`--only` 只过滤**计时循环**。
⇒ **任何 `--only X` 的 PASS 都要求两版都跑完**；因此「`--only fast` 过了」**不能**被解释为「fast 引擎单独没问题」，
也**不能**用来把双引擎分歧归因到某一侧。本轮早期 owner 的「`--only fast` 4.4s PASS」分叉正是在这里被误读（§4.1 ④/⑤）。
⇒ 判读双引擎行为时必须看 `nf=`（一致）或 `NF-DIVERGE basic=… fast=…`（分歧）这一行，而不是 `--only` 的成败。
（我的冻结副本复算全部按此口径：不带 `--only`，读 `nf=`/`NF-DIVERGE` 行。）

### 6.11 【本轮 · 仓库结构】`verilog_compat_tests` 是 **lib 模块**，不是 `tests/` 目标
它定义在 `src/L13_namespace/mod.rs:366`（`#[cfg(test)] mod verilog_compat_tests`）⇒ 只能用 **lib filter** 跑：
`cargo test --lib L13_namespace::verilog_compat_tests`（Lead 实得 **25 passed / 0 failed / 951 filtered out**）。
⇒ 写门禁/清单时不要把它列成 `cargo test --test verilog_compat_tests`（会 0 tests 且 **exit 0** —— 与 §5.4 的「0 tests 洞」叠加就是假绿）。
（同理：`round2_engine_tests` 是**真** `tests/` 目标（7 例），`emit_tests`/`macro_goto_tests`/`parser_error_tests`/`hdl042_engine_tests`/`twin_engine_tests`/`l13_fast_parity` 也都是独立 target。）

### 6.12 【本轮 · 流程条款】**永不**用 PowerShell 文本 cmdlet 编辑 Rust/CJK 源文件（窗口 10 的自伤事故）
事故（来源 `task14_report.md` §15）：为把诊断打印粒度从 1M 降到 100k，owner 用
`(Get-Content -Raw) -replace … | Set-Content -Encoding utf8` 直接改 `src/L13_namespace/mod.rs`。
**PS 5.1 的 `Get-Content` 默认按 ANSI 读 UTF-8** ⇒ **88 处乱码 + BOM + 括号错误**，共享树**短暂不可编译**；1 分钟内用
`git checkout -- mod.rs` + 手工回填 Lead 的 21 行修复恢复（`21 insertions(+), 1 deletion(-)`、mojibake 0、build OK 19:30:55、lib 609/0）。
⇒ **条款**：源码（尤其含中文注释的 `.rs` / `.typort`）**一律**走编辑器工具或 `git diff` + `git apply`；
**禁止** `-replace`/`Set-Content`/`Out-File` 这类文本 cmdlet 做就地改写；脚本产出文件时必须显式 `-Encoding UTF8` 且**先验证再改**。
（这条与 §6.8-6 的 `Copy-Item` mtime 并列，都是「工具细节直接毁掉证据链」的一类。）

---

## 7. 行为变更清单（含证据等级）

| 变更 | 组 | 风险 | 证据等级 |
|---|---|---|---|
| `streamFifoCC` 满/空判据 + 读指针双驱动（第 1 轮修复） | hdl-b | 高 | **真仿真背书**（Verilator 4.024，120 周期；修前 286 MISMATCH / 修后 2 passed，§3.2） |
| `tools/spinalhdl-verify/verify.py` verilator 解析 + 路径修复 | Lead/hdl-a | 中（影响所有行为验证是否真的运行） | 实测：修复前静默跳过全部行为验证；修复后 `vPulseCC`/`vFifoCC` 真跑（§3.2） |
| `tools/gate_l13.ps1` / `tools/probe/*` / `tools/prelude_doc_cov.py` 入库 | hdl-a | 低（只读工具） | 独立复跑：校准 exit 0、必失败 exit 3、必过 exit 0、doc 100%（§5） |
| (F) HDL039 误报 + `srcs` pending 泄漏（已落盘） | hdl-b | 中（改动 `srcs` 语义；影响链识别/HDL037/域传播） | **单变量 A/B（pre 13:56:32 vs w5 冻结副本）**：`hdl_b_hdl039_repro` HDL039 **1→0**、正例 `f1_pos_mid_read` **两侧都报 1**、`examples/21` **两侧都 HDL038=2 且无 037/039**（§4.2）；**新增回归钉** + `lib 609/0`。pending 泄漏本身**只有 owner 插桩证据**（§4.5） |
| (G1) module 宏 `Boolean` 端口诊断（窄设计 v6，已落盘） | hdl-c | 低（新增诊断，不改匹配语义） | **我的独立复算**（w5 冻结副本）：X1 `formA` HDV004×2 + `not in scope`、`formB` HDV004×1、`typoA/typoB` HDV004=0 且仍 `expected 'def'`；我的 `g1` 得到 `[Boolean] x`、`g2` 仍响亮失败、`g3`(`Bool`) 正例不受影响（§4.3）；+1 回归钉，`lib 609/0` |
| **(G2-land) `(e : T)` / annotated-lambda 定向文案（task-18 + task-23 修订；`parser/mod.rs` **+97/−2**，最终落盘）** | owner/Lead | 低（只改解析诊断文本，不改 AST） | **owner 四套件 + Lead 门禁 + 我的独立 A/B 复算（12 自写探针，两个副本）**：新文案 = 「supports **neither** type ascription `(e : T)` **nor** an annotated lambda binder `(x: T) => ...`…」⇒ 一处 ×1（`p1` 真 ascription ∧ 原 `can't unify`/`expected ')'`/`expected newline` **一条不少**；`(y: Nat) => y` 在 def 体 `c5` 与实参位 `c1` **各 ×1**，**task-19 指出的「重复两条」已修**：`c1` 8→7 行）；绕法 `p2` 逐字节同（`note: some 9`）；**7 类反例零命中**（`c2` 声明冒号 / `c3` 方括号 binder / `c4` verilog `w[7:4]` / `c8` 大括号拼接+`w[7:0]` / `c9` `{3 : 4}` / `c7` 类型位 Pi binder / `c6` 无标注 lambda）；既有 10 个诊断夹具逐行 identical（§4.6）；**Lead emit A/B 3/3 逐字节相同**（`57906082…` vs `9844617D…`） |
| **(G2-rfl) `rfl[Nat] 3` 误导文案** | owner/Lead | — | **未落地（正确否决）**：两版尝试均**不触发**；我的读数为 `can't unify` + `expected: (x: ?52502) → ?52503 x`、可用写法 4 种全 PASS ⇒ 失败点在 **`insert_t` 对新鲜 Π 元变量的合一**（head 类型是 `Eq[Nat] ?a ?a`，非 `Val::Pi(_,Impl,..)`）；「按 decl 类型判」会给 `Some 3` 这类**合法自动插隐式**发误导提示 ⇒ 正确否决（§10-④） |
| **(E-参考版) `mod.rs` 零进展(stuck)结局 memo（Step R，**+93/−2**，含 Lead 的 21 行 `CheckIssues`） | engine-quirks | 中（改 force 的 Decl 臂缓存面） | **owner 门禁（`eq_w14`：lib 609/0、parity 15/0、hdl042 2/0）+ Lead 门禁 `lead_w16`（fail=0）+ 我的独立复算**：`r2_zf` pre TIMEOUT → post **3.5s `nf=449` ×2**；`e15` **2.9s `nf=216`**；矩阵 **16 档 nf 一致**、新转「终止且一致」**9 档**（§4.1 ④） |
| **(E-孪生) `bump_spine_iter/force.rs` `PRIM_STUCK` 标记 memo（Step T2，**+80/−1**） | engine-quirks | 中（同上，但只存标记） | **owner 门禁（`eq_w15`）+ Lead 门禁 `lead_w16`（twin 27/0、parity 15/0）+ 我的独立复算**：`TYPORT_STUCK_PROBE=1` 实得 `123/25002/119`（每轮，hits/ins ≈ 203×）、env 关时 stderr **0 字节**；窗口 14 Step T（存句柄）**28 GiB abort 已回滚**，Step T2 无 abort/OOM（§4.1 ① 表 10/11） |
| (E) 3 项算术链不收敛 | engine-quirks | — | **目标形状端到端已修 + 两条残留**（**措辞纪律：不得写成「整项已修」**）：`r2_zf` pre TIMEOUT → post PASS（两引擎 `nf=449` 一致）；矩阵 16 档 nf 一致；**残留 ①`e07_bigcoef` 两引擎仍 TIMEOUT**（typort 入口两版都**栈溢出崩溃**）、**残留 ②`e18/e19` 终止但 `NF-DIVERGE basic=413 fast=222`**（与 memo 无关：两种结构不同的孪生实现给出逐位相同的 `fast=222`；**归因已于第 3 轮更正为「孪生 quote 不 force 卡住应用的未检查实参」，裁决「参考版是期望范式」，见 §4.1 ③ 的更正块与 `docs/prelude-round-3-2026-10-09.md` §2**）。9 条假设证伪 + 窗口 14 否决/回滚 + 窗口 15 落盘见 §4.1 ①；我纠正的基线错误见 §4.1 ⑤ |

---

## 8. 未完成项与理由

1. **(E) 目标形状已修 + 两条残留**（**措辞纪律：不得写成「整项已修」**；完整证据链 §4.1）：
   - **已修（端到端）**：`r2_zf`（`a*100 + x*10 + 5` + 调用）**pre TIMEOUT → post 3.5s `nf=449` ×2**；`e15` **2.9s `nf=216`**；
     矩阵 19 档中 **16 档两版 `nf` 一致**，相对我的 pre 全量基线（**7 PASS / 12 TIMEOUT**）**新转「终止且一致」9 档**、**新转「终止但分歧」2 档**。
     落地 = 参考版 `mod.rs` 零进展(stuck)结局 memo（Step R，+93/−2）+ 孪生 `force.rs` `PRIM_STUCK` 标记 memo（Step T2，+80/−1）。
   - **残留 ①**：`e07_bigcoef`（`a*99999 + x*99998 + 5` + 调用）**两引擎仍一起 TIMEOUT**（l13bench：我复测 90.1s / 90.3s，peakWS 0.42GB ×2）；
     **且 `typort` 入口两版都在 ~60–68s 后 `thread 'main' has overflowed its stack`（栈溢出崩溃）** ⇒ 机理**未定位**（推测卡住链**逐次增长** ⇒ 标记无法收敛，需要链身份/上界策略）。
   - **残留 ②**：`e18`/`e19` 不再 TIMEOUT 但 **`NF-DIVERGE basic=413 fast=222`**；两种结构不同的孪生实现给出**逐位相同的 `fast=222`** ⇒ 与 memo 无关，
     源自两引擎**既有的 `nat_mul` 归约形态差异**；**哪一侧是期望范式尚无裁决** ⇒ 留给第 3 轮（§10-②）。
   - **9 条假设证伪 + 窗口 14 否决/回滚 + 窗口 15 落盘**：见 §4.1 ① 的 11 行表。
   - **我纠正的基线错误**：round-2 曾把「已测四档全挂」写成「全部形状都挂」，导致 owner 引用为「基线除 `e16` 全 TIMEOUT」；本轮全量复算更正为 **pre 7 PASS / 12 TIMEOUT**（§4.1 ⑤、§6.6-5）。
   - **终稿树指纹**（我复核，`git`/`Get-FileHash`）：`HEAD = 645dc3bd`；**0** 个 cargo/rustc 在飞；`git diff --numstat` 见 §9.1；`MT14|mt14|r2probe` 在 `src/**/*.rs` 命中 **0**；lib **609 passed / 0 failed**（Lead 门禁 `lead_w16`）。
2. **(F) 已完成**：单变量 A/B（pre 13:56:32 vs w5 冻结副本，§4.2）+ hdl-b 回归钉 + lib 609/0。
   **遗留**：① 我的 4 个自造夹具（`f2`/`f3`/`f4`）命中不了该误报（已记录，须以 owner 最小复现为锚）；
   ② `f4` 的 11.6s → 82s 需在无并发窗口复测以排除性能回归；③ **(F) 在孪生引擎侧未做同构复算**。
3. **(G1) 已完成**：v6 落盘 + 我的独立复算（X1 四条 + 我的 g1/g2/g3，§4.3）。
   **遗留**：两条覆盖面 —— `MyTypo` 仍不可诊断、混合端口表未覆盖（§6.7）。
4. **`tools/gate_l13.ps1`**：已在在飞树上独立跑过一次并完成取证（§5.3）；**终稿对照跑**由 Lead 权威门禁 `lead_w16` 完成
   （我未再并发跑 cargo）；「0 tests = exit 0」洞与 `ExitCode` 假失败均已实测坐实（§5.4/§5.5）。
5. **零漂移复跑**：268/268 全量结论仍是对 **13:56:32** 副本的（owner 全部落盘后未再全量复跑，收口窗口不做并发 cargo）；
   但我在**终稿**（w12 冻结副本）上补跑了 **10 个既有诊断文本夹具**（`24-verilog-practice`/`21-crossclock`、`hdlc_t10_x1_{formA,formB,typoA,typoB}`、`g1/g2/g3`、`f1`）⇒ **诊断行逐行 identical**（§4.6）；
   另外 (E) 的 19 档矩阵我**两侧全量**跑过（§4.1 ④，这是本轮第一次真正的全量基线）。
6. **PLRU / metaDiv / 大字面量护栏的仿真证据等级**：hdl-a 的 L3 全用例集 **51/51**（新树 w16 与 pre-(E) 逐模块判定流**字节相同、零漂移**、额外非判定行 0，§9），
   但我未逐项把 PLRU/metaDiv 映射到具体用例行（Lead 读数）。
7. **pending 泄漏**：缺**告警文本级**最小复现（§4.5：我的例子与 `hdl_b_fifo_like.typort` 在修前/修后同读数，
   与 owner 声称矛盾；档源 hash 已固定）。
8. **三条工具/仓库口径**（本轮新增）：① `cargo test` 的 `[[bin]]` ≠ `cargo build --bin` 产物（§6.9；窗口 14 实测**同一矩阵 test 产物 0.3s/17 PASS vs build 产物 2.1s/16 PASS**）；
   ② **`--only` 不能隔离引擎**（§6.10，`nf_parity` 无条件跑两版）；③ **`verilog_compat_tests` 是 lib 模块**（§6.11，只能 lib filter，列成 `--test` 会 0 tests 且 exit 0）。
9. **第 1 轮文档更正**：`docs/prelude-round-2026-10b.md` 里「本机无 verilator / 无仿真背书」已改为「仿真可用；FIFO 已有仿真背书」（§3.1）。
10. **(G2-land) 已落盘 + 我复算通过，task-19 提的两条限制都已收口**（§4.6 / §7）：
    ① **文案已覆盖两义且去重** —— 新文案同时提到 ascription 与 annotated lambda binder，`c1` 由 8 行降到 7 行（每处只推一条）；
    ② **`tests/round2_engine_tests.rs` 已进 Lead 清单**：**7 例 / 0 失败**（Lead 亲跑；注意它**不在**门禁那四条原始行内，属「额外套件」）。
    **仍留一条**：annotated-lambda 形态本身**仍不被支持**（`(y: Nat) => y` 两侧都报错）——本轮只改文案，未实现该语法（不在写域内）。
11. **(G2-rfl) `rfl[Nat] 3` 未落地（正确否决）**：两版尝试均**不触发**（证据 `engine_quirks/t15_rfl.typort`；**本次两版 rfl 尝试未留 diff 备份** —— 据实记录）；机理与正确落点见 §10-④。

---

## 9. 门禁 / 覆盖率数字（**终稿** · 权威门禁 `lead_w16`）

**终稿数字来源**：Lead 权威门禁 `tools/gate_l13.ps1 -Label lead_w16`（`fail=0`，**`GATE_EXIT=0`**，total 231.8s）。
源码冻结态 = `HEAD 645dc3bd` + Lead 的 `mod.rs` CheckIssues 修复 + hdl-b (F) + hdl-c (G1) + task-18/23 的 `parser/mod.rs` 诊断 +
**(E)** 参考版 `mod.rs` 零进展 memo（Step R）+ 孪生 `bump_spine_iter/force.rs` `PRIM_STUCK` 标记 memo（Step T2）。
控制台 `target/prelude_scratch/lead_w16_gate_console.txt`，日志 `target/gate_l13_logs/lead_w16-{lib,parity,twin,hdl042}.log`。
（历史冻结态 `lead_w5`/`lead_w12` 的四条计数与下表**完全相同**，出处各自保留备查；**但 §9.1 指纹与下图已不同**。）

| 指标 | 第 2 轮起点（645dc3bd） | **终稿（lead_w16）** | 口径（原始行） |
|---|---|---|---|
| doc 覆盖率 | 1192/1192 = 100% | **1194/1194 = 100%**（`--min-coverage 60 --deny-warnings` → **EXIT=0**） | Lead 亲跑冻结副本 `9844617D…`：`typort doc: 1194 items (1194/1194 documented, 100%), 2 packages`；我独立复跑 `tools/prelude_doc_cov.py` 同口径 100%（§5.2） |
| `cargo test --lib L13_namespace::` | 606 passed / 0 failed | **609 passed / 0 failed / 6 ignored** | `test result: ok. 609 passed; 0 failed; 6 ignored; 0 measured; 361 filtered out`（84.87s） |
| `l13_fast_parity`(skip L13) | 15 passed | **15 passed / 0 failed** | `test result: ok. 15 passed; 0 failed; 0 ignored; 0 measured; 615 filtered out` |
| `twin_engine_tests` | 27 passed | **27 passed / 0 failed** | `test result: ok. 27 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out`（120.93s） |
| `hdl042_engine_tests` | 2 passed | **2 passed / 0 failed** | `test result: ok. 2 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `gate_l13` 汇总 | — | **`gate_l13[lead_w16]: total 231.8s, fail=0`，`GATE_EXIT=0`** | 四套件全绿 |
| **额外集成套件（Lead 亲跑，不在门禁四条行内）** | — | `round2_engine_tests` **7/0**、`emit_tests` **12/0**、`macro_goto_tests` **9/0**、`parser_error_tests` **107/0**；`verilog_compat_tests`（**lib 模块**，lib filter）**25/0**（951 filtered） | ⇒ 新钉文件已进清单（§6.11 说明为何是 lib filter） |
| **emit A/B（Lead 复核，我引用）** | — | **3/3 逐字节相同**：pre-(E) `57906082…` vs 最终 `9844617D…`，覆盖 `21-crossclock:ccFifo`、`24-verilog-practice:vAlu`、`16-counter:counterChain`（len 263–1654） | ⇒ **引擎 force 改动与解析诊断都不改变发射产物** |
| **L3 全用例集**（hdl-a，新树） | — | **51 passed / 0 failed / 51 total**（exit 0、509.2s、MISMATCH=0）；与 pre-(E) `verify_w5_clean.txt` **逐模块判定流字节相同（零漂移）**，**额外非判定行 w5=0 / w16=0** | DUT 指纹与 L3 横幅自证一致（`9844617D…`）⇒ 诊断改动**未**向 L3 输出泄漏新 warning |
| 第 1 轮夹具零漂移 | — | **268/268 项读数一致**（8 个夹具；在 13:56:32 副本上复跑） | `verify2/diff_readings.py`（§2） |
| 仿真（v_dualclock） | 修前 1 passed / 1 failed（286 MISMATCH） | **2 passed / 0 failed** | `tools/spinalhdl-verify/verify.py`（§3.2） |
| `prelude_stdlib_tests` | 9 passed | **9 passed**（我在 `645dc3bd`+回滚树上实测两次 `LASTEXITCODE=0`；含在 lib 609 内） | verifier 集成钉 |
| **(E) 形状矩阵（我的独立复算）** | — | **post：16 档 nf 一致 + e18/e19 NF-DIVERGE + e07 TIMEOUT**；pre：**7 PASS / 12 TIMEOUT** | §4.1 ④（`lead_w16_l13bench.exe` `790BB801…`） |
| **门禁（在飞树，仅取证，非终稿数字）** | 606 passed / 0 failed | ① 三份在飞改动同时存在时 **lib 538/68 红**（我实测，§5.3）；② Lead 补 `mod.rs:4365`（CheckIssues 重置）后 **604 passed / 2 failed**（67 条泄漏红全消）；③ 干净树 **606/0** 由 hdl-b 用新门禁确认 | `tools/gate_l13.ps1`；根因链见 §6.0 |

### 9.1 终稿树指纹（Lead 给出 + **我逐条复核并自己算了 sha256**）

```
HEAD                = 645dc3bd30624703cfb921bece50a54bc56549e8
git diff --numstat（src 侧 7 files = Lead 口径的「7 files」）:
  80   1  src/L13_namespace/bump_spine_iter/force.rs   ← Step T2 PRIM_STUCK 标记 memo
  93   2  src/L13_namespace/mod.rs                     ← Lead 的 21 行 CheckIssues + Step R 零进展 memo
  97   2  src/L13_namespace/parser/mod.rs              ← (G2-land) 诊断（task-18 + task-23 修订）
  86   0  src/L13_namespace/prelude_hdl_b_tests.rs
 135  22  src/L13_namespace/prelude_hdl_c_tests.rs     ← Lead 的 --stat 记法 157 = 135+22
  85  15  src/prelude/hdl/hdl-check-graph.typort       ← Lead 的 --stat 记法 100 = 85+15
  78   0  src/prelude/hdl/hdl-macros.typort
（另有 docs/prelude-round-2026-10b.md 13/5 与 tools/spinalhdl-verify/* 11/4 + 121/14；全树 --stat = 10 files, 799 insertions, 65 deletions）
src 文件 sha256 前缀（我算）:
  src/L13_namespace/bump_spine_iter/force.rs   01CA2CED
  src/L13_namespace/mod.rs                     4BA548F7
  src/L13_namespace/parser/mod.rs              F86105D9
  src/L13_namespace/prelude_hdl_b_tests.rs     52980761
  src/L13_namespace/prelude_hdl_c_tests.rs     04BEBFD4
  src/prelude/hdl/hdl-check-graph.typort       6443838D
  src/prelude/hdl/hdl-macros.typort            54CC2F21
tests/round2_engine_tests.rs = 新增 untracked，sha256 前缀 BC30A1C7（**7 例**，含 HDL 假阳性回归钉；Lead 亲跑 7/0）
插桩残留 MT14|mt14|r2probe（src/**/*.rs）= 0        cargo/rustc 在飞 = 0
TYPORT_STUCK_PROBE = 默认关（`bump_spine_iter/force.rs:248-249` env 判定 + `:433-447` 打印）；env 不设时 stderr = 0 字节（我实测）
冻结副本 target/prelude_scratch/lead_w16_typort.exe   = 22:48:10, 19,999,232 B, sha256 9844617DFA0FBBBB47E6FE9F701F4147A7B70387CFFEA74506F578E147C33152
冻结副本 target/prelude_scratch/lead_w16_l13bench.exe = 23:00:19,  9,283,072 B, sha256 790BB801972A7EBA091B1688B9E4959557F5D7A00642AAD333A0767C573D1EFE
        （与 target/debug/l13bench.exe 字节相同 —— Lead 用 cargo build --bin l13bench 复原过，§6.9）
```

> **口径提示（我复核时发现的一处记法混用）**：Lead 清单里 `prelude_hdl_c_tests.rs 157` 与 `hdl-check-graph.typort 100` 是 `--stat` 的**增+删合计**（我 `--numstat` 实得 135/22 与 85/15），
> 而 `mod.rs 93/2`、`force.rs 80/1`、`parser/mod.rs 97/2` 是 `--numstat` 的**增/删对**。上表已按 numstat 统一列出，避免下一位误读。
> ⚠ **冻结副本是唯一合法 DUT**：`target/debug/typort.exe` 在本轮期间至少出现过 **12,548,608 B / `AAC38623…`**（test 产物）与 **19,999,232 B / `9844617D…`**（build 产物）两种；
> 我全部读数取自冻结副本。§6.9 有窗口 14 的硬证据（同一矩阵 test 产物 0.3s/17 PASS vs build 产物 2.1s/16 PASS）。
> **覆盖面**：`round2_engine_tests`（7 例）与 `verilog_compat_tests`（lib 模块 25 例）**不在**门禁四条原始行内，需单列（Lead 已亲跑，见 §9 表「额外集成套件」）。

> **与 Lead 数字的一致性**：上表逐格与 Lead 给的四条原始 `test result:` 行、doc 输出、emit A/B 3/3、L3 51/51（零漂移）、额外套件计数一致，**无不一致处**；
> 唯一的**记法**差异是上面那条 `--stat` 合计 vs `--numstat` 对（数字本身一致，已在上表统一）。

---

## 10. 第 3 轮候选（本轮发现、本轮不做）

1. **引擎调试输出必须走运行时门控，且封版前清零**（本轮 7 处 `[r2probe]` 无条件 `eprintln!`，含
   `cxt.rs:230` 的 `Backtrace::force_capture!`）——否则任何按行解析 stdout/stderr 的工具都会吃噪声。
2. **`tools/gate_l13.ps1` 三处修复**：加最小计数断言（0 tests = exit 0 洞，§5.4）；FAILED 行打印总数（§5.3）；
   把 `Start-Process` 改成 `-Wait`（或从 `test result:` 行判 fail），消除 `ExitCode` 假失败（§5.5）。
3. **`clone_prelude_state` 的 `CheckIssues` 重置**（§6.0 的根因链）：Lead 已在 `mod.rs:4365` 补；
   建议再加一条回归钉 —— 「新增 prelude 期 warning/check issue 不得泄漏进用户程序」。
4. **参考模型与契约的一致性审计**（task-13）：`RefStreamM2s` 按 F1 契约修正（§3.4），并复核其余 50 个模块的
   参考模型是否停留在旧语义（要求「ref ↔ design doc 章节」对照表）。
5. **①（头号）(E) 残留一：`e07_bigcoef` 的机理**（`a*99999 + x*99998 + 5` + 调用）：**两引擎仍一起失败** ——
   l13bench 侧 TIMEOUT（我的复测 90.1s / 90.3s，peakWS 0.42GB ×2，且 60s 内**无 `[T2]` 轮界输出** ⇒ 该轮从未结束）；
   `typort` 侧两版都在 ~60–68s 后 **`thread 'main' has overflowed its stack`（栈溢出崩溃）** ⇒ **不是「慢」而是爆栈**。
   **第一步（精确）**：先判「键是否逐次变化」——在有 memo 的构建上打印**同一 prim 名**下 `distinct_keys / max_repeat` 的时间序列，
   区分「键稳定但每轮结局翻转」与「**卡住链逐次增长 ⇒ 键不稳定**」（后者需要链身份/`NAT_CHAIN_LIMIT` 语义对齐，而不是任何结局缓存）。
6. **② (E) 残留二：`e18`/`e19` 的 `NF-DIVERGE` —— ✅ 第 3 轮已完成裁决（2026-10-09）**：两版都终止（4.2s），但两引擎范式不同
   （basic：613 字符的 `{a + {a + …}}` 展开；fast：27 字符 `a => x => {a * 100} + x + 5`）。
   **裁决结论（第 3 轮独立复算，`docs/prelude-round-3-2026-10-09.md` §2）**：**参考版（basic）是期望范式；孪生（fast）偏离** ——
   真实机理是**孪生 `quote` 不 force「卡住 prim 应用里 prim 从未检查的那个实参」**（`nat_add` 只看第 2 实参；第 2 实参是裸 rigid 变量时 prim 直接卡住，第 1 实参永不 force）⇒ 孪生范式里留下 redex；
   `(a + 0) + x` / `(a * 0) + x` / `(a * 1) + x` 等**与 mul 无关**的形状同样分歧，且同一输入的用户可见 `expected:` 报错文本两版不同。
   ⇒ **第 2 轮把该分歧归因为「`nat_mul` 归约形态差异」已被证伪**；Lead 已采纳**方案 A（修孪生 quote = task-29）**，判据（含性能护栏与 parity 回归钉 twin 27→28）见第 3 轮文档 §2.8。
7. **③ (E) 孪生 `PRIM_STUCK` 的键 / 保活「长期稳定性」**：Step T2 已证明**轮内**键稳定（`hits/inserts ≈ 203×`、`tbl` 收敛 119、无 OOM，§4.1 ① 表 11），
   但**跨轮**只依赖「轮界 `force_memo_clear()` + `spine.stack.reclaim(...)` 成对」这一纪律；窗口 14 的 28 GiB abort **确切机理仍未钉死**（§4.1 ① 表 10）。
   ⇒ 下一轮应给「标记表」加**轮界不变量断言**（或 env 门控的跨轮命中计数），确认「跨轮永不复用」在**所有** `clear_round` 站点（`entry.rs` 907/908…1800）都成立。
8. **(F) HDL039 误报**：**已由我完成单变量 A/B**（§4.2：HDL039 1→0、正例保持、example 21 同步变绿）。
   遗留两条：(a) 补一条 **CLI 文本级回归钉**（`typort check examples/hdl/21-crossclock.typort` 的 warning 集合断言）
   作为**可选加固** —— 注意这**不是**「空断言」问题（出处核查已推翻该假设，§4.2 ③）；
   (b) **pending 泄漏需要一个「告警文本可判别」的最小复现**：我的自写例子与 `hdl_b_fifo_like.typort`
   在修前/修后**同读数**，与 owner「带 memWrite → HDL037」的声称矛盾（档源 hash 见 §4.5），需 hdl-b 给两版文件名+hash。
9. **`whenBegin` 无 Cd 变体**：结论是**不需要新 API** —— 根因在发射器 `hasRegAssign`（§6.4），
   修法在 `hdl-verilog.typort` 的域归属判据（第 3 轮候选）。
10. **PLRU / metaDiv / 大字面量护栏的仿真证据等级**：hdl-a 的 L3 全用例集已 **51/51**（§9），
    但**逐项**把 PLRU/metaDiv 映射到具体用例行仍未做（§8 第 6 条）⇒ 证据等级仍为「全集合绿」而非「逐项背书」。
11. **(G1) 窄设计留下的两条覆盖面**（§6.7）：① 让拼写错误的类型名（`MyTypo`）也能被诊断（目前只有 `expected 'def'`）；
    ② 覆盖**混合端口表**（同表既有 `= Bool` 又有 `= Boolean`）——需要一种**不误报合法 `Bool` 端口**的通用臂或解析器侧诊断。
12. **四条工具/构建/仓库纪律**：① 转录器**空串实参 `""`** 会让整次宏展开解析失败 → 应在转录器侧或 lint 侧给出可诊断错误（§6.8-3）；
    ② **`Copy-Item` 保留 mtime** 会让 cargo 跳过重编、`build.ps1` 假 OK → 应以 hash/内容校验判断「是否需要重编」（§6.8-6）；
    ③ **`cargo test` 的 `[[bin]]` ≠ `cargo build --bin` 产物**，且**结论会不同**（窗口 14：0.3s/17 PASS vs 2.1s/16 PASS）⇒ 交付物附 **hash + 产生命令**（§6.9）；
    ④ **`--only` 不能隔离引擎**（§6.10）与 **`verilog_compat_tests` 是 lib 模块**（§6.11）——写门禁/清单时按此口径。
13. **④ (G2) `rfl[Nat] 3` 误导文案：正确落点在 `insert_t` 内部，不在 apply 回退之前**（本轮两版尝试均**不触发** ⇒ 正确否决；证据 `engine_quirks/t15_rfl.typort`、`t15_rfl_variants.typort`；**据实记录：这两版尝试未留 diff 备份**，`w12_ascription_hint*.diff` 是改动一的备份，不可当作本项证据）：
    实测现象（冻结副本）：`def e_bad: Eq[Nat] 3 3 = rfl[Nat] 3` → `error: can't unify` + `expected: (x: ?52502) → ?52503 x` / `find: Eq[Nat](?52501, ?52501)`；
    可用写法 `rfl` / `rfl[Nat] [3]` / `rfl [Nat] [3]` / `rfl[Nat]` 全 PASS。
    **机理**：失败发生在 **`insert_t` 对新鲜 Π 元变量的合一**（隐式 `a` 被插成 Pi ⇒ 显式 `3` 走 **apply 回退**），此时 head 类型是 `Eq[Nat] ?a ?a` 而**不是** `Val::Pi(_, Icit::Impl, ..)` ⇒
    在 apply 回退前按「head 是否是隐式 Π」判据**永远不命中**（这解释了「两版尝试均不触发」）。正确的落点在 **`insert_t` 内部**（知道「这里本该自动插一个隐式实参、但用户给了显式」的那一点）。
    **是否值得做**：需要先验证不误报 —— 「按 decl 类型判」会给 `Some 3`（合法自动插隐式）发**误导提示** ⇒ **该版本正确否决**；任何落地方案必须先过「合法自动插隐式不得报警」的反例集。
14. **⑥ (G2-land) 收尾两条**（§4.6）：
    ① **`annotated-lambda` 语法本身仍不支持**（`(y: Nat) => y` 两侧都报错）—— 本轮 task-23 只把文案改成覆盖两义 + 去重（已收口），**未实现该语法**（需 parser + 双引擎，属新特性）。
    ② **`tests/round2_engine_tests.rs`（7 例）仍不在 `gate_l13.ps1` 的四条原始行内** ⇒ 要么并入 lib target，要么给门禁加第五条（否则「7 例绿」永远靠人记得单跑）。
15. **⑤ 第 1 轮遗留项照旧**：`verify/hang/*` 的最小复现集保留（本轮 (E) 已把其中 `r2_zf` 一族修好；`e07` 大系数仍失败，见本条 ①）；
    §6.5 的 `RefStreamM2s` 参考模型陈旧（task-13）、§6.4 的 `whenBegin`/`hasRegAssign` 域归属、§4.5 的 pending 泄漏最小复现仍待第 3 轮。
