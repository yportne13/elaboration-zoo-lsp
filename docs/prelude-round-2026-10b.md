# prelude 完善轮（2026-10b）

> 由 verifier（task-7）独立撰写。所有数字都是**实测**，标注口径、二进制 mtime 与来源；
> 未实测的一律标 `【owner 报告，未独立复核】`；§3 的收官数字已按 Lead 在冻结树（12:01:39 构建）上的实测填入。

- 仓库 HEAD：`df06924c`（本轮改动都在工作树，未提交）
- 读数工具：`target/prelude_scratch/verify/bin/typort_cur.exe`（10:58:44 快照）、
  `typort_cur2.exe`（11:29:28 快照）、`l13bench_cur.exe`（10:56:47 快照）
- 改动规模：`git diff --stat` → **31 files changed, 3362 insertions(+), 346 deletions(-)**

---

## 1. 验证方法（可复现）

### 1.1 独立夹具（不复用 owner 测试代码）

全部在 `target/prelude_scratch/verify/`，与各 owner 的探针目录不重叠：

| 夹具 | 覆盖 | 读数 |
|---|---|---|
| `v1_direction.typort` | Vec 方向家族（append/snoc/reverse/map2/zip/at/head/tail/`::`/fold 家族） | 25 项 |
| `v2a_basic.typort` | List 方向 + 边界（空表/单元素/重复/n 越界/take_while 全真全假/unzip/concat/flat_map/insert/sort） | 44 项 |
| `v3_nat.typort` | Nat 引理**归一化结果**（add/mul 链 + pow + sub/div/rem/max/min + 比较/运算符/Clone/Default） | 74 项 |
| `v4_show.typort` | Show **逐字符**（空表/单元素/负 Int/0/String 原样/str_repeat/str_join） | 44 项 |
| `v5_cross.typort` | 跨文件集成（vec→list→show、option→either→result 转换格、nonempty、product/tuple/Dec） | 54 项 |
| `w_core.typort`/`w_core2.typort`/`w_core3.typort` | prelude-core 本轮新增项抽样 | 17 / 14 / 2 项 |
| `w_data.typort` | prelude-data 本轮新增项抽样 | 51 项 |
| `hang/*` | 非终止性最小复现与形状矩阵 | §6.1 |

**探针技巧**：用真左折 `List.foldl 0 (a => x => a * 10 + x)` 把 `List[Nat]` 折成十进制数，
在无 `show` 口径下逐位暴露**元素顺序**（f 非交换），从而钉死递归/索引方向。

### 1.2 判定器（必须先用必失败样本校准）

- `verify/parse_notes.py`：`note:`/`error:` + 源码片段 → `EXPR = VALUE` 表（兼容 utf-8/utf-16）。
- `verify/bounded_run.ps1`：外部硬超时 + 峰值内存护栏，判定
  `TIMEOUT` / `MEM-LIMIT` / `ZERO-OUTPUT(exe 被 cargo 上浮锁住)` / `ERRORS=n` / `OK(notes=n)` /
  `NO-NOTES` / `INCONCLUSIVE`。
- **必失败对照样本**：`verify/hang/mfail_calib.typort`（未定义名）→ 实测 `DECL-FAIL`
  （twin/basic 都在第 179/179 个 decl 报 `error name not in scope`）。

### 1.3 读数纪律

`target/debug/*.exe` 随时被 rebuild 替换。实测同一条 `typort check`：无并发构建 ~5s、
owner 跑 cargo/rustc 时 ~37s；cargo 上浮复制 exe 时 `Start-Process` 会 **0 字节输出**。
因此关键结论都用冻结副本，且每次读数记录 mtime 与 `git rev-parse HEAD`。

---

## 2. 按文件的改动清单

### core（prelude-core）
- `op.typort`：`compose3`、`Product.bimap`（+5 行）。
- `eq.typort`：`trans3`、`cong3`、`subst2`（+25 行）。
- `bool.typort`（+94 行）：证明层引理 `not_not_neg`/`eq_self_true`/`nat_eq_refl`/`nat_lte_refl`/
  `nat_lt_irrefl`/`nat_lte_succ`/`nat_lt_succ`；`bool_lt`/`bool_lte`/`bool_gt`/`bool_gte` 与
  `impl Compare[Boolean, Boolean] for Boolean`（本轮**唯一新增实例头**）。
  **`not_not` 有意不加**（`bool.typort:201-202`：与 `examples/theorem_proving.typort` 重名会让该
  example 报 `redefine`；prelude 是扁平命名空间）。
- `nat.typort`（+98 行）：`add_one_right/left`、`mul_one_right/left`、`mul_by`、
  `pow_zero/succ/one/add`、`max_self`、`min_self`、`nat_factorial`、`factorial_zero/succ`。

### data + show（prelude-data）
- `list.typort`：`snoc`、`nth`、`find_index`、`intersperse`、`nub`、`partition`、
  `List[Product].keys`/`values`；`insert` 注释修正（相等时 x 在已有相等元素**之前**）。
- `vec.typort`：`Vec.foldl` **改为真左折**（行为变更）、`vec_replicate`、`vec_last_option`。
- `option.typort`：`unwrap_or_else`、`map_or_else`。
- `result.typort`：`Option.ok_or`（加载序所迫住本文件）、`Result.unwrap_or_else`、`map_or_else`。
- `either.typort`：`right_to_option`、`either_right_to_option`。
- `order.typort`：`ordering_min`、`ordering_max`、`Ordering.pick`。
- `decidable.typort`：`get_or_else`、`dec_and`、`dec_refute_fst/snd`。
- `nonempty.typort`：`nonempty_from_list`。
- `show.typort`（+116 行）：新增实例头（含 `Option[List[Nat]]`、`List[List[Nat]]`、
  `Product[Boolean,Nat]`、`Tuple2[Nat,Boolean]` 等）——**逐字符实测见 §4**。

### HDL（hdl-a / hdl-b / hdl-c）
- hdl-a：hdl-core/check/check-graph/types/ops 的 `///` 文档化 + 一致性修补；
  HDL034 行为对照（`when c && !c` → 仅 HDL032；`when (sel==0)&&(sel==1)` → HDL032+HDL034）。
- hdl-b：`streamFifoCC` 满/空判据修复（指针加 wrap 位 + RAM 低位寻址）、树形真 PLRU、
  `hdl-clock/bus/signals/enum/misc` 文档化。
- hdl-c：`hdl-utils/stream/fsm/macros/verilog-compat/verilog` 文档化 + `metaDiv` floor 等。
- **行为类改动的风险与证据等级见 §7。**

### engine-quirks
- 大字面量（`>100000`）走「n 层 succ 链」病态路径（1e6：144s + 栈溢出）→ 新增解析期护栏，
  变成可诊断错误；受支持写法 = `nat_mul`/`nat_add` 分解式。
- `(x: T) => e` 被解析成 Pi 类型（非 lambda 语法）→ 书面定位报告（下一轮候选）。

---

## 3. 实测数字

**收官数字来源**：Lead 在冻结树上实测（`HEAD df06924c`，二进制 `target/debug/{typort,l13bench}.exe`
mtime **2026-10-08 12:01:39**，脚本 `target/prelude_scratch/final_acceptance.ps1`，
日志 `target/prelude_scratch/final_acceptance.log`）。**本表数字与 Lead 门禁一致**；
verifier 的 `prelude_stdlib_tests` 计数为独立实测（见末行）。

| 指标 | 基线（HEAD，本轮起点） | 本轮（Lead 冻结树） | 口径 |
|---|---|---|---|
| doc 覆盖率（全 prelude） | 139/1131 = **12.3%** | **1192/1192 = 100%**（`typort doc --min-coverage 60 --deny-warnings` → exit 0，warnings=0） | `typort doc` 顶层条目；core+data 156/156、hdl 1001/1001、show 35/35 ⇒ **+87.7 个百分点** |
| doc 覆盖率（`doc_cov.py` 逐 item） | 138/1131 = **12.2%** | 与上一行同源（100%） | 只统计 def/struct/enum/trait 顶层（**impl 不计数**、`macro_rules` 不是条目）；基线差 1 = `doc_measure.typort` 自身那个已文档化 decl。两个口径都写，避免混用 |
| `cargo test --lib L13_namespace::` | 571 passed / 0 failed（203.7s 全套） | **606 passed / 0 failed / 6 ignored**（66.96s） | Lead 收官门禁（PowerShell 镜像 `gate.ps1`，总 176.6s，fail=0）⇒ **零回归，测试数 +35** |
| `l13_fast_parity`(skip L13) | 15 passed | **15 passed / 0 failed**（612 filtered，0.03s） | 同上 |
| `twin_engine_tests` | 27 passed | **27 passed / 0 failed**（90.70s） | 同上 |
| `hdl042_engine_tests` | 2 passed | **2 passed / 0 failed**（14.47s） | 同上 |
| `prelude_stdlib_tests` | 5 passed | **9 passed / 0 failed**（verifier 独立实测：19.95s，`LASTEXITCODE=0`，连测两次一致；最新树 `typort.exe` 11:58:05） | verifier 集成钉（既有 5 + 新增 4 个跨文件组合面用例） |
| prelude bench 冒烟 | — | `l13bench --workload prelude-core / prelude-core-show / prelude-hdl`（`--rounds 1`）三档**逐文件解析成功**（op 37 / eq 15 / nat 45 / calc 0 / bool 34 / option 7 / result 6 / order 6 / void 2 / decidable 5 / vec 8 / either 10 / list 25 …），无 `PARSE-FAILED` | Lead 收官冒烟 |
| 树指纹 | — | `43 files changed, 4079 insertions(+), 414 deletions(-)`；新增入库文件 6 个（5 个 `prelude_*_tests.rs` + `tests/prelude_engine_quirks.rs`）+ 本文件 | `git diff --stat` |

> 口径说明：本文件 §4 的抽样读数由 verifier 用**冻结副本**（`verify/bin/typort_cur*.exe`）取得，
> 与 Lead 收官二进制（12:01:39）不是同一构建；两处结论一致（§4.4），但严格同源性以 Lead 为准。

---

## 4. 抽样复算（实测；每条都有可复现命令）

复现命令统一为：
`python -X utf8 target/prelude_scratch/verify/parse_notes.py target/prelude_scratch/verify/<夹具>.after.txt`
（原始输出 = `<夹具>.after.txt`；生成命令 = 冻结副本 `typort_cur2.exe check <夹具>.typort --max-infer-ms 20000`）

### 4.1 prelude-data（51/51 与声称一致）

| # | 条目 | 声称 | 实测 | 判定 |
|---|---|---|---|---|
| 1 | `Vec.foldl` 改真左折 | 左折 | `v3.foldl 0 (a=>x=>a*10+x) = 123` | ✅ |
| 2 | `Vec.fold`（未改） | 右折 | `321` | ✅ |
| 3 | `Vec.reduce`（未改） | 如实文档化 | `132` | ✅ |
| 4 | `List.snoc` 方向 | 追加到尾部 | `[1,2].snoc 3 → [1, 2, 3]`；`[].snoc 9 → [9]` | ✅ |
| 5 | `List.nth` | 0-based，越界 None | `nth 0/1/9 → some 1 / some 2 / none` | ✅ |
| 6 | `List.find_index` | 首个满足者下标 | `some 2` / `none` | ✅ |
| 7 | `List.intersperse` | 相邻间插入，长度 0/1 不变 | `[1, 9, 2, 9, 3]` / `[]` / `[1]` | ✅ |
| 8 | `List.nub` | **保留末次**出现、保序 | `[3,1,2,1] → [3, 2, 1]`；`[1,1,1] → [1]`；`[] → []` | ✅ |
| 9 | `List.partition` | fst=满足，snd=不满足，保序 | `[2, 4]` / `[1, 3]` | ✅ |
| 10 | `List[Product].keys`/`values` | 字段顺序 | `[1, 2]` / `[10, 20]` | ✅ |
| 11 | `Option.ok_or` | Some→ok，None→err | `ok 5` / `err false` | ✅ |
| 12 | `Option.unwrap_or_else` | 惰性默认 | `5` / `9` | ✅ |
| 13 | `Option.map_or_else` | 惰性 map | `6` / `9` | ✅ |
| 14 | `Result.unwrap_or_else` | 错误恢复 | `7` / `9` | ✅ |
| 15 | `Result.map_or_else` | 惰性 map | `8` / `9` | ✅ |
| 16 | `Either.right_to_option` | right→Some | `some true` / `none` | ✅ |
| 17 | `either_right_to_option`（自由函数） | 同方法 | `some true` | ✅ |
| 18 | `Ordering.pick` | 三值选择 | `10 / 20 / 30` | ✅ |
| 19 | `ordering_min`/`ordering_max` | 按 p 取极值 | `3 / 5`；相等时 `4` | ✅ |
| 20 | `Dec.get_or_else` | 取值或默认 | `3` | ✅ |
| 21 | `dec_and` | 两 Dec 合取 | `7`（`(yes 3, yes 4)` 的 fst+snd） | ✅ |
| 22 | `vec_replicate` | n 个 x 的向量 | `[7, 7, 7]`；n=0 长度 `0` | ✅ |
| 23 | `vec_last_option` | 末元素 | `some 3` / `none` | ✅ |
| 24 | `nonempty_from_list` | 空表→None | `3` / `0`（None 分支） | ✅ |
| 25-28 | Show：`Option[List[Nat]]` / `List[List[Nat]]` / `Product[Boolean,Nat]` / `Tuple2[Nat,Boolean]` | 新增实例 | `some [1, 2, 3]` / `[[1, 2, 3], [1]]` / `(true, 3)` / `(3, true)` | ✅ |

（其余 23 项为同一夹具的边界/重复组合，原始输出见 `w_data.after.txt`：readings=51 errors=0。）

### 4.2 prelude-core（14/14 + 2）

| # | 条目 | 实测（`match lem { case refl(a) => a }`） | 判定 |
|---|---|---|---|
| 29 | `add_one_right 5` | `6` | ✅ |
| 30 | `add_one_left 5` | `6` | ✅ |
| 31 | `mul_one_right 5` / `mul_one_left 5` | `5` / `5` | ✅ |
| 32 | `pow_zero 7` / `pow_one 7` | `1` / `7` | ✅ |
| 33 | `pow_succ 2 3` / `pow_add 2 3 4` | `16` / `128` | ✅ |
| 34 | `nat_factorial 5` / `factorial_succ 3` / `factorial_zero` | `120` / `24` / `1` | ✅ |
| 35 | `max_self 7` / `min_self 7` | `7` / `7` | ✅ |
| 36 | `not_not_neg false` / `nat_eq_refl 3` / `nat_lt_irrefl 4` | `false` / `true` / `false` | ✅ |
| 37 | `Compare[Boolean,Boolean]`：`false < true` / `true >= true` | `true` / `true` | ✅ |
| 38 | `trans3`（`e33 : Eq[Nat] 3 3 = rfl`） | `3` | ✅ |
| 39 | `cong3`（具名 `f3(a,b,c)=a+b+c`） | `9` | ✅ |
| — | `subst2` | 【未独立确认：需要显式 `P`，本轮未构造出可钉的具体用例】 | ⚠ |
| — | 使用限制：`rfl[Nat] 3` 形式 | `can't unify`；改 `def e: Eq[Nat] 3 3 = rfl` 即通过 | 记录 |

### 4.3 基线家族（方向/边界/Show，当前树复测）

- `v1_direction`（25 项）与 `v2a_basic`（44 项）：与 HEAD 基线读数**逐项一致**
  （append 双向 712/127、snoc 1239、reverse 321、map2 112233、zip 123/123、at 越界 99、
  take/drop/split_at 越界、range 0123、insert/sort/unzip/concat/flat_map …）。
- `v4_show`（44 项）：逐字符与 HEAD 一致（`[] / [1] / [1, 2, 3] / [1, -2] / [a, b]`、
  `some 0 / none / some -2 / some hi`、`(1, 2) / (true, false)`、`left 1 / right true`、
  `ok 7 / err false`、`-1/-5/-6`、`ababab`、`unit`）。
- `v5_cross`（54 项）：跨文件集成全部符合；3 条为探针自身问题（见 §6.4）。

### 4.4 复核结论

- **声称可用 ⇔ 实际可用**：prelude-data 抽样 51/51、prelude-core 抽样 16/17（1 项未独立确认）。
- **文档描述 ⇔ 实际行为**：见 §5；`Vec.foldl` 的旧文档（"Left fold" 但实现是右折）本轮已按行为改写
  并改实现为真左折；`list.typort` 的 insert 注释已修正为「相等时 x 在已有相等元素之前」。

---

## 5. HDL 文档抽查（≥30 条 `///` 对码）

判定深度：**深** = 对码到函数体/调用方/实测行为；**签** = 对码到签名与类型。

| # | 位置 | 文档声明 | 对码结果 | 深度 |
|---|---|---|---|---|
| 1 | hdl-core:16 `Le` | `le_refl` 证 `n<=n`；`le_step` 在**右端**加一 | 构造器 `le_step(h: Le n m) -> Le (n, succ m)` 一致；只有 `le_step` 带递归参数 | 深 |
| 2 | hdl-core:25 `Fin` | `Fin (succ n)` 是 `0..n`；`fzero`=0；`fsucc(i)`=`i+1` | 两个构造器签名一致；对值递归而非对界递归 | 深 |
| 3 | hdl-core:33 `sub` | `fzero` 返回 x，每个 `fsucc` 从 x 剥一层；双参数同步递归；`zero` 分支不可达 | 函数体逐 arm 一致 | 深 |
| 4 | hdl-core:45 `Exists` | Sigma：`witness` + `proof : P witness`，字段显式 | 结构体字段与类型族一致 | 深 |
| 5 | hdl-core:53 `div2Up` | `ceil(x/2)`；`zero→0`、`succ zero→1`；递归剥**两个** succ；调用方含 hdl-utils 的 `countOnesExpr` 与多数阈值 | 函数体一致；grep 到 `hdl-utils:261`（countOnesExpr）与 `:827`（majority 阈值）两个调用点 | 深 |
| 6 | hdl-core:63 `log2Up` | `ceil(log2 x)`，0/1 都返回 0；经 `div2Up (tail+2)` 减半；消费者含 hdl-utils 计数宽度、hdl-stream FIFO 指针、hdl-misc-io | 函数体一致；grep 到 hdl-utils（countOne/counter 族）、`hdl-crossclock:305`、hdl-misc-io 调用点 | 深 |
| 7 | hdl-core:75 `maxNat` | 双操作数同步递归，跑 `min(a,b)` 步；hdl-check-graph 用它归一化 part-select 边界 | 函数体一致；`hdl-check-graph:292 rPart(maxNat(hv,lv), minNat(hv,lv))` | 深 |
| 8 | hdl-core:87 `minNat` | 「**唯一**调用方是 hdl-check-graph 的 part-select 归一化」 | grep 全 prelude：除自身递归外仅 `hdl-check-graph:292` ⇒ 「唯一」成立 | 深 |
| 9 | hdl-core:100 `ClockEdge` | hdl-verilog 在 `clockEdgeStr` 与每个 `always @(...)` 头渲染 posedge/negedge | 签名一致；`clockEdgeStr` 存在且被 emit 路径使用 | 签 |
| 10 | hdl-core:108 `ResetPolarity` | codegen 用两次：`resetEdgeStr`（异步敏感表）与 `resetCond` | 签名一致 | 签 |
| 11 | hdl-core:116 `ClockDomainConfig` | `Async` 把复位沿并入敏感表，`Sync` 不并入 | 签名一致 | 签 |
| 12 | hdl-core:125 `AssertSeverity` | 渲染进 `TYPORT_ASSERT_<SEV>` 标记行 | 签名一致 | 签 |
| 13 | hdl-core:135 `ClockDomain` | 名字 + 类型 + 沿 + 复位极性；烘进 `ModuleDef.cd` 与 per-register `create*Cd` | 字段一致 | 签 |
| 14 | hdl-core:147 `defaultClockDomain` | 回退域 clk/reset + Async + RisingEdge + ActiveHigh | 值构造一致 | 深 |
| 15 | hdl-core:284 `isDeclaredSignal` | 明确列出**不**算声明信号：`instance`/`instanceWithPorts`（无 arm → false）、`subSignal`、运算符/mux/bitsel/partsel/memRead 链 | 函数体 26 个 arm 无 instance 分支、`_ => false` ⇒ **hdl-a 修正后的文本与实现一致**（旧注释在 HEAD 上本来就是错的） | 深 |
| 16 | hdl-core:339 `ModuleTree` | tail **不**存外层模块；宏每 arm push 单例树丢弃旧树，父树靠 `_prev` 恢复；多 def 树只在手工构造时存在（引 `examples/hdl/09-hierarchy`） | 与宏实现一致（hdl-a 修正）；子声明 `insert` 用 `succ(this.num)` 未独立复核 | 深 |
| 17 | hdl-core:443 `initWhenStack` | **DEAD CODE**：src/、examples/、tests/ 都无调用方 | grep：仅自身定义处出现 ⇒ 成立 | 深 |
| 18 | hdl-core:450 `whenBegin` | push `whenActive(cond, literal(1))`；`literal(1)` 是 `andCond`/`negatePrev` 会消掉的单位元 | 函数体一致 | 深 |
| 19 | hdl-core:459 `whenEnd` | 弹出最内层；空栈不动；`dummy` 参数只为在生成的 let 链里排序 | 函数体一致（`let d = dummy;` 后 change_mutable） | 深 |
| 20 | hdl-core:470 `whenElseBegin` | 空栈 push 新层；`whenActive` → `negatePrev(prev,notPrev)`；`whenOtherwise` 之上重启 `literal(1)` | 三个 arm 逐条一致 | 深 |
| 21 | hdl-core:486 `whenOtherwiseBegin` | 空栈 push `whenOtherwise(literal(1))`；`whenActive` → 取反全部前支；已是 `whenOtherwise` 则不动 | 三个 arm 逐条一致 | 深 |
| 22 | hdl-core:696 `hasInitRegs` | **DEAD CODE**；且**遗漏** `createSIntRegWidthInitCd`（`collectInitLines` 有处理） | 函数体 5 个 arm，确无 `createSIntRegWidthInitCd`；grep 无外部调用方 ⇒ 成立 | 深 |
| 23 | hdl-core:713 `verilogLiteral` | 只支持 `literal(Nat)`，其余默认 `"0"`；直接用 `nat_to_dec` | 函数体一致 | 深 |
| 24 | hdl-core:721 `collectInitLines` | 六个 `*Init` 变体（含 `createSIntRegWidthInitCd`）；DEAD CODE，被 `collectInitLinesCd` 取代 | 函数体恰好 6 个 arm；grep 无外部调用方 ⇒ 成立 | 深 |
| 25 | hdl-signals:12 `autoUInt` | 名字取 `loopName(bn.name)`；节点是 `createWidth`；纯线网 | 函数体一致 | 深 |
| 26 | hdl-signals:17 `autoBits` | 同上（`createWidth`） | 函数体一致 | 深 |
| 27 | hdl-signals:22 `autoSInt` | 节点是 `createSIntWidth` | 函数体一致 | 深 |
| 28 | hdl-signals:27 `autoBool` | 1 bit；节点是 `create` | 函数体一致（`newBool` 路径） | 深 |
| 29 | hdl-signals:32 `autoUIntInput` | 节点 `createInWidth`；端口表加宽度 | 函数体一致 | 深 |
| 30 | hdl-signals:37 `autoBitsInput` | 同上 | 函数体一致 | 深 |
| 31 | hdl-check-graph:1375/1393 `HDL034` | 只做 eq 形态；报文 `driver condition is always false` | 实现只查 eq 项、报文完全一致；实测 `when c && !c` 仅 HDL032 | 深 |
| 32 | hdl-check-graph:1506-1548 `HDL041` | 常量位选/片选越界；part-select **两端都查** | 实现两个函数分别查 idx 与 hi/lo | 深 |
| 33 | hdl-check-graph:2199-2348 `HDL042` | ground 轮记录 (时钟域, 端口 ground 键集)；签名不同才报；首个注册者胜 | 实现与文档一致（port-only 键、order-insensitive、identical 静默） | 深 |
| 34 | hdl-core:258 `isRegExpr` | 寄存器信号判定（含 out-reg 端口） | 签名/arm 一致 | 签 |

**抽查结论**：34 条中 **0 条**与实现/签名不符；2 条（`ModuleTree`、`isDeclaredSignal`）是 hdl-a
本轮修正的**假文档**（`@auto` 继承旧错误注释所致），修正后已对码通过；`subst2` 未独立确认（§4.2）。
`hdl-a` 的 37 个 `@auto` 中 2 条假文档已修 ⇒ 维护者注意：**`@auto` 必须逐条复核语义**。

---

## 6. 已知缺陷与引擎限制

### 6.1 【严重 · 非终止】3 项算术链 + 变量 ⇒ inference 不收敛

```typort
def z_f(a: Nat, x: Nat): Nat = a * 100 + x * 10 + 5
def z_probe: Nat = z_f 1 2
```

- 复现：`& .\target\prelude_scratch\run_probe.ps1 -File target/prelude_scratch/verify/hang/z1_named_vars_3t.typort -Mode core -TimeoutSec 25` → `TIMEOUT`。
- 形状矩阵（全 `--with-prelude core`）：

| 体 | 结果 |
|---|---|
| `a + x + x` | PASS 3.1s |
| `a * x + x` | PASS 2.9s |
| `a * 100 + x * 10` | PASS 2.9s |
| `a * 100 + x * 10 + 5` / `+ x` / `+ x * 1` | **TIMEOUT** |
| `1 * 100 + 2 * 10 + 5`（无变量） | PASS 2.9s |
| lambda 内 `nat_add (nat_add (nat_mul a 100) (nat_mul x 10)) 5` | **TIMEOUT** |

- **内容相关性实验（已做）**：同形状在自足探针（自声明 `outParam` 的 Add/Mul trait + 自有
  Nat enum + 递归 add/mul，`--with-prelude none`，**运算符**与 lambda 两种形态）→ **PASS 0.4s**；
  换成内置 core prelude（primop 版 `nat_add`/`nat_mul`）→ **TIMEOUT**。
  ⇒ 触发点在 **primop 支撑的 Nat 归约路径**，与 `outParam` 实例求解无关（函数式形式同样触发）。
- **归因：未定**（倾向长期既有）：`src/L13_namespace/**` 本轮未改（`mod.rs` 仅加
  `#[cfg(test)] mod prelude_*_tests;`），`nat.typort` 的 primop 注册未改；无可用 pre-HEAD CLI
  （`deps/typort-*.exe` 是测试 harness、`l13bench-*` 不支持 `--file`）。
- **`--max-infer-ms` 无效**：`typort check z1 --max-infer-ms 20000` 实测 70s 仍未返回（0 字节输出，外部超时杀掉），
  与该 flag `--help` 自称的「on timeout aborts with a diagnostic」不符。**探针必须外部硬超时。**
- 旁证：prelude 从不用 3 项运算符链写算术（`nat.typort:144-149` 的 `mul_distrib_left` 用 `let` 绑定绕开）。

### 6.2 【缺陷 · 既有 → 本轮已修并独立复验】`streamFifoCC` 读指针被两个 always 块驱动
- 发现复现：`& .\target\prelude_scratch\verify\bin\typort_cur.exe emit --top ccFifo examples/hdl/21-crossclock.typort`
  → `target/prelude_scratch/verify/emit21_ccFifo.v`（**修前**快照）
- 修前实测：clkA 块 `:43-45` 与 clkB 块 `:55-57` **都**给 `_d_rdPtr` 赋值
  （`if (!(_d_rdPtr == _d_wrPtrSync2)) _d_rdPtr <= _d_rdPtr + 1;`）⇒ 双驱动 + 锁步下每拍 +2；
  clkA 侧那份还读 clkB 域的 `_d_wrPtrSync2`。
- 根因：`hdl-crossclock.typort:347-349` 用 `whenBegin(...)` 包裹 `regAssignCd(..., outCd)`，
  而 **`whenBegin` 没有 Cd 变体**（prelude 无 `whenBeginCd`/`whenCd`）⇒ 该语句同时发射到主域与 outCd 域。
- 对照：同 example 的 `ccPulse`（`emit --top ccPulse`）里 `__toggle` 只在 clkA、`__sync1/2` 只在 clkB，
  **无**双发射（因为用的是裸 `regAssignCd`，无 when 包裹）。
- 归因：HEAD `hdl-crossclock.typort:228-229` 是同一构造 ⇒ **既有**，与 hdl-b 的 G1（wrap 位修复）独立。
- **本轮修复 + 独立复验**（hdl-b 有界修复：Cd 赋值直接带条件值，不新增 Cd 版 when API）：
  `emit --top ccFifo`（二进制 mtime **11:47:26**）→ `target/prelude_scratch/verify/emit21_ccFifo_v2.v`：
  ```
  _d_rdPtr assignments: clkA=0 clkB=2
    [B] _d_rdPtr <= 0;
    [B] _d_rdPtr <= (!(_d_rdPtr == _d_wrPtrSync2) ? (_d_rdPtr + 1) : _d_rdPtr);
  ```
  同一次 emit 的其余钉子全部保持：`reg [2:0]` wrap 位指针、
  `pushReady = !(_d_wrPtr == {~_d_rdPtrSync2[2], _d_rdPtrSync2[1:0]})`（满，最高位取反）、
  `popValid = !(_d_rdPtr == _d_wrPtrSync2)`（空，全等）、`_d_mem[_d_wrPtr[1:0]]` / `_d_mem[_d_rdPtr[1:0]]`
  低位寻址、两域各一条 2FF 链、clkA 复位不再动 `_d_rdPtr`。**双驱动已消除，结构钉子全绿。**
- 遗留：「`whenBegin` 无 Cd 变体」列为**下一轮架构候选**（本轮用条件值绕开）。

### 6.3 【解析/使用限制】`(e : T)` 与 `rfl[Nat] x`

- `(left 9 : Either[Nat, Boolean]).left_to_option` → `error: can't unify`（4 例）。`typort quick` 只有
  `x => 表达式`；`(x: T) => e` 被解析成 Pi 类型（engine-quirks 定位 `elaboration.rs:3185-3252`）。
- `rfl[Nat] 3` 同样 `can't unify`；改 `def e: Eq[Nat] 3 3 = rfl` 通过。绕法：用 `def` 注解。

### 6.4 【口径/覆盖】

- `println <Boolean>` → `Boolean::true`；`println <Ordering>` → `Ordering::gt`（断言须 `.show`）。
- Show 只有具象实例：`Result[Boolean, Nat]`、`Product[Boolean,Nat]`（本轮已补）之外的混合组合仍无实例；
  泛型条件实例（`where T: Show`）引擎不支持。
- 我的 v5 探针 3 条自身问题（非 prelude 缺陷）：`Result[Boolean,Nat]` 无 Show、`result_to_either` 的
  `elim` 两个分支类型不一致。

### 6.5 【文档漂移】`@auto` 继承旧注释

`///` 提取是纯文本扫描（`src/doc/markup.rs::extract_doc_prefix`），`//` → `///` 只换符号不改内容。
hdl-a 的 37 个 `@auto` 中抓出 2 条**假文档**（`hdl-core` 的 `ModuleTree`/`isDeclaredSignal`），
其中 `isDeclaredSignal` 的旧注释在 HEAD 上本来就错。**维护者注意：`@auto` 必须逐条复核语义。**

### 6.6 【缺陷 · 本轮已修】检查模型把「同步链末级的 mux 驱动」误判为链的下一级 ⇒ 误报 HDL039

- hdl-b 补报（代码侧已修）：`hdl-check-graph.typort` 的 `chainWalk`/`chainNextOf`（`:1959-1982`）
  会把「同步链**末级**经 mux 驱动的**同域**寄存器」当成链的下一级，于是末级被升级为「中间级」，
  `midStageScan` 再对末级的其它合法读者误报 **HDL039**（同步链中段被读取）。
- 绕开方式（hdl-b）：把条件先落成具名组合线（`_d_popGo`）再进 mux，使链识别不再把末级接错。
- 类审计（hdl-b）：全 prelude 中「`when*` 包裹内 `*Cd` 赋值」共 **3 处**
  —— `pulseCCByToggle` / `ccByToggleUInt` / `streamFifoCC`，**本轮全部已修**；
  修复后只剩 1 处 `whenBegin`（主域、不含 Cd 赋值）。其中 `streamFifoCC` 那处正是 §6.2 的
  读指针双驱动，已由 verifier 独立复验（`_d_rdPtr` 只出现在 clkB 块）。
- 证据等级：结构级 + emitted-Verilog 实测（§6.2）；HDL039 误报的消除未独立仿真（本机无 verilator）。

---

## 7. 行为变更清单（非纯文档，含风险与证据等级）

| 变更 | 组 | 风险 | 证据等级 |
|---|---|---|---|
| `Vec.foldl` 右折 → **真左折** | prelude-data | 中（语义变更；prelude 内无调用方） | **实测**：`foldl=123` / `fold=321` / `reduce=132` |
| `list.typort` insert 注释纠正 | prelude-data | 低（纯注释） | 对码实现 `case eq => lcons(x, lcons(y, ys))` |
| `streamFifoCC` 满/空判据（wrap 位 + RAM 低位寻址）+ 读指针双驱动修复 | hdl-b | 高（双时钟 FIFO） | **结构级实测**：emitted Verilog 有 `reg [2:0]` 指针、`{~rdPtrSync2[2], rdPtrSync2[1:0]}` 满判据、`_d_mem[..[1:0]]` 低位寻址、双 2FF 链；`_d_rdPtr` 只出现在 clkB 块（双驱动已消除）；**本机无 verilator，无仿真背书**（模型级证据见 §9.7） |
| 树形真 PLRU（原为存根） | hdl-b | 中 | 【owner 报告 + diff 确认函数体从存根变为树遍历；未独立仿真】 |
| `metaDiv` floor | hdl-c | 中 | 【owner 报告，未独立复核】 |
| 大字面量护栏（>100000 解析期报错） | engine-quirks | 低（新增诊断） | 【owner 报告；本轮未独立复核（见 §8.3）】 |
| HDL034 只做 eq 形态 | hdl-a | 低（与实现对齐） | **双引擎实测**：`when c && !c` → 仅 HDL032；`when (sel==0)&&(sel==1)` → HDL032+HDL034 |

---

## 8. 方法论与维护者注意（本轮资产）

1. **判定器必须先用必失败样本校准**。本轮两起假 PASS 事故：`run_probe.ps1` 只扫 stderr
   （l13bench 失败行走 stdout）⇒ 对任何探针判 PASS；`run_check.ps1` 把 0 note/0 error 判 PASS
   （并发负载下 `typort check` 真的会 0 输出）。本仓库的 `verify/bounded_run.ps1` 已加
   `ZERO-OUTPUT`/`NO-NOTES`/`INCONCLUSIVE` 并对 `mfail_calib.typort` 校准。
2. **单次 TIMEOUT 不构成证据**：共享机器 + 并发构建下，刚 rebuild 完起的探针可能被瞬时干扰。
   定性必须在无并发构建的窗口、并用**直接调用**与**包装脚本**两种方式复测。
   （Lead 本轮据此撤回了一条「6 位字面量悬崖」的误判，本文件不引用该结论。）
3. **冻结副本保证「可比」，但也冻结 prelude 快照**：verifier 第一轮 `w_core` 用 10:58 副本跑出
   14 项 `not in scope`，实为副本内嵌 prelude 早于 prelude-core 落盘 `nat.typort`；
   11:29 新副本复测 14/14 全绿。⇒ 跨 owner 节奏复算时，必须「同一二进制内同时包含被验证项」。
4. **`--max-infer-ms` 不可依赖**（§6.1），探针必须外部硬超时。
5. **`typort doc` 口径**：只统计 def/struct/enum/trait 顶层，**impl 不计数**；`macro_rules` 不是条目
   （但可以加 `///`）。markdown 链接检查把 `](` 当链接 → `dead doc link` warning（全组 3 例）。
6. **Windows 上 cargo 的「上浮复制 exe」会被运行中的探针占锁**：`target/debug/deps/<bin>-<hash>.exe`
   才是新产物；`Start-Process` 在复制窗口内会 0 字节输出。
7. **读数必须带二进制 mtime + `git rev-parse HEAD`**，否则不同时刻的读数不可比。
8. **`@auto` 必须逐条复核语义**（§6.5）。

---

## 9. 未完成项与理由

1. **`streamFifoCC` 双驱动**：**已修复并独立复验**（§6.2，二进制 mtime 11:47:26；
   `_d_rdPtr` 只出现在 clkB 块，结构钉子全绿）。
2. **`whenBegin` 无 Cd 变体**：架构级候选（新增 Cd 版 when API）。本轮「`when*` 包裹内 `*Cd` 赋值」
   的 3 处已全部用有界方式修掉（§6.6），但 API 层面仍缺 Cd 作用域，列为下一轮候选。
3. **`subst2` 未独立确认**：需要显式 `P: A -> B -> Type 0` 的具体用例，本轮未构造出可钉值。
4. **HDL 行为变更（PLRU / metaDiv / 护栏）未独立仿真/复核**：本机无 verilator；
   PLRU 与 metaDiv 仅有 owner 报告与源码 diff 证据（§7 已标等级）。
5. **3 项算术链卡死的归因**：内容相关性实验已完成，但无 HEAD 二进制一锤定音 ⇒ 记「未定 + 倾向既有」。
6. **doc 覆盖率与门禁数字**：**已按 Lead 冻结树实测填入 §3**（doc 100% = 1192/1192；
   lib 606 / parity 15 / twin 27 / hdl042 2，fail=0；零回归、测试数 +35）。
7. **`tools/spinalhdl-verify/verify.py` 的 `RefFifoCC`**：已改写为**独立口径**——指针带 wrap 位、
   RAM 只取低位寻址、满/空由**模 2^PW 占用差**判定（`full <=> (wr-rs2) mod 2^PW >= depth`、
   `empty <=> (ws2-rd) mod 2^PW == 0`），不再是 RTL 的 `{~msb,lsb}` 等式形式（旧版与实现同构，
   属循环验证）；同步链改为真非阻塞序（`s2 <= s1_old`）。
   证据：`python -X utf8 target/prelude_scratch/verify/ref_fifocc_check.py` →
   ```
   RefFifoCC at reset  -> pushReady=1 popValid=0   (expected 1 / 0)
   PRE-FIX at reset    -> pushReady=0 popValid=0   (deadlock if 0 / 0)
   RefFifoCC progress  -> cycles accepting push=40, cycles with popValid=16
   PRE-FIX progress    -> cycles accepting push=0, cycles with popValid=0
   ```
   ⇒ **模型级**证明了「修前常数死锁 / 修后可用」，但**本机无 verilator，没有仿真背书**；
   RTL 侧只有 emitted-Verilog 结构钉（§6.2 的 `emit21_ccFifo.v`）。
8. **`streamFifoCC` 双驱动**（§6.2）：已修复并独立复验（mtime 11:47:26，`_d_rdPtr` 只出现在 clkB 块）。
9. **「`when*` 包裹内 `*Cd` 赋值」类审计**（§6.6）：全 prelude 3 处（`pulseCCByToggle` /
   `ccByToggleUInt` / `streamFifoCC`）**本轮全部已修**；`whenBegin` 仍无 Cd 变体 ⇒ 下一轮架构候选。
10. **`readSyncCC` 三处「不一致」**：**未能复现，维持原文**（Lead 裁决，§10 表）。

---

## 10. `docs/**` 漂移审计结果（verifier 独立复核 Lead 转来的清单）

| 项 | 来源 | 复核结果 | 处置 |
|---|---|---|---|
| E1 HDL034 检测范围（phase234 §4.5/:463-465 与 §6 表 :591） | hdl-a | **确认不符**：实现只做 eq 形态，报文固定 `driver condition is always false`（`hdl-check-graph.typort:1375/1393`），与同文件 §11.5/:978-981、§11.12/:1008-1009 自相矛盾 | **已最小修正**（两处，保留原文于更正注中） |
| E2 `hdl-language-spec.md:622` | hdl-a | **确认不符**（同上） | **已最小修正** |
| E3 `hdl-selfcheck-design.md` 码表缺 HDL041/HDL042 + `:117` 写「HDL041+ 留作后续」 | hdl-a | **确认不符**：HDL041/042 已实现（`hdl-check-graph.typort:1506-1548` / `:2199-2348`），HDL060-064 亦已落地（`hdl-fsm.typort`） | **已补 3 行 + 改写 :117** |
| E4 phase234 的 `hdl-check.typort:N` 行号锚点漂移 | hdl-a | **确认存在**：全文 30 处行号锚点（该文件已 901 → 1112 行） | **未逐条改**（改动面大）；建议下一轮统一改成「只用 def 名不写行号」 |
| E5 graph/core 十余处段注释坐在错误 decl 上方 | hdl-a | 未独立复核（属高危文件注释搬迁） | 记入未完成项 |
| G6 `spinalhdl-lib-replication.md` 指向不存在的 `hdl-math`/`hdl-io`/`hdl-logic`，总线组件指向 `hdl-bus.typort` | hdl-b | **确认不符**：三个文件不存在；实测落点为 `hdl-misc-io.typort`（Bcd/Divider/Decoder/Masked/TriState/Gpio/ReadableOpenDrain）与 `hdl-bus-proto.typort`（Apb3/AxiLite4/Axi4Stream/Wishbone/AvalonST/Apb3RegBank） | **已改 12 行 + 加更正注** |
| `:180` 说「真跨时钟需 Rust 侧扩展」与 `:117` 的 ✅ 自相矛盾 | hdl-b | **确认不符**（§6 波次 7 已列落地） | **已改写 :180**（保留原句删除线 + 2026-10 更新） |
| Plru/Bcd 状态标记 | hdl-b | **确认**：`bcdAdd`（整宽）仍是存根 `= a`（`hdl-misc-io.typort:166`）；Plru 本轮由存根升级为树形 PLRU | **已按实现改状态行**（Bcd 标「部分」、Plru 标本轮落地） |
| `hdl-stream-fsm-design.md:14` `Stream.stage` 占位 | hdl-b | **文档正确**：`stage` 确实仍是占位 `this`（hdl-bus.typort 未改） | **无需修改** |
| `hdl-language-spec.md:543/846` 与 `:590` readSyncCC 三处不一致 | hdl-b | **未能复现**：我读下来三处一致（都说 `Mem.readSyncCC` 无同步器，库级 `readSyncCCUInt[depth]` 才有）；hdl-b 也未给出具体冲突点 | **维持原文**（Lead 裁决：不成立，不改） |
| `verilog-compat.md` 文件头停在 M1 | hdl-c | **docs 侧已一致**（:3 明写「M1 + M2 + M3 已实现」）；`.typort` 侧文件头仍写 `(M1)` | docs 侧**无需修改**；`.typort` 头部属 hdl-c scope，转告 |

**审计结论**：Lead 转来的 12 项中，**7 项确认并已最小修正**、1 项文档本就正确、1 项未能复现不一致（已回问）、
1 项（E4 行号锚点）与 1 项（E5 段注释错位）只入册未改。所有修正都保留了原表述作为更正依据。
