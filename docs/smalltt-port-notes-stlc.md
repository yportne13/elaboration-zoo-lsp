# smalltt stlc 家族 → L07/L08 迁移笔记（task-3，porter-stlc）

状态：**完成**。stlc_small（stlcs）、stlc（stlc）、stlc_lessimpl（stlcl）三个家族在
L07/L08 上全部跑通（ref_ok=1 / twin_ok=1），最大档 3121 / 3649 decls，无 fuel/栈失败。
代码：src/bin/smalltt_cases/stlc.rs。本文件记录翻译映射、生成策略、实测与对照。

---

## 1. 源基准与口径

smalltt 仓库：F:\projects\hermes\_ref\smalltt

| smalltt 文件 | 行数 | 模板 defs | GenTestFiles 生成规则 | 本仓库用例名 |
|---|---|---|---|---|
| bench/stlc_small.stt | 71 | 19 | stlc_small5k = times 96、10k = times 192 | **stlcs** |
| bench/stlc.stt | 165 | 39 | stlc5k = times 40、10k = times 80 | **stlc** |
| bench/stlc_lessimpl.stt | 164 | 39 | lessimpl5k = times 40、10k = times 80 | **stlcl** |

生成规则（src/GenTestFiles.hs）：replace 把模板里每个 % 换成拷贝序号
（序号 0 → 空串，其余 → 十进制），再 times N 首尾相接。smalltt 公布的数字
（README「Elaboration speed」，2021 Intel i5-1165G7）：
stlc 0.014s / 5k 0.179s / 10k 0.306s；stlcLessImpl 0.008 / 0.140 / 0.275；
stlcSmall 0.003 / 0.037 / 0.072。

口径对齐：本仓库 smallttbench 的 ref = bench_check（全量 elaborate，不 quote），
ref_nf = 全量 elaborate 后 quote 最后一个 def（对应 smalltt [nftime]；stlc 家族
只计 elab，所以生成的源最后追加极小的 def nf_dummy : U = U，让 ref_nf 的
quote 部分可忽略）。twin = bump_spine_iter::Tycker 同口径。单位均为微秒（CASE 行）。

## 2. smalltt → typort 语法映射

| smalltt | typort（L07/L08） | 备注 |
|---|---|---|
| λ x y. t | x => y => t | 多 binder 折叠 |
| A → B | A -> B | ASCII |
| {Γ A} → T（隐式 Π） | [Γ : _, A : _] -> T | 洞类型由使用处合一解出 Con/Ty |
| def 头 f : {Γ A} → T = e | def f[Γ, A] : T = e | 方括号参数即隐式绑定的 Π/lambda 链 |
| _（smalltt 洞） | _ | 显式实参位置/参数类型位置都可 |
| (Γ : _)(A B : _) → T | (Γ : _) -> (A : _) -> (B : _) -> T | 一个圆括号只能一个 bind 名+类型，多 binder 必须展开 |
| case（def 名/字段名/局部 binder） | scase | case 是 typort 关键字（match 臂），全局与局部都要改 |
| f : U | def f : U = ... | L07/L08 是 type-in-type 单一 U，Church 编码可直译 |
| 隐式实参（full stlc） | 裸应用 vz、vs (x ...) | 依赖 L07/L08 的隐式插入 |
| 显式占位（lessimpl/small） | vz _ _、vs _ _ _ (...) | 与 smalltt 原文件的 less-implicit 写法一一对应 |

其它翻译要点/坑：

1. **换行约束**：typort 只在 =、(、[ 之后允许换行；=>、-> 后面必须紧跟表达式。
   所以每个 def 压成单行（Tm 的 15 字段 Π 一行约 1.4KB），N 份复制后文件
   行数≈decls 数。
2. **Church 编码内 binder 的两种版本**：stlc.stt 的 Var/Tm 字段是隐式 Π
   （{Γ A} →），stlc_lessimpl.stt / stlc_small.stt 是显式 (Γ : _)(A : _)。
   模板严格照抄各自的版本；def 头（{Γ A} → ...）两边都写成 [Γ, A] 参数。
3. **语义等价性验证**：模板单份 = smalltt 单文件（%→空串），三家族 size 1 都
   check 通过；这正是 smalltt README 的 stlc / stlcLessImpl / stlcSmall 单文件行。
4. **literal 名字**：ι / Γ 等希腊字母可直接作标识符（lexer 用 is_alphabetic）；
   % 只出现在被替换的标识符里，模板没有任何其它 % 字符。
5. **循环引用**：模板里 lambda binder 与全局同名（如 Ty/arr/lam/Tm）靠遮蔽实现；
   L07/L08 名字解析局部优先，故每份都是自包含的非递归 def 集合。
6. **不在本文件处理**：L09/L10 分层宇宙无法直译 Church 编码（porter-l09l10 负责），
   本文件只在 L07/L08 的 Family 下被调用。

## 3. 生成策略（stlc::render）

- 模板常量以单份文本保存，% 为序号占位；第 i 份 tpl.replace('%', suffix)，
  i=0 → 空串，其余 → i（与 GenTestFiles.render 逐字一致），份间空一行。
- 末尾追加 def nf_dummy : U = U（唯一名，最后 decl）→ bench_check_nf 的
  quote 只处理它；注意 ref_nf 仍会先全量 elaborate，所以 ref_nf ≈ ref + ε。
- SPECS 声明（--sizes 是硬过滤，未声明的档不会跑）：
  - stlc：1 / 8 / 40 / 80 份（↔ smalltt stlc 单文件 / ≈1k 行 / 5k / 10k）
  - stlcs：1 / 8 / 96 / 192 份（↔ stlcSmall 单文件 / ≈1k / 5k / 10k）
  - stlcl：1 / 40 / 80 份（↔ stlcLessImpl 单文件 / 5k / 10k）

生成文件规模（每份 39/39/19 个 def，每 def 1 行）：

| case | 份数 | 行数=decls | bytes |
|---|---|---|---|
| stlc | 1 | 40 | 6,327 |
| stlc | 8 | 313 | 52,324 |
| stlc | 40 | 1,561 | 270,546 |
| stlc | 80 | 3,121 | 543,986 |
| stlcs | 1 | 20 | 1,890 |
| stlcs | 8 | 153 | 15,785 |
| stlcs | 96 | 1,825 | 200,441 |
| stlcs | 192 | 3,649 | 412,809 |
| stlcl | 1 | 40 | 6,489 |
| stlcl | 40 | 1,561 | 277,026 |
| stlcl | 80 | 3,121 | 556,946 |

（行数=非空行数=def 数；decls 由驱动打印，与上表一致，已核对。）

## 4. 实测（本机 AMD Ryzen 5 5600，6C/12T，Win11；与 4 个 agent 并行跑基准，
载荷噪声较大，min/median 并列给出；ref/twin 单位 µs，min 为主）

### 4.1 L07

| case | 份数 | decls | ref min/med | ref_nf min/med | twin min/med | twin_nf min/med |
|---|---|---|---|---|---|---|
| stlc | 1 | 40 | 91,904 / — | 91,179 / — | 28,886 / — | 18,056 / — |
| stlc | 8 | 313 | 785,060 / 802,057 | 752,806 / 785,017 | 134,311 / 217,082 | 143,189 / 159,577 |
| stlc | 40 | 1,561 | 3,735,091 / 3,735,421 | 3,775,556 / 3,790,464 | 798,905 / 997,213 | 722,352 / 796,158 |
| stlc | 80 | 3,121 | 7,661,833 / 7,731,107 | 7,659,452 / 7,683,488 | 1,843,189 / 2,135,706 | 1,641,423 / 1,658,503 |
| stlcs | 1 | 20 | 7,976 / — | 6,945 / — | 2,238 / — | 1,518 / — |
| stlcs | 8 | 153 | 65,168 / 66,268 | 57,270 / 62,006 | 10,539 / 10,911 | 10,267 / 10,533 |
| stlcs | 96 | 1,825 | 717,117 / 743,082 | 712,822 / 777,171 | 145,871 / 207,833 | 147,724 / 162,817 |
| stlcs | 192 | 3,649 | 1,565,571 / 1,718,373 | 1,474,410 / 1,519,372 | 339,725 / 464,242 | 346,355 / 346,803 |
| stlcl | 1 | 40 | 87,400 / — | 83,233 / — | 15,070 / — | 14,423 / — |
| stlcl | 40 | 1,561 | 3,496,758 / 3,576,352 | 3,476,846 / 3,500,299 | 653,568 / 906,114 | 605,937 / 757,559 |
| stlcl | 80 | 3,121 | 6,866,908 / 6,908,411 | 6,880,247 / 6,891,348 | 1,363,265 / 1,811,987 | 1,347,639 / 1,387,296 |

（1 份档 rounds=1，其余 rounds=2/3；最小档仅作单文件对照。）

### 4.2 L08（同源 struct 层；与 L07 差在噪声内，普遍略快）

| case | 份数 | decls | ref min/med | ref_nf min/med | twin min/med | twin_nf min/med |
|---|---|---|---|---|---|---|
| stlc | 40 | 1,561 | 3,684,913 / 3,712,819 | 3,722,024 / 3,738,346 | 712,421 / 988,781 | 703,441 / 721,661 |
| stlc | 80 | 3,121 | 7,467,186 / 7,659,675 | 7,712,904 / 7,719,871 | 1,664,687 / 2,162,755 | 1,811,942 / 1,853,535 |
| stlcs | 96 | 1,825 | 710,439 / 713,539 | 738,620 / 763,754 | 158,667 / 203,695 | 143,381 / 146,374 |
| stlcs | 192 | 3,649 | 1,438,924 / 1,484,355 | 1,457,076 / 1,479,341 | 343,219 / 448,379 | 328,513 / 337,960 |
| stlcl | 40 | 1,561 | 3,487,551 / 3,499,638 | 3,445,095 / 3,483,761 | 603,952 / 901,608 | 658,171 / 734,186 |
| stlcl | 80 | 3,121 | 6,812,665 / 6,846,877 | 6,836,228 / 6,868,620 | 1,332,428 / 1,792,771 | 1,307,403 / 1,374,955 |

L08 vs L07（ref min）：stlc40 −1.3%、stlc80 −2.5%、stlcs96 −0.9%、stlcs192 −8.1%、
stlcl40 −0.3%、stlcl80 −0.8%。结论：**L08 与 L07 无口径差异**（struct 层同源），
差异量级 ≲ 负载噪声；两层的 ref_ok/twin_ok 全为 1，无 SKIP、无 fuel/栈上限问题。

### 4.3 每千行 / 每 decl 归一化（L07，ref min）

| case | 档 | 耗时 | typort 行数 | s/千行 | 等价 decl 数 | ms/decl |
|---|---|---|---|---|---|---|
| stlc | 80 | 7.662s | 3,121 | 2.45 | 3,121 | 2.455 |
| stlcl | 80 | 6.867s | 3,121 | 2.20 | 3,121 | 2.200 |
| stlcs | 192 | 1.566s | 3,649 | 0.43 | 3,649 | 0.429 |

注：typort 模板把每份压成 39/19 行（smalltt 是 165/71 行），所以不能直接拿
「行数」和 smalltt 的 5k/10k 命名对齐；**可比单位是「份数 × 每份 def 数」**：
stlc 80 份 = 3,121 defs ↔ smalltt stlc10k 80×40 = 3,200 defs；
stlcs 192 = 3,649 defs ↔ stlcSmall10k 192×19 = 3,648 defs。
按 smalltt 等价模板行数折算：stlc 0.58 s/千行（smalltt 0.023）、
stlcl 0.52（0.021）、stlcs 0.115（0.0053）。

## 5. 与 smalltt 公布数字的量级对照

机器不同（本机 Ryzen 5 5600 桌面 Zen3 vs smalltt 表 2021 移动 i5-1165G7，
单核大致快 1.3–1.5×）+ 实现/特性不同（smalltt 有 glued eval / 近似 conversion
checking，L07 的 unify 对 Decl 头会 force 展开做结构比对；twin 版走 bump-spine
迭代器），因此**只作量级参考**。

| 对照 | L07 ref min | smalltt | 倍数（L07/smalltt） |
|---|---|---|---|
| stlc 1 份 ↔ stlc | 0.0919s | 0.014s | 6.6× |
| stlc 40 份 ↔ stlc5k | 3.735s | 0.179s | 20.9× |
| stlc 80 份 ↔ stlc10k | 7.662s | 0.306s | 25.0× |
| stlcl 1 份 ↔ stlcLessImpl | 0.0874s | 0.008s | 10.9× |
| stlcl 40 份 ↔ stlcLessImpl5k | 3.497s | 0.140s | 25.0× |
| stlcl 80 份 ↔ stlcLessImpl10k | 6.867s | 0.275s | 25.0× |
| stlcs 1 份 ↔ stlcSmall | 0.00798s | 0.003s | 2.7× |
| stlcs 96 份 ↔ stlcSmall5k | 0.717s | 0.037s | 19.4× |
| stlcs 192 份 ↔ stlcSmall10k | 1.566s | 0.072s | 21.7× |

扣除 fixed overhead 后按每份/每 def 比较更公平：
- stlc：L07 95.8ms/份 vs smalltt 10k 3.83ms/份 → ≈25×；
- stlcl：85.8ms/份 vs 3.44ms/份 → ≈25×；
- stlcs：8.15ms/份 vs 0.375ms/份（10k）→ ≈22×。
考虑 CPU 单核差（~1.4×），实现级差距约 15–18×，全部落在「同量级但慢一个数量级
以内」的结论上；L07 的 twin（bump_spine_iter）比 ref 快 4–5×（stlc80 4.2×、
stlcl80 5.0×、stlcs192 4.6×），已经把差距压到 ~5×。

附注：
- full stlc（隐式 Church 编码）在 L07 上只比 lessimpl 慢 ~10%（6.867→7.662s），
  与 smalltt 10k 的 0.306 vs 0.275（+11%）一致；单文件差距（0.014 vs 0.008）
  主要是 fixed overhead。
- stlc 家族是「elab 吞吐」用例：ref_nf ≈ ref（都跑全量 elaborate，尾 def 极小），
  twin_nf 与 twin 同量级；没有任何档依赖 quote 大项。

## 6. 复现命令

    # 构建（默认 target/ 被其他 agent 的 exe 进程占用时可用独立目录）
    cargo build --release --bin smallttbench
    # 或：$env:CARGO_TARGET_DIR="...\target_stlc"; cargo build --release --bin smallttbench

    # 全部规模，单层（--sizes 是硬过滤，只跑声明过的标签）
    target/release/smallttbench.exe --layer L07 --case stlc,stlcs,stlcl --sizes 1,8,40,80,96,192 --rounds 3
    target/release/smallttbench.exe --layer L08 --case stlc,stlcs,stlcl --sizes 1,8,40,80,96,192 --rounds 3

    # 只解析验证（PASS 行带 bytes/decls；真正的语义闸门是上面的 ref_ok/twin_ok）
    target/release/smallttbench.exe --layer L07 --validate --case stlc,stlcs,stlcl

    # 落盘生成的源码
    target/release/smallttbench.exe --layer L07 --case stlc --sizes 1 --validate --dump-dir target/smalltt_corpus

原始输出：target/smalltt_probe/stlc/L07_big.txt、L08_big.txt（本笔记所有数字的来源）。
