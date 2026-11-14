# smalltt → L07/L08 用例迁移与初测笔记（task-1 / porter-l07l08）

> 写域：`src/bin/smalltt_cases/l07_l08.rs` + 本文件 + `target/smalltt_probe/l07l08/**`。
> 分支 `perf/l09-carrier-switch`；**未做任何 git commit**。
> ⚠️ 所有时间为**载荷下初测**（同机 4 个 agent 并行编译/跑基准），只用于可行性与量级
> 判断；最终干净数据由 Lead 统一重跑。
>
> **Lead 追加（最终构建）**：L07/L08 孪生版（`bump_spine_iter` 的 `prim/machine/compiler/entry`）
> 也已接入 `TYPORT_UNIFY_FUEL` 覆盖，§9 里「twin 没有 fuel 覆盖」的旧说法作废；
> 最终报告中 twin 的大 size 数据来自新构建。最终数据见 `docs/smalltt-bench-2026-11-14.md`。

## 0. TL;DR

- 生成器 `src/bin/smalltt_cases/l07_l08.rs` 最终版：conv 族 5 例（natconv/treeconv/
  treeconvm/forcetree/nftree）+ asymptotics 族 3 例（idtest/pairtest/vectest）；
  `nat_tower` 扩到 n23，tree 深度支持 8..=24。`cargo build --release --bin smallttbench`
  通过（log: `target/smalltt_probe/l07l08/build4.log`，Finished in 2m43s）。
- **默认 fuel（UNIFY_FUEL=4096）**：natconv ≤ 4k；treeconv/treeconvm ≤ depth 10；
  forcetree/nftree 到 depth 20 都能跑（成本 ~2^d，受时间而非合一燃料约束）；
  idtest 40 PASS；vectest 960 PASS；pairtest ≤ 20。
- **放大 fuel（TYPORT_UNIFY_FUEL=20M）**：natconv 1M PASS、treeconv depth 18 PASS、
  treeconvm depth 15 PASS（11/12/15/18 全 PASS）。1M 需要同时加大栈
  （`SMALLTTBENCH_STACK_MB=8192`；默认 1024MB 在失败路径会 abort）。
- **pairtest 上游 x0..x30（31 let）不可行**：L07/L08 无 smalltt 的 glued eval / meta
  共享，无注解 let 的类型每层被 quote 全展开 ⇒ 指数 2^k：实测 10=3.8ms、
  15=140ms、20=5.68s（每 +1 层 ~2.05x）⇒ 25≈3min、30≈1.6h，不列入 SPECS。
  生成器尾部加 `def nf_dummy : U = U`，否则 ref_nf 会 quote 2^k 节点。
- 参考版规模行为：放大 fuel 下 L07/L08 的 natconv 100k→1M 均近线性
  （L07 9.4x / L08 11.8x 时间比），**未复现 L07 超线性**；L07 ref 稳定比 L08
  慢 ~1.6-1.9x。Lead 观察到的 L07 1M=17.07s 应是当时载荷尖峰（本次同档 L07=4.0s）。

## 1. 用例映射与上游数字

smalltt 源码：`F:\projects\hermes\_ref\smalltt`（README.md Benchmarks 节）。
上游机器：Intel 1165G7 / 16GB / 28W / GHC RTS `-A64M -N8`；下表为上游公布秒数。

| smalltt 用例 | 源文件 | 我们的 case/size | 上游秒数 |
|---|---|---|---|
| NatConv1M/5M/10M | bench/conv_eval.stt | `natconv` 1k..5M（10M 未做） | 0.045 / 0.188 / 0.712 |
| TreeConv15/18..23 | bench/conv_eval.stt | `treeconv` depth 10/11/12/15/18 | 0.055 / 0.088 / 0.161 / 0.408 / 0.834 / 1.722 / 3.325 |
| TreeConvM15/18..23 | bench/conv_eval.stt | `treeconvm` depth 10/11/12/15 | 0.010 / 0.092 / 0.169 / 0.361 / 0.835 / 1.694 / 3.453 |
| ForceTree15/18..23 | bench/conv_eval.stt | `forcetree` depth 10/12/14/15/18/20 | 0.011 / 0.100 / 0.240 / 0.487 / 1.070 / 2.122 / 4.372 |
| NfTree15/18..23 | bench/conv_eval.stt | `nftree` depth 10/12/14/15/18/20 | 0.005 / 0.064 / 0.111 / 0.259 / 0.552 / 1.286 / 3.023 |
| idTest | bench/asymptotics.stt | `idtest` 40 | 0.000 |
| pairTest | bench/asymptotics.stt | `pairtest` 10/15/20（上游 x0..x30=31 let） | 0.000 |
| vecTest | bench/asymptotics.stt | `vectest` 240/960（上游恰好 960 cons U） | 0.078 |

口径：smalltt `[elabtime]` ≈ 我们的 ref（check）；`[nftime]` ≈ ref_nf 中 quote 的部分。
注意 ref_nf 会**重跑一遍 check**，所以 nf 口径 ≈ check + quote。

## 2. 语法/语义映射要点（smalltt → typort L07/L08）

| smalltt | typort | 备注 |
|---|---|---|
| `U` | `U` | L07/L08 单一宇宙 type-in-type，`U : U` 成立（L09/L10 分层不可直译） |
| `A → B` / `(x:A) → B` | `A -> B` / `(x : A) -> B` | 显式 Π |
| `{A : U} → …` | `[A : U] -> …` | 隐式 Π（方括号） |
| `λ x. t` / `λ {A} x. t` | `x => t`；def 头 binder 自动 λ 抽象 | `def f[A](x):T = body` ≡ `λ[A] x. body` |
| 顶层 `f : T = t` | `def f : T = t` | 无 `[elabtime]` 注解 |
| 局部 `let x = t; u` | `let x = t; u` | 无注解 let 会推断类型并 quote（pairtest 爆炸根源） |
| `{n} → A → V n → V (suc n)` | `[k : NatC] -> A -> V k -> V (suc k)` | 内部隐式 Π 显式命名，避免与外层索引 `n` 混淆 |
| 隐式实参缺省 | 自动插入 meta（`insert`） | 与 smalltt 一致；idtest/vectest 的负载来源 |
| type-in-type 的 `id : {A:U}→A→A` 自应用 | `def id[A : U](x : A) : A = x` + 40 次应用 | 每层应用解一个隐式 meta |

其他：
1. 每个用例的最后一个 def 就是 ref_nf 的 quote 对象；非 nf 用例追加
   `def nf_dummy : U = U`（1 节点）以免 ref_nf 被巨型类型/值拖爆。
2. nf 用例（forcetree/nftree）最后一个 def 是基准值，不加 nf_dummy。
3. L07/L08 的 `force` 会展开顶层 def、没有 glued evaluation，因此类型/值在
   check 与 quote 时都是「全展开」的——这是与 smalltt 最大的性能机制差异，
   直接决定了 pairtest 的指数行为和 conv 族的大常数。

## 3. SKIP 分类判据与结果

驱动只打印 `SKIP,...,reason=ref_check_fail`。细分方法：

| 现象 | 判据 | 归类 |
|---|---|---|
| 默认 fuel SKIP，放大 `TYPORT_UNIFY_FUEL` 后 PASS | 两轮对照 | **fuel 耗尽**（can't unify fuel exhausted） |
| 放大 fuel 后仍 SKIP | 两轮都失败 | 语义/结构不匹配（本任务未出现） |
| 进程无输出直接退出（Windows abort 丢 stdout 缓冲） | exit≠0 / 无输出 | **栈溢出** |
| 单档 >30s 量级 | 计时/外推 | **不可行（时间）** |

实测归类（默认 fuel=4096）：
- **fuel 耗尽**：natconv 5k/10k/100k；treeconv 11/12/15/18；treeconvm 11/12/15。
  证据：`TYPORT_UNIFY_FUEL=20000000` + `SMALLTTBENCH_STACK_MB=4096/8192` 后全部
  PASS（见 §4 放大 fuel 表）。
- **栈溢出（失败路径）**：natconv 1M/5M 在默认 1024MB 栈下会 abort（不是干净
  SKIP）——失败时 unify_catch 要 quote 巨型项构造错误消息。`SMALLTTBENCH_STACK_MB=8192`
  后 natconv 1M 变为干净 `ref_check_fail`（仍是 fuel 耗尽，不是语义失败）。
- **不可行（时间）**：pairtest 25/30（指数 quote，外推 25≈3min、30≈1.6h）。
- 未测试（时间预算）：treeconv/treeconvm 19..23（外推每 +1 ~2x，18 已 0.7s）；
  natconv 5M/10M 放大 fuel 口径；forcetree/nftree 21..23（外推每 +1 ~2x，20 已 0.8/0.9s）。

## 4. 可行/不可行上限（逐用例结论）

| 用例 | 默认 fuel 可行上限 | 放大 fuel（20M）+ 大栈后 | 说明 |
|---|---|---|---|
| natconv | **4k**（1k..4k PASS，5k 起 SKIP） | 100k PASS、**1M PASS**（L07 4.0s / L08 2.6s）；5M 未测（外推 ~20s+） | 上限=单次合一燃料；10M 需 >10M fuel 且时间/栈不划算 |
| treeconv | **depth 10** | **depth 18 PASS**（15=98ms、18=700ms）；19..23 未测 | 燃料 ≈ 2~4/leaf；depth 23 约需 17-34M fuel，20M 未必够 |
| treeconvm | **depth 10** | **depth 15 PASS**（11=4.9ms、12=8.4ms、15=74ms） | 含 hole 的近似转换；比 treeconv 便宜 |
| forcetree | **depth 20**（10..20 全 PASS，无 fuel SKIP） | 同左（燃料无关） | 成本 ~2^d：20=0.80s（ref）；21..23 未测、外推 1.6/3.2/6.4s，预算外 |
| nftree | **depth 20** | 同左 | ref_nf 完整展开，节点数=2^(d+2)（20=4.19M 节点/0.88s）；23 外推 33.5M/~7s |
| idtest | 40 PASS | — | 40 次 id 自应用，0.23ms；简单 |
| pairtest | **20**（10/15/20 PASS） | — | 25/30 **不可行**（指数 quote；见 §0/§6） |
| vectest | **960（上游原例）PASS** | — | 240=25ms、960=0.58s；二次型（见 §5） |

放大 fuel 实测（`TYPORT_UNIFY_FUEL=20000000`，载荷下，跑 1 轮 ref）：

| case | size | L07 ref µs | L08 ref µs |
|---|---|---|---|
| natconv | 100k | 428 783 | 216 046 |
| natconv | 1M | 4 019 957 | 2 556 612 |
| treeconv | 11 / 12 / 15 / 18 | 7 127 / 11 840 / 98 200 / 699 575 | （未测） |
| treeconvm | 11 / 12 / 15 | 4 891 / 8 388 / 73 807 | （未测） |

（注：L09/L10 的 treeconv 在默认 fuel 下就能跑到 18 —— 见 Lead 的 L09/L10 报告；
这不影响本文件的 L07/L08 结论。）

## 5. 初测表（默认 fuel，L07/L08，`--rounds 1 --only ref,ref_nf`，载荷下 µs）

CASE 字段：`layer,case,size,bytes,decls,ref_min,ref_med,ref_nf_min,ref_nf_med,...`
（ref/ref_nf = 参考版 bench_check / bench_check_nf；twin 系列本轮未跑，主口径=ref）。
原始日志：`target/smalltt_probe/l07l08/initial_default_L07L08_r1b.txt`。

L07：

| case | size | ref µs | ref_nf µs | nodes |
|---|---|---|---|---|
| natconv | 1k/2k/3k/4k | 3 225 / 4 089 / 4 675 / 7 244 | 997 / 1 544 / 2 267 / 3 675 | 1 |
| natconv | 5k/10k/100k | SKIP fuel | SKIP | - |
| treeconv | 10 | 2 854 | 2 046 | 1 |
| treeconv | 11/12/15/18 | SKIP fuel | SKIP | - |
| treeconvm | 10 | 2 521 | 2 197 | 1 |
| treeconvm | 11/12/15 | SKIP fuel | SKIP | - |
| forcetree | 10/12/14/15/18/20 | 1 051 / 2 534 / 9 536 / 26 066 / 201 122 / 804 430 | 1 153 / 3 882 / 16 994 / 36 563 / 303 808 / 1 224 429 | 4 |
| nftree | 10/12/14/15/18/20 | 522 / 368 / 345 / 392 / 423 / 459 | 958 / 2 509 / 9 922 / 19 823 / 182 725 / 877 946 | 4096/16384/65536/131072/1048576/4194304 |
| idtest | 40 | 230 | 115 | 1 |
| pairtest | 10/15/20 | 3 831 / 139 869 / 5 677 661 | 3 369 / 134 723 / 5 780 505 | 1 |
| vectest | 240/960 | 24 794 / 581 479 | 24 332 / 394 189 | 1 |

L08（同结构，数值接近）：

| case | size | ref µs | ref_nf µs |
|---|---|---|---|
| natconv | 1k/2k/3k/4k | 1 408 / 1 754 / 2 318 / 3 097 | 861 / 1 459 / 1 978 / 3 095 |
| treeconv | 10 | 2 563 | 2 221 |
| treeconvm | 10 | 4 502 | 2 644 |
| forcetree | 10/12/14/15/18/20 | 1 005 / 2 345 / 8 686 / 17 208 / 153 498 / 662 975 | 1 140 / 3 559 / 13 631 / 28 710 / 269 851 / 1 058 826 |
| nftree | 10/12/14/15/18/20 | 611 / 340 / 340 / 373 / 418 / 543 | 998 / 2 391 / 9 445 / 17 837 / 175 782 / 760 603 |
| idtest | 40 | 239 | 107 |
| pairtest | 10/15/20 | 3 951 / 157 210 / 5 765 868 | 2 939 / 132 917 / 5 959 683 |
| vectest | 240/960 | 24 292 / 585 555 | 23 292 / 362 599 |

关键观察：
- **forcetree 默认 fuel 下 ref_nf 的 nodes=4**：quote 在 fuel 耗尽后提前返回（树值展开
  烧 force 燃料），所以默认口径的 forcetree nf 节点数/时间**不代表完整 nf**；
  nftree 的 nodes 是完整展开（quote 中 beta/闭包应用不烧燃料）。
- nftree nodes = 2^(d+2)（d=10→4096, d=20→4194304），与树规模自洽。
- vectest 240→960（4x）：24.8→581ms（≈23x）⇒ 二次型（occurs checking 线性增长 ×
  cons 数），与 smalltt 的定性一致（smalltt 也二次，但常数小 ~7x：960 上游 78ms）。
- pairtest 每 +1 层 ~2.05x（10=3.8ms→15=140ms→20=5.68s）⇒ 指数。
- L08 普遍比 L07 快 ~1.3-2x（同源实现，L08 是 L07 修 Pi-quote bug 后的版本）。

## 6. 参考版随规模的行为（Lead 提的 L07 超线性现象）

Lead 观察到：L07 natconv 100k=346ms → 1M=17.07s（≈49x/10x 超线性），L08 1M=3.82s。
本次**在放大 fuel（20M）+ 8GB 栈**下同机复测（载荷下 1 轮 ref）：

| layer | 100k | 1M | 1M/100k 比 |
|---|---|---|---|
| L07 | 428 783 µs | 4 019 957 µs | **9.4x**（≈线性） |
| L08 | 216 046 µs | 2 556 612 µs | **11.8x**（≈线性） |

结论：**没有复现 L07 超线性**；两者从 100k 到 1M 都接近线性（Church 数转换检查
线性于数值），L07 ref 稳定比 L08 慢 ~1.6-1.9x。Lead 的 17.07s 更可能是当时机器
载荷尖峰（本次 L07 1M=4.0s，与 L08 的 2.6s 同量级）。不排除更大规模（5M/10M）上
栈/分配造成非线性，但未测。

## 7. 最终 SPECS（`src/bin/smalltt_cases/l07_l08.rs`）

```rust
natconv:   ["1k","2k","3k","4k","5k","10k","100k","1M","5M"]
treeconv:  ["10","11","12","15","18"]
treeconvm: ["10","11","12","15"]
forcetree: ["10","12","14","15","18","20"]
nftree:    ["10","12","14","15","18","20"]
idtest:    ["40"]
pairtest:  ["10","15","20"]
vectest:   ["240","960"]
```

## 8. 复现命令

```powershell
# 默认 fuel（主结论；注意 1M/5M 会 abort，用 --sizes 排除或加大栈）
.\target\release\smallttbench.exe --layer all --case natconv,treeconv,treeconvm,forcetree,nftree,idtest,pairtest,vectest ^
  --sizes 1k,2k,3k,4k,5k,10k,100k,10,11,12,14,15,18,20,40,240,960 --rounds 1 --only ref,ref_nf

# 放大 fuel（只对 ref 生效；twin 仍 4096）
$env:TYPORT_UNIFY_FUEL='20000000'; $env:SMALLTTBENCH_STACK_MB='8192'
.\target\release\smallttbench.exe --layer L07 --case natconv --sizes 100k,1M --rounds 1 --only ref
$env:SMALLTTBENCH_STACK_MB='4096'
.\target\release\smallttbench.exe --layer L07 --case treeconv,treeconvm --sizes 11,12,15,18 --rounds 1 --only ref
```

诊断（默认 fuel 的详细错误文本，用不重建的 realbench）：
```powershell
mkdir target\smalltt_probe\one -Force
Copy-Item target\smalltt_probe\dump\L07\natconv__5k.typort target\smalltt_probe\one\
.\target\release\realbench.exe --layer L07 --corpus target\smalltt_probe\one --validate
```

## 9. 异常与注意事项

- **twin（bump_spine_iter）没有 `TYPORT_UNIFY_FUEL` 覆盖**：放大 fuel 口径下
  twin 仍是 4096 ⇒ ref/twin 不一致属正常，主口径=ref。本轮初测未跑 twin（时间）。
- 载荷下数字抖动大（同档可差 2-5x），只用于可行性判断；最终数据由 Lead 干净重跑。
- 默认 1024MB 栈在 natconv 1M 失败路径会 abort（丢 stdout）——全量默认跑务必
  `--sizes` 排除 1M/5M 或设 `SMALLTTBENCH_STACK_MB=8192`。
- 已存日志：`target/smalltt_probe/l07l08/{build4.log, initial_default_L07L08_r1b.txt,
  amp_nat_100k_1M.txt, amp_tree_L07.txt, def_nat_1M_stack8192.txt, probe_asym_*.txt}`。
