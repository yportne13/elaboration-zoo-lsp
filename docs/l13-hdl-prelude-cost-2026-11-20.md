# L13 hdl prelude 装载成本画像（2026-11-20）

> 背景：2026-11-19 补 hdl 基线时，`l13bench --with-prelude hdl` 单例跑到
> 9.7 GB / 7 分钟仍未出判定行，两次把整机拖到无响应。本文是那次事故的
> 定量归因，以及第一处修复。
>
> 结论先行：**bench 口径的峰值内存主要不是"prelude 太大"，而是 bench 把
> 整串 prelude 当成一个文件塞进同一个 bump arena、从不压实**；产品加载器
> `prime_resident` 是逐文件边界 + 384 MB 累计阈值就地压实的。

## 1. 测量方法

三个手段，都可复现：

1. **看门狗**（`tools/bench_watchdog.ps1`）：给任意命令加墙钟上限与 RSS 上限，
   回报峰值。**任何 l13bench 调用都必须经过它**——裸跑就是 2026-11-19 两次
   事故的直接原因。
2. **prelude 规模扫描**（`--prelude-files N`）：只装 CORE + HDL 前 N 个文件，
   用**空用户文件**跑，把"prelude 成本"与"用户文件成本"分离。
3. **内存探针**（`L13BENCH_MEM=1`）：进程内计数分配器（`l13bench` 的
   `memprobe`）+ 分阶段/分步标记（parse / parity 的 ref,twin,pretty 各步 /
   逐 decl live/peak）。

复现示例：

~~~powershell
# 规模扫描（N = 0,2,4,...,20）
& ./tools/bench_watchdog.ps1 -Exe target\release\l13bench.exe \
    -ArgList @('--file','%TEMP%\empty.typort','--with-prelude','hdl','--rounds','1','--only','basic','--prelude-files','20') \
    -TimeoutSec 90 -CapMB 4500

# 分阶段探针
$env:L13BENCH_MEM='1'
target\release\l13bench.exe --file <empty.typort> --with-prelude hdl --rounds 1 --only basic --prelude-files 20
Remove-Item Env:L13BENCH_MEM
~~~

> 注：`--only basic` **只过滤计时轮**，正确性互检 `nf_parity` 仍然两版都跑。
> 因此本文的"进程峰值"始终包含孪生一趟。

## 2. 数据：prelude 规模 → 成本

空用户文件，`--with-prelude hdl --prelude-files N`，单进程：

| N | decls | 墙钟 | 峰值 RSS |
|---:|---:|---:|---:|
| 0（仅 core） | 209 | 0.5 s | ~0 MB（采样不到） |
| 4 | 593 | 2.5 s | 401 MB |
| 8 | 846 | 3.0 s | 340 MB |
| 12 | 1112 | 6.7 s | 807 MB |
| 13 | 1133 | 10.8 s | 1676 MB |
| 16 | 1208 | 14.5 s | 2408 MB |
| 20（全量） | 1371 | 17.4 s | 2453 MB |

**渐变、无单点断崖** ⇒ 是"随 decl 数累积"的效应，不是某个具体 prelude 文件的交互。
（hdl-crossclock / hdl-misc-io 两文件边际最贵，各 +650~870 MB，但只是斜率上的高点。）

排除项：

- **不是线程栈**：`L13_STACK_MB` 取 64/256/1024 时峰值分别 2542/2363/2595 MB。
- **不是 allocator 未归还**：`MIMALLOC_PURGE_DELAY=0` 只降 12%（2497 → 2196 MB）。

## 3. 分阶段分解（全量 hdl prelude）

`L13BENCH_MEM=1`，按阶段报 live/peak：

| 阶段 | live | peak |
|---|---:|---:|
| parse（34 文件、1371 decls） | 7.6 MB | 8.8 MB |
| parity: ref 一趟 | 580 MB | **685 MB** |
| parity: twin 一趟 | 582 MB → **2808 MB** | 2815 MB |
| parity: ref pretty 一趟 | 2808 MB | 2912 MB |
| parity: twin pretty 一趟 | 2808 → **3892 MB** | 3899 MB |

- **参考版一趟只吃 685 MB**，且跑完大部分会归还；
- **孪生一趟 +2.2 GB**，pretty 再 +1 GB；
- parse 只要 7.6 MB —— "prelude 源码太大"完全不是原因。

## 4. 根因（孪生侧）

产品加载器 `Tycker::prime_resident`（`bump_spine_iter/entry.rs`）在

- 每个 prelude **文件边界**（`prelude.file_ends`），以及
- arena 累计分配超 `PRIME_COMPACT_BYTES`（384 MB）时

调用 `compact_state` **就地压实**，arena 只承载可达状态。

而 bench 口径 `Tycker::bench_check_nf_bounded` 走 `elab_all(bump, ast)`：把整串
prelude 当**一个文件**，一个 arena 从头用到尾，**一次压实都没有** —— 于是每个
decl 的中间 garbage 全部累积。

即：**bench 口径测的不是产品装载路径**，峰值 RSS 不代表产品行为。

## 5. 第一处修复（2026-11-20）

`bump_spine_iter/entry.rs` 新增 `bench_check_nf_bounded_files(ast, nat_after, file_ends)`：
镜像 `prime_resident` 的压实纪律（文件边界 + `PRIME_COMPACT_BYTES`），
`file_ends` 为空时回落旧口径。`l13bench` 的 `--with-prelude` 路径改用它。

实测（同一批命令）：

| 语料 | 修复前峰值 | 修复后峰值 |
|---|---:|---:|
| 空文件 + 全量 hdl prelude | 2458 MB | **1616 MB** |
| `01-basics` | 3705 MB | **1764 MB** |

`nf` **逐位不变**（219 / 219 / nf 列全等），证明压实不改变语义。
pretty 对比（两次全量装载）在大语料上关闭（>512 decls 时退回尺寸口径），
省下约 1 GB，且它本来的用途只是给 `NF-DIVERGE` 解释差异。

## 6. 根因：bench 把 println 的**展示 nf** 当成了求值（已修）

### 6.1 现象

`examples/hdl/10-bundle.typort` 在参考版上冲到 >12 GB 仍不出判定行；而
`01-basics` 只要 763 MB。两者 prelude 相同、字段规模不同，早期用"字段数扫描"
看到的是每字段约 2.3× 的增长，容易误判成模块树渲染或 `#[derive(Bundle)]` 的
问题（本文早先版本就是这么写的，**已被证伪**）。

### 6.2 决定性证据：一次 nf 物化 7M 节点

在 `Infer::nf` 上加慢调用探针（`L13BENCH_PROF=1` 时 >50ms 打印），4 字段 bundle
"两个实例 + 一条 `println(moduleTreeVL(...))`" 的用例给出：

```
[MEM] ...
[NF-SLOW] 2095ms size_in=9 size_out=7078582
[NF-SLOW] 2089ms size_in=9 size_out=7078582
```

**输入项只有 9 个节点，归一化结果 707 万节点**——而且全程 `nf` 的**次数不变**
（3598 次），只有单次成本涨了 112×。也就是说：不是算法指数，是**某一次 nf 把
一个巨大的值物化成了项**。

### 6.3 根因

参考版 `Decl::Println` 的处理（`elaboration.rs:1716`）：

```rust
if self.defer_println { /* 入队延迟 */ } else {
    let t_pretty = super::pretty_tm(0, cxt.names(),
        &self.nf(&cxt.decl, &cxt.env, &tm));   // ← 纯展示成本
    DeclTm::Println(tm, t_pretty, span)
}
```

`t_pretty` 是**纯展示**用的：把 println 的实参求值再 quote 成字符串。对
`println(moduleTreeVL(m.tree))` 来说，这一步会把整个模块树渲染结果**物化成一个
项**，而模块树随实例数 × 字段数增长——于是内存/时间爆炸，且与 `#[derive(Bundle)]`、
`:=`、`asSlave` 都无关（那些变体只是**间接改变了实例数与 println 的规模**）。

**产品不受影响**：`lib.rs:2597` 的 LSP 路径一直设 `defer_println = true`，展示
nf 从不在求值主路径上。**只有 bench（走 CLI `run()` 口径）把它算进去了**。

### 6.4 修复

`L13_namespace::bench_check_nf_bounded`（hook 变体）入口加：

```rust
infer.defer_println = true;   // bench 只读末 def 的 nf，println 展示 nf 无用
```

与 LSP 口径对齐，把纯展示成本从 bench 里拿掉。

### 6.5 修复实测

| 用例 | 修复前 | 修复后 |
|---|---:|---:|
| `01-basics` | 762 MB / 9.6 s / nf=219 | **763 MB / 9.6 s / nf=219**（不变） |
| 4 字段 bundle × 2 实例 | 1782 MB / 17 s | **760 MB / 9.6 s** |
| `10-bundle`（AxiLite 6 字段） | **>12 GB，跑不完** | **767 MB / 9.6 s / nf=302** |

`nf` 判定对常规用例**逐位不变**（01-basics 仍是 219），bundle 类从"跑不完"变成
"9.6 秒出判定"。

> 教训：这次是**第二次**"bench 口径 ≠ 产品口径"造成的假爆炸（第一次是孪生
> bench 不压实，§4）。定位同类问题优先问一句"这个成本产品真的会付吗"。

## 7. 口径落地（2026-11-20）

hdl 基线采集**只需要参考版判定**（P2/P3 改的是参考版与产品面；孪生对位另算）。
`l13bench` 已加：

- `--ref-only`：跳过 `nf_parity` 的孪生趟与 fast/fast_ss 计时，判定行标
  `(ref-only)`；参考版单跑失败时报 `REF-FAILED`（不再误报 BOTH-FAILED）；
- `--eval-budget <ms>`：把参考版趟包进 `eval_budget::scope(ms)` + `catch_unwind`，
  超时记 `BUDGET aborted (…ms, ref-only)` 并跳过计时（**注意 §6：本 bug 不在
  eval checkpoint 上，预算拦不住它**）。

实测（`--ref-only` + 看门狗）：`01-basics` 9.6 s / 762 MB（含孪生时 1764 MB）。

下一步：bundle 指数膨胀按 §6 单独修（产品面 bug）；修好前 hdl 基线里的 bundle 类
示例只能记 `MEM-CAP` 行，其余照常采。

## 8. 解封：hdl 基线 32/32 全量采完（2026-11-20）

修完之后 hdl 基线采集能力恢复：

- 口径：`l13bench --ref-only`（参考版判定；P2/P3 改的是参考版与产品面），每例经
  `tools/bench_watchdog.ps1`（-TimeoutSec 180 / -CapMB 4000），采集器
  `tools/l13_rebase_baseline.ps1 -Mode hdl -RefOnly`；
- 结果：27 个 hdl 例子全部采到，基线表 **32/32**；
- 单例成本：**9.4–10.7 s / 761–775 MB**（此前 10-bundle 是 >12 GB 跑不完）；
- 3 条 `REF-FAILED (参考版未跑完)`：23-verilog-compat / 24-verilog-practice /
  25-verilog-reset。两版一起跑（不加 --ref-only）是 BOTH-FAILED——属**既有缺口**
  （与 11-17 基线里 alu.typort 的 BOTH-FAILED 同族），不是本次改动引入，记为待查。

> 采集器同时修了三处：判定行从看门狗返回的**对象**里取（PS 5.1 下多行字符串会被
> 拍平成空格分隔的单串）；看门狗用 UTF-8 读子进程输出（判定行含中文，否则乱码写表）；
> 脚本恢复单 BOM（重复 BOM 会让 param 块解析失败）。
