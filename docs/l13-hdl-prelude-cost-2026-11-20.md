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

## 6. 未解：bundle 模块树渲染在**参考版**上指数膨胀

用 `--ref-only` + 逐 decl 探针（`[MEM] ref decl=…`）把 10-bundle 拆到单条声明：

- 炸弹是最后一条 `println(moduleTreeVL(bundleTop.create.tree))`；
- 前置 decl 全部正常（prelude 1371 条 + `enum AxiLite` / `impl` / `AxiLite.create` /
  `class bundleTop` / 第一条 `println`），跑到 decl=1377 时 live 只有 **684 MB**；
- `bundleTop.create.tree` 本身**很便宜**（`println(bundleTop.create.tree)` 正常出
  nf=533 / 763 MB），炸点只在 `moduleTreeVL`（Verilog 渲染）这一条路径上。

字段数扫描（`#[derive(Bundle)]` + 1 条 `m := m` + `moduleTreeVL`）：

| 字段数 | nf | 峰值 RSS | 墙钟 |
|---:|---:|---:|---:|
| 1 | 47 | 762 MB | 9.6 s |
| 2 | 91 | 761 MB | 9.6 s |
| 4 | 179 | **1782 MB** | 12.9 s |
| 6（AxiLite） | — | **>3.6 GB（被抓停）** | — |

nf 随字段数**线性**（≈44/字段），内存却超线性（4 字段已 2.3× 于 2 字段）——
说明爆炸在**检查期**而不是最终范式大小。

`--eval-budget 5000` 也没能在 3.3 GB 之前中止 ⇒ **不在 `eval` 主循环的
checkpoint 上**（更可能在 force/nf/quote 或精化上下文复制路径）。

### 6.1 触发器：`:=` 批量赋值（derive(Bundle) 生成的那条）

同一份 4 字段 bundle，只差一句 `m := B4.create.asSlave`：

| 变体 | 峰值 RSS | 墙钟 | nf |
|---|---:|---:|---:|
| 不含 `:=` | 768 MB | 9.5 s | 179 |
| 含 `:=` | **1783 MB** | 12.9 s | 179 |

⇒ 爆炸在 **`#[derive(Bundle)]` 生成的逐字段 `:=` 批量赋值**的求值上，
不在模块树渲染、不在 derive 展开本身（`class top4` 单独求值很便宜）。

字段数扫描（含 1 条 `:=`，`Bool` 字段）：

| 字段数 | 峰值 RSS | 墙钟 | nf |
|---:|---:|---:|---:|
| 1 | 762 MB | 9.6 s | 47 |
| 2 | 761 MB | 9.6 s | 91 |
| 3 | 834 MB | 10.0 s | 135 |
| 4 | **1782 MB** | 12.9 s | 179 |
| 5 | **>4000 MB（被抓停）** | — | — |
| 6（AxiLite） | >3.6 GB（被抓停） | — | — |

从 3 字段起每加一字段约 **2.3×** 内存 ⇒ 指数。

### 6.2 函数级归因（`L13BENCH_PROF=1`）

4 字段，含/不含 `:=` 的差值（其余完全相同）：

| 计数器 | 不含 `:=` | 含 `:=` | 差 |
|---|---:|---:|---:|
| check / infer_expr | 134846 / 383312 | 134890 / 383420 | ≈0 |
| unify / solve_trait | 734196 / 79718 | 734230 / 79728 | ≈0 |
| eval | 15.51M | 19.50M | +3.99M |
| force | 13.72M | **26.94M** | **+13.2M** |
| v_app | 9.55M | 16.97M | +7.4M |
| force_leaves | 8.75M | 20.27M | +11.5M |
| nf 次数 | 3598 | 3598 | 0 |
| nf 独占耗时 | 16 ms | **1805 ms** | **112×** |

**类型检查侧（check/infer_expr/unify/solve_trait）完全不变**——不是精化上下文、
不是合一、不是类型级物化；是**求值/强制**侧，且 `force` 调用量翻倍、
`nf` 每次调用的成本涨了 112 倍。

> 这是**产品面可见**的问题：LSP 对一个 bundle 模块做「生成 Verilog / 悬浮渲染」
> 会走同一条 prelude 求值路径并同样爆掉。后续单独开一单（P2 首个实质 bug）。

### 6.3 下一刀（留给下一轮）

1. 看 `parser/derive.rs` 的 `build_bundle_body` 生成的
   `let __b0 = this.f0 := that.f0; …` 在求值期是否对同一子项**重复求值**
   （nbe 下 `let` 若不被共享，嵌套 let + 二次引用会指数化）；
2. 看 `hdl-types.typort` 里逐类型 `:=`（UInt/Bits/Bool 版）与
   `createSignalExpr` 的组合是否每次重建整张模块表达式表；
3. 若确认是"每字段一次 force 整棵表达式表"，优先改增量追加 + let 共享。

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
