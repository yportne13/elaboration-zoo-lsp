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

## 6. 未解

- `examples/hdl/10-bundle.typort`（`#[derive(Bundle)]` 展开）在修复后**仍然**
  冲过 8 GB 被抓停 —— 炸弹在**用户文件段**（derive 展开后的 impl 检查），
  不在 prelude 装载。下一步按参考版单独定位（见 §7）。
- 参考版一趟 685 MB 对 bench 仍偏高，但已不是阻塞项。

## 7. 口径决定（2026-11-20）

hdl 基线采集**只需要参考版判定**（P2/P3 改的是参考版与产品面；孪生对位另算）。
下一步给 `l13bench` 加 `--ref-only`：跳过 `nf_parity` 的孪生趟与孪生计时，
判定行标 `(ref-only)`，基线表同批换口径并重冻。
