# smalltt 参考侧：本机安装、构建与同机基准脚本

本目录固化「把 András Kovács 的 smalltt 在我们本机跑起来并与 L07–L10 同机对比」
所需的脚本。smalltt 源码本身不 vendored（clone 到仓库外即可），这里只保存可复现的
构建/测量/解析/对比流程。对应报告：`docs/smalltt-bench-2026-11-14.md` §11。

## 1. 安装 Haskell 工具链（Windows，一次性）

用 GHCup 官方 Windows bootstrap（只装 ghcup + msys2，GHC 版本与 smalltt 的
`stack.yaml`（lts-21.17）对齐为 **9.4.8**）：

~~~powershell
# 下载 https://www.haskell.org/ghcup/sh/bootstrap-haskell.ps1 后：
powershell -NoProfile -ExecutionPolicy Bypass -File bootstrap-haskell.ps1 -Minimal
# 安装 GHC / cabal（GHCup 默认在 C:\ghcup）
& C:\ghcup\bin\ghcup.exe install ghc 9.4.8
& C:\ghcup\bin\ghcup.exe install cabal latest
~~~

安装后把 `C:\ghcup\bin` 与 `C:\ghcup\msys64\mingw64\bin`、`C:\ghcup\msys64\usr\bin`
加入 PATH（本目录脚本不自动改 PATH，请在调用前设置，或使用 GHCup 的 env 脚本）。

## 2. 构建 smalltt（本机遇到的 cabal index 问题与规避）

本机 `cabal update`（hackage index 约 140 MB）会卡住，因此采用 **全本地依赖**：

1. 依赖里只有 `flatparse-0.5.0.1` / `utf8-string-1.0.2` 来自 Hackage，其余是
   GHC boot libs 或 git pin。下载这两个 tarball 并解包到任意 vendor 目录；
2. 把 `cabal.project.smalltt`（本目录）复制到 smalltt 根目录为 `cabal.project`，
   按需修改其中 `packages:` 的 vendor 路径；
3. 把 `C:\cabal\config` 里的 `repository hackage.haskell.org` stanza 注释掉，
   并置 `active-repositories: :none`（避免 cabal 要求 package list）；
4. 构建：

~~~powershell
cd <smalltt clone>
cabal build -w ghc-9.4.8 exe:smalltt --jobs=6
cabal list-bin -w ghc-9.4.8 exe:smalltt   # 得到 smalltt.exe 路径
~~~

> 改造 `C:\cabal\config` 会影响本机其它 cabal 工程；只想跑本基准时不打紧，
> 恢复办法：把 repository stanza 注释恢复、删除 `active-repositories: :none`，再
> `cabal update`。smalltt 的三个 git pin 与 `stack.yaml` 的 extra-deps 完全一致。

## 3. 跑官方基准

~~~powershell
# 每个 .stt 文件一个进程：:l 首载 + :r 热重载 Rounds-1 次，然后 :q
powershell -File run-smalltt-bench.ps1 -SmallttDir <smalltt clone> -OutDir <日志目录> -Rounds 3
~~~

脚本要求 PATH 里能找到 `cabal`（以及可选 `ghc-9.4.8` shim）；smalltt 的 RTS 参数
由 cabal 的 `-with-rtsopts= -A64M -s -N8` 内置。输出为每个用例一个 `.log`。

## 4. 解析与同机对比

~~~powershell
python parse-smalltt-bench.py --dir <日志目录> --out <日志目录>\parsed.json
python same_machine_compare.py --parsed <日志目录>\parsed.json \
    --our-dir <repo>/target/smalltt_bench/final \
    --our-dir <repo>/target/smalltt_bench/same_machine
~~~

`parse-smalltt-bench.py` 解析 REPL 的 `<name> elaborated in 0.xxx s` /
`normalized in` / `total load time` 行，同一 name 多次 `:r` 按 min 汇总。
`same_machine_compare.py` 把 smalltt 的 per-def 时间与我们的 `smallttbench` CSV
（`CASE,<layer>,<case>,<size>,...` 行）按用例/尺寸映射成对照表（stdout Markdown）。
映射表覆盖 conv_eval / asymptotics / stlc 三个家族。

## 5. 注意

- smalltt 的 `[nftime]` 只计 quote+eval；我们侧表中 nf 口径用 `ref_nf - ref_check`
  估计同口径（forcetree 的 check 占比较高、减法误差略大）。
- 本机 smalltt 实测与 README 公布值可差数倍（见报告 §11.5），跨机器引用公布值会
  系统性扭曲差距结论。
