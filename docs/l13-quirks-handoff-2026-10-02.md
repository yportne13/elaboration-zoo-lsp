# L13 quirk 修复轮交接文档（2026-10-02）

本文档交接"prelude 补充轮发现的引擎怪癖修复"的当前进展。上一份分析文档
[docs/l13-quirks-analysis-2026-10.md](l13-quirks-analysis-2026-10.md) 记录了
四项怪癖的根因与修复草图；本文档记录**已提交的修复**、**工作区里未提交的
三个进行中修复**（每个的完成度、验证状态、剩余工作），以及排查过程中发现
的环境坑与独立遗留问题。

> **状态更新（2026-10-08）**：§2 的三个进行中修复已全部验证并落地，另修掉
> 一颗会拖垮主机的内存地雷——**先读 §0**。§1–§5 是交接当时的原始记录，保留
> 供追溯；其中"未提交/未验证"的表述以 §0 为准。

> 环境提醒（先读）：本会话所在 shell 对含 heredoc / 大量中文的命令会间歇性
> 报伪错误（exit 127），**文件内容一律用编辑器工具写，不要走 heredoc**；
> cargo 会因残留进程持锁而"假挂起"（管道 tail 还会缓冲输出造成日志空白）——
> 测试请重定向到文件再读文件；L13 lib 测试过滤器大小写敏感
> （`cargo test --lib L13_namespace::`，小写会静默跑 0 个）。

---

## 0. 落地结果（2026-10-08：接手收尾）

**§2 的三个进行中修复已全部验证并落地；另修掉一颗主机级地雷。工作区现已
干净（只剩 §4-5 那两个与本轮无关的历史未跟踪文件）。四个 commit：**

```
3c5d8f3c fix(l13): R4 大数显示压缩（参考版 quote_dec）+ 延迟 println 排水兜底
ddd0fb9b feat(l13): Level A 终止性检查（双引擎成对）+ 12 项 allowlist
c22c3f26 fix(parser): Q2 缩进感知续行——EndLine 不再是 spine 实参硬终结符
0f19ae8d fix(l13): Nat succ 链展开内存护栏——修掉 121.8GB 提交量耗尽主机
```

`0f19ae8d` 不在原交接计划内，原因见下——它**必须先于任何全量 lib 套件运行
落地**，否则跑一次就炸一次机。

### 0.1 内存事故（性质：跑一次全量 lib 套件 = 一次主机级内存耗尽）

§2C 末尾那个"编不过、改完未重跑"的 lib 侧钉
`eval_budget_tests::twin_big_nat_display_pending_watchdog_catches` 是引信。
它跑 `println (nat_mul 100000 100000)`（k = 10^10）：孪生显示位 quote 把原生
Nat 展开成 succ 链，而 `bump_spine_iter/quote.rs::quote_nat_chain`、参考版
`mod.rs::quote_nat`、两版 prim 的 NatAdd/NatMul k 层回退链**全是
`for _ in 0..k` 的裸分配循环，循环内零 checkpoint**（`eval_budget::tick` 只挂
在两版 eval 主循环）——预算到期也拦不住，内存先到极限。

本机实锤（Windows 资源耗尽检测器 **事件 2004**）：

| 时间 | 进程 | 虚拟内存 |
|---|---|---|
| 23:43:05 | `elaboration_zoo_lsp-647b90ef7f32ef90.exe` (19804) | **121.8 GB** |
| 23:21:35 | 同一二进制 (7212) | **118.6 GB** |
| 21:53:32 | 更早一次 ⇒ 主机非正常关机，22:26 重启（事件 41 + 6008） | — |

取证判据（下次同类问题照此看）：lib 日志里 569 个测试全 `ok`、0 失败，却
**没有 `test result` 汇总行**——进程被内存耗尽打断；唯一没打 `ok` 的就是它。
该测试在之前的会话里从未真正执行过（编译错误挡住了），所以交接时没有任何
人见它跑过。

**修法**（`0f19ae8d`）：`eval_budget::NAT_CHAIN_LIMIT = 2^22` 节点
（≈ 单次展开 ≤0.4 GB）+ `guard_nat_chain`（超限**立即**中止、零分配）；新增
`NatChainOverflow` payload 并纳入 `is_timeout` 族 ⇒ 既有边界按"放弃本次引擎
运行"处理：孪生作废 resident → 回落参考版（参考版 nf 走 `quote_dec`，十进制
输出仍正确）。6 处链展开全部加护栏，链循环补 `tick` 作时间第二道；prim 侧
超限保持"卡住"（返回 None）。该测试改判为钉护栏本体。
**实测**：定向 6/6 通过（8.9s，原为挂死）；全量 lib 571 passed / 0 failed
（65s），测试二进制峰值 **5.5 GB**（原 121.8 GB）。
阈值取 2^22 的依据：仓库内全部语料与测试用到的 Nat < 10^4，低 3 个数量级，
不改变任何现存输入的行为。

### 0.2 全量门禁（在最终代码树上跑过两次）

`GATE_FULL=1 bash tools/gate_l13.sh` → **fail=0**（total 380s）：

```
[lib]      571 passed / 0 failed   (66s)
[parity]   586 passed / 0 failed   (66s；不 skip，511 个重复面也跑)
[twin_lsp]  27 passed / 0 failed   (90s；examples 全树双引擎)
[hdl042]     2 passed / 0 failed
```

跑法注：本机 `bash` 默认解析到 WSL（`C:\Windows\system32\bash.exe`，其中
**没有 cargo**）。要跑真脚本请用 Git Bash：`D:\git\Git\bin\bash.exe`（cargo /
grep / sed 都在 PATH）。另外建议外挂内存闸（每 0.5s 采样进程 WS，超阈值
`taskkill /T`）：本次两次门禁都在 10 GB 闸下跑，峰值 5.5 GB 未触发。

### 0.3 §2B（交接时"完全没有跑过"的那件）验证已补齐

- parser 内联 AST 形状钉（`spine_continuation` 模块）随 lib 571 过；
- `tests/spine_paren_args` **12 passed / 0 failed**：Q2 五件（def 体续行 /
  match 臂 + let 链续行 / 花括号块更深缩进续行 vs 同缩进仍断开 / calc 同缩进
  `(`-起头步骤 / 逗号跨行调用读法不变）+ 双引擎 parity 冒烟；
- `tests/known_bug_pins` **8 passed / 0 failed**（旧报错形态无需翻转）；
- `examples/adder_proof.typort` / `theorem_proving.typort` 的 calc 招牌形状
  （10+ 处同缩进 `(`-起头步骤）由 `twin_engine_tests`（27 件）双引擎端到端
  覆盖——"calc 不被 Q2 击穿"这条承重墙因此有门禁级证据。

### 0.4 顺手修掉的两处缺陷

- `elaboration.rs` 的 allowlist 注释被重复粘贴两遍（上一轮编辑残留），已合并；
- `machine.rs` Println 臂注释谎称"显示位走 quote_dec"（实际仍走 `quote`，与
  §2C"孪生侧未接线"自相矛盾），已据实改写并写明接线前提与当前兜底链。

### 0.5 仍未做（原样留给下一轮）

见 §4：孪生显示压缩接线（需先对齐值层 succ 折叠）、大字面量 elaboration 慢
路径、声明级 opt-out 语法、Level B/C 健全档、循环证明可靠性专项。

---

## 1. 已提交（全部通过过 tools/gate_l13.sh，最后一次全量门禁 fail=0）

```
c449c08 docs(l13): quirk 分析文档同步修复落地结果（5 已修 / 2 遗留）
c77391b fix(l13): 错误级联三面修复——def 失败降级 / inherent 逐方法隔离 / trait impl 部分注册
9a04ab2 feat(l13): 求值预算看门狗——循环定义从"LSP/CLI 永久冻结"降级为可诊断错误
685a70b fix(l13): XCell::Obj 挂起选择子 + 具证唯一不推迟——cong+字面 lambda 解锁
632d064 fix(l13): 成员访问接收者补 insert——裸构造器 lnil.show/None.and 定向
820f9aa fix(parser): SPINE_ESCAPE 递归摊平——实参位括号组 run≥2 不再错分组
3971cfe docs(l13): prelude 补充轮引擎怪癖四项根因分析
...（更早：prelude 标准库补充轮的 6 个 commit，5794d51..e12a25b）
```

这些是干净的：每个都经过全套门禁（lib 569 / parity / 孪生 LSP / hdl042）。

## 2. 交接时的状态：工作区未提交的三个进行中修复（历史记录；均已于
2026-10-08 落地并验证，见 §0）

三个子代理并行做的，会话中途两次撞账号 5 小时限额 + 会话重启，**未做单独
commit**。文件所有权可切开（§3 有分 commit 的映射）。按完成度排序：

### 2A. Level A 终止性检查 —— 最完成，我亲手验证过

**文件**：`src/L13_namespace/elaboration.rs`（参考版 walker `TermWalker` +
`check_def_termination` + Def 臂挂载点，check 与 wrap 之间）、
`src/L13_namespace/bump_spine_iter/termination.rs`（**新文件**，孪生版
`Walker` + `ALLOWLIST`，与参考版逐句对齐）、
`src/L13_namespace/bump_spine_iter/machine.rs`（孪生挂载点）、
`src/L13_namespace/bump_spine_iter.rs`（一行 `mod termination;` 声明）、
`src/L13_namespace/termination_check_tests.rs`（**新文件**，13 个测试）、
`src/L13_namespace/mod.rs`（测试注册一行）。

**判据**（不健全的语法启发式，防呆非证明）：体里每个自调用要求至少一个实参
是「结构位置模式变量」（某 match 的模式变量，且 scrutinee 链下落到 def 参数/
已标模式变量；实参允许这类模式变量的构造器应用）。已知放行 ping-pong 换参。
裸自引用（`def p: Eq 1 2 = p`）拒——**顺手封掉了最简循环证明洞**。

**我做的收尾**（相对 agent 原样）：
- 去掉两侧 `TEMP-PROBE` 放行（原样是"永远 Ok + eprintln 枚举误杀"的审计态）。
- 全量枚举参考侧误杀（一次 prelude 装载收集），allowlist 定为 12 项，两侧同步：
  `nat_div / nat_rem`（nat.typort 重复减法回退，加载后被 primop 换装）、
  `combReach`（hdl-check-graph worklist）、`gcd`（examples 欧几里得）、
  `log2Up`（折半度量）、`metaDiv`（同 nat_div 形）、`countOnesExprAt`（位宽
  对半拆分）、`designVisit`（worklist）、`bbParamsDeclStr/bbInstItemsStr`
  （scrutinee 是 `list_reverse(gs)` 计算值）、`NonEmpty.last`（struct 构造器
  包裹——`is_ctor` 只认 SumCase 注册形状，struct mk 形状待精化，见 TODO）、
  `adder_tree`（折半经 `adder_tree_step` 计算值）。
- **tuple-scrutinee 精化**（两侧 `chain_level`）：构造器应用（含 `(a, b)`
  元组的 TupleN.mk spine）当全部显式实参自身是链根时视为链根——修掉
  legacy `test`（`match (a, b)` 对模式）与 `vec_adder_correct` 两个误杀。
- 修 3 个测试输入 bug（`let` 多语句缺 `;`、`int_neg 2` 须 `int_neg (ofNat 2)`、
  测试枚举构造器改名避开 prelude `lnil/lcons` 裸名抢先）。

**已验证**（本会话实跑）：
- `cargo test --lib termination_check` → **13 passed / 0 failed**（21s）
- `cargo test --lib L13_namespace::` → **569 passed / 0 failed**（69s）
- `cargo test --test l13_fast_parity -- --skip "L13_namespace::"` → **15 passed**
- `cargo build --bin typort` → 0 error

**未验证**：`cargo test --test twin_engine_tests` 全套（在 2C 的孪生显示位
回退之后只单跑过 `twin_information_diagnostics` 一件 → passed）。
**门禁尚未在终止检查激活的状态下跑过**。

### 2B. 解析器缩进续行（Q2）—— 完成度未知，风险最高

**文件**：`src/L13_namespace/parser/lex.rs`（+61 行）、
`src/L13_namespace/parser/mod.rs`（+321 行，含内联测试）、
`tests/spine_paren_args.rs`（+168 行）。

**设计**（依分析文档 §2.4）：EndLine 词法 token 记录"下一行缩进列"；p_spine
实参循环只在**续行缩进更深**时消费换行继续解析实参，失败回退。同缩进不粘
（守护 `calc` 块——分析文档明确：无条件跳行会把整个 calc 宏击穿）。

**状态：本会话完全没有跑过它的任何测试**（agent 实现+写测试后在重启中丢失
报告，我接手时优先收尾了 2A/2C）。**下一步必须先验证它**：
```
cargo test --lib L13_namespace::                          # 内联 parser 测试
cargo test --test spine_paren_args -- --skip "L13_namespace::"
cargo test --test known_bug_pins                          # 若钉了旧报错形态需翻转
```
重点守护用例（分析文档 §2.4/§2.5）：`examples/adder_proof.typort` 的 calc
多步骤块（10+ 处同缩进 `(` 开头步骤）、花括号块同缩进语句、`case` 臂、
逗号跨行调用 `f(a,\n b)`。探针参考 `target/quirks/fix_continuation/`
（agent 放置；target/ 可能被清理，必要时按分析文档 §2.3 的三种失效形态重建）。

### 2C. 大数显示压缩（R4）—— 参考侧完成，孪生侧明确暂缓

**参考侧（完成）**：`src/L13_namespace/mod.rs`（`quote_dec`：原生
`Val::Nat(k)` → 十进制 `LiteralIntro`；`nf()` 改走 `quote_dec`，附调用方
审计注释）、`src/L13_namespace/bump_spine_iter/quote.rs`（`quote_go` 加
`nat_dec` 参数，`quote_iter` 包装传 false —— 引擎内部消费方（unify/pattern/
rename）的 succ 链形状逐字节不变；`nat_dec=true` 时 `XCell::Nat(k)` 直接
`LiteralIntro(k.to_string())`）。

**孪生侧（未接线）**：`Machine::quote_dec` 已写好（machine.rs，
`#[allow(dead_code)]`），但 println 显示位**已回退为 `quote`**——原因：
孪生值层不把 `succ(原生 Nat)` 折叠成 `Nat(k+1)`（参考版 eval 折叠），
nat_dec 路径会把 `println (succ (nat_mul 3 4))` 渲染成 `12 + 1`，参考版是
`13`，`twin_engine_tests` 的诊断 parity 分叉（本会话实测复现）。
另一个更深的值层分歧：`nat_pow 2 64` 溢出后，孪生值是 64 层嵌套
`nat_mul 2 (...)` spine（渲染 `2 * {2 * {...}}`），参考版折叠成单层
`2 * 9223372036854775808`。**接线孪生显示前需先对齐值层语义**（succ 折叠
进 eval，或 nat_dec 路径内做 succ-折叠特判 + 溢出 spine 形状对齐），急不得。
孪生大数显示挂死当前由看门狗兜底（LSP 默认预算会中止并回落参考版）。

**测试**：`tests/bignum_display.rs`（我改写为钉当前口径：参考版大数/溢出
十进制、小数基线双引擎、多行大数字面量用例已删——见独立问题 §4-3）；
孪生兜底钉在 lib 侧 `src/L13_namespace/eval_budget_tests.rs::
twin_big_nat_display_pending_watchdog_catches`。
另在 `src/lib.rs` 延迟 println 排水点（`println_jobs` 的 nf 处，约 2785 行）
补了 `catch_unwind + is_timeout` 兜底（原先 ElabTimeout 会从该排水点逃逸）。

**已验证**：`cargo test --test bignum_display` → **3 passed / 0 failed**
（最终形态）。
**未验证**：`cargo test --lib eval_budget` —— 最后一次跑编不过，错误是
我追加的测试里 match 臂类型（`observe_user` 返回 `Result<(), Error>`，
catch_unwind 后是 `Ok(Result)`），**已修（`Ok(res)` 臂），修复后未重跑**。
下一次跑应期望 5 passed（原 4 + 新钉）。

## 3. 分 commit 的映射（交接时的建议；实际已按 §0 落成 4 个 commit）

实际拆分与本映射一致，仅**新增一个安全提交**（内存护栏，排在最前）：
`0f19ae8d` 护栏 → `c22c3f26` continuation → `ddd0fb9b` termination →
`3c5d8f3c` bignum。`mod.rs` / `machine.rs` / `quote.rs` 的混合 hunk 按
`git apply --cached` 拆分（拆分脚本与四个 patch 见
`target/handoff_verify/split.py`、`patch_{A,B,C,D}.patch`，target/ 不入库）；
拆完校验：工作区无残留未提交改动 ⇒ HEAD 树与门禁跑过的树逐字节一致。
分 commit 的映射建议保留如下（供复核拆分是否合理）：

- **termination**：`elaboration.rs`、`bump_spine_iter/termination.rs`(新)、
  `bump_spine_iter.rs`(一行 mod)、`machine.rs` 的**终止检查挂载 hunk**、
  `termination_check_tests.rs`(新)、`mod.rs` 的**注册 hunk**。
- **continuation**：`parser/lex.rs`、`parser/mod.rs`、`tests/spine_paren_args.rs`。
- **bignum**：`mod.rs` 的 **quote_dec/nf hunk**、`bump_spine_iter/quote.rs`、
  `machine.rs` 的 **quote_dec 包装器 hunk**（dead_code 注释）、
  `tests/bignum_display.rs`、`lib.rs` 排水兜底、`eval_budget_tests.rs` 新钉。

`mod.rs` 与 `machine.rs` 混了两个修复的 hunk，需 `git apply --cached` 拆分
（本会话已有先例：`awk '/^@@/{h++} h<N{print}'` 提单 hunk）。

**建议顺序**：先跑 §2B 的验证命令把解析器续行钉死（风险最高）→ 三个 commit
→ `bash tools/gate_l13.sh` 全量门禁 → 通过后 symc 分析文档落地结果。

## 4. 独立遗留问题（不在上述三个修复里）

1. **循环证明可靠性（R1）**：Level A 只封了最简形态（`def p: Eq 1 2 = p`）。
   经 eliminator transport 的变体、worklist/换参绕过仍可造循环证明（allowlist
   里每一项都是"真非结构递归"，一旦被滥用于命题就有风险）。与 §2A 的
   allowlist 退出机制（声明级 opt-out 语法）是同一议题，见分析文档 §4.4。
2. **孪生大数显示**：§2C 未完成部分（值层 succ 折叠 / 溢出 spine 对齐）。
   **内存安全一面已由 §0.1 的护栏兜住**（超限立即中止 + 回落参考版），本条
   现在只剩"孪生自己就能直接显示十进制"的体验/性能项。
3. **大字面量 elaboration 慢路径**：`println (nat_add 1000000000 1000000000)`
   这类**大十进制字面量**本身走 succ 链展开，字面量构造即耗分钟级——与
   R4（显示压缩）无关，是 elaboration 侧问题（可查 parser/elaboration 的
   数字字面量处理，理想是直接建原生 Nat）。本会话实测：1e9 字面量的多行
   用例超 60s，已从测试中移除。
4. **Level B/C 终止检查**：Level A 是不健全防呆；健全档（同位结构递归 /
   单函数 SCT-lite）与 allowlist 清零路线见分析文档 §4.3。
5. **未跟踪的历史文件**：`docs/l13-perf-replace-2026-09-27.md`、
   `docs/wip/l13-perf-replace-2026-09-27/` 是本轮之前就存在的未跟踪文件，
   与本次工作无关，不要顺手提交。

## 5. 排查时发现的环境/工具坑（省下下一位的时间）

- 本环境 shell 对 heredoc / 大量中文的复合命令会间歇性 exit 127（命令实际
  没执行）——用 Write 工具写文件；失败重试或拆小。
- 残留 cargo 进程会持 target 目录锁，新命令表现为"无输出长时间挂起"；
  管道 `| tail` 会把输出缓冲到结束才显示，误判为卡死。**重定向到文件再读**。
- 测试二进制间共享进程级 prelude 缓存（首测付装载费）；`run_with_prelude`
  首错即中止（只能钉第一个错误），"继续型"行为（错误恢复/诊断收集）要用
  `tests/error_recovery_backend.rs` 的 Backend 驱动模式。
- 诊断 parity 的权威是 `tests/twin_engine_tests.rs`（27 件）与
  `tests/l13_fast_parity.rs`；动 println 渲染/错误文案前先看它们。
- **跑重活（全量 lib / 门禁）一定外挂内存闸**：本机 32 GB RAM + 56 GB
  页面文件，2026-10-07 就被一个测试的 121.8 GB 提交量拖到系统级耗尽并重启
  （§0.1）。闸 = 每 0.5s 采样 `cargo|rustc|<测试二进制>` 的 WS，超 10 GB
  `taskkill /F /T /PID`。另外别只看 "exit 0"：被内存打死的进程可能留下
  一堆 `ok` 却没有 `test result` 汇总行。
- 重定向日志别混编码：`Out-File -Encoding utf8` 起头再用 `*>>` 追加会写成
  UTF-8 BOM + UTF-16LE 混合体，`Select-String` 直接静默匹配不到（本次踩过）。
  要嘛全程 `| Out-File -Encoding utf8`，要嘛读的时候按 UTF-16LE 解。
- `tools/gate_l13.sh` 要用 Git Bash 跑（`D:\git\Git\bin\bash.exe`）：
  本机 `bash` 默认是 WSL，里面没有 cargo；脚本本身正常，只是 shell 选错。
