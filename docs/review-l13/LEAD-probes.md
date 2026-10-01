# Lead 独立探针记录（双引擎差分）

工具：`tests/zz_lead_engine_diff.rs`（**临时 scratch，交付前删除**）。走真实 LSP 面
（`Backend::new_with_engine` + `load_prelude` + `process_file`），同一份源码分别喂
`Engine::Reference` 与 `Engine::Twin`，逐项对比 errors / warnings / println(INFO) 输出，
并抓 `window/logMessage` 里的 twin 回落原因。

运行：`cargo test --test zz_lead_engine_diff -- --nocapture`
日志：`_lead_engine_diff.log`、`_lead_engine_diff2.log`

## 用例结果矩阵

| 用例 | errs | warns | infos | 说明 |
|---|---|---|---|---|
| `gadt_tuple_match`（文档 GADT 复现） | = | = | = | 两版都对，无 non-exhaustive 误报 |
| `bare_apply_block_lambda`（`hdl_fsm_tests.rs:189` 的 ignore 钉子） | = | = | = | 两版**同错**：`find unsolved meta with type Type 0` + 级联 `error name not in scope: fsmBare` |
| `let_unit_module`（`docs/for-hdl-blocker.md` 最小复现） | = | = | = | 两版都正常，文档「已解决」属实 |
| **`for_loop_unroll`** | = | **≠** | = | **见 F1** |
| `no_for_control`（同形模块，无 for） | = | = | = | 对照：无 HDL042 |
| `for_with_ports`（有 for + 有端口） | = | = | = | 对照：无 HDL042 |
| **`plain_calc`**（def 合一失败 + 再引用该名字） | **≠** | = | **≠** | **见 F2** |
| `undefined_name`（纯未定义名 `println(nope(1))`） | = | = | = | 对照：单纯未定义名两版一致 |
| `utils_18`（`examples/hdl/18-utils.typort`） | = | = | = | twin 按 `untrusted-error` 回落（`solve trait failed: LetNamed[…]`），与 `EXPECTED_FALLBACKS` 一致 |

## F1 [P1] 孪生版对无端口 for 循环模块误报 HDL042

- **位置**：检查器 `src/prelude/hdl/hdl-check-graph.typort:1985-2133`（HDL042 段，`:2097` 是文案）
- **复现**（`examples` 无关，纯源码）：
  ```
  module forDemo {
      let a = UInt[8]
      for i in 0 until 4 {
          let x = UInt[8]
          x := a
      }
  }
  println(moduleTreeVL(forDemo.create.tree))
  ```
- **实测**：
  - `Engine::Reference`：warnings 里 **0 条 HDL042**
  - `Engine::Twin`：warnings 里 **2 条 HDL042**
    ```
    [hdl][warning] HDL042 [forDemo] forDemo: second registration under the same module name with
    a different declaration signature (port widths / clock domain) is ignored (first def wins,
    designVL emits one def per name) - declare the second parameterization as its own module
    ```
- **隔离**：`no_for_control`（同形模块去掉 for）与 `for_with_ports`（有 for 但模块有 input/output）
  都**不触发**。⇒ 触发条件至少需要「for 循环」且「模块无端口」。
- **影响**：LSP **默认走孪生版**（`Engine::lsp_default()`），所以编辑器里会凭空出现这条
  warning（Diagnostic）。这不是"慢了"，是"**错的诊断**"——正是 `src/lib.rs` 信任闸注释里
  写的「错的诊断比慢的诊断更糟」要防的事。信任闸只比 **error**，不比 warning，所以这条
  溜过去了。
- **注意**：HDL042 是最近的提交 `815d12a`（P3-10）新加的检查。**新加的检查在孪生版上误报**，
  很可能是「孪生版对同一模块做了两次注册且两次的签名不同」——owner 需确认是检查器太宽还是
  孪生版重复注册。

## F2 [P1] 孪生版与参考版在"合一失败 + 再引用该名字"时诊断与**程序输出**都不同

- **位置（参考侧）**：`src/L13_namespace/elaboration.rs:2479`（`error name not in scope`）
- **位置（孪生侧）**：`src/L13_namespace/bump_spine_iter/machine.rs:2822 / 2848 / 2940`
- **位置（信任闸）**：`src/lib.rs:1555`（`error name not in scope: X` 的放行判据）
- **复现**：
  ```
  def add : Nat -> Nat -> Nat =
      fun a b => match a {
          case zero => b
          case succ(n) => succ(add n b)
      }
  def two : Nat = succ(succ(zero))
  println(add two two)
  ```
  （`add` 是非递归 def，体内自引用 ⇒ 合一失败）
- **实测**：
  - `Engine::Reference`：errs = [`can't unify\n expected: Nat\n find: (b: Nat) → Nat`,
    `error name not in scope: add`]；**infos = []（没有任何 println 输出）**
  - `Engine::Twin`：errs = [同一条 `can't unify`, **同一条再来一遍**]（**没有** "not in scope"）；
    **infos = [`add 2 2`]** —— 孪生版把 `add` 当成不透明 rigid，**照常求值并打印了一个看似合理的结果**
- **为什么没回落**：孪生版的错误集恰好**全部**是信任名单里的 `can't unify` 前缀，
  所以 `is_trusted_error` 放行，孪生版拥有该文件。
- **影响**：同一个源文件，编辑器里：
  1. 报错集合不同（少了"名字不在作用域"这条真正有用的诊断）；
  2. **输出面板内容不同**（孪生版多打了一行 `add 2 2`）。
  未定义名字被当成中性项打印出来，比报错更危险——用户会以为程序算出了一个值。
- **对照**：`undefined_name`（单纯 `println(nope(1))`）两版**一致**，所以不是"凡未定义名都分叉"，
  而是"**合一失败之后的恢复路径**"分叉。
- **注意**：`plain_calc` 的程序本身是 ill-typed（自引用非递归 def），所以这不是"两版对
  良构程序判不同"，而是**错误路径的 parity 裂缝**。严重度按 P1 记（可达、用户可见、
  产生误导性输出），若 owner 能证明孪生版行为其实更"宽容但不误导"再降级。

## 已澄清/已排除的旧线索

- `docs/review-l01l12/FINAL.md` 的 `cargo test --lib` `STATUS_ACCESS_VIOLATION`：
  **不复现**（885 用例全跑完，exit 0）。见 `BASELINE.md`。
- `docs/wip/README.md` 声称「孪生版编译器结构性缺少逐列 GADT 精化 ⇒ 覆盖索引类型 match 的
  REF/TWIN parity 必然分叉」：**本探针未能复现**。`gadt_tuple_match` 两版逐项一致
  （零错误零警告、两臂求值结果一致），`utils_18` 亦一致。该文档描述的可能是**移植分支**
  （显式替换，未落 master）的状态，不是 master@350b35a 的行为。
  ⇒ 结论按「该声称在 master 上不成立」记录；若 owner 在代码侧找到结构性证据反驳，以代码为准。
## F1 修复的验证（A5 R1a）

A5 把 HDL042 的签名收窄为「端口声明」（`isPortKind` + `declKeysOf` 加门，`src/prelude/hdl/hdl-check-graph.typort`），并新增双引擎钉子
`tests/hdl042_engine_tests.rs`（`hdl042_portless_for_loop_silent_on_both_engines` +
`hdl042_second_parameterization_fires_on_both_engines`）。

**实测：`cargo test --test hdl042_engine_tests` = 2 passed / 0 failed。**
⇒ F1 修复有效且**已被双引擎钉子锁住**（原两条 HDL042 测试只走参考版，正是它漏过门禁的原因）。

**同时发现一个构建级陷阱（P0 级，已修）**：A5 第一版把这两条测试写进
`src/L13_namespace/hdl_check_graph_tests.rs`，用了 `crate::Backend`/`crate::Engine`/`crate::client`。
`tests/l13_fast_parity.rs` 用 `#[path = "../src/L13_namespace/mod.rs"]` 把整个 L13 **再编译**进
测试二进制，那里 `crate` 不是 lib ⇒ 8 个 E0433/E0425，**`tests/l13_fast_parity` 编译失败
⇒ `tools/gate_l13.sh` 直接红**。`--lib` 却是绿的（`crate` = lib），所以自测发现不了。
修法：搬到集成 target。Lead 已加进 `tools/gate_l13.sh`（第四件套），并请 A5 把该纪律写进报告 §4。

## F2b —— 错误集面（无 println）

A7 的 R1 修复（值输出面闸）只覆盖「错误 + println」。用 A7 的逐字源码去掉 println 后：

| 变体 | REF errs | TWIN errs | twin 回落 | 判定 |
|---|---|---|---|---|
| v0 无 println | `can't unify…`, **`error name not in scope: add`** | 只有 `can't unify…` | **无** | **P1 确认** |
| v1（+ `def use2: Nat = use`） | 3 条（逐条 not-in-scope） | 1 条 | **无** | 分叉随引用链放大 |
| v2 对照（`def bad: Nat = true`） | `can't unify expected Nat find Boolean` | 同 | 无 | **一致** ⇒ 非"凡错误态都分叉" |

⇒ **P1：孪生拥有该文件并发布一个不完整的错误集**，真实病因（`add` 未定义）在编辑器里被隐藏。
根因（A3）：`fake_bind` 就地写**调用方** `Cxt`（`machine.rs:789-823`，写入点 `:805`）+ Def 臂三个错误出口
`:3543/:3552/:3616` 不回滚 stub + `entry.rs:1258` 保留同一 cxt；参考版靠
`elaboration.rs:1063-1066` 的 `cxt.clone()` 隔离、其 `infer_in_place` 调用者全部首错即停。
本轮**不落地**（方案 A 定点回滚 ~20 行需编译 + parity 验证，按 3 轮上限收口）。

## F2b v3 —— 否证 A3 的"第二机制"

A3 预测：`fake_bind` 先 insert 后判 `prev.is_some()` ⇒ 失败的**重定义**会把旧条目换成 stub 类型，
使后续同名引用产生参考版没有的类型错。探针：
```typort
def foo: Nat = zero
def foo: Boolean = false
def bar: Nat = succ foo
```
**实测**：`REF errs = ["redefine foo"]`；`TWIN errs = ["redefine foo"]`；
`TWIN fallback = ["untrusted-error (redefine foo)"]` ⇒ **`errs_match=true`、`twin_fell_back=true`**。
⇒ `redefine` 不在信任名单，孪生直接回落，**该机制在用户面前不可见**，不构成独立 P1。
（若将来把 `redefine` 加入信任名单才会暴露——已作为前瞻提示写进报告。）

## `twin_engine_tests` 那 1 个失败 —— 是标注错误，不是回归

`CORPUS` 条目 `("def ok: Nat = zero", None)` 失败（"unexpected twin fallback"）。
实测两种 prelude 口径下孪生回落原因都是 **`untrusted-error (redefine ok)`**，`twin_owned=false`；
对照 `def foo: Nat = true` / `def qux: Nat = nope` 都是 `reason=None, twin_owned=true`。
**`ok` 确实是 prelude 名字**：`src/prelude/data/result.typort:6` 的
`enum Result[T, E] { ok(val: Ok) err(...) }` ⇒ `def ok` 真的重定义构造子，孪生判定正确。

⇒ **该条一直就是错的**：在 A3 R2 加 `reason == None` 断言之前，孪生早已回落、诊断比对退化成
"参考版 vs 参考版"，**测试照样绿**。A3 的收紧正是发现了它（他 R2 文档自述的"2026-09-30 之前的漏洞"）。
修法：把源码里的 `ok` 换成非 prelude 名（保留"合法程序由孪生拥有"的测试意图）。

## A7 的两个 P1 —— LSP 进程级实测

用 A7 的 `docs/review-l13/a7-probe.py` + 本工作树构建的
`target/debug/elaboration-zoo-lsp.exe`：

| 探针 | 结果 | 判定 |
|---|---|---|
| 冒烟（`builtin`） | `harness OK; server is alive` | 探针与服务器都活着 |
| **(a) shutdown** | `process exited rc=0 after 0.1s`，stderr 有 `shutting down server` | **P1-1 修复成立**（干净关闭自退出） |
| (b) `open lvl2ix twin` | 150s 仍存活；stderr **无** `main loop panicked` | **该夹具在 LSP 全 prelude 口径下不 panic** ⇒ 不适用 |
| (b) `open lvl2ix reference` | 同上 | 同上 |

⇒ (b) 需要故障注入（A7 的 Plan B，2 行临时 patch）才能确定性验证；Lead **未执行**该注入
（`src/lib.rs` 是 A7 的切片，A7 当时仍在 R2 写入中，注入会违反 write-scope 纪律）。
因此 **P1-2 为"静态验证 + A6 独立会签"**，非进程级实测——最终报告如实标注。

**副产物（重要）**：`tests/l13_fast_parity.rs:745-791` 的 `lvl2ix` 夹具**只在 bare 口径
（`L13_namespace::run(&src, 0)`，无 prelude）下 panic**；经真实 LSP 路径（带全 prelude）**不 panic**。
⇒ 该 P0 的"用户可见崩溃"结论需要限定：**库/测试路径已证；LSP 路径未证**（同一 fixture 不触发）。

## 附：`hdl_fsm_tests.rs:189` 的 `#[ignore]` 钉子准确

`bare_apply_block_lambda` 形态（`sA.whenIsActive { u => when go { sB.goto() } }`）：
**两版都**报 `find unsolved meta with type Type 0`，且**两版都**多报一条级联
`error name not in scope: fsmBare`。⇒ 是引擎侧 apply-block/lambda 缺陷，不是 HDL 层问题，
也不是 REF/TWIN 分叉。`#[ignore]` 的理由（"not reachable from hdl-fsm.typort"）与实测一致。


