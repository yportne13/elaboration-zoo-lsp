# L13 深层嵌套 Bundle 的 force 递归栈溢出（2026-08-13）

> 场景：`examples/hdl/11-bundle-deep.typort`（3 层嵌套 Bundle）的调试构建测试。
> 现象：debug 测试线程（默认 2 MiB 栈）栈溢出 `STATUS_STACK_OVERFLOW`；release / CLI / LSP（主线程
> 64 MiB）正常。
> 结论：`Infer::force`（mod.rs:1490）的递归深度随**文件累积状态**增长，深层嵌套 Bundle 场景下达到
> ~500–750 层；debug 帧 ~2–3 KB × 750 ≈ 2 MiB 恰好顶爆测试线程默认栈。这是既有脆弱性（同族问题：
> eval / force_chain / Val·List Drop 都曾因栈溢出改过迭代式），当前以"拆文件绕开"处理，未改 force 本身。

---

## 1. 现象与触发条件

- **必现**：把 10-bundle 的 10a–10e 与 11-bundle-deep 的 10f/g/h（3 层嵌套 + 方向化）放在**同一文件**
  时，debug 下 `cargo test --lib L13` 的 `test_examples_hdl_dir` 栈溢出。
- **单独文件不溢**：11-bundle-deep 单独成文件（force 深度 502）在默认 2 MiB 测试线程内通过；
  10a–10e 单独也通过。
- **不依赖 `moduleTreeVL`**：去掉 `println(moduleTreeVL(...))` 后仍然溢出 → 问题在 elaboration 阶段，
  不在 Verilog 生成。
- release 构建（LTO，主线程 64 MiB 栈）任意组合都正常 → 是"栈预算"问题而非逻辑错误。

## 2. 定位过程（临时探针，已全部移除）

在 `infer_expr` / `quote` / `force_inner` 入口各加 thread_local 最大深度计数器，`run_with_prelude`
末尾打印。测量（debug，RUST_MIN_STACK=32MB 保证不溢出以便读数）：

| 场景 | infer_expr 最大深度 | quote 最大深度 | force 最大深度 |
|---|---|---|---|
| 11-bundle-deep 单独 | 43 | 19 | **502** |
| 10a–e + 深嵌套同文件 | 43 | 19 | **752** |

关键观察：
- **infer_expr 递归很浅（43）**——3 层嵌套的 AST 深度本来就不深，elaboration 递归本身不是元凶。
- **force 深度 502→752 随文件累积状态线性增长**——每多一批 bundle 类型/模块，底层值结构更深一层。
- 深度最大处的值类型采样：`Sum(Nat)` / `Sum(Expr)` / `Sum(Vec)` / `SumCase` / `Rigid` 交错出现的
  "锯齿"链——是 module 宏摊平链 + 信号表达式树（`Expr` AST）形成的深结构，不是 `succ(succ(…))`
  那种一元构造器链（那种已被 `force_chain` 迭代化覆盖）。

## 3. 根因：`Infer::force` 的递归结构

`force`（mod.rs:1490）→ `force_inner`（mod.rs:1496）对以下变体**递归下降**：

- `Val::Flex(m, sp)` 已解 → `force(v_app_sp(解, sp))`（mod.rs:1507-1510）——meta 解链；
- `Val::Obj(x, …)` → `force(x)`（mod.rs:1513）——对象成员链；
- `Val::Call(name, args, body)` → `force(body)` + 逐个 `force(args)`（mod.rs:1521）；
- `Val::Sum` → 逐个 `force` 参数的类型/值（mod.rs:1550）；
- `Val::SumCase` → `force(typ)` + 逐个 `force(数据字段类型)`（mod.rs:1571）；
- `Val::Decl` + prim_fn → 结果再 `force`（mod.rs:1537）。

现有的唯一分摊机制 `force_chain`（mod.rs:1597）只处理**一元 SumCase 链**（`datas.len()==1` 且
连续下降到底）。module-tree/bundle 的深结构（混合 `SumCase`/`Sum(Expr)`/`Sum(Vec)`/`Match`/`Rigid`
的嵌套）不满足该条件，退化为每层一个原生栈帧的递归。

## 4. 为什么只有 debug 测试线程炸

- `.cargo/config.toml` 给 `x86_64-pc-windows-msvc` 目标 `-C link-arg=/STACK:67108864`，把**主线程**
  栈提到 64 MiB（CLI / LSP 的 elaboration 都在主线程）→ 750 层毫无压力。
- Rust 测试 harness 在**独立线程**跑 `#[test]`，默认栈 2 MiB（`bignat_large_add_no_stack_overflow`
  的注释里也明确提到"default test thread (2 MiB stack)"）。
- debug 帧大：`force_inner` 的 match 局部变量多，单帧 ~2–3 KB；750 层 ≈ 2 MiB，正好临界。
  故"10a–e + 深嵌套"必溢，"深嵌套单独"（502 层 ≈ 1.35 MiB）通过但余量不大。

## 5. 已采用的绕开方案（随 9f68465 提交）

- 把 3 层嵌套例子独立为 `examples/hdl/11-bundle-deep.typort`，与 10-bundle 分开 → 每文件 force
  深度回到预算内（502），`test_examples_hdl_dir` 连续多次运行稳定。
- 文件头部注释了此限制，提示后续往 11 里加内容时注意累积深度。

**注意**：拆文件只是缓解测试线程的栈预算，没有消除 force 深层递归本身。用户代码里任意文件只要
累积足够的 module/bundle 声明，debug 测试路径仍可能再次顶爆 2 MiB；CLI/LSP 不受影响。

## 6. 修复方向（未实施，供立项参考）

按"影响 × 改动成本"排序：

1. **给 force 补一条迭代路径（推荐，成本中-高）**：仿照 `force_chain`，识别 module-tree/bundle
   的深结构形态（例如"SumCase 的数据字段类型为同名 Sum"或"Obj 链 + 嵌套 Sum"的重复模式），
   迭代下降后再从内向外重建；无法识别时回退现有递归。收益：消除 debug 测试线程的脆弱性，
   也顺带减少 release 下的大栈占用。风险：`force` 分支多且含 prim_fn 副作用（`Val::Decl` 分支会
   回调 `prim_fn`），必须逐分支对照语义；用 11-bundle-deep + 10-bundle 全量做回归。
2. **统一测试线程栈（成本低，治标）**：让 `run_with_prelude`（或测试入口）在
   `std::thread::Builder::new().stack_size(32 MiB)` 线程上执行 elaboration，与 CLI/LSP 主线程
   （64 MiB）对齐。改动小、风险低，但掩盖了递归深度问题本身，且线程边界上要处理
   `input: &str` 的所有权与 `Result` 回传。
3. **不再新增深嵌套 bundle 到现有 example 文件（已做，成本零）**：仅作为临时约束。

## 7. 附：可复现的测量手段

- 临时探针（已移除，若复测需重新加）：`infer_expr` / `quote` / `force_inner` 入口维护
  thread_local 最大深度，`run_with_prelude` 末尾 `eprintln!` 打印。
- 复现：把 `examples/hdl/11-bundle-deep.typort` 内容合并进 `examples/hdl/10-bundle.typort`，
  debug 下 `cargo test --lib test_examples_hdl_dir` 即栈溢出。
- 验证绕开：`cargo test --lib test_examples_hdl_dir`（现拆分状态）应连续多次通过。
