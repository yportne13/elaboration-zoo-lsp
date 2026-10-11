# Review 2026-10-11 — 轮次 9:LSP 行为

> 主题:**编辑器可见面**:诊断发布、println 两阶段、hover、goto、
> completion、跨文件、重解析、鲁棒性。
> `tests/r9_lsp_probes.rs` 30 个测试(60+ 断言),**终局 30/30**。

## 1. 通过的关键行为
- 错误 span 落在肇事 token(非文件头);undefined 名报 not in scope;
  解析垃圾不 panic;空文件静默。
- **println 两阶段**:错误先发布、note 后到,两者共存于最终集;
  字符串 note 正常。
- **重解析替换**:didChange 序列(broken → fixed)最终诊断集恢复为空
  (最新 publish 完整替换旧集)。
- goto:def 使用点 → 定义行;prelude 函数可跳转;undefined 不 panic。
- completion:顶层与点号补全调用不报错。
- 跨文件:`import pkg._` + 使用点 def 全局可见;依赖类型变更后
  dependent 重解析并报错(依赖追踪双向生效)。
- TY001 以 WARNING severity 出现在 LSP 诊断(R3 修复的 LSP 面验证)。
- 300 def 大文件不挂;CJK 标识符、CRLF、无尾换行都正常。

## 2. 记录的行为细节/quirk(测试已固化)
- **Nat 字面量与裸枚举构造子使用点无 hover 条目**(Raw::Nat 臂与构造子
  使用路径从不 push_hover)——hover `42`/`apple4` 得 <none>;def 使用点
  有。记 P3(易补)。
- binder token(`def f(p: Boolean)` 的 p)无 hover 条目;类型经使用点
  字面量可查。
- **仅 println 的文件 hover 表为空**(两阶段 deferred 路径不登记)。
- goto 使用点 offset 语义:hover/goto 表按 byte offset 查询,调用方
  (LSP handler)负责 Position→byte 转换——测试侧曾把全文件字节当
  line0 列号,属测试 bug 非产品 bug。

## 3. test-harness quirk(非产品问题,记录)
- **并行 cargo test 下跨文件测试 panic**(`lookup_meta` index out of
  bounds,mod.rs:2608):两个 Backend 在同线程交错 elaborate 时,
  thread_local/全局 budget/hint 状态互踩。`--test-threads=1` 全绿;
  真实 LSP 单 Backend 单线程不受影响。现有测试套件并行全绿是因为
  官方测试的形态恰好不触窗口;R9 的 30 个探针更密。记 P3(测试隔离)。

## 4. 验证
- `cargo test --test r9_lsp_probes -- --test-threads=1`:30/30;
- 全量门禁见 commit。
