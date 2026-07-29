# LSP 服务器架构

## 文本同步：为什么选择增量同步

**2026-06-02** — 从 `TextDocumentSyncKind::FULL`（全量同步）切换为 `INCREMENTAL`（增量同步）。

### 问题

LSP 服务器通过 stdio 与 VS Code（或 Web 演示版）通信。在 WASM（Web 演示版）构建中，stdio 通过 `SharedArrayBuffer` 环形缓冲区实现——LSP 线缆格式（Content-Length 头部 + JSON 主体）序列化到此缓冲区并由客户端读取。

当文档很大（例如 1000+ 行）时，**全量**同步下的每次 `didChange` 通知将**整个文档文本**作为单条消息发送。大消息可能会溢出或错位共享缓冲区，导致**组帧错误**（俗称"粘包"）。后果：多次快速编辑导致 LSP 连接损坏，Web 演示版挂起。

### 解决方案

切换到**增量**同步：
- 客户端每次编辑只发送更改的 `range` + `text`，而非整个文件
- 服务器维护 `document_buffers: HashMap<String, String>` 按 URI 存储完整文档文本
- `didOpen` 时：从通知中存储完整文本
- `didChange` 时：应用增量编辑（使用 `Rope` 进行位置/偏移转换）到存储的缓冲区，然后将重构的完整文本传递给分析工作线程
- `didClose` 时：清理缓冲区

这大幅减少了每次编辑的消息大小（大文件约 100 字节而非约 100 KB），消除了 WASM 传输中的共享缓冲区溢出问题。

### 权衡
- 服务器必须维护自己的文档副本（每个打开文件多一个 `String`）
- 位置/偏移转换需要 UTF-16 → 字节偏移映射（已在 `lib.rs` 中由 `position_to_offset` / `offset_to_position` 处理）

---

## Stdio 线缆监视器

**2026-06-02** — 添加了 LSP 线缆格式检查的调试支持。

调试 LSP 协议问题（特别是共享缓冲区组帧）时，启用 `stdio-monitor` 特性：

```bash
cargo build --features stdio-monitor
```

这会创建代理线程，将每条 LSP 消息（双向）连同完整的 Content-Length 头部和 JSON 主体转储到 stderr。用于诊断组帧错误、格式错误的消息或意外的服务器响应。

详见 `lib.rs` 中的 `create_monitored_connection()`。

---

## Quick Fix（代码操作）

服务器通过 `typort.applyQuickFix` 命令支持代码操作。

- 带有相关修复的诊断在 `diagnostic.data` 中存储唯一 ID
- `codeAction` 请求返回一个链接到修复的"Search solution"操作
- `workspace/executeCommand` 配合 `typort.applyQuickFix` 执行修复闭包并通过 `window/showMessage` 显示结果

在提交 `d003e52`（2026-05-26）中禁用，在 `33bea4c`（2026-06-02）中恢复。
