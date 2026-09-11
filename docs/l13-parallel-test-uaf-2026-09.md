# L13 并行测试 STATUS_ACCESS_VIOLATION：悬垂 decl 表句柄（2026-09-11）

> 分支 `master`（70ec7b9）。现象：`cargo test` 默认并行口径在高并发下以
> `0xC0000005` 崩溃，`--test-threads=4` / 串行全绿。本文件记录已完成的
> 归因链、已排除项与下一步；**未修复**（属低层 UB，需专门工具）。
> 本轮新增诊断开关 `TYPORT_NO_PRELUDE_POOL=1`（见 §6）。

---

## 1. 复现

```
# 默认并行（本机 12 逻辑核）稳定崩，4/4
cargo test --test l13_fast_parity              # exit 0xC0000005
# 8 线程也崩；4 线程与串行稳定绿
cargo test --test l13_fast_parity -- --test-threads=4   # 393 passed，多次复跑绿
cargo test --test l13_fast_parity -- --test-threads=1   # 393 passed
# `cargo test --lib` 间歇崩（本轮 2 次 1 崩 1 绿）
```

崩溃点会漂移（一次 117 个测试后，一次 2 秒内；gorup 单独跑全绿，混合才崩；
被测测试单跑 10×（-j12 与 -j1）全绿）。

**存量化验证**：在 `d711fde`（L01-L13 连续性评审合并 `66da950` 之前）建
worktree 复测，同样 `0xC0000005` → **不是评审合并引入的回归**，早在
`docs/review-cont/a5-r2.md` §3.2（2026-09 初）就已作为主嫌疑记录。

## 2. 现场证据（gdb + llvm-objdump + dumpbin）

- 三次 gdb 运行故障地址 RVA **恒为 `0x29DC`**（模块基址随机化，偏移不变），
  说明是**系统性悬垂**而非随机堆破坏。
- 故障指令：`cmp qword ptr [rcx+18h], 0`，其中 **`rcx = 0xFEEEFEEE_FEEEFEEE`**
  —— Windows 堆的"释放块填充"模式。即：从一块**已被释放**的堆内存里读出了一个
  指针字段（= 填充值），再去解引用它。
- 该 RVA 的符号（dumpbin `/disasm` 的 PDB 标注）：
  `HashMap<smol_str::SmolStr, bump_spine_iter::DeclEntry, rustc_hash::FxBuildHasher>::get::<str>`
  —— **孪生（bump 版）的 decl 表按名查找**。`[rcx+0x18]` 即 hashbrown
  `RawTable.items` 空表快路径检查。
- 故障线程栈上的返回地址符号化（dumpbin 函数标签 + 栈扫描）：
  `eval_iter`（直呼者；`Tm::Decl` 求值查表）← `Machine::check` /
  `infer_expr` / `infer_after_prefix` / `unify_iter` / `solve_flex_side_bump` /
  `check_universe` / `unify_catch` / `insert_global` / `bind_name` / `new_meta`；
  一处运行里还含 `Tycker::prime_resident` 与 `Tycker::new`，以及
  `RawTable<SmolStr>::reserve_rehash`（decl 表重哈希）、`RawVecInner::finish_grow`。
  即：**孪生运行期（prime 或用户段）某处的 `Cxt/Decls` 句柄所指向的
  `Rc<Decls>`/map 已失效**。

## 3. 已排除项（均带 A/B 实测）

| 候选 | 实验 | 结论 |
|---|---|---|
| prelude 池跨线程交接（a5-r2 主嫌疑） | `TYPORT_NO_PRELUDE_POOL=1` 关池：-j4 套件 31s → **9m42s**（确认开关生效，每线程重新 elaborate）；-j12 仍崩，**且故障 RVA 仍为 0x29DC** | **排除**（不是池） |
| arena 压实（`compact_state`） | `TYPORT_TWIN_NO_COMPACT=1`：-j12 **4/4 仍崩**（两处 `compact_state` 调用均受 `compact_enabled` 门控，已核对） | **排除** |
| 内存耗尽 | 崩溃全程系统空闲 commit ≈ 43GB；`PrivateMemorySize64` 无异常 | **排除** |
| 栈溢出 | 故障是数据指针野读（0xFEEEFEEE），非 guard page | **排除** |
| 无同步全局可变状态 | 枚举 parity 二进制内嵌模块全部 `static`：仅原子量 / `Mutex<Vec<PoolState>>`（可关）/ `LazyLock<AtomicBool>`（实验开关）；无 `static mut`、无未同步全局 | 无共享可变状态 |
| 越界写 | `copy_nonoverlapping`/`ptr::write`/`set_len` 全量筛查（孪生 + 参考版 + 共享 parser）：仅 `StringConcat` 快路径（长度计算正确）与 lex 两处 `get_unchecked`（只读） | 未见 OOB 写 |
| 跨测试 TLS 残留 | libtest 每测试新线程（gdb 日志逐测试 spawn/exit），TLS 全新 | 排除 |

## 4. 剩余的机制判断

在"每测试独立线程 + 无共享 Rc + 无共享可变全局 + 无 OOB 写"的前提下，崩溃
却**必须并发同伴**才现形，指向孪生内部的一次**生命周期/别名 UB**：某个
`&Decls` / `Rc<Decls>` 或 `&'static` 重写句柄在其拥有者释放后仍被使用，释放
块的页在低并发时往往仍驻留且内容"看似有效"（读不炸、测试仍过），高并发堆
churn 下页被回收/填充后即 `0xFEEEFEEE` → 解引用炸。孪生有大量刻意的
`transmute::<Cxt<'a>, Cxt<'static>>`（`MetaSnap.cxt`、`prime_resident` 的局部
`cxt`）与 `mach_ptr: *mut Machine` 别名写，均属 UB 高危面，具体生产点尚未
定位。

## 5. 为什么没修

已尝试的工具路径：

- **AddressSanitizer**：仓库 toolchain 未随附 `clang_rt.asan*`，
  `-Zsanitizer=address` 的 build script 因 `STATUS_DLL_NOT_FOUND` 失败；
  需要另装 clang/LLVM。
- **PDB 符号化**：`llvm-tools` 组件不含 `llvm-symbolizer`；mingw gdb 不读 PDB；
  WER 未为本进程落 1000/1001 事件。已用 dumpbin `/disasm` 的函数标签 + 栈扫描
  完成"函数级"符号化（§2），但拿不到源码行级归因。
- 已装 `llvm-tools`（llvm-objdump/nm/readobj 可用）供后续复用。

## 6. 本轮落地的诊断开关

`src/L13_namespace/mod.rs`：`TYPORT_NO_PRELUDE_POOL=1` 完全禁用跨线程
prelude 池（取池改空、退池改销毁）。用于把"并行崩溃"二分到池交接或别处；
本轮据此排除了池。语义中性（只影响速度），默认关闭零开销。

## 7. 下一步建议（按性价比）

1. **装 cdb/WinDbg**（Windows SDK Debugging Tools）→ 用 PDB 直接取故障线程
   的源码行级栈，一小时内可定位到具体 `&Decls`/`transmute` 点位。
2. 或装 clang 运行时后用 nightly + `-Zsanitizer=address` 跑本套件，ASan 会
   直接给出 free/alloc/access 三处栈。
3. 或对孪生做**提交二分**（`d85a759` 移植 force memo 之后至 `d711fde`），
   定位引入 commit 后再看语义。
4. 在上述任一之前，回归闸请用 `--test-threads=4` 或串行（已验证稳定）；
   `0xC0000005` 是签名，不是随机噪声。
