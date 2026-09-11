# L13 并行测试 STATUS_ACCESS_VIOLATION：悬垂 meta 快照——**已修复**（2026-09-11）

> 分支 `master`。现象：`cargo test` 默认并行口径在高并发下以
> `0xC0000005` 崩溃，`--test-threads=4` / 串行全绿。**根因已定位并修复**
> （§8），修复后 12 线程 16/16 复跑绿、完整 `cargo test` 默认并行全绿。
> 本文件保留完整归因链与已排除项，供后续参考。本轮新增诊断开关
> `TYPORT_NO_PRELUDE_POOL=1`（见 §6）。


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

## 5. 工具路径（为什么一开始没直接定位）

- **AddressSanitizer**：仓库 toolchain 未随附 `clang_rt.asan*`，
  `-Zsanitizer=address` 的 build script 因 `STATUS_DLL_NOT_FOUND` 失败；
  需要另装 clang/LLVM。
- **PDB 符号化**：`llvm-tools` 组件不含 `llvm-symbolizer`；mingw gdb 不读
  PDB；WER 未为本进程落 1000/1001 事件。
- **最终解法**：用本地 cargo 缓存里的 `pdb-addr2line 0.10.4` + `pdb 0.8`
  写了一个 ~30 行的临时符号器（读 PDB → RVA → 函数 + **源码 file:line**，
  含内联帧），配合 gdb 在崩溃时的栈转储，拿到行号级调用链（§8）。

## 6. 本轮落地的诊断开关

`src/L13_namespace/mod.rs`：`TYPORT_NO_PRELUDE_POOL=1` 完全禁用跨线程
prelude 池（取池改空、退池改销毁）。用于把"并行崩溃"二分到池交接或别处；
本轮据此排除了池。语义中性（只影响速度），默认关闭零开销。

## 7. 下一步建议

1. **已完成**：装 `llvm-tools`（llvm-objdump/nm/readobj）已装；PDB 行号
   符号器已用 `pdb` crate 现搭（临时工具，未入库）。**若再遇同类并行 UAF，
   直接复用该配方**（WER/cdb 亦可，但本机没有）。
2. 回归闸恢复默认并行即可（修复后已验证）；`TYPORT_NO_PRELUDE_POOL` /
   `TYPORT_TWIN_NO_COMPACT` 保留为对照测量用。

---

## 8. 根因与修复（**已落地**）

### 8.1 行号级调用链（崩溃线程栈 + PDB 符号化）

```
prime_resident:12398            // prelude 装载循环：infer_decl(&cxt, d)
→ infer_decl:8507 → infer_after_prefix:8544 → infer_expr:8297/8245
→ Machine::check:6808 → unify_iter:4117 → solve_flex_side_bump:4469
→ solve_multi_trait_ref:6197
→ solve_trait_ref:6390/closure:6404 → Machine::eval:6014
→ eval_iter:2261                // ← 故障：decl.get(*x)
```

### 8.2 机制

`solve_multi_trait_ref`（bump_spine_iter.rs:6190）从 `self.metas[idx]` 的
`Rc<MetaSnap<'static>>` 里借出 meta 创建处上下文：

```rust
let meta_cxt: &Cxt<'a> = unsafe {
    &*(&s.cxt as *const Cxt<'static> as *const Cxt<'a>)   // 裸指针洗掉生命周期
};
let typ = self.solve_trait_ref(bump, meta_cxt, x, allow_flex_defaulting)?;
```

`meta_cxt` 指向 `MetaSnap`（堆分配，内含 `cxt: Cxt`）的**内部**；随后调用的
`solve_trait_ref` 是 `&mut self`，其候选实例的嵌套 unify/eval 会把
`self.metas[idx]` 替换成 `MetaEntry::Solved`（`self.metas[m] = ...`，多处），
**丢掉该快照的最后一个 `Rc` 并释放它** —— `meta_cxt` 随即悬垂；后续
`eval` 读 `meta_cxt.decls`（`Cxt.decls: Rc<Decls>` 字段）时拿到的就是释放块
填充值 `0xFEEEFEEE`，`HashMap::get` 解引用野指针 → `0xC0000005`。

- 为什么"只在并发下崩"：这是**确定性悬垂读**，低并发时释放堆页仍驻留、
  填充模式未必落在被解引用的字段上（读不炸、测试仍过），高并发堆 churn
  下页回收/填充后必炸。
- 为什么"混合才崩 / 崩点漂移"：同一 UB 的受害点取决于哪次嵌套求解替换了
  对应槽位；故障函数恒为 `HashMap<SmolStr, DeclEntry>::get`（受害字段是
  `cxt.decls`）。

### 8.3 修复

与参考版同点位对齐（`unification.rs:597-601` 是 `arc_cxt.as_ref().clone()`——
**先克隆 `Arc` 再调 `&mut self`**）：孪生改为同时克隆快照 `Rc` 作保命引用：

```rust
let (x, snap): (V, Rc<MetaSnap<'static>>) = match &self.metas[idx] {
    MetaEntry::Unsolved(v, s, ..) => (*v, s.clone()),   // ← Rc 强引用保命
    _ => continue,
};
let meta_cxt: &Cxt<'a> =
    unsafe { &*(&snap.cxt as *const Cxt<'static> as *const Cxt<'a>) };
```

`snap` 是局部强引用，即使槽位被替换，快照也活到本轮求解结束；语义与参考版
的 `Arc` 克隆完全一致（只防提前释放，不改任何判定）。`x` 是 `V`（Copy），
无额外成本。

### 8.4 验证

- **12 线程复跑**：修复前约 5/6 崩、修复后 **16/16 全绿**
  （`l13_fast_parity --test-threads=12`）。
- **完整 `cargo test`（全 target，默认并行）全绿**（此前 `--lib` 亦间歇崩）。
- `cargo test --lib` 默认并行 681 过；`l13_fast_parity` 393 过；
  `twin_engine_tests` 11 过。
- 性能冒烟：`l13bench prelude-hdl fast` 2758ms（修复前基线 2711ms，噪声内）。

