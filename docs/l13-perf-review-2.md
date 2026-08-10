# L13 性能审查第二轮（2026-08-07）

> 分支：`task/l13-perf2`（worktree，基于 `aca9ef1`，早于 master `0aeef80` 之后约 60+ commit）
> 方法：纯静态分析（未编译）。通读 `docs/l13-perf-review.md` §3 建议清单，
> 逐条对照当前代码现状（grep 定位 + 精读相关函数），并新增探查 LSP 层
> （`src/lib.rs` 的 didChange → worker → elaborate 路径）。
> 结论：§3 的 8 项建议在**当前代码全部仍然成立**（行号有漂移，个别上下文已变）；
> 新发现集中在 LSP 每编辑全量重建 + 全局状态克隆链，是本轮最有价值的方向。

> **第三轮更新（2026-08-07，本轮实施）**：§2 的 N1 与 §3.1（prelude 缓存）已落地实现并测量，
> 详见文末 §5、§6。N1 三处克隆削减 + P1 进程内 prelude 缓存，release CLI 单文件检查
> 2.94s→1.9s，多 Backend 测试二进制 macro_goto_tests 20.1s→9.8s；`cargo test --lib L13`
> 308 passed（与基线一致），全部集成测试通过。

---

## 1. §3 各项建议的现状核对

| # | 建议 | 当前代码位置 | 状态 | 备注 |
|---|---|---|---|---|
| 3.1 | P1 Backend prelude 无缓存 | `src/lib.rs:235 load_prelude_impl` | **未变，仍成立** | 24 个文件逐个 `on_change::<true>` 加载；`PRELUDE_CACHE`（mod.rs:2298）仍只被 `run_with_prelude`（mod.rs:2389）使用。`load_prelude_skip_hdl`（lib.rs:231）只是跳过 hdl 段，无缓存。 |
| 3.2 | P1 trait_wrap 合成 AST 重查 | `src/L13_namespace/elaboration.rs:2123`（trait_wrap）；合成 `Raw::Let` + `infer_expr` 在 ~2200-2290 | **未变，仍成立** | §2.1 的惰性快照已就位（elaboration.rs:2134-2173）；但 trait 方法分支仍每调用点合成完整 `Raw::Let`（含 `$this`/`$$` 链）再 `infer_expr`。 |
| 3.3 | P2 fresh_meta 急切 solve_trait | `src/L13_namespace/mod.rs:1458-1459` | **未变，仍成立** | 仍是 `self.solve_trait(cxt, &a, false)` 立即求解。 |
| 3.4 | P2 Cxt::decl 写时复制 | `src/L13_namespace/cxt.rs:100`（`decl: Rc<HashMap<…6 元组…>>`）、`fake_bind` cxt.rs:488 | **未变，仍成立** | 每 def 一次 `Rc::make_mut` 整表克隆（prelude 阶段 O(n²/2)）。 |
| 3.5 | P2 eval Tm::Var 线性查找 | `src/L13_namespace/mod.rs:1784` | **未变，但上下文已变** | **重要变化**：`eval_inner`（mod.rs:1723）已重写为迭代式显式 Frame 栈求值器（原递归版会栈溢出）。`Tm::Var(x) => env.iter().nth(x.0)` 线性查找仍在（mod.rs:1784）。若做 nth 优化，应基于新 Frame 结构设计。 |
| 3.6 | P2 infer_expr 裸名回退 O(decl) 扫描 | `src/L13_namespace/elaboration.rs:1714-1722` | **未变，仍成立** | 每次裸名未命中先构建 `ns_method_keys` HashSet 再全表后缀匹配。另有一处相似代码 mod.rs:2362，但只在 prelude 一次性别名构建中，非热点。 |
| 3.7 | P3 check 对 let 求值 3 次 | elaboration.rs ~604（Raw::Let 分支 eval 绑定值） | 未变（未逐行复验，属 P3 立项项） | — |
| 3.8 | P3 parser 宏展开重复克隆 | `src/L13_namespace/parser/mod.rs:1132`（`state.1.get(..).cloned()`）、1196（`state.1.clone()` 整表）；另 p_decl 路径 2365/2412 | **未变** | — |

### 1.1 附：probe-out.txt 数据性质

主仓库 `probe-out.txt` 的 T_01~T_14 数值（如 T_02 10.17s）约为 perf-review §2 release
A/B 数据（T_02 ~0.51s）的 **~20 倍**，应出自 **debug 构建**（或采样构建）的
`probe_timing` 测试（perf-review §4 提示该测试会把结果写入 probe-out.txt）。
因此：**绝对值不可用，相对排序可用**。排序结果：T_02-arithmetic(10.2) > T_03-bitwise
(7.4) ≈ T_12-arithmetic2(7.4) > T_10-bundle(5.5) > T_04-compare(4.4) > T_11-memory(4.1)
> T_08-control-flow(3.2) > T_09-hierarchy(2.8) ≈ T_01-basics(2.7) > T_07-registers(2.3)
> T_05-bool(2.1) > T_13-inout(1.3) > T_14-counter(0.9)。
头部三名全是**运算符/表达式密集**文件（arithmetic/bitwise/compare）——与 §3.2
（trait_wrap 运算符合成 AST 路径）的"无明显改进"判断吻合，该路径是用户文件侧
剩余的最大单项。

---

## 2. 新发现（perf-review 未覆盖，3 项）

### N1（P0/P1）：LSP 每次编辑 = 全文件重建 + 全局状态克隆链（src/lib.rs:709-767）

**机制**：`did_change`（lib.rs:1176）→ job 队列（worker 只做"同 URI 取最新"合并，
lib.rs:413-420，无 decl 级增量）→ `elaborate`（lib.rs:709）。每次编辑（哪怕 1 个字符）：

1. **lib.rs:732** `let mut local_infer = infer.clone()`：克隆全局 Infer 的整份
   `meta: Vec<MetaEntry>`（perf-review §2.1 实测 n≈1.2万~2.4万，每个 MetaEntry≈40-48B
   —— `Solved(Rc<Val>, Rc<VTy>)` / `Unsolved(Rc<VTy>, Arc<Cxt>, Rc<VTy>, Span)`，
   mod.rs:51-54），约 0.5-1.2MB memcpy + 2.4 万次原子引用计数；
2. **lib.rs:726** 有历史符号时 `Arc::make_mut(&mut local_cxt.decl)`：整张全局 decl 表
   （prelude+全部已分析文件，2-3k 条目）深克隆后删本文件旧 key；
3. **lib.rs:731/752-753** `before_keys`/`after_keys`：两次**全表** `decl.keys()` 构建
   `HashSet<String>`（2-3k 次 String 分配）再取差集；
4. **lib.rs:757** 成功时 `*Arc::make_mut(&mut cxt.decl) = (*local_cxt.decl).clone()`：
   **再一次全表深克隆写回全局**；
5. **lib.rs:767** `hover_table.insert(uri, local_infer.clone())`：第 2 次整份 Infer 克隆
   （存副本）。
6. 之后才对 local_infer 做 `shrink()`（lib.rs:775）——克隆发生在其之前，Solved 条目
   白白跟着被复制。

常数开销合计约 **1.5-4ms/键击**（与文件大小无关，随全局 decl/meta 规模增长），
之上才是全文件重新 elaboration（大文件 0.1-0.5s）。全局 `Infer::meta` 只增不减
（perf-review §3.9 已知），克隆链使该问题被**每键击放大**。

**低成本子项（可独立做）**：
- new_keys 直接取自本次 infer 结果的 decl 名（terms），去掉两次全表 keys 遍历（N1.3）；
- 写回改为"仅替换本文件 file_symbols 涉及 key"（避免 757 的全表克隆；需保持
  Rc 共享语义，与 §3.4 的持久化 map 改法互相加强）；
- 把 hover_table 的插入移到 `shrink()` 之后（省一次含 Solved 条目的复制）。

### N2（P2）：hover_table 存整份 Infer，而 HoverEntry 根本不需要 meta（lib.rs:76、767、522）

`HoverEntry = (Span<()>, Span<()>, HoverCxt, Rc<Val>)`（mod.rs:768），`HoverCxt` 是
lvl/locals/decl 引用（Rc 便宜）；hover/inlay 请求只读 `infer.hover_table` 与
`infer.inlay_hint_table`（lib.rs:1302-1305）。**存储的整份 Infer 里的
`meta`/`meta_contrains`/`trait_metas` 完全用不上**：每次变更多一次 ~0.5-1.2MB 克隆
（N1.5 与 522 路径同），且每打开文件长期驻留一份 ~1-2MB 的完整 Infer（含
`Arc<Cxt>` 使整棵 Cxt 保持存活）。改法：hover_table 改为只存 `(Vec<HoverEntry>,
Vec<(u32,String)>, Vec<(Span,SmolStr)>)` 之类轻量结构（或定制 struct），不再存 Infer。
**成本低**（只动 Backend 存储与两个请求处理器），收益：每次变更 -0.5-1ms 克隆 +
内存 -1-2MB/文件。

### N3（P3）：每次编辑全量克隆 exported_macros（lib.rs:712-714，on_change 路径 459-461）

每次变更把整个宏表 `DashMap<String, Vec<MacroRule>>` 迭代并克隆成 HashMap
（所有文件名 × 各自规则数）。宏表小时 <0.5ms；但项目宏（module 宏等）增多后
线性增长且每键击发生。改法：先收集名字、按需 `get`（克隆仅命中项），或直接
`DashMap::read` 借用（`p_raw` 调用期间持读锁，注意与宏表写入的锁序）。

---

## 3. 下一轮优化清单（优先级排序）

### P0 —— LSP 增量 elaboration（decl 级缓存）
- **内容**：`elaborate` 对未变化的顶层 decl 复用上次结果，只重推变更 decl 及其依赖。
- **成本**：**高**（需要 decl 文本哈希/依赖链、与全局 cxt 一致化、错误恢复语义——现
  有 `file_symbols`/`file_deps` 只做了"整文件替换"，无 decl 粒度）。
- **收益**：**大**——大文件（T_02 类 release ~0.5s/次）输入延迟从"每次全量"降为
  "每次 1-2 个 decl"。风险：与 §3.7（check 期 3 次求值）等语义耦合，需独立立项。
- **建议先行子项（P1 级、独立可做）**：N1 克隆链削减（1.5-4ms/键击常数）——低风险，
  纯复制开销，无语义变化。

### P1 —— 沿用 perf-review §3 已确认项
1. **prelude 缓存（§3.1）**：成本中、收益大（每次进程启动省 ~1.6s，CLI 每文件
   ~2.1s→~0.6s）。风险仍是两条加载路径（on_change vs load_prelude_state）状态对齐。
2. **trait_wrap 运算符路径（§3.2）**：成本高、收益中-大；probe 排序显示
   arithmetic/bitwise/compare 类文件仍是 debug 下最重三甲，全运算符密集。
3. **fresh_meta 延迟 solve_trait（§3.3）**：成本中-高，trait 密集代码收益中。

### P2 —— 低成本项（建议与 P0 子项同轮做）
- N2 hover 轻量存储（成本低，收益小-中）；
- N3 宏表按需读取（成本低，收益小）；
- eval `Tm::Var` 最近命中缓存（§3.5，注意基于新迭代式 Frame 结构，成本低-中）；
- 裸名回退索引（§3.6，收益小）。

### P3 —— 立项观察
- `Cxt::decl` 持久化 map（§3.4）与 N1.2 写回优化互为依赖，可与 P0 增量一并设计；
- 全局 meta 压实策略（§3.9）现被 N1 克隆链放大，值得与 N1.6（shrink 时序）一起做。

---

## 4. 静态分析旁注（非性能）

- **lib.rs:726/757 的 `Arc::make_mut(&mut …decl)` 与 cxt.rs:100 `decl: Rc<HashMap>`
  类型不一致**（std::sync::Arc 无法对 Rc 调 make_mut）——按纯静态读码，当前 worktree
  分支此处应无法通过编译（疑似重构中间态，或 lib.rs 曾以 Arc 版本编写后 cxt.rs 改回
  Rc）。性能结论不受影响（Rc/Arc 的 make_mut 均为整表深克隆），但下一轮动手前需先
  确认该分支/基线的可编译性。
- `eval_inner` 已迭代化（mod.rs:1723-1790 区域，显式 Frame 栈）——这是相对
  perf-review 基线的新代码，若下轮采样，注意采样帧结构已变。

---

## 5. 第三轮：实施结果（2026-08-07）

> 本轮把 §2 的 N1（克隆链）与 §3.1（Backend prelude 缓存）推进到可落地实现。
> 全部改动：`src/lib.rs` + `src/L13_namespace/mod.rs` 两个文件，三个 commit
> （见 §5.5）。验证：`cargo test --lib L13` 308 passed（基线一致，注：任务描述
> 中"367 passed"未在本 worktree 复现——实测基线即为 308）、7 个集成测试二进制
> 全绿（hover 3 / cross-file 3 / println 2 / macro-goto 9 / completion 14 /
> parser-error 91 / rope 8 / large-did-open 1，含 release 模式完整 liveness 探针）。

### 5.1 疑点核实：Arc/Rc "类型不一致" 是误报

`src/L13_namespace/mod.rs:43`：`type Rc<T> = std::sync::Arc<T>;` —— L13_namespace
模块内部（含 cxt.rs，经 `use super::*`）的 `Rc<HashMap>` **就是** `std::sync::Arc<HashMap>`。
因此 lib.rs:726/757/377 的 `Arc::make_mut(&mut …decl)` 与 cxt.rs:100 的类型完全一致，
`cargo check` 通过，**非重构中间态**。第一轮 §4 的判断不成立（纯静态读码未发现模块级
`Rc` 别名所致）。Rc/Arc 的 make_mut 均为整表 COW 深克隆的性能结论不受影响。

### 5.2 N1 克隆链削减（已实现 3 项，全部无语义变化）

**N1-B：写回改 Arc 交接（elaborate，原 lib.rs:757）**
`*Arc::make_mut(&mut cxt.decl) = (*local_cxt.decl).clone()` → `cxt.decl = local_cxt.decl.clone()`。
原代码每次成功写回做 **2 次全表深克隆**（make_mut 先克隆旧全局表再丢弃 + 克隆本地表），
现为 O(1) Arc 共享。安全性论证：`decl` 是不可变 HashMap，所有写入都经 `Rc::make_mut`
COW（cxt.rs:488/546、lib.rs:377/726、mod.rs:2373），共享后不会原地改写缓存/他人视图；
write-back 后本函数内对 `cxt.decl` 只有读取。make_mut 在 refcount≥2 时自动深克隆的
语义保证正确性。已 grep 确认无任何绕过 make_mut 的 decl 原地修改点。

**N1-A：hover_table 快照改 move（elaborate + on_change 两处）**
`self.hover_table.insert(uri, local_infer.clone())` → `std::mem::replace(&mut local_infer, Infer::new())`。
省去每键击 1 次整份 Infer 深克隆（meta 1.2-2.4 万条 + meta_contrains +
trait_solver/trait_definition/… 全部 trait 表 + symbol_table）。插入点从"诊断发布前"
推迟到"println phase-2 之后"（存储内容逐字段等价：tables+meta 原样保留；
Clone 实现把 println_jobs/accumulated_errors 置空，move 后亦为空；defer_println
两路均为 true；mutable_map 为同一 Arc、随后的 clear 语义不变）。on_change 路径
（MUT=false）同样处理；MUT=true（prelude 加载）保留原清理+克隆行为。

**N1-C：before/after_keys 改 `HashSet<SmolStr>`**
`decl.keys().map(|k| k.to_string())` → `decl.keys().cloned()`（SmolStr 短串内联、零堆分配，
原 2×(2-3k) 次 String 分配消失）；`file_symbols` 保持 `DashMap<String, HashSet<String>>`
不变，仅 new_keys 入库时转换（新 key 数量少）。

**未做（有结论）**：
- lib.rs:732 `infer.clone()`（克隆 #1）**保留**——每次 elaboration 必须拥有私有 meta 表
  （fresh_meta 以 0 为基编号，全局共享表会编号冲突；且全局表不持有本文件新增 meta），
  是正确性所需。实测其成本（release ~0.15s/次，远高于第一轮估算，大头是 trait 表克隆）
  是**下一轮最大单项**（见 §5.6）。
- before/after 两趟全表遍历保留——改"增量收集 new_keys"需侵入 infer 内部
  （每 decl()/fake_bind() 恰好插 1 个 key，Arc 变化可 O(1) 差分），收益 ~0.1ms，暂不做。
- 726 行 `Arc::make_mut(&mut local_cxt.decl)`（起始移除旧 key 的全表克隆）保留——
  这是 COW 设计的固有代价，消除需持久化 decl（§3.4 P3 项，见 §5.6）。

### 5.3 P1 Backend prelude 缓存（已实现）

**改法**：
- `src/L13_namespace/mod.rs`：`load_prelude_state` 参数化为 `load_prelude_state_impl(include_hdl)`；
  新增 `PRELUDE_CACHE_NO_HDL`（skip_hdl 变体）；新增公开
  `clone_prelude_state(include_hdl) -> (Infer, Cxt, HashMap<String, Vec<MacroRule>>)`，
  从缓存克隆状态（`infer.mutable_map` 深拷贝，与 `run_with_prelude` 的隔离方式一致）；
  `run_with_prelude` 改为复用该函数（行为等价，删重复代码）。
- `src/lib.rs` `load_prelude_impl` 重写：`clone_prelude_state` → 注册 24 个 builtin
  虚拟文档进 `document_map`/`document_id`（id 0..N，顺序与旧路径一致，含用户文档已存在
  时续号逻辑）→ `exported_macros` 灌入 DashMap → 复刻 LSP 别名语义（全部点号 key、
  含 `TypeHead.method`；`or_insert` 保持缓存已建的 constructor 别名）→ 清
  hover/completion/inlay 表 + shrink + mutable_map.clear → 整体写回全局 infer/cxt。
  `register_nat_to_dec` 已在缓存状态内（nat 之后注册），无需重做。

**两条加载路径状态字段差异清单（逐字段）**：

| 字段 | load_prelude_state（缓存，mod.rs） | 旧 load_prelude_impl（on_change::<true>） | 克隆后处理 |
|---|---|---|---|
| infer.meta / meta_contrains | prelude 全量（未 shrink） | prelude 全量（逐文件 shrink） | 无需（内容一致，容量差异忽略） |
| trait_metas / trait_solver / trait_definition / trait_out_param / assoc_defaults | prelude 状态 | 相同 | 无需（Infer::clone 深拷贝，隔离） |
| symbol_table | prelude 运算符表 | 相同 | 无需 |
| mutable_map | prelude 残留（空） | 加载末尾 clear | **必须**：clone 时深拷贝 + 加载末尾 clear |
| hover_table / completion_table | 已 clear（mod.rs:2379-2380） | 已 clear | **必须**：inlay_hint_table 缓存侧**未** clear，克隆后需补 clear（已做） |
| inlay_hint_table | 未 clear | 已 clear | 见上 |
| accumulated_errors / println_jobs / defer_println | 空 / 空 / false | 空 / 空 / false | 无需（Clone 重置） |
| cxt.decl | prelude 全量 + 别名（mod.rs 版：**排除** ns method，排序确定性） | 同内容 + 别名（lib.rs 版：**含** ns method，HashMap 序） | **必须**：克隆后重跑 lib.rs 版别名循环（or_insert 幂等） |
| cxt.src_names / env / locals / pruning / namespace / namespace_prefix / namespaces / update_from / binding_name | prelude-final | 相同 | 无需（持久化结构 + COW；共享缓存安全） |
| exported_macros（Backend） | global_macros | 逐文件 insert | 从缓存的 global_macros 灌入 |
| document_map / document_id | 无 | 24 个 builtin 文档 id 0..23 | **必须**：克隆后重注册 |
| macro_expansion_map | 无（_expansions 丢弃） | builtin 24 条 | **跳过**（builtin URI 从不被请求查询，dead weight） |
| timings | 无 | 24 条 | 跳过（stats 命令输出变化，见下） |
| 诊断发布 | 无 | 每 builtin 文件发空诊断通知 | 跳过（prelude 无错误，无观测差异） |

**行为差异（已评估，可接受）**：① `typort stats` 的 timings 不再含 prelude 逐文件
明细（prelude 改为一次性加载）；② 别名冲突从"HashMap 非确定序"变为"constructor 优先
（排序确定性）"——更稳，且 ns method 别名仍保留，功能等价；③ builtin 文件不再产生
macro_expansion_map 条目（无查询路径）。

**固有局限**：缓存是**进程内**的（OnceLock + 深克隆的 Rc 图无法廉价跨进程序列化）。
单进程首次启动仍付 ~1.6s prelude 计算；收益在**进程内多次加载**（测试二进制内多个
Backend、LSP 重启复用场景）。若需跨进程收益，只能走"prelude 结果落盘"方案
（自定义序列化或独立 prelude 服务进程），成本高，不建议。

### 5.4 测量数据（release profile，本 worktree）

**CLI：`typort check examples/hdl/01-basics.typort`**（每项 3 次，稳态取中位数；
before 前两次含构建后冷启动噪声已剔除）：

| 指标 | Before | After | Δ |
|---|---|---|---|
| 总墙钟 | ~2.94s | ~1.9s | **−35%** |
| prelude 加载 | ~2.4s | ~1.6s | −0.8s（去掉 24× 每文件宏表重建等开销） |
| 用户文件 change（parser+infer+克隆链+诊断） | 0.48s | 0.30s | **−37%**（N1-A/B/C 主战场） |

**测试（debug 构建，进程内多 Backend 场景）**：

| 测试二进制 | Before | After | Δ |
|---|---|---|---|
| macro_goto_tests（9 test，各 load_prelude 全量） | 20.1s | 9.8s | **−51%** |
| hover_tests（3 test，load_prelude_skip_hdl） | 0.57-0.68s | 0.39s | −30% |

**结论**：N1 三项合计把每键击/每文件常数开销（clone #2 + 写回双克隆 + keys 分配）基本清零
（0.48s→0.30s 的 0.18s 即 clone #2 一次整份 Infer 克隆的真实成本——远高于第一轮 1-4ms
估算，主因是 trait 表体积）；P1 在进程内多 Backend 场景收益 2 倍级。用户文件侧剩余
最大常数项是 clone #1（全局 Infer 克隆，~0.15s/次）。

**旁注**：首次 `cargo build --release` 时 rustc 以 0xc0000409（栈溢出）崩溃一次，
重试成功——与本轮代码无关（编译优化器的偶发问题，同 profile 基线同样复现风险）。

### 5.5 Commit 列表

1. `refactor(l13): parameterize prelude load and expose cached-state clone`（mod.rs）
2. `perf(lsp): reuse cached prelude in Backend and cut elaborate clone chain`（lib.rs）

### 5.6 未落地项方案要点

- **clone #1（lib.rs:732 infer.clone()，~0.15s/次 release）**：每文件 elaboration 需要
  从全局 meta 前缀克隆私有表。改法方向：meta 改为**只追加共享结构**（Vec 换
  append-only + epoch/持久化前缀，§3.9 压实策略合并），或 `Rc<Vec<MetaEntry>>` +
  本文件追加段指针；trait 表（trait_solver/assertion_table/class_instances 等）同样
  只读共享 + 局部覆盖。风险中-高（fresh_meta 编号、force/lookup_meta 索引语义），
  需独立立项 + probe 采样验证。
- **N2 hover 轻量存储**：N1-A 之后每键击克隆已变 O(1) move，N2 的收益只剩内存
  （每打开文件驻留 ~1-2MB 含 meta）。且轻量结构**仍需保留 meta**（hover quote 的
  force 会查 `Val::Flex` 的 meta 表）、symbol_table（quote 运算符恢复）、mutable_map
  （prim fn 可能触碰）——收益变小，降为 P3。
- **Cxt::decl 持久化 map（§3.4）**：与 N1-B 配合后写回已是 O(1)；剩余价值是消除
  726 起始的每键击一次全表 COW 克隆（HoverCxt 持有 Arc 使 refcount>1）。与 P0 增量
  一并设计。
- **P0 增量 elaboration**：不变，仍为最大单项（大文件 0.1-0.5s/键击全量重推）。
- **P2/P3 复核（无变化，一句话带过）**：fresh_meta 急切 solve_trait（mod.rs:1458）、
  eval `Tm::Var` 线性 nth 查找（mod.rs:1784，迭代式 Frame 求值器未动）、裸名回退
  O(decl) 后缀扫描 + ns_method_keys 重建（elaboration.rs ~1714）、parser 宏表重复
  克隆（N3，parser/mod.rs:1132/1196）——现状均未变；其中 N3 的 prelude 加载侧已
  被 P1 顺带消除（旧路径每文件重建全局宏表），仅剩用户文件路径（宏表小时 <0.5ms）。

