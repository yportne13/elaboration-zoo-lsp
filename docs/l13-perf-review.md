# L13 性能审查报告（2026-08-05）

> 分支：`task/l13-perf-review`（基于 master `0aeef80`）
> 范围：`src/L13_namespace` 全部实现（parser/、elaboration.rs、pattern_match.rs、
> typeclass.rs、unification.rs、canonical.rs、cxt.rs、pretty.rs、mod.rs）。
> 方法：静态审查 + `typort check --sample`（backtrace 采样 flamegraph）+ 基准 A/B 对比
> （同一 release 二进制，min-of-5 计时）。
> 结论：实现 4 项低风险优化，已验证；其余为大改项，仅记录建议。

---

## 1. 测量方法

- 构建：`cargo build --release --bin typort`（LTO + codegen-units=1）。
- 采样：`cargo build --profile release-profiling --features sampler` →
  `typort check --sample <files>`，从 `flamegraph.svg` 的 `<title>` 元素聚合样本
  （注意 release 无调试符号时采样结果全是空名，必须用 `release-profiling`）。
- 计时：`typort check` 输出的 `[LOG log] change <sec>` 是**用户文件**的
  elaboration 耗时（不含 prelude）；prelude 各文件的 parser/infer 分项也在日志里。
- 关键事实：CLI/LSP 每次进程启动都重新 elaborate 整个 prelude（24 个文件），
  **hdl-verilog.typort 的 infer 独占 ~1.3s**（总 prelude ~1.6s），是单进程最大
  固定开销。测试路径（`run_with_prelude`）有 `PRELUDE_CACHE` 不受影响。

采样画像（02-arithmetic，537 样本）显示耗时全部集中在 elaboration 递归：
`infer_expr`/`check`（递归极深）、`compile_aux`（模式匹配编译，2450 帧次）、
`trait_wrap`（1266 帧次）、`check_universe`。`unify` 在算术类文件仅 34 样本，
但在定理证明类文件（adder_proof）是热点（见 §2.2）。

---

## 2. 已实现优化（4 项，均通过 `cargo test --lib L13` → 266 passed / 0 failed）

### 2.1 trait_wrap 的 meta 快照改为惰性（elaboration.rs:1848、2049）

**位置**：`trait_wrap` 的两个命名空间探测块（原 elaboration.rs:1852-1879 与
2042-2069）。

**为什么慢**：两处都在**每次**成员访问失败路径上无条件执行
`self.meta.clone()`（整份 `Vec<MetaEntry>` 深克隆，n≈1.2 万～2.4 万条目），
即使 `ns_entries` 为空（97% 的调用）也要克隆一遍再丢弃。实测 09-hierarchy 的
单次检查中 `trait_wrap` 被调用 **2480 次**、平均 meta_len **12410**、最大 23963
（探测插桩数据），即每个文件浪费 ~2480 × 12.4k × 64B ≈ 2 GB 的 memcpy。

**改法**：`ns_entries.is_empty()` 时直接返回空结果，快照只在存在候选条目时取；
补全路径的探测块改为 `get_or_insert_with` 惰性快照。

**收益**：09-hierarchy **-29%**（0.304s→0.217s），10-bundle **-21%**
（0.825s→0.66s）。无语义变化（快照/恢复范围不变，仅跳过无操作的情形）。

### 2.2 unify 的 Call 快速路径增加无-Flex 预检（unification.rs:781-802）

**位置**：`unify` 的 `(Val::Call, Val::Call)` 同名快速路径。

**为什么慢**：每次对两个同名内联调用（如 `nat_add_helper a b`）做 spine 合一前
都克隆整份 meta（+trait_metas +meta_contrains），**成功路径也克隆**（快照随后被
丢弃）。探测显示 adder_proof 一次检查中该路径触发 **960 次**、平均 meta_len
**25445**（最大 26458）。

**改法**：先做只读的 `spines_contain_flex` 扫描（`val_has_no_flex`，unification.rs:44），
两个 spine 均不含任何未解 meta 时直接跑 `unify_sp`——纯 ground 比较不可能产生
求解副作用，无需快照/恢复；失败时照旧落入 body 比较（无需恢复）。含 Flex 时走
原快照路径。Lam/Pi/Match/Call 值保守地按"含 flex"处理。

**收益**：adder_proof **-39%**（1.470s→0.895s）。

### 2.3 filter_accessible_constrs 快照只包住慢路径（pattern_match.rs:223-335）

**位置**：`Compiler::filter_accessible_constrs`。

**为什么慢**：原实现无论走哪条路径都在函数入口克隆整份 meta+trait_metas、出口
恢复。对非 Sum 类型与非索引 Sum（Bool/Nat/Option/Expr——绝大多数 match）的
快速路径根本不触碰任何状态，纯属两次 O(meta_len) 克隆。

**改法**：快速路径提前 return；快照/恢复只包住"索引类型逐构造器 check_pm 探测"
循环。

**收益**：hdl-verilog.typort 的 infer 1.29-1.36s → **1.17s**（-9%~-13%）；对含大量
match 的用户文件亦有贡献（01-basics -13%、hdl_ops -12%）。

### 2.4 simpl_decl 简化 decl 表共享缓存（mod.rs:324，unification.rs:354/896）

**位置**：`quote`/`rename`/`unify` 处理 `Val::Match` 时各自内联重建整张
"body 替换为 Decl 引用"的简化 decl 表（O(decl) 每 case 每 Match）。

**改法**：提取 `pub(crate) fn simpl_decl(decl)`，复用 quote 原有的按 decl 地址
缓存（decl 是持久化 `Rc<HashMap>`，指针稳定），三处共用同一缓存。

**收益**：消除 rename/unify 中每次 Match 值比较的 O(decl) 重建；定理证明/复杂
模式匹配路径受益（与 2.2 共同作用于 adder_proof）。

### 验证

- `cargo test --lib L13`：**266 passed / 0 failed**（优化前后均通过）。
- 全量 `cargo test --lib` 的 49 个失败全部位于 L01-L12 遗留模块
  （L12_canonical/L11_macro/L10_typeclass/L07a/L07），与本次改动无关（diff 仅
  涉及 `src/L13_namespace/` 4 个文件）。

### A/B 汇总（用户文件 `change` 秒数，min of 5；±20% 噪声）

| 工作负载 | 基线 | 优化后 | 变化 |
|---|---|---|---|
| examples/adder_proof.typort | 1.470 | 0.895 | **-39%** |
| examples/hdl/09-hierarchy.typort | 0.304 | 0.217 | **-29%** |
| examples/hdl/10-bundle.typort | 0.825 | 0.66 | **-21%** |
| examples/hdl/01-basics.typort | 0.117 | 0.102 | -13% |
| examples/hdl_ops.typort | 0.563 | 0.496 | -12% |
| examples/alu.typort | 0.0365 | 0.0329 | -10% |
| examples/hdl/02-arithmetic.typort | 0.525 | ~0.51 | ~0（噪声内） |
| prelude hdl-verilog.typort infer | 1.29-1.36 | 1.17 | -9%~-13% |

---

## 3. 未实现的发现（按"影响 × 改动成本"排序）

### 3.1 P1：Backend prelude 无缓存，每次进程启动重算 ~1.6s（src/lib.rs:235）

**位置**：`Backend::load_prelude_impl`——CLI 与 LSP 每次启动都重新 elaborate 24
个 prelude 文件（hdl-verilog 独占 ~1.3s）。`run_with_prelude`（mod.rs:1681）已有
`PRELUDE_CACHE`，但 Backend 不用它。
**为什么慢**：prelude 的 elaboration 与用户文件等重（check/infer_expr 递归 +
31 构造器 Expr 的大 match 编译），单次 ~1.6s。
**建议**：`load_prelude_state()` 成功后缓存 `(Infer, Cxt, PreludeMacros)`，Backend
启动时克隆（按 run_with_prelude:1779-1783 的模式：`mutable_map` 深拷贝、清空
hover/completion 表）。
**成本**：中——两条加载路径（Backend 的 `on_change` vs `load_prelude_state`）状态
必须逐字段对齐，`nat_to_dec` 注册时机（mod.rs:1731 按内容判断，Backend 在
nat.typort 后手动注册）也要一致；风险是两条路径漂移后产生隐蔽差异。
**预估收益**：CLI 每文件 ~2.1s→~0.6s；LSP 启动延迟显著下降（大）。

### 3.2 P1：trait_wrap 每次运算符调用重建合成 AST 并重新 elaborate（elaboration.rs:1928-2030）

**位置**：`trait_wrap` 的 trait 方法分支——对每个 `a + b`/`x := y` 构造一整个
`Raw::Let`（Pi/Lam 链 + `$$.method` 体）再 `infer_expr` 全量重新检查，方法体
内的嵌套 `$$.method` 又递归进入 trait_wrap。
**为什么慢**：运算符调用的解析成本 ≈ 一次完整的小型 elaboration；
02-arithmetic 类文件（大量 `+`/`:=`）在此路径上无明显改进。
**建议**：把 `check_app_obj_direct`（CANONICAL 专用，elaboration.rs:501）的直查
decl 表路径推广到普通 `check::<false>`；或在 trait 声明时预计算"方法名 → 实例
匹配"索引，避免每调用点做全 trait×方法扫描 + 合成 AST。
**成本**：高——方法解析语义（implicit 参数、重载消歧、错误信息）需逐一对照；
**收益**：中-大（运算符密集代码）。

### 3.3 P2：fresh_meta 急切调用 solve_trait（mod.rs:1142-1143）

**位置**：`fresh_meta` 对 trait 类型立刻 `solve_trait(cxt, &a, false)`——Phase 2 会
对匹配实例做完整 `infer_expr` + unify。每次插入 trait 类型隐参都重复此过程。
**建议**：推迟到 `solve_multi_trait` 批量求解（opt-typeclass.md 问题 5）。
**成本**：中-高（求解时机变化可能改变实例选择/报错顺序）；
**收益**：中（trait 密集代码）。

### 3.4 P2：Cxt::decl 的写时复制整表克隆（cxt.rs:544-561）

**位置**：`Cxt::decl`/`fake_bind`/`import` 每次 `Rc::make_mut` 克隆整张
`HashMap<SmolStr, …>`（每个 def 声明 O(decl)，prelude 累计 O(n²/2) ≈ 1.1M
条目克隆 + 重哈希）。
**建议**：换成持久化 HAMT/红黑树 map（如 `rpds`）或"分层 overlay"；
**成本**：高（全代码库依赖 `decl.get` 语义与指针稳定性）；**收益**：中（prelude
阶段 ~100ms 级，非主热点）。

### 3.5 P2：eval 的 Tm::Var 查找 O(env 深度)（mod.rs:1334）

**位置**：`eval` 对 `Tm::Var(x)` 用 `env.iter().nth(x.0)` 线性走持久链表
（`List` 只有 size 缓存，无索引）。deep env（嵌套 let/match，深度 30-50）下每个
变量引用 O(depth)。
**建议**：`List` 增加 O(1) `nth`（每节点存父指针+偏移不可行；可改用
`Vec`+版本号，或缓存"最近 n 个 Var 的节点地址"）。eval 被内联进
infer_expr/check 热路径，收益难以精确测量。
**成本**：低-中；**收益**：小-中。

### 3.6 P2：infer_expr 裸名回退的 O(decl) 扫描（elaboration.rs:1464-1472）

**位置**：`Raw::Var` 未命中时先构建 `ns_method_keys` HashSet（O(所有 ns 方法)）
再遍历整张 decl 表做 `.name` 后缀匹配。每个裸构造子模式（`case mux(...)`）触发。
**建议**：以 (decl 指针, namespace 指针+len) 为键缓存"裸名 → 全名"倒排索引；
但 prelude 加载期 decl 每 def 都变更，缓存命中率低，收益有限。
**成本**：中；**收益**：小（实测单次扫描 ~45µs）。

### 3.7 P3：check 对 let 绑定值求值 ~3 次（elaboration.rs:588-607 等）

35x 教训的现状：`check` 的 Raw::Let 分支类型检查绑定值时已求值一次、`eval`
再求值一次、外层 def 求值时第三次——module 宏副作用依赖"幂等+restore"抹平
（见 module-redesign-analysis.md §2.2）。**消除 check 期求值是编译器核心改动**
（惰性化 let），单独立项，风险大，本次不动。

### 3.8 P3：parser 宏展开的重复克隆（parser/mod.rs:1072-1100）

`p_raw` 每次宏展开 `state.1.get(...).cloned()` 克隆匹配宏的规则 Vec、并克隆整张
宏表给 `temp_state`，外加展开文本重 lex。实测 parser 各文件 <15ms，非热点；
如未来宏增多可改为 `Rc<HashMap>` 共享。

### 3.9 其他记录

- **meta 向量只增不减**：`Infer::meta` 的 Solved 条目永不回收（`shrink()` 已存在
  但仅 CLI 调试调用）。内存峰值（dhat-heap.json 时代 ~14MB JSON 堆转储）主要来自
  此向量 + 各 Cxt 共享 decl/env。可考虑在 def 边界压实（需处理悬挂索引，中风险）。
- **`Cxt::update_cxt` → `refresh`**（cxt.rs:618-642）对每个环境条目 quote+eval
  O(env)，GADT 细化频繁时线性放大；目前仅在 Vec 类索引类型触发，收益小。
- **`pretty_nat`/`pretty_tm` 递归**：大 Nat 打印栈溢出风险（L13-code-review P0），
  与性能无关但值得顺手修（迭代实现）。

---

## 4. 附：可复用的测量手段

- `tools/measure_one.sh`、`tools/memory_sweep.sh`（主目录，只读参考）：跨提交
  计时/内存扫描；`measure_peak.ps1` 用 Windows 进程峰值工作集。
- `cargo test --lib --release L13_namespace::prelude_tests::bench_hdl_verilog_decls
  -- --nocapture`：hdl-verilog 逐 def 计时基准（当前 Total ≈ 0.75s）。
- `src/L13_namespace/module_probe_tests.rs::probe_timing`：10 个 HDL 示例端到端
  计时，**注意该测试会把结果写进主工作树的 probe-out.txt**（本次已按原样恢复）。
- 注意：`cargo test --lib`（全量）在 L01-L12 遗留模块有 49 个既有失败，与 L13
  无关；L13 验证请用 `cargo test --lib L13`。
