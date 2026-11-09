# L11 参考版性能移植报告（L07 → L11，2026-11-10）

> 分支 `feat/l11-hardening`（worktree `C:\ezl-wt-l11`），基线 `feat/all-layers-hardening` @
> `deef97f7`（已 Fast-forward 合入 `07f737d6` L08 depth 残留修复 + `deef97f7` L07 check_ty）。
> 构建目录 `CARGO_TARGET_DIR=C:\ezl-target-all-l11`（F: 盘不构建）。未 push、未改 main worktree、未改 L07/L08。
> 标签：`[实测]` = 本次本机跑出；`[码]` = 源码核对；`[推断]` = 判断。

## 0. 结论（TL;DR）

| # | 移植项（L07 模板 commit） | L11 commit | 结果 |
|---|---|---|---|
| 1 | decl 表就地写 + `infer_owned`（`c2fffd3f`） | `b2353d96` | ✅ 编译/测试/parity 全绿；def-heavy 负载 **~15–16×** |
| 2 | `FxHashMap` for decl 表与 hot side maps（`72f12101`） | `0defec1d` | ✅ 同上（与 #1/#3 合窗收益不可单独拆分） |
| 3 | `name_map + trail` 替代按值 `BiMap`（`d411debe`） | `647fadd6` | ✅ 同上 |
| — | 验收 | — | lib L11 **33 passed**；`l11_fast_parity` **52 passed**；`l11bench` 内建两版输出 parity 断言全过（bench 全程 exit 0） |

**A/B 实测（k=11，`--only basic`，`--rounds 3`，两二进制逐轮交错，取 3 次调用 min）**：

| workload | L11 基线 basic (ms) | 移植后 basic (ms) | 加速 |
|---|---:|---:|---:|
| macro | **1134.514** | **76.181** | **14.9×** |
| struct | **1111.125** | **68.553** | **16.2×** |
| natadd | 1.921 | 1.705 | 1.13× |

natadd 顶层 def 数少（O(D²) 项不存在），只保留 ~10% 常数收益；macro/struct 的 2^(k+1)=4096 个 def
正是 L07 模板针对的 O(D²) 放大器。

## 1. 背景与移植顺序

- L11 与 L07 同构缺陷：`Cxt::fake_bind/decl(&self)` 先 `self.decl.clone()` 再 `Rc::make_mut`
  ⇒ 强计数恒 2、每个顶层 def 深拷整表；`src_names` 按值 `BiMap` ⇒ 每次 bind/define 深拷两张表。
- 实际落地顺序 **#2 FxHashMap → #1 就地 COW → #3 name_map+trail**（而非 1→2→3）：
  #2 与 #1 改同一批文件（`mod.rs` 的 `HashMap` 别名、`cxt.rs` 的 `decl` 初值），
  先用最小 diff 把哈希器换掉，再让 #1 的 diff 只含 COW 语义，便于逐 commit 审阅；
  #1 与 #3 严格分离（各自独立 commit）。
- `src_names` 在基线其实是 `crate::bimap::BiMap`（内部已是 FxHashMap），不是 L07 的
  `Rc<HashMap>`；#2 因此对它是**结构替换的前置无关项**，#3 才把它换成 `NameState`。
  基线 `Locals` 已是 `Rc`（Lead 已确认），本任务未动。

## 2. 逐项改动

### 2.1 `alloc 72f12101`：FxHashMap（commit `0defec1d`）

- `mod.rs`：`use rustc_hash::FxHashMap as HashMap;`，`type Decl = HashMap<…>` 与
  `Infer` 的 `trait_definition / trait_out_param / mutable_map` 随之换 Fx。
- `cxt.rs`：`Cxt::empty` 的 decl 初值 `Rc::new(Default::default())`。
- `parser/mod.rs`：`MacroState` 的宏表 `Rc<HashMap<String, Rc<Vec<MacroRule>>>>` 换 Fx；
  `parser/macros.rs` 的显式 collect 路径同步。
- `typeclass.rs`：`class_instances / assertion_table / Subst` 换 Fx（`Subst::new()` → `Default`）。
- `unification.rs`：`PartialRenaming.ren` 等 `HashMap` 换 Fx。
- 语义零变化（只换 hasher）；errors/parity 未动。
- **不纳入首波**：`pattern_match.rs` 的 `HashSet`、`namespace` 的 `HashSet` 等非 decl 热表（避免无谓 diff）。

### 2.2 `port c2fffd3f`：decl 表就地 COW（commit `b2353d96`）

- `cxt.rs`：新增 `fake_bind_mut(&mut self)`（先 `contains_key` 做 redefine 判定，保持旧 Err 文案/顺序）与
  `decl_mut(&mut self)`（撞名静默覆盖，保持旧行为）；旧 `fake_bind(&self)` / `decl(&self)` 保留为
  "浅克隆 + 就地写" 包装（旧 API 零破坏）。
- `elaboration.rs`：`infer(&mut self, cxt: &Cxt, …)` 变薄包装（`clone` 后委托）；
  新增 `infer_owned(&mut self, cxt: Cxt, …)` 为顺序声明路径入口——Def/Enum/Impl/Trait 臂改为
  `&mut Cxt` + 就地占位/登记、`drop` 不再需要（占位与真值写同一张表）；`Println` 臂直接返回 `cxt`。
- `mod.rs`：`run` 的 `infer.infer(&cxt, …)` → `infer.infer_owned(cxt, …)`。
- **L11 特有条目：hover 观察表**。`Infer.hover_table` 是 `(Span, Span, Cxt, Rc<Val>)`，
  在 `infer_expr` 的变量解析处每次 push 一个 `cxt.clone_without_src_names()`；这些条目钉住
  `decl` 的 `Rc`，会让 `make_mut` 每次仍深拷整表（移植收益从 ~15× 掉到 ~2×）。全仓 grep 确认
  L11 的 hover/completion 表**无任何读点**（L11 不接 LSP，生产观察面在 L13），因此：
  加 `Infer.collect_observations: bool`（默认 `true` 保持库行为），`run()`（bench/CLI 顺序路径）
  置 `false`，4 处 hover push 加门控。`L11_macro::run` 的 Ok 输出/错误文案不变，parity 不涉及该表。
  **行为注记**：经过 `run()` 的 `Infer.hover_table` 现在为空；仓库内无消费者，若未来给 L11 接
  LSP/观察面需改用显式 `CollectObservations` 入口或恢复默认收集。
- `elaboration.rs` 内部 3 处递归 `self.infer(&cxt, …)`（impl/trait 展开）保持旧包装，不追改。

### 2.3 `port d411debe`：name_map + trail（commit `647fadd6`）

- `cxt.rs`：删除按值 `BiMap` 字段，改 `names: Rc<RefCell<NameState>>` + `name_mark: u32`：
  - `NameState { by_name: FxHashMap<String, Lvl>, by_lvl: FxHashMap<Lvl, (Span<()>, Rc<VTy>)>, trail }`；
  - `NameTrailEntry` 记录 `(name?, old_lvl, lvl, old_val?)`：`bind`/`define` 双表插入 + 追加轨迹，
    O(1)；`Wrap` 式条目（`subst_cxt` 包 `VSub`）只动 `by_lvl`；
  - 每次名字表访问前 `unwind(name_mark)` 惰性回滚（与 L07 同款 DFS 纪律，`debug_assert` 越界）；
  - `lookup_src(&str)` 取代外部 `cxt.src_names.get(..)`（返回拷贝的 `(Lvl, Span, Rc<VTy>)`）；
  - `subst_cxt` 不再重建新表：先裁回本 mark，再逐 `lvl` 把类型包成 `VSub` 并记旧值；
  - `clone_without_src_names()`（hover 快照）给全新空 `NameState`，不与活轨迹共享（避免快照后
    被后续 bind 的 undo 破坏）。
- `elaboration.rs`：`Raw::Var` 分支改 `cxt.lookup_src(...)`，其余不变。
- 语义等价性：名字集 = 创建时快照（惰性 unwind 保证）；条目值仍是 `Rc<VTy>`（无 Val 深拷贝）。
  风险：共享轨迹要求**深度优先访问**（L07 同一假设）；L11 的 pattern compiler 只在臂内 DFS
  使用 Cxt，且 hover 快照已隔离。当前 release 测试 + parity + bench 内建断言全过。

## 3. 测试与门禁（`[实测]`）

| 命令 | 结果 |
|---|---|
| `cargo test --release --lib L11_macro` | **33 passed / 0 failed**（EXIT 0） |
| `cargo test --release --test l11_fast_parity` | **52 passed / 0 failed**（EXIT 0） |
| `l11_blackbox*` | 不存在（L11 只有 `tests/l11_fast_parity.rs`，无 blackbox 套件） |
| `l11bench` 内建双 oracle | A/B 全部 18 次调用 EXIT 0：各 k 的参考版 `run` 与孪生 `run_fast` Ok 输出逐字节一致、nf 节点数断言通过 |

原始日志：`C:\ezl-target-all-l11\test-lib-l11.log`、`test-parity-l11.log`；bench 原始输出
`C:\ezl-target-all-l11\ab\r{1..3}-{base,new}-{macro,natadd,struct}.txt`。

## 4. 基准方法（A/B）

- 二进制：同一 worktree 先构建 `HEAD`（移植后）`l11bench.exe` → 存 `bins\l11bench-new.exe`；
  再 `git checkout HEAD~3 -- src/L11_macro`（= `deef97f7` 基线）构建 → `bins\l11bench-base.exe`，
  随后 `git checkout HEAD -- src/L11_macro` 还原（工作树恢复干净，见 §5）。
- 3 轮 × 每轮按 base/new 交替顺序（r1 base→new，r2 new→base，r3 base→new）×
  workload ∈ {macro, natadd, struct}；`--max-k 11 --rounds 3 --only basic`；每格取 3 次调用
  输出里的 min 再取 min。l11bench 每次调用内部先跑一次不计时的 basic（预热）+ 双 oracle 校验。
- 数字上界参考 L07 同类上线（strchain 13–33×、global 7–25×），L11 的 14.9–16.2× 与之一致；
  natadd 的 1.13× 符合"只有 def 数大才受益"的预期。

## 5. 未做 / 限制 / 后续

1. **未做的 L07 优化**：`a78daec7`（exhaustive match 跳过覆盖探测）、`9530205d`/`d411debe`
   的后续微调、`f627746e` C2 尾任务寄存器化（只落孪生 eval，参考版无对应控制流）、L07 其它
   hardening 的语义收紧（属正确性项，非本轮性能移植）。
2. **#2 范围**：只换 decl 表/宏表/typeclass/unification 的 hot map；`HashSet` 与 parser 的
   span/side tables 未换。若要继续，下一波可把 `pattern_match` 的 `HashSet`、`Cxt.namespace`
   的 `HashSet` 换 Fx。`[推断]` 收益小。
3. **A/B 未做单因子拆分**：3 项合窗测量；若要归因，可用上述 3 个 commit 逐级构建
   （`0defec1d` → `b2353d96` → `647fadd6`）各跑一次 macro k=11。
4. **未改 L07/L08/twin**：L11 孪生代码与 parity 判据零改动；`l11_fast_parity` 的 `?N` 归一化
   口径未变。
5. **未 push / 未动 main worktree / 未 commit 到 master**；本分支仅本地 3 个 port commit + 本报告。
6. 验证环境：Windows，release（LTO + codegen-units=1，Cargo.toml 既有配置）；单机单窗口交错，
   绝对值受机器负载影响，比值可复现。

## 6. 复现命令

```powershell
# worktree
cd C:\ezl-wt-l11
git log --oneline -4                      # 647fadd6, b2353d96, 0defec1d, deef97f7
$env:CARGO_TARGET_DIR = 'C:\ezl-target-all-l11'
cargo test --release --lib L11_macro
cargo test --release --test l11_fast_parity
cargo build --release --bin l11bench
# A/B：见 §4；基线二进制构建见 §4 的 checkout HEAD~3 步骤
```
