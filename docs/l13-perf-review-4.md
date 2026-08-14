# L13 性能审查第四轮（2026-08-11）—— HDL 文件慢的根因定位

> 分支：`master`（`2dbf651`）。方法：release 实测 + 两次修正后的 git bisect + 逐 commit
> 直接测量 + 用户文件窗口采样（sampler skip 20）+ 临时探针计数器（已全部移除，
> 工作树与基线一致）。
> 核心结论：**用户 HDL 文件较 perf1 时代（21f353e）一致变慢 ~3x，根因不是 elaborator
> 回归，而是 task/module-tree-def 的两个提交：`647d1e9`（class 两阶段化，+52%）与
> `67519ae`（模块宏摊平链，+88%）——两者叠加正好构成完整的 3x。机制：每个模块
> 字段值被完整检查 3 遍（Phase A + create 体 + tree 体）。prelude 侧（hdl-verilog
> ~1.09s/进程）是固定成本而非回退，最大单项是 clockedVL 0.42s（字符串 `+` 链的
> trait_wrap 合成路径，perf1 §3.2 未落地）。

---

## 1. 测量基线（release，min-of-3，本机实测）

### 1.1 用户文件 change 耗时（master）

| 文件 | 耗时 | | 文件 | 耗时 |
|---|---|---|---|---|
| 01-basics | 0.253s | | 09-hierarchy | 0.505s |
| 14-counter | 0.197s | | 08-control-flow | 0.561s |
| 13-inout | 0.262s | | 11-memory | 0.641s |
| 15-output-reg | 0.318s | | 10-bundle | 0.771s |
| 05-bool | 0.383s | | 04-compare | 0.780s |
| 07-registers | 0.381s | | 06-select-cat | 0.867s |
| 12-adder-tree | 0.862s | | 12-arithmetic2 | 1.315s |
| 02-arithmetic | 1.052s | | 03-bitwise | 1.108s |
| hdl_ops | 1.194s | | adder_proof | 2.134s |

### 1.2 CLI 总墙钟（prelude + 用户文件）

| 文件 | 总墙钟 | 用户 change | prelude（差） |
|---|---|---|---|
| 01-basics | 1.66s | 0.28s | ~1.38s |
| 02-arithmetic | 2.59s | 1.17s | ~1.42s |
| 10-bundle | 2.19s | 0.84s | ~1.35s |
| adder_proof | 3.74s | 2.29s | ~1.45s |

小文件被 prelude 固定成本支配，大/运算符密集文件被用户 elaboration 支配。
LSP 每键击 = 全量重推（用户 change 全量重算），HDL 文件 0.2-1.3s/键击。

## 2. 核心发现：用户文件侧 ~3x 回退（perf1 时代以来）

### 2.1 回退量级（同机同文件）

| 文件 | 21f353e（perf1 优化后） | master | 倍率 |
|---|---|---|---|
| 01-basics | 0.080s | 0.253s | 3.2x |
| 02-arithmetic | 0.347s | 1.052s | 3.0x |
| 09-hierarchy | 0.158s | 0.505s | 3.2x |
| 10-bundle | 0.484s | 0.771s | 1.6x |
| adder_proof | 0.685s | 2.134s | 3.1x |

### 2.2 定位过程（bisect 修正记录）

- 第一次 bisect 失效：驱动脚本 `cd $(dirname $0)/..` 把构建/测量目录指到了**主仓库**
  （恒在 master），6 步全部测得 master 值，误报 0ee24ca。已重写脚本（见
  `tools/bisect_l13_perf.sh`，不 cd，阈值用 awk 几何均值，可复用）。
- 第二次 bisect（修正后，`2dbf651..21f353e`）：首坏 = `ed334a3`（merge
  task/module-tree-def）。
- 第三次 bisect 阈值恰好卡在 647d1e9 的测量值上（gm 0.30 vs 阈值 0.29），结果落在
  test-only commit —— 弃用，改为**逐 commit 直接测量**（最可靠）。

### 2.3 逐 commit 直接测量（01-basics / 02-arithmetic）

| commit | 01-basics | 02-arithmetic | 说明 |
|---|---|---|---|
| 0aeef80 / 21f353e / 0ee24ca | 0.080-0.088 | 0.35-0.37 | 回退前基线 |
| **647d1e9** two-phase class elaboration | **0.134** | **0.669** | +52% |
| **67519ae** flatten module chain (plan C2) | **0.252** | **1.037** | +88% |
| aca9ef1 / 1332d90 / 1ad572e / b58cb6e / bb03dfb / 2dbf651 | 0.248-0.255 | 1.03-1.06 | ≈ master，无进一步变化 |

结论：**全部回退来自 task/module-tree-def 的两个提交，两者叠加 = 完整 3x**。
其后的 namespace / output-reg / perf2 改动对用户文件耗时几乎无影响（±2%）。

### 2.4 机制

**647d1e9（class 两阶段化）**：`Decl::Class` 不再在 parser 展开，elaborator 两阶段处理：
- Phase A（elaboration.rs:1609-1672）：在 create 参数上下文（params + bn）里**前向**
  逐个检查字段值（check_universe 注解 + check 值 + eval + quote + tm_to_raw_type）；
- Phase B（elaboration.rs:1680-1686）：`expand_class_decls` 重新生成 struct + create +
  impls，create 体的 let 链把字段值**再查一遍**；
- 加上宏生成的 `tree` 方法体（与 create 几乎相同的链），每个字段值一共被
  **完整检查 3 遍**。

**67519ae（摊平链）**：模块宏展开从 ~25 个 let 增到 **41 个 let**（每个脚手架
`let _ = ...`、每个端口双声明都成为 class 字段），字段数 ×1.6，叠加 ×3 遍检查。
round 3 的逐 def 数据吻合：每个 module ≈ create 32ms + tree 37ms，全部在 check 体。

**调用次数证据**（探针计数器，01-basics 用户窗口，0aeef80 vs 0ee24ca 一致）：
trait_wrap=15、fresh_meta=186、ns_scan=655、meta_clone_calls=15 —— 两时代完全相同，
即"同样的调用次数、每次贵 3 倍"是表象，真相是**字段检查次数 ×3**（check/infer_expr
调用数相同是因为 Phase A/B/tree 走同一批函数，只是调用次数整体翻倍后被相同采样掩盖）。

## 3. prelude 侧（固定成本，非回退）

hdl-verilog.typort 逐 def 计时（release，`bench_hdl_verilog_decls`）：

| def | 耗时 | 特征 |
|---|---|---|
| **clockedVL** | **0.416s** | 长字符串 `+` 链（~30 个 `+`） |
| moduleDefVL | 0.139s | 大函数 + concat |
| exprVL / exprVL_proc | 0.109 / 0.108s | 31 构造器 Expr 大 match |
| memWriteLineRaw | 0.093s | **无大 match，纯 ~7 个 `+` → 每 `+` ≈ 13ms** |
| collectInstHelp | 0.066s | — |
| Total | 1.087s | — |

机制：每个 `+`（String concat）→ trait_wrap → ns 候选探测（每候选一次整表
meta 快照/恢复，meta ~28.5k）+ 合成 `Raw::Let` + 重新 infer —— perf1 §3.2
"运算符调用解析成本 ≈ 一次小型 elaboration"的实测版。perf2 后进程内只算一次，
但 CLI 每进程仍付 ~1.4s（其中 hdl-verilog ~1.09s）。

## 4. 修复建议（优先级排序）

### P0 —— 消除 3x 回退（预计用户 HDL 文件 0.25-1.1s → ~0.1-0.4s）

**复用 Phase A 的检查结果**（两阶段 class 的语义化缓存）：
- Phase A 已产生每个字段的 `(t_checked, vt, a_checked, va)`（elaboration.rs:1655-1656）。
- 把 `expand_class_decls` 的 create 体改为**前向顺序**组装（与 Phase A 的上下文推进
  顺序一致：params + bn → 字段 1..N → mk 应用），并在 Tm 层直接拼
  `Tm::Let(x, a_checked, t_checked, ...)` 链 —— create def 不再对字段值做任何
  Raw 重查，只保留 mk 应用的类型核对（字段类型已 concrete）。
- `tree` 体（宏生成的第二份链）同样复用同一份 Tm 链（差异仅 mkInstanceIfParent
  一行与结尾 `_res`）。
- **风险**：create 体当前按 `items.iter().rev()` 反向绑定（parser/mod.rs:2262），
  前向化需验证 shadowing / `_` last-wins 字段 / bn 解析语义不变；错误定位
  （span）需保留。验证：`cargo test --lib L13` + 集成测试 +
  `class_module_shape_flattened_chain`（moduleTreeVL 输出 pinned）。

### P1 —— 运算符路径（perf1 §3.2 落地，用户与 prelude 双侧受益）

- `check_app_obj_direct`（decl 表直查，elaboration.rs:523）目前只在
  `CANONICAL=true`（定理证明路径）启用；推广到普通 `check::<false>`，运算符调用
  绕过 trait_wrap 合成 AST。
- ns 探测循环（elaboration.rs:2330-2370）加**廉价 head 预过滤**：候选方法首个显式
  参数 head ≠ 接收者 head 时，在 meta 快照之前跳过（当前每候选都做整表快照 +
  fresh_meta + unify_catch）。

### P2 —— 观察项

- hdl-verilog 的字符串拼接函数（clockedVL 等）在 P1 落地后自然下降；若仍需
  立竿见影，可把 `+` 链改 `joinLines` 风格（list + 单次 join）。
- LSP 每键击全量重建（P0 增量 elaboration，round 2 已立项）仍是输入延迟的根本
  上限；P0 修复后模块文件每键击可望 0.25s → ~0.1s。

## 5. 附注

- `tools/bisect_l13_perf.sh`：修正后的 bisect 驱动（不 cd、awk 几何均值、阈值
  sqrt(0.14×0.60)，可直接复用）。
- `analysis/l13-perf` worktree：现成的 `TYPORT_PROBE=1` 调用计数器与 `bench.ps1`，
  可作后续测量的基础（注意该 worktree 的 mod.rs 存在注释编码损坏，改动前先修）。
- 全部临时探针已移除，master 与 perf1-verify worktree 均已恢复基线；
  `cargo test --lib L13` 基线 310 passed（未跑，代码零改动，无需复验）。

---

## 6. 第五轮（2026-08-13）—— P0 落地：Phase A 结果复用，3x 回退基本消除

> 分支：`master`。全部改动在 `L13_namespace`（elaboration.rs / parser/mod.rs /
> parser/syntax.rs / mod.rs），方法：release 实测 min-of-3。

### 6.1 实现

- **`Raw::Tm(Rc<Tm>, Rc<Val>)`**（内部专用变体）：包装 Phase A 已检查的字段值
  及其类型；`check` 首臂 eval（副作用/良构）+ 直接解 Hole 的 fresh meta（或
  unify 复核注解），不再重新 infer 字段值。`infer_expr` 对 Raw::Tm 报内部错误
  （不可达）。
- **Phase A 收集** `PrecheckedItems`：每个 class item（字段 + 语句，声明序）的
  `(name, t_checked, va)` + `bn_refs`（值是否引用 create 专用的 `bn`，用于
  tree 复用安全门）。
- **create 体**：保持 Raw::Let 链结构 + mk 应用（正常 infer，构造器应用正确
  归约为 SumCase），仅字段值替换为 `Raw::Tm`。
- **tree 方法体**：位置+名字配对检查通过后（macro 的 tree 链 = class items 除
  最后一个外），同样复用；任一值引用 `bn` 或配对不符则回退原 Raw 体。
- **`v_app_pruning` 容错**：剪枝比求值 env 多（trait wrapper `$+` 内创建的
  meta 在其参数位求值）时跳过缺失参数，不再 panic。
- **ns 探测 head 预过滤**（P1 低风险项）：候选方法首个显式参数 head 与接收者
  head 不等时，在 meta 快照 + unify 探测之前跳过。

### 6.2 结果（release，min-of-3，本机；prelude 基线 1.364s）

| 文件 | 总墙钟 old | 总墙钟 new | 用户侧 old | 用户侧 new | 加速 |
|---|---|---|---|---|---|
| 01-basics | 1.66s | 1.55s | 0.30s | 0.19s | 1.6x |
| 02-arithmetic | 2.59s | 1.85s | 1.23s | 0.49s | 2.5x |
| 03-bitwise | 2.51s | 1.93s | 1.15s | 0.57s | 2.0x |
| 12-arithmetic2 | 2.77s | 2.05s | 1.41s | 0.68s | 2.1x |
| adder_proof | 3.74s | 3.52s | 2.38s | 2.15s | 1.1x |

HDL 模块文件用户侧约 2-2.5x（3x 回退的 infer 部分已消除；每值 eval 仍 3 次，
属固定成本）。adder_proof（定理文件，无模块类）约 1.1x（噪声）。

### 6.3 验证

- `cargo test --lib L13`：321 passed（基线 310 + 新增）。
- 集成测试（hover/goto/namespace/completion/parser-error 等 8 个套件）：全过。
- L12_canonical 49 个失败为**预先存在**（stash 验证），与本次改动无关。

### 6.4 遗留

- **P1 的 `check_app_obj_direct` 推广**（elaboration.rs:523，当前仅
  CANONICAL=true）未做：运算符路径仍走 trait_wrap 合成，风险较高，留待
  独立验证。
- LSP 每键击全量重建（P0 增量 elaboration）仍是输入延迟的根本上限。

---

## 7. 第六轮（2026-08-14）—— `no_metas` 的 quote 风暴：11-bundle-deep 4.4s → 1.5s

> 分支：`master`（`251118a`）。方法：TYPORT_PROFILE 逐声明归因 → trait_wrap
> 插桩（证伪）→ release-profiling + force 入口采样（符号化修复后）→
> no_metas 分点计时。全部探针已移除，最终改动仅 `L13_namespace/mod.rs`
> （+87/−13）。

### 7.1 现象与归因过程

- 全套件唯一异常点 `11-bundle-deep.typort` 4.40s（其余 0.09-0.83s）；
  60.8% 在 `class bundleDeepMS`，26.9% 在 `impl IMasterSlave for Axi4`。
- **第一假设（trait_wrap 的 quote→eval 往返 + 整表 meta 克隆）被插桩证伪**：
  trait_wrap 仅 2984 次调用，quote+eval 合计 0.001s、meta 快照 0.006s、
  探测 73 次。
- release-profiling（debug=2）+ force 入口采样（临时无锁 tick，skip 20000）
  后符号化正常：**65% 样本（4525/6975）落在 `Tm::no_metas`**，叶子是
  force_inner。
- 分点计时实锤：`no_metas[def-body]`（elaboration.rs:912，def 体的未解
  meta 检查）**30 次调用共 3.11s（均 101ms/次）**：每次调用 quote 388 个
  已解 meta 的解，每个解图 ~7800 节点 → 每次调用 ~300 万次 force。

### 7.2 根因

`Tm::no_metas` 对已解 meta 走 `quote(解) + 递归 walk`（原 mod.rs:360-364）：

- quote 会 **force + 物化整张解图**，而摊平模块/bundle 链的解内嵌巨型已求
  值结构（模块树 / Expr AST 的 Val 图）；
- 解图经 Rc **共享**，但 quote 在每个出现处都整图重走；
- def 体检查（含 Nat defaulting 重试）+ create/tree 三遍检查重复付费。

### 7.3 修复（`no_metas` 改为 visited-set 图遍历）

- `Tm::no_metas_seen`：Tm 遍历所有递归点按 `Rc::as_ptr` 去重（Phase-A 复用
  使 create/tree 体共享同一批已检查子树，普通递归会重访）。
- `Tm::Meta` 已解分支不再 quote，改走新增的 `Infer::val_no_metas`：直接在
  **Val 图**上检测未解 meta（Flex 未解命中；已解跳到解继续走；Rigid/Decl/
  Obj/Sum/SumCase/Match/Call/Pi/Lam（闭包 env + 体）全覆盖），全程不
  force、不 quote。
- 指针稳定性：调用期间 meta 表不变（&self），所有可达节点经 Rc 链存活，
  地址不会复用，指针即身份是安全的。
- 罕见的"已解 meta 带骨架"（Flex+spine）回退 quote 路径；quote 层用
  `NM_QUOTE_LVL = u32::MAX/2`（检测结果只看 Tm::Meta，de Bruijn 指数无关，
  但过小的层会在解内含更深 Rigid 层级时使 lvl2ix 下溢——首个版本因此挂了
  14 个测试，修复后 326 全过）。

### 7.4 结果（release，min-of-3）

| 文件 | 修复前 | 修复后 | 加速 |
|---|---|---|---|
| 11-bundle-deep | 4.400s | **1.461s** | 3.0x |
| 10-bundle | 0.825s | **0.490s** | 1.7x（已优于 perf1 时代的 0.484s） |
| 11-memory | 0.309s | 0.180s | 1.7x |
| 07-registers | 0.197s | 0.138s | 1.4x |
| 其余 HDL / 定理文件 | — | ±0-10% | 持平或小幅改善，无回归 |

验证：`cargo test --lib L13` 326 全过（与基线一致）；8 个集成套件 157 全过；
11-bundle-deep 的 Verilog 输出与修复前逐字节一致。

### 7.5 遗留热点（下一轮候选）

- 修复后 11-bundle-deep 剩余 1.46s 中 `impl IMasterSlave for Axi4` 占
  0.84s（1.15 万次 quote × ~2100 节点/次）——**check/unify 路径上对嵌套
  bundle 类型图的重复 quote**，方向：按 (Rc 指针, 层级) 的结构化 quote 缓存
  或 unify 的 Val 直通路径。
- `class bundleDeepMS` 0.37s（868 万次 force / 11.7 万次 eval）——摊平链
  求值的固有成本。
- 测量手段备忘：release 无 PDB 时 backtrace 最近符号归因会把大片 std 地址
  误标（本轮曾误报 93% 在 `str::to_lowercase`，实际只有 parser 冷路径 2 个
  调用点）；采样前用 `--profile release-profiling` 构建。

---

## 8. 第七轮（2026-08-14）—— 剩余 1.46s 的归因：eval 摊平链求值（负结果 + 路线图）

> 承接第六轮修复（`d8c518e`）。目标：11-bundle-deep 剩余的 1.46s。全部探针
> 已移除，**本轮无代码改动入库**（一个微优化实测无效已撤销），产出为归因
> 结论与下一轮（eval 记忆化）的量化依据。

### 8.1 归因结论（逐层排除）

1. **quote 已不是热点**：第六轮修复后 quote 全程累计仅 0.015s / 3.5 万次
   （0.4µs/次）。7.5 节"1.15 万次 quote × 2100 节点"的推断**有误**——那次
   计数是 quote 调用次数，但单次成本已随 no_metas 修复一并消失。
2. **unify 内三个 quote 位点均便宜**（插桩实测）：Pi 域绑定 16,136 次
   0.0027s；Decl-t 往返 12,000 次 0.0068s；Decl-u 0 次。采样中"80% quote
   样本 caller=unify"实为 unify→**子路径**（unify_pm/compile 等）启动的
   quote 链，成本同样已被第六轮消化。
3. **force 风暴的来源是 eval 的 `Frame::Obj`（字段投影）**：force 入口采样
   （996/1041 样本）全部指向 `eval_inner`；37M 次 force(Sum) 是 Obj 投影对
   Sum 类型接收者的重复身份操作，单次极便宜，**总量即成本**。
4. **真热点 = 32 万次 eval / 31.6 万次 v_app（累计 3.3s，均 10.5µs/次）**：
   每次应用都在求值 ~千节点闭包体——摊平链（create/tree/Phase-A 三遍）的
   真实求值工作。
5. **`Tm::Sum` 求值臂占 eval 的 55%**（179,137 / 322,655 次），且其中
   **40%（72,379 次）是完全相同的 (tm 指针, env 头指针) 重复求值**。

### 8.2 已试并撤销的微优化（负结果，防止重蹈）

- Obj 帧 Sum 快速跳过 force + SumCase 分支 find 先定位后 clone（避免扫描
  路上的无谓 clone）：实测 1.485s vs 1.461s，噪声内无改善——LTO 下 force
  入口本身近乎免费，撤销以保持代码最小差异。

### 8.3 下一轮建议：Sum 臂 eval 记忆化（量化依据见 8.1.5）

- 缓存 `eval(Tm::Sum, env) → Rc<Val>`，键 `(Rc::as_ptr(tm), env 头指针)`；
  **必须持有键对象的 Rc**（防地址复用造成错命中）。
- 失效纪律：`Tm::Decl` 查找依赖 decl 表，decl 插入（class Phase-B 展开等）
  会使结果过期 → 按顶层声明粒度清缓存（on_change 的 decl 循环内）。
- eval 是 `&self` → 需 `Mutex<HashMap>`（Infer 须保持 Send+Sync，存于
  DashMap）；17.9 万次锁开销 ~ms 级，可忽略。
- 预期：消除 40% Sum 臂重复 ≈ 11-bundle-deep −0.2~0.35s；其余文件受益更小。
  属"值得做但需完整验证周期"的改动（错误命中=错误类型，难排查）。
- 更根本的方向（长期）：三遍检查只省了重检查（round 5），**重求值**仍在；
  create/tree 体求值结果按模块缓存或 lazy 化，才能把摊平链成本从 3× 降到
  1×。
