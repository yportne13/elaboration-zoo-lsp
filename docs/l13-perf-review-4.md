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

---

## 9. 第八轮（2026-08-14）—— Sum 臂 eval 记忆化：完整实现并实测，**净损失，已撤销**

> 按 8.3 建议完整实现、验证、测量后**整体撤销**（负结果）。记录于此，
> 防止按同样思路重试。

### 9.1 实现（已撤销的工作树，验证通过后才撤销）

- 缓存：`Infer.eval_sum_cache: Mutex<Map<(tm 指针, env 头节点指针), (Rc 保持,
  env 头保持, Rc<Val>)>>` + `sum_cacheable: Mutex<Map<tm 指针, bool>>`。
- 安全门控（静态，按 tm 指针记忆化）：子树无 `Tm::Meta`（meta 解不随 decl
  版本失效）、无**有状态 prim** 的应用（change_mutable / create_global /
  get_global / file_* 读写 mutable_map 或文件系统，跳过重执行不等价）。
  prim 完整名单经审阅 cxt.rs 全部 15 个 add_builtin 确定。
- 失效：全局 `DECL_VERSION` 在全部 6 处 decl 表 `Rc::make_mut` 写点
  （cxt.rs ×2、lib.rs ×3、mod.rs ×1）自增；版本变化清空缓存。
- 锁纪律：计算（含参数递归 eval）前必释放 guard，防重入死锁。

### 9.2 验证与结果

- 正确性：22 个示例（全部 hdl + 定理文件）输出与 HEAD **逐字节一致**；
  `cargo test --lib L13` 326 全过；集成 157 全过。实现本身是对的。
- **性能全线回归**（release，min-of-3）：01-basics +22%、02-arithmetic +33%、
  hdl_ops +21%、adder_proof +30%、10-bundle +12%、11-bundle-deep +5%。

### 9.3 为什么 8.1.5 的"40% 重复"没能兑现

- 40% 重复统计的是**调用次数**，省下的是被重复者的求值成本——多为小类型
  的廉价求值；而 10.7 万次**一次性**求值每次都要付：子树安全检查
  （嵌套 bundle 类型子树很大，逐节点 ptr 去重 + 哈希）×1 + 缓存锁 ×2 +
  哈希插入 + keep-alive Rc。一次性求值占 60%，其书页开销 > 重复者的节省。
- `DECL_VERSION` 在 class Phase-B 展开（每 decl 多次表写）期间频繁清空，
  命中窗口被切碎，实际命中率远低于 40%。

### 9.4 结论

- 沿"在 eval 内做点级记忆化"的方向，在当前值规模分布下**无利可图**；
  除非能免费获得安全性（如求值器改为带共享的 NbE，值节点自带 memo），
  否则不再按此路径重试。
- 剩余的 1.46s 归因不变（见 8.1）：真热点是摊平链三遍**重求值**的固有
  成本；值得投入的下一步仍是 8.3 末条的长期方向——create/tree 体求值
  按模块缓存或 lazy 化（3× → 1×），以及 LSP 每键击增量 elaboration。

---

## 10. 第九轮（2026-08-14）—— 最终归因：`change_mutable` 的 O(N²) 累加器（占剩余时间 99.5%）

> 承接 round 7/8。本轮修正了 round 7 采样聚合的一个 awk 状态机错误（它把
> `infer_expr`/`check` 帧从归因中丢掉了），看到原始栈后结论完全改写。
> 无代码改动入库。

### 10.1 原始栈（release-profiling + force 入口采样，1040 用户样本）

```
infer_after_prefix > infer_expr > check<false> > infer_expr > eval
  > v_app > cxt::change_mutable > v_app > eval > force_inner × 深链(12-60帧)
```

- **1035/1040（99.5%）样本包含 `change_mutable`**。
- round 7 所测位点（def 四处直接 eval、class Phase-A 三处、println-nf）
  复测合计仅 ~0.1s——全部不是热点。8.1 的"eval 摊平链求值"需要修正为：
  **eval 的成本几乎全部来自 `change_mutable` 内部的 v_app/force**。

### 10.2 机制：端口注册的整树重放

- HDL 的 `out(...)`/`in(...)`（asMaster/create/tree 体里每字段一次）通过
  `change_mutable(name, f)` 更新 mutable_map 中的模块树值；
- `change_mutable`（cxt.rs）对**当前累积值**执行 `v_app(f, 旧值)`——f 是
  合并函数，其求值对旧值做深度 fold（Match 递归）；
- N 个端口/字段 → N 次全树 apply+force → **O(N²)**，三遍检查再 ×3。
- 这同时解释了：round 6 之前 no_metas 为何在巨型"解值"上爆炸（解值就是
  这些累积树）；round 7 的 Sum 臂 (tm,env) 重复统计（重放的是**结构等价**
  的链，几乎无指针复用）；round 8 的记忆化为何无效（每次 apply 产生全新
  值，(tm,env) 指针级命中率远低于结构重复率）。

### 10.3 修复方向（prelude/HDL 层设计，非 elaborator 补丁）

1. **O(1) 追加 + 单次组装**（推荐）：`out`/`in` 只把端口描述追加进全局
   pending 列表（mutable_map 存列表或新 prim），树读取（moduleTreeVL）时
   一次性组装。嵌套 asMaster 分派期间继续产生的 out/in 按追加顺序保持
   注册顺序；需与 hdl-redesign-plan.md 对齐。
2. **不可变累积结构**：树值改 cons 风格，合并 O(1) 构造、不 force 旧值
   （要求 + 对该结构 WHNF 即可构造）。
3. 任何方案必须过：全部 hdl 示例 Verilog 输出逐字节对比 + L13/集成套件。

### 10.4 方法学教训（记录以防再犯）

- round 7 的"caller=eval / caller=infer_after_prefix"聚合是 awk 状态机
  bug（`gsub` 先改写了 `$i`，后续匹配依赖原始文本）。**聚合前必须先肉眼
  看原始栈**。
- 位点插桩与采样结论矛盾时：先怀疑聚合脚本，再怀疑插桩覆盖面，最后才是
  假设本身。

---

## 11. 第十轮（2026-08-14）—— `succ` 计数器修复落地 + 5.7× 潜力的投影快速路径（未竟）

> 代码提交 `412dd12`（prelude 计数器 succ 化，已验证）。另有一个 5.7×
> 的 evaluator 快速路径实验，**验证失败已撤销**，失败用例即下一轮规范。

### 11.1 已落地：计数器 succ 化（`412dd12`）

- `addExprToModuleHelper` 的 `head.expr_num + 1` → `succ(head.expr_num)`、
  `insert` 的 `this.num + 1` → `succ(this.num)`：一元 Nat 加法每次行走整条
  计数链（每信号 O(N) → 每模块 O(N²)）；`succ` 是定义相等的 O(1) 构造子
  包装。计数器无消费者（仅 Vec 长度索引；Verilog 生成结构匹配 Vec）。
- 结果（release，min-of-3，22 示例**完整 note 块**逐字节一致 + 326/157
  测试全过）：hdl_ops −10%、12-arithmetic2 −7%、01-basics −8%、
  11-memory/09-hierarchy −6%、10-bundle −5%；11-bundle-deep 仅 −2%。

### 11.2 未竟：`Frame::Obj` 构造子头快速路径（5.7×，撤销）

- 修改：eval 的 Obj 投影对已是 `Sum`/`SumCase` 头的接收者跳过 `force`
  （与 769962c 的 Sum 叶子化同族）。机制：`force(SumCase)` 递归 force
  **所有** data 字段，投影 `x.num`/`x.data` 每次整树重走——这是 11.1
  之后剩余 O(N²) 的真正来源（succ 化只是把链变成惰性，force 仍走它）。
- 实测收益：11-bundle-deep **1.45→0.256s（5.7×）**、10-bundle 0.47→0.25、
  01-basics 0.095→0.082。
- **验证失败（撤销）**：2 个测试红——`test_hdl_bundle_master_slave_param`
  （master 字段方向错）与 `test_examples_hdl_dir`（07-registers 丢失
  `reg [7:0] da;` 声明）。投影返回未归一化字段破坏了依赖投影期归一化的
  下游匹配（Verilog 生成器侧）。这两个用例就是下一轮的规范。
- 另暴露本报告早前的方法学漏洞：`grep "^note:"` 只截取 note 块首行，
  "输出一致"结论曾因此误报。现已改用完整块捕获
  （`target/perf-probe/full_out.py` 的逻辑）重新验证过全部结论。

### 11.3 下一轮（如果有）：把 5.7× 拿下

1. 以 2 个失败用例为规范，找出依赖投影期归一化的消费点（大概率是
   hdl-verilog 生成器的 match 处未 force 的位置），在那里显式 force——
   修消费点而不是放弃快速路径；
2. 或评估 `force(SumCase)` 的 datas 递归本身是否可安全惰性化（注释声称
   "side effects must run"，需在严格求值器里核实该说法的年代）；
3. 验证门槛照旧：完整块逐字节 + 326/157 测试。

---

## 12. 第十一轮（2026-08-14）—— 5.7× 拿下：投影快速路径 + Nat prim 消费点修复（`2916374`）

> 按 11.3.1 执行：重新应用快速路径，修消费点而非放弃。全部验证通过。

### 12.1 消费点定位与修复

- 两个失败用例的共同根源不在 hdl-verilog 的 match（match 自身会 force
  scrutinee），而在 **Rust 内建 Nat prim**：`try_count_nat` 只认纯
  SumCase 链，未归一化值（Call/Flex 骨架）直接计 0——`width_range` 返回
  空串（`reg d;` 丢宽度）、`nat_to_dec` 输出 0（连带方向逻辑错）。
- 修复：新增 `count_nat_forced(infer, decl, val)` 逐级 force 计数；
  `nat_to_dec`/`width_range` 改用它（二者本就接收 infer/decl，此前忽略）。
  非强制版本无其他使用者，删除。

### 12.2 结果（release，min-of-3）

| 文件 | 会话起点 | round 10 后 | 本轮后 | 会话累计 |
|---|---|---|---|---|
| 11-bundle-deep | 4.400s | 1.45s | **0.261s** | **17×** |
| 10-bundle | 0.825s | 0.47s | **0.254s** | 3.2× |
| 02-arithmetic | — | 0.26s | 0.197s | — |
| 12-arithmetic2 | — | 0.35s | 0.265s | — |
| hdl_ops | — | 0.38s | 0.327s | — |
| 01-basics | 0.253s* | 0.095s | 0.083s | 3.0× |

（* round-4 表值。）定理文件（adder_proof 1.14s 等）不变——不走模块树
路径。prelude 固定成本（wall_min ~0.75s）基本不变。

### 12.3 验证

- 22 个示例**完整 note 块**逐字节一致（含多行 Verilog 体）；
- `cargo test --lib L13` 326 全过；8 个集成套件 157 全过。

### 12.4 状态

- change_mutable O(N²) 线程至此关闭：计数器 succ 化（`412dd12`）+
  投影快速路径 + prim 消费点 force（`2916374`）。
- **附带消除的脆弱性**：深嵌套 bundle 的 debug 测试线程栈溢出（
  `l13-force-recursion-stack-overflow.md` 的复现方法：10+11 合并文件）
  现已连续 3 次通过——force 调用从数千万次崩塌到数千次，深递归不再
  触达。
- 剩余观察项：11-bundle-deep 0.29s 中 class bundleDeepMS 0.09s（摊平链
  求值）+ println 组装 0.05s（一次性 O(N)，均健康）；LSP 每键击全量重建
  仍是输入延迟上限（老项，与本次无关）——但用户文件侧重推成本现已降到
  0.08-0.26s/键击，全量重推的实际体感已可接受。

---

## 13. 第十二轮（2026-08-16）—— Wave 1-6 HDL 库复刻后 prelude 固定成本 0.75s → 24.7s（~30x）

> 分支：`master`（`40c0341`，round 11 之后 9 个提交）。方法：release 实测 +
> `load_prelude_state_impl` 临时逐声明探针（`TYPORT_PRELUDE_PROF`，含
> FUNC_PROF 计数器快照 + force(Call name) 按名直方图）+ prelude 因果替换
> 实验。全部探针与实验改动已还原（工作树与 HEAD 一致，326 测试复验通过）。
> 采样器（sampler）本轮无效：tick 只挂在 infer_expr 入口 + LTO 内联吃掉
> force/eval 帧，栈归因不可用，结论以探针 + 因果实验为准。

### 13.1 现象

- `typort check`（prelude-only 最小文件）总墙钟 **24.7s**（round 11 约
  0.75s+0.08s），用户文件侧（on_change 窗口）**无回归**：01-basics 0.092s
  （round 11 0.083s）、10-bundle 0.296s（0.254s）、新库示例 17-stream
  0.722s / 19-crossclock 0.265s / 20-widthadapter 0.140s。
- 影响面：**每进程一次**（OnceLock 缓存进程内复用）——CLI 每次调用 ~25s；
  LSP 冷启动到首份诊断 ~25s；`cargo test --lib L13` 143s/326 全过（套件
  基线时间此前未记录，其中至少含一次 prelude  elaboration + 每 Backend
  克隆更大状态的开销）。
- elaborator 核心（`L13_namespace/mod.rs` 等）自 `2916374` 以来仅 +6 行
  （加载 6 个新 prelude 文件），回退全部来自 **prelude 内容本身**。

### 13.2 逐文件归因（TYPORT_PRELUDE_PROF，release）

| prelude 文件 | 耗时 | 热点 def（耗时 / force 次数） |
|---|---|---|
| hdl-crossclock | **9.03s** | streamFifoCC 6.9-7.2s / 1.96 亿；ccByToggleUInt 1.2s / 3260 万；pulseCCByToggle 0.64s / 1780 万 |
| hdl-misc-io | **6.35s** | dividerCore 6.4-6.5s / 1.93 亿 |
| hdl-stream | **5.36s** | streamFifoConnect 2.75s / 7630 万；streamFifo 1.31s / 3620 万 |
| hdl-misc | **1.89s** | watchdog 1.0s / 2950 万；timer 0.57s / 1600 万 |
| hdl-utils | **1.28s** | ccByToggleUInt 家族（见 crossclock） |
| hdl-bus-proto | 0.28s | — |
| hdl-verilog | 0.83s | （较 round 4 的 1.09s 已改善） |
| 其余（core/data/hdl 前排） | 合计 ~0.3s | — |

8 个热点 def 合计约占全部 **6.98 亿次 force 调用**的 86%；每次 force 均
价 ~36ns，force 总量即全部墙钟。eval 453 万次 / unify 12.9 万次——
都不是热点。

### 13.3 机制

- force 入口形状：**Match 4885 万 + Call 4885 万 + Decl 1064 万，Sum/SumCase
  为零**——不是 round 9/10 的模块树 O(N²)（change_mutable 家族），是
  **递归函数应用被反复 force**。
- force(Call) 按名直方图：**pred 1767 万、log2Up 1176 万、maxNat 998 万、
  andCond 936 万**——四个函数恰好构成全部 Match+Call 风暴。逐 def 相关性：
  每个热点 def 的 top 名单都是这四个；用到 `maxNat(1, log2Up …)` 位宽惯用语
  的 def 中两者计数**完全一致**（锁定同步 force）。
- 这些函数全部活在**类型位宽表达式**（`UInt[log2Up (depth+1)]`、
  `CounterMod[maxNat(1, log2Up stateCount)]`、`pred w` 等）与 when 条件
  累积（andCond）里；`Val::Call` 的 force 会递归 force body + 全部参数且
  无任何共享/记忆化，同一应用树在检查/回引的每次出现处被整棵重走。
- **因果实验**（prelude 临时替换为恒等函数后还原）：
  - `log2Up → x`：24.7 → 22.8s（−8%，递归体本身不是大头）；
  - 再加 `maxNat → a`、`andCond → cond`、`pred → n`：**→ 4.02s（累计 −84%）**。
  - 结论：风暴 = 这四个函数应用被反复求值/重走；恒等替换仍生成 Call 节点
    而成本坍塌，说明"走 Call 节点"本身便宜，贵的是**走函数体展开的结果**。
- 剩余 4.02s ≈ 旧 prelude 0.75-0.9s + 新库 2700 行的正当 elaboration 成本
  ~3.1-3.3s（这部分是真实内容成本，非病理）。

### 13.4 修复建议

- **P0（预计 prelude 24.7 → ~4-5s）**：为 `pred`/`log2Up`/`div2Up`/
  `maxNat`/`minNat` 添加 Rust prim 覆盖（cxt.rs add_builtin 基础设施现成，
  参照 round 11 的 `count_nat_forced`）。具体 Nat 链上 O(n) 直走、Rigid
  参数上原地卡住，均不再生成待重走的 Call/Match 展开树。语义不变（区别于
  本轮的恒等实验），验证门槛：22+ 示例完整 note 块逐字节 + 326/157 测试。
  用户侧同样受益：17-stream 0.72s 中实例化 streamFifo 的宽度计算属同族。
- P1（若 prim 后仍有残余）：stuck 宽度表达式的结构化共享（按 (Rc 指针,
  decl 版本) 的 Call-force 记忆化）。round 8 对 eval 记忆化的负结果教训
  适用：prim 副作用（Val::Decl → change_mutable 等）必须门控，一次性
  求值的记账开销可能吃掉收益——先测 P0 残余再决定。
- P2（观察项）：测试套件每 Backend 克隆的 prelude 状态随库增长（~28.5k
  meta → 更多），143s 套件时间中除 prelude 外可能含克隆放大，P0 落地后
  复测再评估。
- 顺带发现（功能非性能）：`lib.rs load_prelude_impl` 的 builtin 文档注册表
  未随新文件扩展（缺 hdl-utils/stream/crossclock/bus-proto/misc-io/misc
  六项），对这批库函数的 goto/hover 跳不进 builtin 源码。

### 13.5 方法学记录

- 每进程 ~25s 使 min-of-3 全量扫描不可行（27 文件 ×3 ×25s）；本轮以
  单次墙钟 + 探针窗口为准，量级结论不受影响。
- 采样器两处坑（再犯即第三轮）：tick 仅挂 infer_expr 入口（选择偏差）+
  release-profiling 下 LTO 仍内联 force/eval（帧不可见）。归因应优先
  FUNC_PROF 计数器 + 按名直方图 + 因果替换实验。

---

## 14. 第十三轮（2026-08-16）—— 系统性 Nat prim 层：完整实现后测得净收益为零，已撤销（负结果）

> 按 round 12 §13.4 的"彻底版"方案执行：25 个 Nat 函数的 Rust prim 覆盖
> （算术/比较/位宽/元级工具全套）+ 值槽中性化 + quote OpCall 显示对等 +
> unify Decl/Flex 修复。实现-调试-测量全流程完成后**整体撤销**，工作树
> 恢复 r12 基线（326 测试复验通过，prelude 24.3s）。**唯一落地项**：lib.rs
> builtin 文档注册表补 6 个新文件（hover/goto 功能缺口，+6 行）。

### 14.1 机制层面的发现（未来任何 prim 化尝试都会撞上的四类坑）

1. **count_nat_forced 把 succ(卡住) 误读为 0**：它对链尾非构造子返回
   0，而 succ len（Vec/GADT 索引的标准形状）恰恰是这种链。prim 用它读
   参数会把符号索引"算"成 0，Vec[T](succ len) 的构造子可达性检查全线
   崩溃（vec.typort 全部 unreachable pattern）。三态链走（zero 终止才
   Some(k)，链尾卡住即 None）是必须的。
2. **prim 必须是定义体的忠实 WHNF 镜像，不能只做"全具体才计算"的闭式
   求值**：解释器对 add(x, succ m)（m 为 Rigid）会规约出 succ (add x m)
   ——这是 rfl 可证的定义等价，证明文件（adder_proof）全靠它。闭式
   prim 在参数部分卡住时拒绝，产生与解释器不同的卡住形态，unify 失败、
   证明雪崩。正确写法是逐层 nat_step 镜像每一步 match，卡住处以中性
   Val::Decl spine 为规范叶（op_spine）。
3. **force(Val::Decl spine) 对 prim 结果递归 re-force 会死循环**：忠实
   镜像的规范结果内嵌 spine 叶（succ^k(spine)），re-force 叶子再次触发
   同一 prim、再造同形 spine——无限递归栈溢出（adder_proof/01-basics
   实测）。prim 结果按契约已是规范 WHNF，force 应直接返回（v_app 路径
   本就不 re-force）。
4. **unify 的 (Decl, X) 燃料重试臂排在 Flex 吸收之前**：prim 拒绝产生
   的 spine 与 meta 相遇时被卷进 quote→eval 重试直到燃料耗尽
   （UInt[width2+width1] vs ?meta 失败）。需要 (Decl,Flex) 直通 Flex
   臂 + 重试无进展即停。另：quote 的 spine→OpCall 显示对等必须限制在
   attach 集合内（否则 string_concat 等老 prim 的显示被误改）、args
   顺序是应用序（spine 是 newest-first）、body 不得二次求引
   （hdl-verilog 曾因此 0.83→7.0s）。

### 14.2 性能结论（全部坑修完后的实测）

- **prelude 总量不变**（~25s）：Call/Match 风暴确实被消灭（force(Call)
   计数归零），但同一批 def 的重走成本**原样转移**成 Sum 1.95 亿 +
   SumCase 1.9 亿 + Rigid 8300 万的 re-force——总量仍 ~6.93 亿次。prim
   把"卡住 Match 的重走"换成"具体值的重走"，而求值器对值图无任何共享/
   记忆化，每次重走都是全价。
- **指针键控的 prim 结果缓存无效**：重 force 打在 v_app 每次新建的
   spine 节点上（指针不命中）；同一现象解释了 round 8 记忆化实验的失败。
- **bignat 测试回归**：0 + 100000 等用例从毫秒级劣化到分钟级——解释器
   的 Call 节点体即缓存（求值一次），prim 每次被 force 都重走 10 万步
   链并重建 10 万节点。
- round 12 的恒等替换实验（4.02s）因此被证实**高估了可达收益**：恒等
   函数破坏了宽度语义，下游消费"错误宽度"做了更少的工作。

### 14.3 结论与真正的下一步

- 在当前求值器架构（不可变 Rc 值图、force/eval 无记忆化、quote↔eval
   往返重建节点）下，**点级优化（prim / 点级缓存）已两次被证伪**
   （round 8 的 eval 记忆化、本轮的 prim 层）。风暴的根源是结构性的：
   检查路径对同一计算的大量重复强制。
- 值得投入的方向（与 round 8 §9.4、round 10 §10.3 一致，本轮再添证据）：
  1. **求值器层面的值图共享**（NbE 风格、值节点自带 memo）——让重
     force 免费而不是让单次更快；
  2. **LSP 增量 elaboration**（老项）：用户侧每键击全量重推的上限问题；
  3. **加载期 def 体求值的懒化**（create/tree 体按模块缓存，round 8 末条）。
- 本轮全部实验代码已撤销，git 历史之外无残留；14.1 的四类坑写成记录，
  供未来重试时直接绕开。

---

## 15. 第十四轮（2026-08-20）—— 复测基线：prelude 固定成本现为 17.6s，热点与 round 12 一致

> 分支 master（bbe350f，LSP 功能提交之后，未动本轮代码）。方法：
> TYPORT_PRELUDE_PROF 逐文件/逐声明探针 + 加载期 FUNC_PROF 快照。
> 探针保留为**常驻诊断工具**（env-gated，关闭时零开销；区别于 round 12/13
> 的临时实验探针，这是给后续轮次复用的正式工具）。

### 15.1 复测结果（release，单次墙钟）

- prelude-only（tiny 文件 def warm: Nat = 0）总墙钟 **17.6s**（round 12
  记录 24.7s；差异来自当时探针/机器开销，量级一致）。
- 逐文件（parse+expand 均 ≤0.01s，成本 100% 在 infer 循环）：
  hdl-crossclock 6.16s / hdl-misc-io 4.73s / hdl-stream 3.50s / hdl-misc
  1.38s / hdl-utils 0.82s / hdl-verilog 0.58s / hdl-check 0.21s。
- 逐声明（>5ms 门槛）：**streamFifoCC 4.73s / dividerCore 4.64s /
  streamFifoConnect 1.81s / streamFifo 0.83s / ccByToggleUInt 0.77s /
  watchdog 0.73s / pulseCCByToggle 0.43s / timer 0.39s** —— 与 round 12
  热点完全一致，8 个声明占 prelude 总成本 ~81%。
- 加载期函数级（accumulated）：**force 698,527,036 次**（round 12 同量级），
  check 490s/42,433 次、infer_expr 75s/114k、unify 26.7s/199k、eval
  23.3s/5.05M、check_universe 13.7s/10.8k。
- force 入口形状（全量，TOTAL 与 force 计数逐位相等）：Sum 195.3M +
  SumCase 190.5M + Rigid 78.6M + LiteralIntro 69.9M + Obj 54.8M +
  Match 48.9M + Call 48.9M + Decl 10.7M。→ 当前代码**同时**具备 round 12
  的 Match/Call 风暴（各 48.9M）与 round 13 prim 时代的 Sum/SumCase 具体
  值重走（195M/190M）——round 13"成本转移到具体值重走"的结论在未加 prim
  的当前代码里同样成立。

### 15.2 本轮排查并排除的候选

1. **unify 的 (Decl,_)/(_,Decl) 燃料重试**（round 13 §14.1-4 病理）：
   counter 实测仅 8,080 次/加载期，且每次 quote→eval 的对象不变——不是
   成本（预取计数后移除，未改代码）。
2. **per-Backend 克隆放大**（round 12 §13.4 P2）：probe_timing 现
   01-basics 156ms（round 11 110ms），克隆只多 ~45ms，非此前工作树 1.1s
   所暗示的 10×——那 1.1s 是 round 13 实验代码的残留测量，已被当前数据
   覆盖（probe-out.txt 已重采为 15 文件 131-450ms）。
3. **解析/宏展开**：全部文件 parse ≤ 0.01s，非热点。

### 15.3 结论

- prelude 17.6s 的根源仍是 **~7 亿次 force 调用的固有成本**（点级优化两次
  证伪后，本轮复测确认 round 12/13 分析不变）。用户文件侧重推成本仍健康
  （131-450ms/文件）。
- 下一步仍是 §14.3 的三条结构方向（NbE 值共享 / LSP 增量 / 加载期 def 体
  懒化）。**新增证据**：cost 主体在 check（490s accumulated）而非 eval
  （23s），故"加载期 def 体懒化"对 prelude 固定成本帮助有限——除非同时
  缓存检查结果；LSP 用户侧增量与 NbE 值共享仍是最大杠杆。

---

## 16. 第十五轮（2026-08-22）—— force 指针备忘：prelude 22.4s → 6.0s（3.7×），round 14 的"NbE 值共享"方向落地

> 分支 master（c00712d + 本轮改动）。方法：FUNC_PROF force 深度分拆 +
> 指针冗余度探针（临时，已移除）→ 因果明确后实现。改动集中在
> `L13_namespace/mod.rs`（+134）、`cxt.rs`（+9）、`lib.rs`（+14）。

### 16.1 归因（实现前的两个决定性测量）

1. **深度分拆**：636,627,783 次 force 调用中 **99.7%（634.45M）是 force
   自身的递归重入**（force(SumCase) 走 typ+全部 datas、force(Call) 走
   body+args、force(Obj) 走 x），外部入口只有 2.18M 次。风暴不是"很多
   地方调 force"，而是"每次外部 force 把整棵卡住值深走一遍"。
2. **指针冗余度**：全部 636M 次调用的输入里只有 **188,292 个不同
   `Rc<Val>` 指针**（~3400× 冗余）。外部入口多为叶子形状，真正的放大器
   是 Obj/Call/Flex 复合入口 × 平均 ~600 节点的树（模块树值、卡住的
   宽度/类型树）。
   → 结论：按输入指针缓存 force 结果即可消掉几乎全部风暴；这正是
   round 8/13/14 反复指向的"让重 force 免费"，只是做在 force() 这一层，
   不需要改 Val 表示。

### 16.2 实现（`FORCE_MEMO`）

- **键/值**：`HashMap<usize, (Rc<Val> 输入 keepalive, Rc<Val> 结果, u64 版本)>`，
  thread-local（无锁、天然绕开 Infer 的 Send+Sync 约束）。只对
  `SumCase | Call | Obj` 三种复合形状走 memo；其余形状是 O(1) 叶子臂，
  直接进 force_inner（连哈希查找都省）。
- **正确性三支柱**（round 8 记忆化失败的教训逐条对应）：
  1. **keepalive**：条目持有输入 Rc，地址不可能被新值复用（round 8
     明确过的坑）；
  2. **taint 传播**：walk 途中 consult 了不可抽象状态——meta 表
     （解会变，ns 探测还会快照回滚）或有副作用 prim（mutable 全局/
     文件 IO/诊断）——就 bump 线程局部计数器；计数器在 walk 中动过的
     条目一律不插入。与 round 8 的"子树安全预扫描"不同，taint 在
     本来就要做的同一次遍历里传播，零额外遍历；
  3. **prim-ness 版本**：force 读的唯一 decl 表状态是名字的 prim-ness
     （Decl/prim-Call 两臂）。`Cxt::decl` 的 prim-ness 变更（注册
     nat prim、shadow）与 lib.rs 两处移除 prim 条目的地方 bump 全局
     `PRIM_VERSION`；条目记录版本，lookup 不匹配即 miss（惰性失效，
     跨线程安全）。纯 prim 名单 `prim_is_pure`（nat 五则运算 +
     nat_to_dec/width_range + string 三件），其余全部按 impure 处理。
- **epoch 清理**：prelude 每文件边界 + 加载结束 + 每次 on_change 开始
  `force_memo_clear()`；另有 1M 条目 CAP 兜底。这不是正确性要求，
  是内存卫生（见 16.3 的教训）。

### 16.3 途中踩的坑：批量 drop 回归（已修复）

首版只在 on_change 开头清 memo，用户文件 change 从 0.17s 恶化到 0.53s：
prelude 加载期间的中间垃圾值被 memo keepalive 钉住，直到下一次 clear
才**一次性**级联释放（自定义迭代 Drop 走数百万节点，0.35s）。相位计时
定位后改为 per-file epoch，垃圾死亡摊回加载期内，用户侧恢复 0.172s。
教训：memo 的 keepalive 会把"随用随丢"变成"批量丢弃"，epoch 边界必须
跟垃圾产生节奏对齐。

### 16.4 结果（release，min-of-3，本机）

| 指标 | 前 | 后 | 加速 |
|---|---|---|---|
| prelude 固定成本（总墙钟） | 22.4s | **6.0s** | 3.7× |
| force 调用次数 | 636.6M | **4.41M** | 144× |
| check（accumulated） | 509s | 113s | 4.5× |
| eval / unify（accumulated） | 23.6s / 22.9s | 5.2s / 5.7s | ~4.5× |
| hdl-crossclock / misc-io / misc（逐文件） | 5.73 / 8.34 / 5.84s | 1.05 / 1.68 / 1.11s | 4.5-5.5× |
| 用户文件 probe（15 文件） | 177-597ms | 175-584ms | 持平略好 |
| 峰值内存（tiny 文件进程） | 7MB | 7MB | 持平 |

用户文件侧无变化的原因：单次 elaboration 内的值几乎全是新节点（指针
不重复），冗余主要存在于 prelude 的跨 def 共享图里。

### 16.5 验证

- `cargo test --lib L13`：338 全过；集成 12 套件全过（hover 1 +
  completion 2 失败为 HEAD 存量，stash 复验确认）。
- 27 个示例（examples/ + examples/hdl/）完整输出与 HEAD 基线**逐字节
  一致**（仅计时日志行不同）。
- 边界手动用例：用户 shadow `nat_add`（被语言 redefine 拒绝，版本机制
  作为纵深防御保留）；`10000+10000`/`300*300` 大数算术正确。
- `cargo test --lib L13` 套件墙钟 95.4s。

### 16.6 遗留观察项

- 剩余 6.0s 的构成（accumulated）：check 113s（inclusive 嵌套主导）、
  unify 5.7s/191k 次（~30µs/次）、eval 5.2s/5.0M、quote 1.2s/389k、
  check_universe 2.96s/10.8k。热点 def 不变（streamFifoCC 1.25s /
  dividerCore 1.07s / streamFifoConnect 0.49s），但已无单一"风暴"形状
  ——force 入口直方图回到叶子为主。下一杠杆按 §14.3 仍是 LSP 用户侧
  增量 elaboration。
- FORCE_MEMO 为 thread-local：若未来 LSP 真正多线程并行 elaboration，
  各线程独立建缓存（正确性无关，内存 ×线程数）。

---

## 17. 第十六轮（2026-08-22）—— 剩余 6.0s 的彻底归因：无冗余线性工作（负结果）+ FUNC_PROF 升级为 exclusive 计时

> 承接 round 15（`1334cba`）。目标：prelude 6.0s 里还藏着什么风暴。
> 方法：FUNC_PROF 升级 exclusive + 十余个临时探针逐一验证/排除
> （全部已移除，仅保留 exclusive 计时与逐 def eval 列两个诊断改进）。
> **结论：无风暴。剩余成本是 HDL prelude 库检查期"真实线性求值量"
> 的常数开销，进一步优化需要架构级改动**（详见 17.3 路线）。

### 17.1 exclusive 计时升级（本轮唯一落地代码）

`ProfGuard` 改为**独占时间**：thread-local 子时间栈，嵌套 profiled 调用
的时间记入内层计数器，打印的各行相加 ≈ 墙钟（原 inclusive 版本
check 490s 这类数字不再出现）。prelude 加载循环的逐 def 行同时新增
`eval` 时间列（该 def 检查期间的 eval 独占增量）。用法不变
（`TYPORT_PRELUDE_PROF=1`）。

### 17.2 归因过程（排除法，全部带数据）

exclusive 计时下 prelude ~5.9s 的分布：**eval 4.76s（自时间，503 万次
调用）**，其余全部 <0.4s。于是问题变为"eval 的 4.76s 是重复浪费还是
真实工作"，对每个候选假设做了测量：

| 假设 | 测量 | 结论 |
|---|---|---|
| class 三遍检查的 Raw::Tm 重求值 | 6476 次 / 0.003s | 排除（round 5 已消） |
| eval (tm,env) 指针冗余 | 105 万外部入口 / **86.1 万不同 (tm,env)** | 排除（~1.2× 冗余，不可 memo） |
| unify (Decl,_) 燃料重试的 quote→eval | 1000 次 | 排除（round 15 的 is_prim_application 门控后已近乎消失） |
| meta 风暴（fresh_meta 331 万？） | fresh_meta 仅 3.41 万次 | 排除 |
| trait_wrap 运算符重推理 | 6752 次 | 排除（量级不足） |
| mutable 重执行（round 9 复发？） | change_mutable("ModuleTree") 5563 次 / WhenStack 4100 次 | 排除（静态调用点同量级） |
| when 栈深遍历（andCond/wrapLevels/levelCond 占 Tm::Call 求值 97%：104 万/52 万/52 万次机器遇见） | WhenStack 深度 max=2 avg=0.6；wrapWithWhenContext 仅被遇见 2476 次 | **机器步计数是内联展开的遇见数，非执行放大**；栈浅、无重执行 |
| quote 产物爆炸（往返重放） | 全部 quote 输出合计仅 6399 个 Call 节点 | 排除 |
| def 体重复求值 | per-let 计时：最慢单 let 0.138s（hdl-verilog 字符串拼接 header），streamFifoCC 的 ~35 个 let 全部 <20ms | 成本均摊在每个 let 的检查递归里，无单点 |

**机器步分布**（39.6M 步 × ~127ns/步 ≈ 5.0s）：Var 11.8M、App 6.8M、
Lam 4.9M、Decl 4.1M、Match 3.2M、Call/Sum 各 2.15M、Meta 1.33M、
Let 1.24M。Lam 构造 4.9M 次与闭包应用量自洽（v_app 283 万）。语法
节点比例正常——**这是 ~2700 行 HDL DSL 库在检查期执行构造子应用
（每个赋值/信号/when 语句在 let 值求值时真实运行）的线性总量**。

### 17.3 每步 ~127ns 的构成与真正的下一步

单步成本偏高（理想 20-50ns）的主因：

1. **全局 `use std::sync::Arc as Rc`**（list.rs 等）：所有值/项节点的
   clone/drop 走原子 refcount（x86 LOCK 前缀 ~20 cycles）。40M 步
   × 每步 2-4 次原子操作 ≈ 1-1.5s。改真 Rc 要求 Infer/Cxt 摆脱
   Send+Sync（LSP 的 hover_table 跨线程共享 Infer）——线程模型重构。
2. 机器循环每步的 `tm.clone()`/`env.clone()`（Arc inc）+ Frame
   push/pop。
3. `Tm::Var` 的 `env.iter().nth(i)`：cons 链走 i 步（11.8M 次 × 平均
   索引深度）。

结构性方向（按杠杆排序，均超出"补丁"量级）：
- **LSP 用户侧增量 elaboration**（老项）：每键击全量重推 0.17-0.53s，
  是输入延迟的根本上限；
- **Arc→Rc + 单线程 elaborator + 跨线程快照**：预计 prelude/用户侧
  再 ~20-25%；
- **检查结果缓存**（def 粒度签名→已检查 Tm/Val）：跨键击复用，配合
  增量 elaboration 才有意义。

### 17.4 方法学教训（继 round 9 §10.4、round 13 §13.5）

- **探针改变语义**：给 `change_mutable_default("WhenStack")` 加深度
  观察时提前 `return Some(r)`，跳过了 mutable_map 写回——后续一轮
  测量（eval 从 503 万骤降到 198 万）全部作废才发现。**侵入 prim 内部
  的探针必须走完原路径**；测量数据突变应第一时间怀疑探针而非被测
  系统。
- 机器步按 Tm 变体/Call 名的"遇见计数"会高估执行语义：内联体
  （Tm::Call 的 body）在每次外层求值时整体重走，遇见数 ≈ 调用点数 ×
  内联链深，不代表独立执行。归因时应配合**外部入口计数 + 副作用
  prim 执行计数**（如 change_mutable 次数）交叉验证。

### 17.5 验证

- 干净构建（探针全移除）prelude 5.97-6.03s（min-of-3），与 round 15
  提交基线一致；用户文件 spot-check（10-bundle 0.52-0.53s）持平。
- `cargo test --lib L13`：338 全过。probe-out.txt 已刷新。
