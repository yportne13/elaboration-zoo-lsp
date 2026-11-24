# L07 ↔ L13 跨层 known-diff 登记表

> 2026-11-24 建立（UPGRADE-L13-PLAN.md P5）。用途：把两版**当前**的行为差显式登记，
> 而不是假装它们该一致。每条形如「差异 / 锚点 / 是否计划修复 / 锁定它的测试」。
> 判定规则：**接受/拒绝判定必须一致**（共有语义内核）；渲染文本**故意不同**；
> L13 明确放宽的少数规则登记为已知分叉。

## 1 已锁定（有测试）

| # | 差异 | L07 | L13 | 测试 |
|---|---|---|---|---|
| 1 | `def` 撞构造子裸名 | 报 `redefine succ` | **接受**（裸名让位给构造子） | `tests/l07_l13_known_diff.rs::known_diff_redefine_ctor_name` |
| 2 | Nat 渲染 | `Nat::succ(Nat::succ(Nat::zero))` | 原生 `2` | `tests/l07_l13_known_diff.rs::known_diff_nat_rendering` |
| 3 | 8 个纯共有 CORE 程序 | 判定一致 | 判定一致 | `tests/l07_l13_known_diff.rs::core_programs_keep_the_same_verdict` |
| 4 | 缺失模式诊断形状 | 单句中文，指向模式 span | 单句中文（本轮由 3116 字符的定长通配见证改为 `match 不完整：缺少构造子 succ`） | `tests/l13_diag_shape.rs` |

## 2 已知但未锁定（需要单独决断）

| # | 差异 | L07 锚点 | L13 锚点 | 影响 | 计划 |
|---|---|---|---|---|---|
| 5 | 不可达臂文案 | `分支不可达：模式 succ(n) 被前面的通配臂遮蔽` `pattern_match.rs:325-330` | `unreachable pattern: n`（指绑定名不指模式） | 用户可见文案退化 | 待定 |
| 6 | 精化载体 | σ 显式替换（`Val::VSub` / `frcs` / `subst_cxt`） | `update_cxt` + `refresh` | 同一 GADT 程序走两条路径 | **不修**（FINAL §7 路线 1：产品层独立维护） |
| 7 | 覆盖义务方向 | Undecided 按可达 ⇒ 要求覆盖 `pattern_match.rs:402-411` | Undecided 不计义务 `:203-214,653-659` | L13 可能静默接受非穷尽 match | 待定（需先有跨层语义用例） |
| 8 | `struct_eq` 结构快路径 | 有（`struct_eq.rs`，Match/Match 先试快路径） | 无 | 卡住 match 自比较成功率不同 | 待定 |
| 9 | 观测面载荷语义 | `check_issues:(decl 下标, 行)` / `println_spans` 真串 / `failed_decls` 有序 Vec | `Vec<String>` / 恒空 / `HashSet` | 消费端契约不同 | 待评审（涉及 LSP 消费方） |
| 16 | 孪生 hover 绑定器命名 | 参考版 `(n: Nat) → Nat` | 孪生 `(n': Nat) → Nat`（同样的 span 删去后又生成） | `tests/l13_fast_parity` 的 `prelude_full_observation_tables_match_reference`（`bump_spine_iter/observe.rs:1344`） | 封印 2026-11-23↔2026-11-24 期间产生的漂移；**本周唯一一条 "-Full" parity 红灯** | 待修（改孪生 `push_hover_decl` 的 binder 命名口径） |
| 10 | 孪生燃料 | `Fuel=Cell<u32>` 共享池，`(fuel exhausted)` 尾注 | force 无 fuel、unify 顶层写死 100、墙钟 `eval_budget` | 终止点确定性不同 | **不修**（产品选择） |

## 3 本轮已修复（不再是差异）

| # | 项 | 说明 |
|---|---|---|
| 11 | L13 缺失模式诊断 3116 字符 | 改为只打构造子名，1 行 < 200 字符；参考版 + 孪生同步 |
| 12 | L13 缺 `pretty` 深项保护 | 补 `MAX_DEPTH = 1024`（`indent` 计数器，无 thread_local 回退坑） |
| 13 | L13 缺 `TYPORT_UNIFY_FUEL` 环境覆盖 | 补 `unify_fuel_budget()`（OnceLock，缺省 4096，未设置时逐位不变） |
| 14 | L13 ‘MATCH_CMP_BUDGET’ 文档说记 `Undecided`、代码记 `Fuel` | 注释订正为 `Fuel` 分档，与代码一致 |
| 15 | 孪生 parity 被 feature 关成空跑 | `tools/gate_l13.ps1 -TwinParity` 恢复真实运行（`--features l13-twin`） |

## 4 维护规则

1. 新增已知分叉：先往本表加行，再加测试（列表在前、断言在后）。
2. 修掉一条：从 §2 移到 §3，并在对应测试里把「记录差异」改成「断言一致」。
3. 本表的每条都要能被 `cargo test --release --test l07_l13_known_diff` 或 `--test l13_diag_shape` 覆盖到；
   未锁定的条目要写清楚为什么不能锁（通常是缺跨层语料）。
