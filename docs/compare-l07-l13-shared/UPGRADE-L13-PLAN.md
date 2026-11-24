# L13 升级计划（2026-11-24 · 按 FINAL §7 的"最低成本七件事"）

> 用户指令：「那就升级 L13 吧」。本文件是**可执行补丁清单**，不是又一份分析。
> 默认档 = **A 档：定向回灌 + 修缺陷 + 补门禁**（不动 L13 架构、不换载体）。
> 每条含：改哪个文件、改什么、为什么、验收命令、回退点。开工前请确认档位（见 §7）。

## 0 现状基线（开工前记录）

| 项 | 值 |
|---|---|
| 分支 / HEAD | `master` / `911628b3`（工作区另有未跟踪 `docs/compare-l07-l13-shared/`、`tmp/`） |
| 工具链 | cargo 1.98.1 / rustc 1.98.1（`rust-toolchain.toml` 固定） |
| 构建可行性 | **可行**：`cargo check --lib` 增量 0.3 s；F 盘剩 26.4 GB；`target/` 86 GB 已热 |
| L13 层内用例 | 静态 `#[test]` 445（23 个 `*_tests.rs`，含 `legacy_tests.rs` 139） |
| 门禁 | `tools/gate_l13.sh`（lib + `l13_fast_parity` + `twin_engine_tests` + `hdl042_engine_tests`）；**`l13_fast_parity` 被 `#![cfg(feature="l13-twin")]` 关成空跑** |
| 跨层门禁 | 仅 `tests/prim_identity_cross_layer.rs`（7 层 × 5 条 prim 判等断言） |

> 上一轮（7 名分析员）的结论见 [FINAL.md](FINAL.md)；本计划只挑**低风险、高收益、可独立回退**的项。

## 1 补丁清单（按收益/风险比排序）

### P1 · 修 L13 缺失模式诊断（独立缺陷，用户可见）

**症状**：非穷尽 `match` 的诊断在 HEAD 是**单行 3116 字符、2005 个 `_`**（如 `succ(_, _, …)`）。
**位置**：`src/L13_namespace/pattern_match.rs:50`（用 `{}` 打 `pat`）+ 见证模式构造处（`04-match.md` §4.1 已定位到"arity 取错字段"但未定位到具体行，`[未核实]`）。
**改法**：
1. 用 `L13BENCH_DIAG=1` + 最小复现（`enum Nat{zero,succ(x:Nat)}` + 缺 `succ` 臂的 match）先定位**见证模式的 arity 来源**；
2. 修正 arity / 只按构造子真实字段数展开；
3. 在诊断产出处加**长度上界**（超过 N 字符截断为 `...`），并补一条断言测试。
**验收**：`cargo test --release --lib L13_namespace::`（613+ 全绿）+ 新增 1 条复现测试；用 `target/release/typort.exe check` 对复现文件确认单行 < 200 字符。
**回退**：单文件、单函数级改动，`git revert` 即可。

### P2 · 回灌纯防护项（L07–L12 有、L13 无）

四小项，每项独立可回退。**先逐项确认在 L13 的等价插入点**，不要照搬 L07 的代码（值表示不同）。

| 项 | L07 锚点 | L13 等价插入点 | 做法 | 风险 |
|---|---|---|---|---|
| `pretty` 深项保护 `MAX_DEPTH=1024` | `L07 pretty.rs:17-29,82-89` | `L13 pretty.rs`（当前 `pretty_tm_indent` 自底向上 `format!`） | 加 depth 参数 + `DepthGuard`/`thread_local`，超限输出 `…`；同时保留 L13 的 `pretty_nat` 迭代化 | 低（仅显示层） |
| `occurs_transitive`（两跳环守卫） | `L07 mod.rs:442-452`，用于刚性解臂 | `L13 mod.rs` 的刚性解臂 / `unification.rs` 解 meta 处 | 补传递扫描（浅扫 + 传递），命中即失败而不是靠 fuel 烧穿 | 中（动合一失败路径，需 `l13` lib 测试 + `gadt` 跨层用例） |
| `TYPORT_UNIFY_FUEL` 环境覆盖 | `L07 mod.rs:779-787` | `L13 mod.rs:1468`（`UNIFY_FUEL=4096` 常量处） | 读环境变量并按需覆盖（保留默认 4096） | 低（默认行为不变） |
| `decl_cache` / `trail` 惰性回滚 | `L07 cxt.rs:106-142,365-369` | `L13 cxt.rs`（`Rc<BiMap>` 每次 `make_mut` 深拷，`cxt.rs:330,1209-1210`） | 先做**测量**：深作用域下 `clone_without_src_names`/`refresh` 的实际分配量（`l06l13mem.exe`/`l13bench --mem`）；**只在证明有收益时**再改 | 中（改上下文表示，影响面大）——**建议默认不做，只出测量结论** |

**验收**：每项单独 `cargo test --release --lib L13_namespace::` + `cargo test --release --test l13_fast_parity --features l13-twin`（见 P4）。
**回退**：每项一个 commit，独立 revert。

### P3 · 补 L13 侧完全缺失的共有机制测试（零代码风险，纯加测试）

`07-evidence.md` §3.5 指出三条"L07 时代就有、L13 完全没有测试"的语言面：

| 机制 | L07 侧覆盖 | L13 侧 | 补法 |
|---|---|---|---|
| `def` 撞构造子裸名（`redefine`） | 有 | **无**（L13 直接接受） | 在 `legacy_tests.rs` 或新文件加钉子：先钉**当前实际行为**（接受），并在注释里写明这是已知分叉（见 P5 登记） |
| 裸构造子值 `println succ` | 有 | **无** | 同上：先钉当前行为 |
| 泛型构造子值 `println nil` / `List::cons` | 有 | **无** | 同上 |

**关键**：这三条不是"修复"，是**给已知分叉上锁**——先有测试，未来谁改都会红。
**验收**：新增测试必须**先跑通当前行为**（如果当前行为本身是 panic/垃圾输出，那就先记录成 `#[ignore]` + 注释，不要伪造通过）。

### P4 · 恢复孪生 parity 门禁（把"封印"改成"夜间/显式 job"）

**现状**：7 个 `lNN_fast_parity` 首行 `#![cfg(feature="lNN-twin")]`，`Cargo.toml:186-198` 的 feature 默认关，`gate_l13.sh`/CI 不传 `--features` ⇒ **编成空、跑 0 例**。
**改法**（最小侵入）：
1. `tools/gate_l13.sh` 增加一个**可选**阶段：`GATE_TWIN=1` 时额外跑 `--features l13-twin`；
2. 新增 `.github/workflows/twin-parity.yml`（`schedule: cron` 或 `workflow_dispatch`），跑 `cargo test --release --features l07-twin,l08-twin,…,l13-twin` 的 7 个 parity 套件；
3. **不改默认构建**（保持夜间成本可控）。
**验收**：本地 `cargo test --release --test l13_fast_parity --features l13-twin` 能跑出真实例数（当前应为 ~630，见 `docs/l13-rebase-decision-2026-11-17.md` §现状验证）。
**风险**：低。若跑不通，说明封印期间孪生已经漂移——**这本身就是有价值的发现**，记录成 known-diff 而不是回滚。

### P5 · 新增跨层文本门禁 + known-diff 登记表

**现状**：L07↔L13 无任何自动一致性门禁；`tests/audit_crosslayer_probe.rs` 只写 TSV、**不做断言**。
**改法**：
1. 新增 `tests/l07_l13_known_diff.rs`：把 `07-evidence.md` §5 的 7 个 CORE 程序 + 4 条诊断程序钉成**两侧各自期望值**（不是"要求相等"，而是"记录当前的差"），任何一侧漂移就红；
2. 新增 `docs/l07-l13-known-diff.md`（登记 §4 的十条差异 + 五处文档/代码不一致 + `error vs Warning` 等级差 + `redefine` 规则差），每条带锚点与"是否计划修复"。
**验收**：`cargo test --release --test l07_l13_known_diff`。
**风险**：低（纯新增测试 + 文档）。

### P6 · 修三处文档/代码不一致（纯文档，零风险）

1. `src/L13_namespace/mod.rs:1474` 注释说预算耗尽记 `Undecided`，代码记 `Fuel`（`unification.rs:1259`）；
2. `src/L13_namespace/bump_spine_iter.rs:172` 说"结构比较由 unify 快路径承担"，实际孪生只有位相等 + memo；
3. `src/L07_sum_type/README.md` 的 `PM_FUEL` 已不存在（`grep -i pm_fuel` 两章均 0）。

## 2 明确**不做**的（A 档边界）

- 不换精化载体（σ ⟷ `update_cxt`）：这是 B/C 档，且 `rebase/l13-on-l12` 分支证明重定基也没换载体。
- 不重建值表示（`Rc<Val>`/`Nat`/`Call` 保持 L13 现状）。
- 不恢复 `struct_eq` 模块本身；只评估"卡住 match 自比较"是否需要一条 L13 版快路径（若 `l13` lib 测试或跨层 known-diff 显示真实成功率问题，再单独立项）。
- 不动 LSP 观察面契约的载荷语义（`check_issues`/`println_spans`/`failed_decls`）——那是消费端契约变更，需单独评审。
- 不改 `src/L07_sum_type`（本任务是"升级 L13"；L07 侧只读）。

## 3 执行顺序与并行度

```
P1（诊断 bug）┐
P3（补测试）  ├─ 可并行（不同文件）
P6（文档）    ┘
P2（防护回灌）—— 每项独立 commit，P2-a(pretty) / P2-c(env fuel) 可并行；P2-b(occurs) 串行且最后
P4（门禁）    —— 依赖 P3 完成（先用新测试确认真实例数）
P5（跨层钉）  —— 依赖 P3 的复现手段（同样的最小程序）
```

## 4 验收总门禁

1. `cargo check --lib`（0 警告新增）
2. `cargo test --release --lib L13_namespace::`（基线 613+，改动后不减）
3. `cargo test --release --test l13_fast_parity --features l13-twin`（真实例数，非空跑）
4. `bash tools/gate_l13.sh --release`（若环境无 bash，用 `tools/gate_l13.ps1` 等价项）
5. 新增测试全绿（P3/P5）
6. `git status` 干净、每个补丁独立 commit、`docs/l07-l13-known-diff.md` 落地

## 5 需要你确认的三件事

1. **档位**：A（本文件，推荐）/ B（A + 机制对齐）/ C（大爆炸重定基）。
2. **P2-b（`occurs_transitive`）与 P2-d（`cxt` 名字表）要不要做**：这两项动合一/上下文核心，收益是鲁棒性、风险是中等级回退；我默认**只做 P2-b**、P2-d 只出测量结论。
3. **P4 的门禁形态**：本地可选开关（`GATE_TWIN=1`）+ 新增 GitHub nightly workflow；如果你的 CI 不用 GitHub Actions，我改成 `tools/gate_twin.ps1` 脚本 + 文档里的手动流程。
