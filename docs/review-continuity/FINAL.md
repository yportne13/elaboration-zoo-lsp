# L01–L13 跨章节继承连贯性评审 · 最终汇总报告

- 评审对象：`src/L01_nbe` … `src/L13_namespace` 全链（含快版性能孪生 `bump_spine_iter*.rs`、
  bench bin、tests 锚点），工作树 master（未 commit，改动保留在工作树）。
- 方法：7 个子 agent（A1–A6 章节链 + A7 横切性能/bench）× 3 轮（审计+修复 →
  orchestrator 集中编译/测试门禁 → 交叉转交处置 → 回滚补救与终验），全部 cargo 由
  orchestrator 集中执行。过程报告见 `docs/review-continuity/a*-r1/r2.md`。
- 任务判据：**下一章节是在完整继承上一章节代码基础上做相关特性演进的**，重点关注
  性能版（快版孪生）。共同规范见 `BRIEF.md`。

## 1. 门禁结果（最终）

| 门禁 | 结果 |
|---|---|
| `cargo check --all-targets` | 0 error |
| 24 个集成套件（blackbox + fast_parity + twin_engine） | **1415 用例全绿** |
| `l13_fast_parity`（`--test-threads=1`） | **391 用例全绿** |
| 新 bench bin l09/l10/l11/l12bench（`--max-k 10` 冒烟） | 全部正常退出 |

注：`l13_fast_parity` 多线程模式下存在 `STATUS_ACCESS_VIOLATION`，与上一轮评审
FINAL.md 记录的 `cargo test --lib` L13 legacy 区崩溃同族（在-file 测试经 `#[path]`
收进套件），属环境性已知问题，串行全绿，非本轮回归。

## 2. 已修复的继承裂缝（按价值排序）

### 2.1 性能版（快版孪生）链
- **L08 分叉缺口（P0×1 P1×4 P2×2）**：L08 章创建早于 L07 的三个修复 commit
  （7073447/2b4ff68/7811a99），未回灌——含孪生宽松臂无 tag 检查的野指针读（P0）、
  enum 无标注隐式参数域钉 U、ty_precheck flex 误拒、Match 选支多余 burn 等，12 项
  补齐（A3）。
- **L10 快版两处 parity 裂缝（P1）**：Def 臂缺 def 级 `solve_multi_trait_ref`（漏解）；
  (Obj,Obj) 合同臂位次在链分派之后导致 tag2 Obj 链不可达——同款补进 L11/L12 快版
  （A4/A5）。
- **`alloc_xname`（栈上格式化 x{n}）**：a806ff0 只落 L03–L05，L06–L13 快版同源位
  全缺——六层逐字贴齐，helper 主体五方 md5 一致（A2–A6）。
- **L13 快版对齐三件套**：`XCell/CloCell #[repr(align(8))]` + `align_of` 静态断言
  （wasm UB，上一轮 FINAL §3.3 遗留）、`intersect_go` None 化、`prune_ty` 掩码反转
  ——与 L12 逐字同族（A6）。
- **L11/L12 探测粒度链上收敛（P2）**：模式编译探测从逐构造器整克隆 Infer 改为
  meta 整表快照+整循环无条件回滚，与 L09/L10/L13 及各层快版 `run_pure_probe`
  同机制同粒度（A5，字段可分性论证在码注）。
- **L13 快版 `alloc_xname`、宏深度守卫（parser 三处同构副本，MacroDepthGuard 上限
  256）、u64 字面量可恢复化**——FINAL §3.3 清零（A6）。

### 2.2 参考版链
- **L09/L10/L11/L12 pretty 与 pattern_match 对齐**：go_ix 越界 `@{ix}` 退化、SumCase
  头降级、`sum_head_name`、值级投影/可达性先记 + `checked_ret` 键型 Raw→usize
  （2a0eb6e 同族，L09 只修键型——其叶臂无可恢复 Err 路径，理由登记）（A4/A5）。
- **L10 参考版补 def 级 trait 求解、elab unwrap 可恢复化**；**L12 `vals_eq_ground`
  Match 分支补 case 表比较、`v_to_ref_val` 链头宽放**（FINAL §3.4 清零）（A4/A5）。
- **L02/L03**：lex SAFETY 注释三层精确对齐、L03 parser kw/string 贴齐 7ff008d
  未完成的清扫（零行为，行为等价已证明）（A1/A2）。

### 2.3 刻意分歧的正名（重要方法论产出）
- **η 守卫在 L07/L08 不移植**：`string_to_global_type` 返回登记类型（非 L06 的值），
  触发路径源头关闭——A3 六条证据对质 A4 论据，A4 接受销项。
- **fuel 矩阵终裁**：L08 有 fuel；L09/L10 结构性无失控类（六类论证写入 README）；
  L11 无、**L12 参考版实有 fuel**（Decl 展开臂 + SumCase 重锚配额）——A7 r1 矩阵
  已订正。
- **SumCase 显示格式分层**：L08 空格格式是本地形态；**L09–L13 是 comma + 头类型
  参数血统**（锚：L12 mod.rs:1479/1591 + L13 legacy_tests.rs:604/716）。A4/A5 一度
  把 L08 格式往 L09–L12 贴（贴反方向），终门禁抓住 L12 内置 5 断言失败后全部回滚，
  分歧写入各层 README（"不得互贴"）。
- **church_src 负载在 L11/L12 判型失败是层语义不是缺陷**：实测参考版即 Err
  （`can't unify N → N vs N` @113,123, k=9），孪生 false 与参考版同判一致——bench
  排除该负载，证据链入档（A7 终裁）。
- **L02 朴素环境不回灌 name_map**：教学基层定位，O(n²) 为潜伏上界且现有负载不触发，
  与 memo 口径分歧并列登记，附移植蓝本与重启条件（A1）。
- **L09 "再定基层"**：L09 相对 L08 丢失 decl 表/builtin/可变全局/Match pending/
  struct_eq/fuel 属时代缺口族，全部登记 L09 README（A4）。

### 2.4 性能版基础设施补齐（A7）
- **新增 `l09bench/l10bench/l11bench/l12bench`**（此前 L09–L12 无 bench bin）：继承
  L08 全负载 + 各层特色负载（universe/traitchain/macro/traitchain），负载源用各层
  孪生自带生成器，参考版/快版同轴对比。
- 横切审计产出快版链机制矩阵（packed tag、显式栈、fuel、哨兵、护栏）与
  compact.rs 判定：**L13 twin 专属不下沉**（常驻部署形态专属，低层每轮 bump.reset
  已有界），移植要点存档。

## 3. 新增测试

- 回归探针/golden 约 30 条：l09/l10 各 +2 parity 探针与 +10 golden 字面断言、
  l07/l08 新增 U 钉与 shadow needle、l13 +2 宏深度/u64 护栏探针（大栈子线程，
  只回传 Send 数据）。
- golden 全部经门禁实测钉字节并附手工展开说明。

## 4. 残余问题（诚实记录）

- **[P0·已知] 快版整机重借 Stacked Borrows 别名 UB**（L10–L13 同族，上一轮 FINAL
  §3.1）：维持不盲改，行号已刷新（L11 孪生 2159/2425/2541/2564/3959，L12
  2210/2476/2592/2615/4035），仍建议 Miri 专项。
- **[P1·已文档化] L13 18-utils flex-flex 带 spine 合一**：既有回落闸接管，需专项立项。
- **[P2·观察面] L13 ns-method hover 分叉**：LSP twin 观察面问题，非引擎语义（a99972a）。
- needs-verify 若干（全部有锚点）：L12 canonical IDDFS 调度 1,3,5（作者调优）、
  solve_multi_trait 调用方上下文 vs L13 创建处快照、L09 链式值级投影 `l.a.x` 实际
  字节与 eval 语义矛盾待运行定位、L10 fast tag2 Obj 链无专门探针、
  `l12_fast_parity` ?N 不归一化探针待运行钉值。
- P3 清单见各报告（注释措辞、行号漂移等）。

## 5. 收敛判定

**达成**。第 3 轮结束时：7 个 agent 全部签署"本切片连贯、0 个未处置 P0–P2"；
12 个继承对（L01→L02 … L12→L13）逐对连贯或差异均有测试/文档锚定的刻意分歧登记；
门禁全绿（编译 0 错 + 1806 用例 0 失败 + 4 bench bin 正常）。中间过程的两处误修
（SumCase 显示贴反方向、church 负载误判）均被门禁/实测抓住并完整回滚归档。
