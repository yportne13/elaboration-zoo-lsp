# L01–L13 跨章节继承连续性评审 · 最终汇总报告

- 评审对象：`src/L01_nbe` … `src/L13_namespace` 全部 13 章，参考版与性能版（bump_spine_iter / L13 孪生）双线
- 工作树：`F:/projects/hermes/elaboration-zoo-lsp-cont`，分支 `review/l01l13-continuity`
  （基于 master `a99972a`；主线工作树未被触碰）
- 方法：6 个子 agent（A1:L01-03、A2:L04-06、A3:L07-09、A4:L10-12、A5/A5':L13、A6:全链矩阵+基建）×
  3 轮（审计+修复 → 门禁+路由落地+交叉审计 → 矩阵复扫+最终判定），编译与测试由协调者集中执行
- 提交：`8eff89c`（R1，36 文件 +881/−284）→ `cac125a`（R2）→ `7f88a55`（R3+P13）
- 过程报告：`docs/review-cont/a1-r1..r3.md`、`a2-r1..r3.md`、`a3-r1..r3.md`、`a4-r1..r3.md`、
  `a5-r1..r3.md`、`a6-r1/r2.md`

## 1. 门禁终态（分支 7f88a55）

| 门禁 | 结果 |
|---|---|
| `cargo check --all-targets` | 0 error |
| L02–L08 blackbox（17 目标） | 全绿 |
| l07–l12 fast_parity + namespace_tests | 288 通过 0 失败 |
| l13_fast_parity（单线程） | 393 通过 0 失败 |
| wasm32-wasip1-threads `check --lib` | 通过（新增对齐断言生效） |
| l01/l02/l03 bench 冒烟 | 正常（尾行栈溢出为 L01 readme 记载的递归变体演示） |
| l13 多线程默认模式 | 间歇 STATUS_ACCESS_VIOLATION——**基线 a99972a 同样崩溃（3/3、2/2 复现）**，非本轮引入，见 §4 |

## 2. 已修复（按主题归并，位点详见各轮报告）

### 2.1 传播黑洞清偿（上轮 L01-L12 评审的 L13 欠账）
- XCell/CloCell `#[repr(align(8))]` + align_of 断言（wasm32 真实 UB）、MacroDepthGuard（256，三展开点）、
  intersect_go 失配→None、prune_ty 掩码反转、u64 超大字面量可恢复化——均按 L11/L12 已合入形态移植（8eff89c）。

### 2.2 修复"只落部分章节"的传播遗漏（本轮主战场）
- **L01**：回灌防御守卫（65269fb 落了 L02–L13 唯独漏起点）回移。
- **L07/L08/L09**：Pi/Pi η 下探 quote 层级越界回移；L08 丢失的 L07「enum 隐式域钉 U」回移；
  L08 快版 ty_precheck 的 is_flex（L07 已修 L08 未跟进）；L09 Obj 剥链 U(0) 占位消除 + (Obj,Obj) 合同臂
  （L08 8988f7c 三件套传播）+ L09 钉 U(0)。
- **L10–L12**：SB 别名 UB 重写（§2.4）；η 可应用守卫补齐（v_applicable/vapp_ok，与全链对齐）；
  L10 solve_multi_trait unwrap 可恢复化 + 快版 Def 臂补 solve_multi_trait_ref；L12 val_match 假匹配修复
  （上轮 FINAL §3.2 的"L12/L13 已对齐"断言有误——or-模式第三臂仍放行目标侧 rigid）；
  L12 IDDFS 偶数预算（+=1 + <=，L13 镜像同构）；fuel 护栏前向传播（L08 有→L09 重写丢失→L10-L13 补齐，
  L13 参考版落地、孪生按家族一致不设池）。
- **L13**：val_match 假匹配镜像修复（参考/孪生共用 Synth 一处双效）；Pi/Pi quote 层级；
  参考版 fuel 池；Drop 推池前清 TLS 缓存加固（try_with 容忍析构序）。
- **P13·钉 U 全链**（A6 终轮矩阵复扫发现的最后断档）：enum 隐式无标注域（含 case 级隐式绑定器）钉 U(0)
  在 L09/L10/L11/L12/L13 双版落地——主线并行评审只覆盖了 L07/L08，两轮合并后 L07–L13 全链闭合。

### 2.3 探针/测试基建
新增回归探针：L08 钉 U+parity、L09 Obj 投影+钉 U(0)（is_ok+parity 双断言+失败诊断输出）、
L10/L11/L12/L13 钉 U(0)、L13 val_match、L12 val_match、L11/L12 packed-align、l13 宏深度/u64 护栏
（线程边界只回传 Send 数据）。README 订正（L01 变体数 22、examples/hdl 第 23 组）。

### 2.4 [P0] 快版 unify 的 Stacked Borrows 整机重借 UB——已修
L10/L11/L12 的 `mach_ptr` 整机重借改为**挂起-续跑驱动**：trait 合成点写 `solve_req` 挂起返回，
unify 驱动在字段借用死亡点以独占 `&mut self` 执行合成，每轮重新解构。`mach_ptr` 全消除，
新增 unsafe 为零。A1 独立交叉审计判 **SOUND**（等价性/嵌套/记忆化/NLL 四核查点全过）。
L13 孪生因 trait 求解被主线重写、续跑状态在栈帧局部，同款不可移植——已精确刻画并附四步立项方案
（a5-r2 §2），需 Miri 终裁，**留主线另案**。

## 3. 收敛判定

六切片终判：A1/A2/A3/A4/A5（L13 由 A5' 接续）**均 CONVERGED**；
A6 全局矩阵复扫（13 章 × 13 修复签名）**全部闭合或"合法缺位"**（该章无此代码路径）。
判定标准：第 N 章完整继承第 N-1 章 + 本章特性演进，无已知未处理的传播遗漏；
已文档化的主线另案（孪生 SB、hover/trait 求解分叉、AV、L12 快版 trait 文案分叉）不算阻塞。

## 4. 残余（全部有去向，不阻塞合并）

| 项 | 状态 |
|---|---|
| l13 多线程间歇 AV | 基线既有。已锁定触发配方：observation_tests × legacy_tests × ≥3 线程；PRELUDE_POOL 已用禁用实验排除为载体（4/5 仍崩）、mimalloc 未链接测试二进制亦排除；临时规避：`-- --test-threads=1`（单线程全绿）。主线立项（候选面：两引擎经进程级状态的其余交互） |
| L13 孪生 mach_ptr SB UB | 四步立项方案见 a5-r2 §2，需 Miri |
| L13 孪生 hover/trait 求解分叉 | 主线演进中（docs/l13-*.md 登记） |
| L12 快版 trait 错误文案分叉 | canonical-Val 桥上游分叉，套件文件头已登记剔除 |
| L09 v_app 卡住 match / check_universe U(0) | 模块头注/needs-verify 承接 |
| 嵌套 unify 擦除外层工作表（快版共模，新旧实现同） | A1 刻画，建议另案（mem::take 保存工作表） |
| l09–l12 无 blackbox | **主线 766bb94 已补 l09-l12bench**；blackbox 缺口仍开放（记录覆盖权衡） |

## 5. 主线重叠审计（终检，master 已推进至 bb5fe18）

主线在本评审进行期间独立落地了一轮同主题评审（7 agent，a99972a..bb5fe18，73 文件 +6131/−388）。
**两轮高度互补，合并是必需的**：

| 主题 | 主线 | 本分支 |
|---|---|---|
| L13 §3.3 同族（align8/宏守卫/prune/intersect/u64） | 5e98b54 ✓ | 8eff89c ✓（同族形态，合并冲突取任一） |
| P13 钉 U | L07/L08（7cfbb8e） | L09–L13（7f88a55）——**互补，合并后全链** |
| (Obj,Obj) 臂 / is_flex | L11-L12（d82006a）/ L09-L10（295ea69） | L08 ty_precheck / L09（R2）——章节互补 |
| L13 val_match 假匹配 | **未修**（or-模式第三臂仍在，typeclass.rs:289） | ✓ 已修+探针（**分支独有，合并务必保留**） |
| L10-L12 SB 挂起-续跑重写 / Pi/Pi quote 层级 ×4 / IDDFS / fuel 传播 / L13 参考版 fuel | 无 | ✓（分支独有） |
| vals_eq_ground case 表 / 探测隔离 | ✓（d82006a，超出本分支） | 记录为 needs-verify |
| l09-l12bench | ✓（766bb94） | — |
| η 守卫 L07/L08 | 裁定"触发源头关闭、刻意分歧登记" | 已加守卫（零行为加固）——合并时文档需统一口径 |

合并指引：以主线为基将本分支 rebase/merge；预期冲突集中在 L13 四文件与 L09-L12
（双份同族修复取任一）；**L13 val_match、SB 重写、Pi/Pi 层级、fuel、P13 L09-L13 五类为分支独有必须保留**；
η 守卫 L07/L08 取"守卫在位+注释指向登记"的合成口径。
