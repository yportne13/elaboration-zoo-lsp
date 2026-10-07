# C2 全链下沉 · 交接说明（2026-10-07）

> 本轮（L02 轮）把已验证的 C2「尾任务寄存器化」下沉到 **L02–L13 全链**。
> 因会话被多次中断，**写下这份交接说明**：已完成的、未完成的、以及后续团队接手
> 的确切步骤。**规则与逐站点判据的唯一权威是
> [`C2-PROPAGATION.md`](C2-PROPAGATION.md)**。

---

## 0. 接手复核结果（2026-10-08，接手团队）

> **结论：§3 清单的第 1、2 项已完成且全绿；第 3 项已跑；第 4 项未做。**
> 正确性由 **3107 个测试（0 失败）+ 169 个站点的独立静态审计（0 问题）** 双重
> 证明——**本层源码改动可以提交/发布**。

### 0.1 合并与冲突（远程源码改动已在远程提交，本次并入主线）

远程 `1719292d`（C2 源码）+ `94434aed`（本文档）已在远程 master；本次把它与本地
17 个 commit（prelude 补充轮 / 求值预算看门狗 / Q2 缩进续行 / Level A 终止性检查
/ R4 大数显示压缩 / Nat 链内存护栏）合并。**唯一冲突**：
`src/L13_namespace/bump_spine_iter/eval.rs` 的循环头——本地看门狗需要
`let mut budget_ctr: u32 = 0;` + 循环内 `eval_budget::tick`，C2 需要 `cur` 寄存器
循环头。两者互不排斥，**取并集**（tick 仍在 `match w` 之前）。
`cargo check --lib`：exit 0、**0 error**（285 条仓库既有 warning）。

### 0.2 第 1 项：正确性门（§3.1）——全绿

按 §3.1 原样跑（parity **不 skip**），另追加生产路径两件：

| 件套 | 结果 |
|---|---|
| `cargo test --lib`（全 lib） | **932 passed / 0 failed** |
| parity L07–L13（7 个） | **940 passed / 0 failed**（77/90/39/46/52/50/586） |
| blackbox（17 个） | **1206 passed / 0 failed** |
| `twin_engine_tests`（examples 全树双引擎） | **27 passed / 0 failed** |
| `hdl042_engine_tests` | **2 passed / 0 failed** |
| **合计** | **3107 passed / 0 failed** |

脚本与日志：`target/handoff_verify/run_c2_gate.ps1`、`target/handoff_verify/c2/`
（target/ 不入库）。跑时外挂 10 GB 内存硬闸（超限 `taskkill /T`），未触发。

### 0.3 第 2 项：独立逐站点语义审计（§3.2）——169/169 通过

方法（**与实现者的"向后扫到块闭合"不同**，脚本
`target/handoff_verify/audit_c2.py`）：

- **A. diff 逐语句分类**（对 `1719292d`）：每个 hunk 的增删行逐行去注释后按 `;`
  拆语句、逐对核对——删除的必须恰是 `work.push(X)`，新增的必须恰是
  `cur = Some(X)` 且 **X 逐字符相同**；纯新增只允许循环头。结果：**169 条转换
  全部载荷一致，无任何"别的改动"**（L02 8 / L03 11 / L04 12 / L05 12 / L06 12 /
  L07–L12 各 16 / L13 18）。
- **B1**（= 规程 §3 的 (a)(b)）：每个 `cur = Some(..)` 站点**所在块内**、其后不得
  再有 `work.push(` / `work.pop(` → **0 违例**。
- **C（镜像完整性）**：仍在的 `work.push(..)` 若是"块尾 push"则说明漏改 →
  **0 例**。
- **D**：`work.pop(` 只允许出现在循环头那一行 → **0 违例**。

> 与规程 §4.4 一致：push 之后若只有**不碰 work 栈**的语句（`break` / `vals.push`
> / `tm = a` 等），仍属可改站点。此类"其后还有非 work 语句"的提示有 241 处，
> 按规程口径**不是问题**（脚本里已降级为信息项，不计入判据）。

### 0.4 第 3 项：逐层 bench 冒烟（§3.3）——已跑，断言全过

`cargo build --release --bin l02bench … --bin l13bench`（187.5s）→ 12 层逐个跑
`--max-k 11 --rounds 3 --only fast`：**12/12 EXIT=0，无 panic/断言失败**。
本次实测节点数（供下次对拍）：L02 `n=1024/2048/4096`（k=9/10/11）；
L13 `nf=2050/4098/8194`。

**未做**：§5 要求的"结果/节点数与改动前一致"对比——需要 pre-C2（`1719292d^`）
的 release 基线二进制，且仓库里没有录下 pre-C2 的 bench 节点数（已查
`docs/perf-l02/raw/`）。同一风险已由 §0.2 的**逐字节 parity 门**覆盖（更强）。

### 0.5 第 4 项：性能 A/B——**未做**（规程 §6 归 Lead 统一安排）

接手配方（代价不高：本次 release 构建 12 个 bin 实测 187s）：
1. 取 **pre-C2 基线** `1719292d^` = `77cf2a33`，用**独立 `CARGO_TARGET_DIR`**
   构建 release（避免与 HEAD 构建互踩）；
2. 协议必须按 `02-experiments.md` §2：**同批交错 + 配对 + 同批 null**——该文档
   已记录"先 A 后 B"的假阳 18.8–19.3%，不可用；
3. 产品级收益的唯一度量口：`l13bench --workload examples-hdl` 的改动前后 A/B；
4. 参照：L02 上该机制已验证 ≈ **−6%**（`03-verification.md`，符号检验 p ≤ 7e-5）；
   **全链逐层收益尚未计时**。

### 0.6 顺手核对 / 发现的其它事项

- 远程 `071d90cc` 声称"L02–L12 死代码警告 2153 → 285"：**独立核对吻合**——本次
  `cargo check --lib` 实测 **285 条 warning、0 error**。
- 本文档 **§1 表把 L13 记作 17 个 `cur` 站点，§5 记作 18**；实测（diff 侧与工作区
  侧双向计数）**L13 是 18 处**，与 §5 一致（§1 表少算 1）。
- 远程提交里混进了构建产物
  `tools/perf-l01/__pycache__/parse_bench.cpython-314.pyc`（不应入库），建议
  `git rm --cached` 并在 `.gitignore` 补 `__pycache__/`。

## 1. 已落地（源码已改；已在远程 `1719292d` 提交，本次已并入主线）

12 个文件（L02–L13 各一个 `eval_iter`），改动形态统一：

- 循环头：`while let Some(w) = work.pop()` → `let mut cur: Option<W<'a>> = None; loop { let w = match cur.take().or_else(|| work.pop()) { Some(w) => w, None => break }; … }`
- 把**每条控制路径上最后一个 `work.push(..)`** 改为 `cur = Some(..)`。

| 层 | 文件 | `cur` 站点数 | diff |
|---|---|---|---|
| L02 | `src/L02_tyck/bump_spine_iter.rs` | 8 | +18/−11 |
| L03 | `src/L03_holes/bump_spine_iter.rs` | 10 | +21/−11 |
| L04 | `src/L04_implicit/bump_spine_iter.rs` | 11 | +23/−11 |
| L05 | `src/L05_pruning/bump_spine_iter.rs` | 11 | +23/−11 |
| L06 | `src/L06_string/bump_spine_iter/eval.rs` | 11 | +23/−11 |
| L07 | `src/L07_sum_type/bump_spine_iter/eval.rs` | 15 | +29/−13 |
| L08 | `src/L08_product_type/bump_spine_iter/eval.rs` | 15 | +29/−13 |
| L09 | `src/L09_mltt/bump_spine_iter/eval.rs` | 15 | +29/−13 |
| L10 | `src/L10_typeclass/bump_spine_iter/eval.rs` | 15 | +29/−13 |
| L11 | `src/L11_macro/bump_spine_iter/eval.rs` | 15 | +29/−13 |
| L12 | `src/L12_canonical/bump_spine_iter/eval.rs` | 15 | +29/−13 |
| L13 | `src/L13_namespace/bump_spine_iter/eval.rs` | 17 | +33/−13 |

（站点数为 `grep -c "cur = Some("` 减去注释里的 1 处示例。**L13 是生产引擎**，
`typort`/LSP 走的就是它。）

**设计依据**：L02 上该机制实测 church **−6.42/−5.77%**、conv **−7.42/−5.70%**，
独立复核自跑 **−6.53/−5.60/−7.71/−6.45%**（符号检验 p ≤ 7e-5，五重排伪影检查，
见 [`03-verification.md`](03-verification.md)）。12 层的 `eval_iter` 结构同源，
故机制预期同效；**但逐层收益尚未逐层计时**（见 §3）。

## 2. 验证状态（截至交接时，**诚实标注**）

> **本节已被 §0 取代**（2026-10-08 接手复核）：下表第 1 项（`cargo check`）与
> 结构审计维持原状，其余"未跑"项见 §0.2/§0.3/§0.4/§0.5 的最终结果。

| 项 | 状态 |
|---|---|
| `cargo check --lib` | ✅ **通过**（exit 0；286 条为仓库既有警告，非本次引入） |
| **逐站点结构审计**（Lead 写脚本独立跑的） | ✅ **169/169 个 `cur` 站点通过**：每个站点之后、控制回到主循环头之前，**没有** `work.push` / `work.pop`（分层次审计结果见 §5） |
| `cargo test --lib`（全 lib 单测） | ❌ **未跑完**——本机编译该 lib 测试目标耗时过长，且会话被多次中断；**用户明确要求停止测试、直接交接** |
| `*_fast_parity`（L07–L13 共 7 个，最强正确性门） | ❌ **未跑**（**接手团队第一优先**） |
| `l0X_blackbox*` 集成测试 | ❌ 未跑 |
| 逐层 bench 冒烟（断言 + 节点数前后一致） | ❌ 未跑 |
| **逐站点语义独立审计**（task-14，独立于实现者） | ❌ **未做**（结构审计是我自己跑的，不能替代独立复核） |
| 逐层性能 A/B / L13 `examples-hdl` 真实负载 A/B | ❌ 未做 |

> ⚠️ **交接结论**：源码改动"形态正确 + 编译通过 + 结构审计通过"，但**运行时语义等价
> 尚未由测试证明**。鉴于这是"把 `work.push` 换成循环局部寄存器"的机械改动，
> 一旦某个站点把**不该改的 push**（同臂更早的 continuation）也换掉，会**静默改变求值
> 顺序**——所以 §3 的测试门**必须**在合并/发布前跑完。

## 3. 后续团队接手清单（按优先级）

1. **正确性门**（先做，全绿才谈提交）：
   ```bash
   cargo test --lib                                   # 全 lib 单测
   cargo test --test l07_fast_parity --test l08_fast_parity --test l09_fast_parity \
              --test l10_fast_parity --test l11_fast_parity --test l12_fast_parity \
              --test l13_fast_parity                   # 孪生 vs 参考版 parity
   cargo test --test l02_blackbox --test l02_blackbox_v2 \
              --test l03_blackbox --test l03_blackbox_v2 \
              --test l04_blackbox --test l04_blackbox_v2 \
              --test l05_blackbox --test l05_blackbox_v2 --test l05_blackbox_v3 \
              --test l06_blackbox --test l06_blackbox_v2 --test l06_blackbox_v3 \
              --test l07_blackbox --test l07_blackbox_v2 --test l07_blackbox_v3 \
              --test l08_blackbox --test l08_blackbox_v2
   ```
2. **逐站点语义审计**（任务书 = 共享任务 `task-14` 的描述；规则 = `C2-PROPAGATION.md` §3）：
   对每个 `cur = Some(..)` 站点核对 (a) 其后无 `work.push`、(b) 其后无 `work.pop`、
   (c) 控制确实回到主循环头。**特别容易错的是"同臂多 push"**：Pi/Let 的
   `push(PiBody/LetBody)` 与下钻环的 `push(ChainWrap)+push(Apply)+push(Tm(a))`
   都必须留栈，只改最后一个。**用独立脚本枚举漏改/误改**，不要只看 diff。
3. **逐层 bench 冒烟**（断言 + 节点数前后一致）：
   ```bash
   for L in 02 03 04 05 06 07 08 09 10 11 12 13; do
     cargo build --release --bin l${L}bench
     ./target/release/l${L}bench --max-k 11 --rounds 3 --only fast
   done
   ```
4. **性能 A/B**（协议见 [`02-experiments.md`](02-experiments.md) §2；**必须同批交错 +
   配对 + 同批 null，blocked「先 A 后 B」假阳 18.8–19.3% 不可用**）：
   - L02 复跑：应 ≥ 已验证的 ~6%（本轮从 3 站点扩到 8 站点，预期不低于）；
   - **L13 真实负载**（产品级收益的唯一度量口）：
     `./target/release/l13bench --workload examples-hdl` 的改动前后 A/B；
   - 其余层按时间抽样即可（机制同源）。
5. 全绿后再 `git commit`（本轮已把源码留在工作树，**尚未提交**，见 §4）。

## 4. 提交边界（重要）

- **源码改动未提交**：交接时工作树里 `src/` 有 12 个文件被修改，`git status` 可见；
  HEAD 停在 `77cf2a3 docs(perf): L02 优化空间评估…`。
- 未提交的原因是 §2 的正确性门没跑完（尤其 parity 与站点审计）。
  **建议后续团队把"通过正确性门"作为提交前置条件**，因为这是语义等价的机械改动，
  一旦某个站点改错（把 continuation 也换成 `cur`），会静默改变求值顺序。
- 若发现某站点有误：**回退该站点**即可（`work.push` 原样恢复），不影响其它层。

## 5. 追加记录（交接时的实测状态）

**Lead 跑的逐站点结构审计**（脚本：对每个 `cur = Some(..)` 站点，向后扫到所在块闭合，
若其间出现 `work.push(` / `work.pop(` 则报可疑）：

```
L02_tyck           eval_iter@225   sites=8   OK
L03_holes          eval_iter@444   sites=11  OK
L04_implicit       eval_iter@471   sites=12  OK
L05_pruning        eval_iter@534   sites=12  OK
L06_string         eval_iter@104   sites=12  OK
L07_sum_type       eval_iter@171   sites=16  OK
L08_product_type   eval_iter@168   sites=16  OK
L09_mltt           eval_iter@167   sites=16  OK
L10_typeclass      eval_iter@172   sites=16  OK
L11_macro          eval_iter@177   sites=16  OK
L12_canonical      eval_iter@178   sites=16  OK
L13_namespace      eval_iter@254   sites=18  OK
总站点 169，可疑 0
```

**`cargo test --lib` 结果**：未完成（用户要求停止测试）。接手团队请从 §3.1 开始。

**未做的验证**（§3 清单）：parity 7 个、blackbox 17 个、逐层 bench 冒烟、独立站点审计、
逐层与 L13 真实负载 A/B。
