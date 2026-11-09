# D3 复杂度、简洁优雅、模块结构评估

> 作者：elegance-architect · 时点 2026-11-09 · 只读静态分析，**未运行 cargo/bench**
> 度量口径：`[码]` = 源码/构建配置核对；`[文档]`；`[推断]`。行数 = **非空行**（ReadAllText 逐行统计，
> 与 read/Select-String 行号一致）。⚠️ 与 FACTS.md §2 的差异见 §1 末尾——FACTS 的行数口径系统性偏低。

## 0. 结论先行

1. **复杂度的 80% 来自两个结构性决定，而不是语言/算法本身**：①"13 层 copy-forward"（每层一套完整实现，
   同一机制文件跨层 Jaccard 80–90%）；②"每层双引擎"（参考版 + bump 孪生，两套值表示/求值器/合一器）。
   真正独有的技术复杂度（NbE/σ/逐臂/arena）只占约 1/5。
2. **现状规模**：`src/` 层代码 **185,432** 非空行 / 284 文件，其中孪生 **85,411**、参考版 **100,021**
   （含测试 17,075 → 参考生产 82,946）；另有 bin 7,186、glue 12,290、`src/bench_head+bench_pre` 归档
   **25,334**、`.bak` **12,464**、`tests/` **34,963**、`docs/` **51,873**。**产品真正需要的能力 ≈ 18.5k 行**
   （L13 孪生层量级），即当前 230k 行 `src` 里约 92% 是历史层/第二引擎/归档/测试脚手架。
3. **单引擎判断（推荐）**：生产用**一个** arena/迭代引擎（孪生系），参考引擎冻结为 **test-only `oracle/` crate**
   （不进 product graph、不改 API）；7 层退化为 `tests/golden/L0x/` 快照 + 差分 oracle 一份。
   可删除/移出生产约 **82,946 行（46%）**，认知负担减半；性能不损失（孪生在全部层领先，见 FACTS §4）。
4. **不能省**：arena + 打包值 + 迭代内核 + 双记忆化 + σ（`Subst`/`VSub`/`frcs`/`SpecSolve`）——这些是
   正确性与性能主载体（L08 struct 32.3×、strchain 38.4× 的孪生优势靠它们），也是 D2/D5 的证据来源。
5. **可量化预算**：生产 core ≤ 18,000 行、单文件 ≤ 1,200 行、Val 变体 ≤ 16、Tm 变体 ≤ 26、unsafe ≤ 60
   （全集中在 `arena.rs`/`lsp_stdio.rs`）、环境开关 33→≤4、`.bak`/归档 = 0、跨层复制 = 0、
   文档 ≤ 8,000 行、bin ≤ 6、0 个 `#[path]` 重编译。

## 1. 度量方法与口径校准（重要：FACTS §2 需要订正）

- 本次用 `[IO.File]::ReadAllText` 逐行统计（= read 工具/Select-String 的行号空间）。PowerShell
  `Get-Content | Measure-Object -Line` 在本环境会**漏行/少计**（同一文件差 5–10%），FACTS §2 正是该口径。
- 校准结果：FACTS 的"参考版侧"实际是**生产代码**（不含 `tests.rs`），但其脚注又写"参考侧 − 测试文件"，
  对 L07/L08 做了**二次减法**，把生产 LOC 低估约 40%：

| 层 | FACTS "生产 LOC" | 本次真实非空行 | 倍差 |
|---|---:|---:|---:|
| L07 | 4,319（=6212−1893） | **6,835** | 1.58× |
| L08 | 3,716（=5333−1617） | **5,760** | 1.55× |
| L09 | 4,940 | 5,230 | 1.06× |
| L10 | 6,245 | 6,566 | 1.05× |
| L11 | 9,174 | 9,539 | 1.04× |
| L12 | 9,398 | 9,710 | 1.03× |
| L13 | 9,319（=22817−13498，但 22817 实为生产） | **24,248** | 2.60× |

→ 结论：**"参考版生产代码 ≈ 37k 行、孪生 76k"是被低估计的**；真实是参考生产 82,946、孪生 85,411。
D1/D2/D5 引用 LOC 时请改用本表。也说明"唯一事实来源"缺失已造成跨文档数字漂移（§6 P6）。

## 2. 复杂度度量总表（`[码]`，本次静态统计）

### 2.1 规模与形态

| 层 | 参考非空行(含测试) | 参考生产 | 孪生 | 文件 | 最大单文件(参考) | 最大单文件(孪生) |
|---|---:|---:|---:|---:|---|---|
| L01 | 5,619 | 5,619 | 472 | 27 | bench.rs 1,200 | — |
| L02 | 1,139 | 1,139 | 1,628 | 4 | mod.rs 686 | bump_spine_iter.rs 1,726 |
| L03 | 1,568 | 1,568 | 2,523 | 4 | mod.rs 1,107 | bump_spine_iter.rs 2,649 |
| L04 | 1,830 | 1,830 | 2,800 | 4 | mod.rs 1,302 | bump_spine_iter.rs 2,947 |
| L05 | 2,182 | 2,182 | 3,526 | 4 | mod.rs 1,654 | bump_spine_iter.rs 3,684 |
| L06 | 2,720 | 2,720 | 4,644 | 21 | mod.rs 553 | machine.rs 1,385 |
| L07 | 8,883 | 6,835 | 8,758 | 28 | mod.rs 2,074 | machine.rs 1,830 |
| L08 | 7,483 | 5,760 | 8,441 | 28 | tests.rs 1,723→mod 1,626 | machine.rs 2,085 |
| L09 | 5,230 | 5,230 | 7,474 | 25 | mod.rs 1,386 | machine.rs 2,129 |
| L10 | 6,566 | 6,566 | 9,224 | 26 | mod.rs 2,005 | machine.rs 3,716 |
| L11 | 9,539 | 9,539 | 8,713 | 27 | mod.rs 2,515 | machine.rs 3,085 |
| L12 | 9,710 | 9,710 | 8,715 | 27 | parser/mod.rs 2,440 | machine.rs 3,359 |
| L13 | 37,552（其中测试 13,304） | 24,248 | 18,493 | 59 | **mod.rs 7,872** | machine.rs **5,402** |
| **合计** | **100,021** | **82,946** | **85,411** | **284** | | |

其它 `src`：glue 12,290（`lib.rs` 4,227、`doc/collect.rs` 896、`format/layout.rs` 582、…）；
bin 7,186 / 21 文件；**归档** `bench_head` 12,606 + `bench_pre` 12,728 = 25,334；`.bak` 12,464 / 17 文件。

### 2.2 质量/风险指标

| 指标 | 分布 | 读数 |
|---|---|---:|
| `unsafe` | ref 91（L13 46、L01 30）/ twin 226（L13 48、L09 21、L10 20） | **317** |
| `panic!/unwrap/expect` | L13 276/238/197 为绝对大头（LSP/HDL 错误路径） | 层内 ≈2,100 |
| `eprintln!/println!/dbg!` | L13 345、L12 95、L11 65、L10 62、L09 41；L07/L08 各 7 | **663** |
| 状态开关 | 33 个 distinct（`*_STACK_MB`×7、`*_NO_CONV_MEMO`×5、`*_NO_NAME_MAP`×4、`L07/L08_DEBUG|LOOP`、`L11_LOOPCAP`、`L13_TW_DBG`…） | **33** |
| `std::env::var` | L13 18、L07–L12 各 1–4 | 28 |
| 概念数（`Val::`/`Tm::`/`UItem::` 变体） | Val 13–14、Tm 18–25、UItem 6–8 | 每层 37–47 |
| `enum`/`struct` 定义数（含测试） | 每层 100–160 | L13 160/162 |
| pub fn（API 面） | 每层 21（L02）–199（L13）；13 层合计 ≈1,100（L07–L13 814） | ≈1,100 |
| `#[test]` | src 1,114 + `tests/` 1,363；`#[ignore]` 17 | **2,477** |
| 文档 | `docs/` 51,873 行 / 234 文件；src README 16 个 ≈4.7k（L07 564、L13 392、L12 353、L08 351） | 文档:层代码 ≈ 0.28:1 |

## 3. 复杂度来源 Top 3（本质 vs 事故）

### C1 双引擎：46% 的层代码是"第二实现"
孪生 85,411 行 = 层代码的 46%；它与参考版的重复并非"优化开关"，而是**第二套**值表示（打包 `V` tag）、
求值器（`eval_iter`/`machine.rs`）、合一器（`unify.rs`）、quote/rename/force、模式编译器。
同层孪生/参考生产比：L07 8,758/6,835=1.28×、L10 9,224/6,566=1.40×、L13 18,493/24,248=0.76×（L13 参考侧含
LSP/HDL）。机制文件族总量：`machine.rs` 22,599/8 层、`unify.rs` 7,686/8、`rename.rs` 6,549/8、
`force.rs` 4,849/7。→ **事故复杂度**：算法每改一处要改两处；11-08 加固只落 L07 即其代价（FACTS §6）。

### C2 13 层 copy-forward：机制文件被复制 7–12 份
同层对之间行集合 Jaccard（去短行）：L07↔L08 `pretty.rs` **86.4%**、`elaboration.rs` **82.1%**、
`pattern_match.rs` **80.5%**、`parser/mod.rs` **73.2%**；L10↔L11 `typeclass.rs` **89.7%**、
`unification.rs` **71.2%**；L11↔L12 `unification.rs` **81.9%**；L12↔L13 `lex.rs` **85%**。
按文件名族累计：`elaboration.rs` 10,105/8 层、`unification.rs` 6,937/8、`pattern_match.rs` 4,462/7、
`cxt.rs` 3,549/8、`lex.rs` 3,517/12、`pretty.rs` 2,694/8、`typeclass.rs` 1,756/4、`macros.rs` 1,070/3。
**完全逐字节相同**的只有 5 组 / 1,756 行（lexer、macros 拷贝）——说明其余都是"**复制后各自演化**"，
这比纯复制更糟：修复/加固无法自然传播（P1–P11 只在 L07 就是证据）。
→ 本质复杂度：层间差异（语言特性）真实存在；事故复杂度：**用完整实现副本表达差异**。

### C3 单文件巨兽 + 观察面/实验设施混入产品代码
`L13 mod.rs` **7,872 行**同时承载 namespace/elaboration/LSP 入口/HDL/观察面；孪生 `machine.rs` 5,402；
L11 `mod.rs` 2,515、L12 `parser/mod.rs` 2,440。观察/实验设施混入核心：
`FUNC_PROF` 83 处/10 文件、`observe` 103/15、`prime_resident` 27/6、`Val::Call` 63/10、
`iddfs` 15/8（L12 canonical 的 Err 重试路径，run/run_fast 不经——FACTS §4）；`lib.rs:20-32` 自承
"product build 只用各层 API 的 sliver，其余约 **1,800 个 dead-code 站点**"。
另外 `src/bench_head` + `src/bench_pre` 是 L07 的**冻结副本**（25,334 行，13% 层代码），
`L11` 14 个 `.bak` + `L12` 3 个 `.bak`（12,464 行，6.7%）——**归档进了源码树**。
→ 大部分是事故复杂度：可移到 `oracle/`、`tools/`、`experiments/`。

### C4 构建/测试/文档复杂度（并列第三）
- 构建：19 个显式 `[[bin]]`、20 个手工 `test=false`（`Cargo.toml`）、**118 个 `#[path]` 跨层重编译**
  （bench bin 各自把整层源码再编一遍）、5 个 profile、1 个 feature（`sampler`）。`src/lib.rs` 无条件编入
  L02–L13（13 层），每个测试/工具都付全量编译成本。
- 测试：2,477 个 test fn（src 1,114 + tests 1,363）、17 个 `#[ignore]`；`tests/` 是一个 63 文件的杂物层
  （7 个 parity 套件共 ≈7,452 行 + 7 组 blackbox ≈ 12k + LSP/format/doc/sim 各自套件 + r1–r9 临时回归 +
  `known_bug_pins.rs`/`repro_sumcase_panic.rs`）。多数套件 `#[path]` 把层源码编入 → 同一批 lib 测试被
  重复执行 N 次（Cargo.toml 注释自承"pure duplication"）。
- 文档：`docs/` 51,873 行/234 文件；`review-*` 7 个目录 ≈15k 行（多轮已结束的评审存档）、`wip` 1,322、
  两个 compare 目录 3,755；src README 里 **90 处** "2026-09-xx" 过期数字或"以 Lead 实跑为准"。

## 4. 概念与不变量清单：本质 vs 事故

**本质复杂度（保留；约 1/5）**

| 概念 | 说明 | 现状载体 |
|---|---|---|
| 核心 5 值形态 | `U / Pi / Lam / Sum / SumCase`（+`Match` 卡住、`Obj` 投影、`Flex` meta、`Literal`、`Decl/Prim`、`VSub`） | 每层 `mod.rs` Val |
| 项形态 | `Var/Pi/Lam/App/Sum/SumCase/Match/Obj/Meta/Decl/Prim/Literal` | `Tm`（L13 加到 25 变体） |
| 求值 | NbE：eval / force / quote / rename / closure_apply | `mod.rs` + twin `machine/eval/force/quote/rename` |
| 合一 | invert / prune / solve / spine 比较 / 卡住 match 结构快路径 | `unification.rs` + `struct_eq.rs` |
| 精化 | σ：`Subst` 单链 + `VSub` 包裹 + `frcs` 读点 + `SpecSolve` 穿参 | `subst.rs` / `unification.rs` |
| 匹配 | 逐臂下钻 + 两段式嵌套覆盖 + 值级探测 | `pattern_match.rs` |
| 资源 | fuel / `MATCH_CMP_BUDGET` / occurs BUDGET / EQ_BUDGET / 栈深 | 各层常量 |
| 错误 | 单一 `Error` 载体（现状分裂为 `Error(String)` 与 `Error::new(span,..)`） | 各层不同 |

**核心不变量（跨层重复声明，是真正的"必须显式列清单"对象）**：①`l == cxt.lvl`（η descent 破坏即越界，
L08 README §5）；②σ 槽位纪律"只包裹不物化"（L07 设计文档 §4）；③decl 占位"只对本定义可见"；
④memo 只在成功时写（success monotone）；⑤fuel 耗尽按"未出现/未判定"保守处理；⑥逐臂首匹配语义；
⑦覆盖探测的 meta/σ 快照回滚；⑧quote/rename 用简化 decl 表防中性递归；⑨模式特化只在 `spec` 携带槽集时解；
⑩bump 值只在轮内有效（tag-2 句柄寿命）。→ 建议做成 `docs/invariants.md` 10 条，每条的**唯一**代码落点。

**事故复杂度（可删/可搬）**：13 层并行实现、33 个环境/调试开关、观察面混入、实验归档入 `src/`、
`.bak`、日期化 bench 数字写进 README、`Error` 双载体、`Val::Call`/`iddfs` 未接线路径。

## 5. 单引擎 + oracle vs 双引擎：量化

| 方案 | 生产 LOC | 测试期 LOC | 编译成本 | 每机制改动点数 | 正确性证据 | 判定 |
|---|---:|---:|---|---:|---|---|
| **A 现状双引擎** | 168,357 | 17,075 | 2× | 2（含再×层数） | parity 差分（强，但只覆盖同错区外） | 维护面积最大 |
| **B 单引擎（twin）+ frozen oracle crate** | **85,411**（若再收成一套能力模块 ≈18.5k） | 82,946（`oracle/`，`--features oracle`） | 1×（release 不含 oracle） | 1 | parity 差分保留（CI 跑 oracle feature） | **推荐** |
| **C 单引擎 + 删参考版，仅 golden/Lean** | 85,411 | 0 | 1× | 1 | golden 快照 + Lean oracle（`tests/lean_oracle_parity.rs` 202 行 + `lean/OracleMain.lean`） | 收益最大、证据需 D2 认可 |

- **接口/认知负担**：现状每层各自导出 module + bench 私有 API（pub fn ≈1,100，L13 199）；
  方案 B 可把公开面收敛到 `core` ~120 pub fn + 4 个 feature 模块，**认知单位从"13 层×2 引擎=26 套实现"
  降为"1 套核心 + 4 个能力模块 + 1 个冻结 oracle"**。
- **不能省的部分（性能路径）**：arena/打包值（twin 全层领先：match 0.10–0.80×、大值负载 10–800×，
  FACTS §4/§5）；迭代内核 + 常驻缓冲 + memo（D5 的技术矩阵将给净收益）；σ（正确性载体，D2）；
  fuel/预算（安全，D2）。参考版的"可读性"价值（教学）可保留在 `oracle/` 注释里，不必双份生产代码。
- **敏感性**：若 D2 判定"差分 oracle 不可替代"→ 选 B（oracle 留 CI，不进产品）；若 D5 证明孪生优势只在
  合成负载（L13 真实 prelude 只差 ~1.2×）→ 可改选"参考版语义 + 孪生热点内核"混合，但复杂度回升，
  不如坚持 B + 局部热路径。

## 6. 优雅原则（可检验，不是口号）

| # | 原则 | 检验方式 | 现状反例 |
|---|---|---|---|
| P1 | **单一事实来源**：一个机制只有一份实现 | 跨层同名文件 Jaccard >40% 即违规 | L07↔L08 `elaboration` 82%、L10↔L11 `typeclass` 90% |
| P2 | **数据/算法分离**：值表示（tree/arena）与 elaboration 语义解耦 | 换值表示时语义代码 0 改动 | 现在每个 engine 复制全部算法（85k 行） |
| P3 | **错误载体统一**：一个 `Error{kind,span,msg}`；诊断分级在类型里 | 错误构造点只 1 个类型 | `Error(String)` vs `Error::new` 两套（L08 无 span、L07 有） |
| P4 | **观察面/实验设施与核心解耦**（feature 或独立 crate） | `core` 无 `FUNC_PROF`/`eprintln!`/env 开关 | L13 345 处 print、FUNC_PROF 83 处 |
| P5 | **层 = 测试快照，不是代码分支** | 每层是 `tests/golden/L0x/*` 而非 `src/L0x/` | 13 层 284 文件 / 100k 行参考实现 |
| P6 | **口径单一**：LOC/测试数/bench 数字由脚本生成并标注 | 文档里的数字可一条命令复现 | FACTS 生产 LOC 低估 1.5–2.6×；90 处过期日期 |
| P7 | **删除优于开关**：开关=未测配置组合 | 生产代码 0 个 `env::var` 行为开关 | 33 个开关（2^33 未测空间） |
| P8 | **文件边界 = 概念边界**：单文件 ≤1,200 行、一个模块一个概念 | 超过即拆分 | L13 `mod.rs` 7,872、twin `machine.rs` 5,402 |

## 7. 目标目录/模块结构（文件级，可落地）

```text
crates/
  elab-core/                       # 生产核心 ≤18k 行；deny(dead_code)、0 unsafe 白名单外
    src/lib.rs                     # 只 re-export + feature 装配 ≤150
    src/syntax/{tm.rs,val.rs,pattern.rs,decl.rs}     # ≤250/文件
    src/eval/{eval.rs,force.rs,quote.rs,rename.rs}   # ≤400/文件
    src/unify/{unify.rs,invert.rs,prune.rs,solve.rs} # ≤350/文件
    src/match/{compile.rs,probe.rs,coverage.rs}      # ≤350/文件
    src/subst.rs  src/cxt.rs  src/diag.rs            # 单一 Error{kind,span,msg}
    src/arena.rs                   # 唯一 unsafe 区（≤40），每处 SAFETY 注释
    src/features/{typeclass.rs,canonical.rs,macro_.rs,namespace.rs,prelude.rs}  # ≤800/文件
  elab-parse/                      # ≤3k；lex/ast/parser/derive 一份
  elab-observe/                    # ≤1.5k，feature="observe"；pretty/report/prof
  elab-lsp/                        # ≤4k；server/hover/completion/hdl
  oracle/                          # test-only：现 reference engine 冻结，只读 API，不进 product
  tools/                           # 1 个 cli（typort）+ 1 个 bench（l14bench 统一负载）
tests/
  golden/L02..L13/*.golden         # 层差异 = 快照，不是代码副本
  oracle_diff/*.rs                 # 现 l07..l13_fast_parity 收敛为 1 套参数化差分
  lean_oracle_parity.rs
docs/
  invariants.md  architecture.md  bench-matrix.md(生成)  # ≤8k 行总量
```

层级映射：L02–L13 的能力差异 → `features/` 的 capability 开关 + `tests/golden/`；历史 diff 说明保留在
`docs/history/L0x.md`（≤150 行/层），不再保留源码副本。

## 8. 可量化复杂度预算（建议写入架构验收门禁）

| # | 预算项 | 现状 | 目标 | 检验命令（静态） |
|---|---|---:|---:|---|
| 1 | 生产引擎 core LOC | 85,411（+82,946 ref） | **≤18,000** | `cloc`/nonblank 统计 `crates/elab-core/src` |
| 2 | 单文件非空行 | 7,872 | **≤1,200** | 逐文件 max |
| 3 | 生产文件数 | 284 层文件 + 32 glue | **≤80** | `find` 计数 |
| 4 | `Val` 变体 / `Tm` 变体 | 14 / 25 | **≤16 / ≤26** | grep `Val::[A-Z]` 去重 |
| 5 | 工作栈任务种类（twin） | 6–8 | **≤8** | `UItem::` 去重 |
| 6 | `unsafe` | 317 | **≤60**（arena ≤40 + lsp_stdio ≤20，其余 0） | grep |
| 7 | 环境/调试开关 | 33 distinct | **≤4**（LOG、STACK_MB、bench-only 消融） | grep `L\d\d_[A-Z_]+` |
| 8 | 生产路径 print/panic | 663 / ≈2,200 | **≤20 print、≤20 panic**（诊断化） | grep |
| 9 | 跨层复制 | 机制族 33k + Jaccard 80%+ | **0**（同机制唯一文件） | 同名文件行集合 Jaccard ≤40% |
| 10 | `.bak`/归档入 src | 12,464 + 25,334 | **0** | `find src -name '*.bak' -o -name 'bench_*'` |
| 11 | 构建目标 | 19 bin + 20 `test=false` + 118 `#[path]` | **≤6 bin、0 test=false、0 `#[path]`** | Cargo.toml/ grep |
| 12 | 文档 | 51,873 行/234 文件；src README 4.7k | **≤8,000 行/≤30 文件**；代码内禁日期数字 | wc |
| 13 | 测试 | 2,477 fn/17 ignore | 保留黑盒+golden；ignore ≤5 且全部 `#[cfg]` 门控 | grep |
| 14 | 口径 | FACTS 低估 1.5–2.6× | 1 个 `tools/metrics` 生成所有数字 | 复现 diff=0 |

## 9. 风险与依赖（给 Lead 的输入）

1. **D3 的"删除参考引擎"依赖 D2 结论**：若 D2 认为差分 oracle 是唯一可靠正确性证据，则参考引擎必须
   保留——但应降级为 `oracle/` crate（B 方案），而非继续与生产代码同置；D3 的预算是 B 方案。
2. **D5 反向约束**：若 D5 证明某些孪生配置（如 `L13_NO_MEMO_SHARE`）在真实负载无收益，预算 #7（开关 ≤4）
   可进一步收紧到 ≤2。
3. **迁移成本**：从现状到目标树是"先建 `core` 抽取 + oracle 冻结 + golden 化层"三步，第一步即可
   删除 `.bak`/归档（37,798 行，零风险）：**建议立即执行的低风险清理项**：
   ①删 `src/bench_head`+`src/bench_pre`+17 个 `.bak`（37,798 行）；
   ②`docs/review-*`（19k 行）移入 `docs/archive/` 并从导航摘除；
   ③把 19 个 bench bin 合并为 1 个 `--layer` 参数化 bin（消 118 个 `#[path]`）；
   ④统一 `Error` 载体（L07/L08 的 `Error(String)` → `Error::new`，消 P10 类分叉）。
4. **不改变的范围**：`tests/` 的黑盒用例是行为证据，迁移时保留为 golden 输入，不按行数删减。

## 10. 给 Lead 的一句话结论

**复杂度不是来自 NbE/σ 这些真本事，而是"13 层 copy-forward × 2 引擎 × 归档入源码"；最优架构 = 1 个
arena 引擎（≤18k 行、单文件 ≤1.2k、unsafe ≤60）+ 冻结的 test-only oracle + 层退化为 golden 快照，
可立即零风险删除 37.8k 行归档/`.bak`。**
