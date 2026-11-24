# 07 · 行为证据与门禁覆盖：L07 ⟷ L13「共有部分」差异能不能被看见、会不会被抓到

> 分析员：evidence ｜ HEAD `911628b3`（2026-11-24）｜ 只读 src/ ｜ 附带产物：`tmp/evidence/probe/*.typort`（13 个复现语料）

## 1 范围与方法

- 角度：把别的分析员的静态差异落到「**有没有可观察后果 / 会不会被自动门禁抓到**」；不重复算 token 与 shingle。
- 证据源三档：① `.audit/raw-correctness/probe-matrix.tsv`（39 程序 × 7 层，基线 `57a11c28`/11-16，**已过期**；`.audit` 被 `.gitignore:73` 忽略，不属仓库事实）；② 本轮**实际运行**的预编译二进制（`realbench.exe`、`l13bench.exe`）；③ `tests/` + `.github/workflows/ci.yml` + `Cargo.toml` 的门禁事实。
- 动态复现在 `tmp/evidence/probe/`：13 个**纯共有特性**程序（无 namespace/HDL/class/trait/macro），从 `tests/audit_crosslayer_probe.rs` 的 CORE/SEMANTIC 语料逐字复刻，可与旧矩阵逐行对读。
- 未做且不做：`cargo build/check/test`。凡「必须重新编译才能拿到的输出文本」一律 `[未核实]`，不猜。

## 2 模块对位表（本角度：**证据/门禁覆盖**，不是 token 复算）

`tok`/`保留率` 引自 MAP.md §1（本轮未复算，仅作索引）；后三列是本轮实测或可核锚点。

| 共有模块 | L07→L13 tok（MAP） | 保留(归一) | 本角度行为证据（实测） | 跨层门禁 | 判读 |
|---|---|---|---:|---|---|
| `unification.rs` | 9.6k→10.6k | 56% | prim 判等 5 条断言在 **7 层同时成立**（`tests/prim_identity_cross_layer.rs:88-105`） | **有**（唯一） | 继承 |
| `bump_spine_iter/unify.rs` | 6.4k→9.1k | 70% | 孪生侧零门禁（feature 关死，§4.3） | 无 | 继承但无人守 |
| `pattern_match.rs` | 5.0k→5.3k | 48% | 缺失模式诊断在 L13 爆炸成 3.1KB（§4.1，HEAD 复现） | 无 | 重写 |
| `cxt.rs` | 3.0k→12.3k | 48% | L13 **接受** `def succ` 撞构造子，L07 报 `redefine succ`（§3 #5） | 无 | 重写 |
| `mod.rs` | 17.2k→46.8k | 57% | `MATCH_CMP_BUDGET=64` 两侧同值同口径（L07 `mod.rs:801` / L13 `mod.rs:1475`） | 无（层内） | 继承+扩张 |
| `pretty.rs` | 0.8k→7.0k | 54% | Nat 十进制 vs succ 链、η `x + 1` vs `x => Nat::succ(x)` | **无** | 重写 |
| `surface.rs` | 1.4k→0.8k | 27% | 隐式 binder 打印两侧均 `[]`（旧矩阵 #5 已验） | 无 | 重写但契约同 |
| `parser/lex.rs` | 1.8k→2.4k | 95% | 接受/拒绝面实跑一致（§3 #1–#2） | 无（层内） | 继承 |
| `bump_spine_iter/env.rs` | 0.8k→0.9k | 98% | 无行为面（纯容器） | 无 | 继承 |
| `shape.rs` | 0.7k→0.9k | 86% | 11-23 成对提交 `6f7e245e`⟷`c824c43a` 同步「形状认回 decl」 | 无 | 继承（成对改） |

**读法**：保留率高的模块行为证据也一致（env/lex/shape）；**保留率低的三处（pretty/cxt/pattern_match）恰好就是唯一能观察到的分叉所在**，而这三处两侧都不共享门禁。这不是巧合——它们正是「同角色、重写」的地方。

## 3 逐机制差异表

「可观察后果」列只记本轮能复现、或能从旧矩阵直接读到的；E 档按 MAP §4。

| # | 机制 | L07（锚点/实测） | L13（锚点/实测） | E 档 | 可观察后果 / 门禁 |
|---|---|---|---|---|---|
| 1 | 程序接受/拒绝面 | `realbench --layer L07`：13 语料 7 PASS / 6 SKIP | `l13bench --file`：7 个 `nf=` 过、5 个 `BOTH-FAILED` | **E1** | 7/13 判定一致；差异见 #2–#6 |
| 2 | 卡住 match 比较预算 | `MATCH_CMP_BUDGET: u32 = 64`（`src/L07_sum_type/mod.rs:801`，burn @ `:905`） | 同值 64，注释写明「镜像参考版」（`src/L13_namespace/mod.rs:1475`、`unification.rs:1251-1255`） | **E1** | 无后果；11-18 `9e37627b` 显式回灌 |
| 3 | 缺失模式诊断 | `Error("match 不完整：缺少构造子 succ")`（realbench 实捕） | “non-exhaustive pattern: succ(_, ×~1000) not covered”，单行 **3116 字符 / 2005 个 `_`** | **E2** | 用户可见 3KB 垃圾；零断言（§4.1） |
| 4 | 不可达臂诊断 | `分支不可达：模式 succ(n) 被前面的通配臂遮蔽` | `unreachable pattern: n`（指绑定名不指模式） | **E2** | 文案退化；层内有、跨层无测试 |
| 5 | `def` 撞构造子裸名 | `Error("redefine succ")`（实跑） | **接受**；`println succ` → `0`（`l13bench nf=2`，HEAD 复现） | **E2/E3** | 遮蔽规则语义分叉；L13 侧**无测试**（§3.5） |
| 6 | 卡住 prim 判等 | 11-16 时误拒 ctrl；`c6c0e892`(11-16 19:29) 补 literal-equality 臂 | 一直正确（args-preserving 模型 `26c53eb7` 起） | **E1**（已回灌） | 现 7 层全 Ok，**有跨层门禁** |
| 7 | Nat 值显示 | `Nat::succ(Nat::succ(…))` | `4` / `0` / `1` | **E2** | 纯显示分叉；跨层文本零门禁，快照不可跨层复用 |
| 8 | 构造子 η / 裸构造子值 | `x => Nat::succ(x)`（旧矩阵 #7）；`println succ` 未被 realbench 判 run_err | `x => x + 1`；同程序 `l13bench` 报 `BOTH-FAILED` | **E2`[未核实]`** | 入口不同（nf vs run），不敢断言「L13 拒收」 |
| 9 | 错误文案/span | `can't unify (x: ?0) → ?1 x == Nat` | `can't unify\n expected: …\n find: … @ 49,58`（含零宽空格 `\u{200b}`） | **E2+E4** | L13 多出 span（新能力）；L07 文案被层内测试钉死 |
| 10 | 泛型构造子值打印 | `[A] => List::nil` / `List::cons(Bool::true List::nil)` | `[A] => List[A]::nil` / `List[Bool]::cons(Bool::true, List[Bool]::nil)` | **E2** | 逗号 + 类型实参；同一套 pretty 契约已分家 |
| 11 | 诊断「类别」契约 | `class=coverage`（`.audit` 分类器按「不完整」命中） | 文案变英文 → 落到 `class=other`（`audit_crosslayer_probe.rs` 的 `classify_err` 不认 `non-exhaustive`） | **E2** | 统计口径层面：同一缺陷在两侧被归到不同类别，矩阵自动对读会误判 |
| 12 | 语言面 gate（package/namespace） | 不支持（`parse error`） | `demo.Nat::succ(…)` | **E4** | 单边新功能，不算共有部分差异 |

**旧矩阵已过期处（本轮实测修正）**：`R1`（L07 假阴 / L09–L10 panic / L11–L12 假阳）已由 `c6c0e892`+`26c53eb7` 修掉——本轮 `realbench` 对 `prim_identity_ctrl` 在 **L07 PASS**；`R2`（L12 丢索引投影）已被 `73d68cf2`(11-17 重建 canonical 层) 修掉——`core_vec_len_proj` 在 **L12 PASS**。⇒ `.audit/correctness.md` §5 R1/R2 不可直接引用到本轮。

## 3.5 测试资产 × 覆盖矩阵（必答 #3）

静态计数（本轮 `Select-String '^\s*#\[test\]'` 实测，非引用）：

| 侧 | 资产 | 实测 `#[test]` | 与「共有机制」的关系 |
|---|---|---:|---|
| L07 | `src/L07_sum_type/tests.rs` | **66**（任务书说 64，本轮实测 66） | 层内单元；含预算/覆盖/诊断 |
| L07 | `tests/l07_blackbox{,_v2,_v3}.rs`+`l07_fast_parity.rs` | **176** | 黑盒 run 面 |
| L13 | `src/L13_namespace/*_tests.rs`（23 文件） | **445** | 其中 `legacy_tests.rs` **139** |
| L13 | `tests/l13_fast_parity.rs` | **15** | ref↔twin，且被 feature 关死 |

| 共有机制 | L07 侧覆盖 | L13 侧覆盖 | 跨层门禁 | 危险度 |
|---|---|---|---|---|
| prim 判等（stuck prim / Eq） | 有（realbench PASS） | 有 | **有**（`prim_identity_cross_layer.rs:88-105`） | 低 |
| 缺失/不可达模式诊断 | 有（`tests.rs` 预算/诊断用例） | 有（`legacy_tests.rs:5235` 提到文案） | 无 | 中（文案已分叉） |
| `def` 撞构造子（redefine） | 有 | **无**——L13 直接接受，无测试钉 | 无 | **高** |
| 构造子裸名 `println succ` | 有（黑盒） | **无**（`l13bench` 直接 BOTH-FAILED） | 无 | **高** |
| 泛型构造子值打印 `println nil` | 有 | **无**（`l13bench` BOTH-FAILED；旧矩阵说 Ok ⇒ 入口不一） | 无 | **高`[未核实]`** |
| Nat 十进制 / η 渲染 | 各自层内有 | 各自层内有 | 无 | 中（显示契约） |
| `MATCH_CMP_BUDGET` | 有（`tests.rs:239`） | 文档+实现（`mod.rs:1475`） | 无 | 低 |

**结论**：真正的危险区是**「L13 侧完全没有测试」的三条共有机制**——`redefine` 撞构造子、裸构造子值、泛型构造子值。它们不是「新功能」，而是 L07 时代就存在的语言面；L13 的 445 个测试全部绕开了它们。

## 4 抽样深挖

### 4.1 缺失模式诊断：L13 一行 3.1KB、1000 个 `_`（E2，已复现）

```
$ l13bench.exe --file core_missing_case.typort --with-prelude none
[diag] … Some("non-exhaustive pattern: `succ(_, _, _, …(×~1000)…, _)` not covered")
-- core_missing_case.typort (2 decls) BOTH-FAILED
```
量测：该行 3116 字符、下划线 **2005** 个。链路：`src/L13_namespace/pattern_match.rs:50` 用 `{}` 打 `pat`，`pat` 的 Display 在 `src/L13_namespace/parser/syntax.rs:63-77` 逐子模式 join——**Display 无罪**，是上游给「缺失分支见证模式」塞了约 1000 个 `Pattern::Any`。L07 同场景只报一句中文（realbench 实捕）。
为什么算 E2 不算 E1：同角色（覆盖检查报告）、不同机制（结构化见证 vs 定长中文），**有可观察后果**（IDE 诊断面板/日志 3KB 单行），且两侧都没有长度断言。根因（arity 取错字段）本轮未定位，`[未核实]`。

### 4.2 唯一真·跨层门禁：`tests/prim_identity_cross_layer.rs:96-105`

```rust
fn l07_l13_prim_semantics() {
    check_layer!("L07", L07_sum_type::run);   // … L08…L12 …
    check_layer!("L13", L13_namespace::run);
}
// :88-92 每层 5 条：literal 自反 Ok / 不同字面量 Err /
//        stuck prim 自等 Ok / 不同 stuck prim Err / 部分应用不 panic
```
这是「一脉相承」最硬的**正面**证据：7 层必须对 prim 判等给出同一组判定，L13 一旦改坏 prim 载体就会红。但它也是**唯一**把 L07 与 L13 绑在一起的行为门禁，只覆盖 5 条、只断言 Ok/Err（不断言文本）。判 E1 且「有门禁」的理由即在此。

### 4.3 门禁现状：层内 parity 已被特性开关**关成空跑**

| 事实 | 锚点 |
|---|---|
| 7 个 parity 套件首行 `#![cfg(feature = "lNN-twin")]` | `tests/l07_fast_parity.rs:1`、`tests/l13_fast_parity.rs:1`（l08–l12 同） |
| 这些 feature **默认关闭**（「封印后 ref 可独立演进」） | `Cargo.toml:186-198`（`l07-twin`…`l13-twin` 全 `= []`，无 default 定义） |
| 没有任何门禁开这些 feature（`--features` 在 `gate_l13.sh`/`gate_p0.sh`/`ci.yml` 零命中） | `tools/gate_l13.sh:84-98` |
| CI 实跑：`gate_l13.sh`（lib + l13_fast_parity + twin_engine_tests + hdl042）→ `cargo check --examples --tests` → `gate_p0.sh` → 全量 `cargo test --no-fail-fast` | `.github/workflows/ci.yml`（test / test-full） |

⇒ **L07↔L13 的输出/诊断一致性没有任何自动门禁**；层内 ref↔twin 的逐字节 parity 也随封印停跑（这些 target 编成空、执行 0 例）。`.audit/correctness.md` §4 的「1140 passed」是封印落地**之前**的成绩，今天复现不了同等覆盖 `[推断]`。

## 5 本角度评级与 Top-3

**评级：中。** 语义内核（合一/求值/模式判定/预算守卫）确实同源，prim 面甚至有跨层门禁互锁；但**能被人看见的那一层（pretty 文本 + 诊断文案 + 重定义规则）已经分家**，而它恰好是零门区。

| Top-3 | 差异 | 锚点 | E 档 |
|---|---|---|---|
| 1 | prim 判等：真同源且**有跨层门禁**（7 层同 5 条断言）——正面样本 | `tests/prim_identity_cross_layer.rs:88-105`；`L07 mod.rs:801` ⟷ `L13 mod.rs:1475` | E1 |
| 2 | 缺失模式诊断：L07 一句话，L13 `succ(_,×~1000)` 3.1KB（HEAD 复现），零断言 | `L13 pattern_match.rs:50`+`parser/syntax.rs:63` vs L07 realbench 实捕 | E2 |
| 3 | 门禁真空：7 个 parity 套件被 feature 关死；L07↔L13 仅 #1 一条门禁 | `Cargo.toml:186-198`、`l07_fast_parity.rs:1`、`gate_l13.sh:84-98` | E3 |

## 6 给 Lead 的提醒（超出我角度但必须知道）

1. **`.audit/correctness.md` 的 R1/R2 已作废**：`c6c0e892`(11-16 19:29)、`26c53eb7`(11-16 23:39)、`73d68cf2`(11-17) 之后，L07 prim ctrl 假阴与 L12 索引投影回退都已修好（本轮 realbench 实测）。DELTA.md 的 L12→L13 段若引用这两条，请改写为「曾发生、已回灌」。
2. **`realbench` 的 `bytes=` 是源文件字节数，不是输出长度**：13 个语料的 `bytes` 与磁盘大小逐一相等（204/94/373/283/195/115/208/155…）。另：`--layer` 不收 `L13`（报 `unknown layer: L13`），`l07bench` 无 `--file` ⇒ **跨层 Ok 输出文本没有任何已编译工具能导出；「不可比」本身是结论**。缺的入口就是 `tests/audit_crosslayer_probe.rs` 那种全层矩阵，但它必须加断言并接进 gate 才有意义。
3. L13 缺失模式消息的 ~1000 个 `_` 是**独立缺陷**（不属 L07/L13 对比），建议单独开 issue + 补一条诊断长度上界断言。
4. `tests/audit_crosslayer_probe.rs` 文件头自述「本文件不做断言」，只写 TSV：它会在 CI 全量 `cargo test` 里执行，但**永不会红**，不要计入覆盖率。
5. 复现命令：`tmp/evidence/probe/` 下任一文件 →
   `target\release\realbench.exe --corpus tmp\evidence\probe --validate`（L07–L12）与
   `target\release\l13bench.exe --file <f> --with-prelude none`（L13 + `L13BENCH_DIAG=1` 取逐 decl 文案）。
