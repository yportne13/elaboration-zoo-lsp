# typort 测试用例目录（按章节适用性）

> 2026-09-19 首版。目的：把分散在 30+ 个测试文件里的用例经验整理成一份
> **成体系、可按章落地的用例目录**，并标注每个用例组「从哪一章起适用」。
> 用例设计参考了以下项目的测试套件组织方式：

| 来源项目 | 借鉴的测试组织经验 |
|---|---|
| [elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo)（01-eval ×3 / 02-typecheck ×2 / 03-holes / 04-implicit-args / 05-pruning / 06-first-class-poly） | **每章一组 ex0..exN 示例程序就是用例**；正误混合（ex0 按预期报错）；本仓 L02–L05 的 `EX*_SRC` 常量即其移植。上游没有归纳类型，L07 起为本仓自研延伸 |
| [dpm-nbe](https://github.com/KonjacSource/dpm-nbe)（本仓 L07 的机制蓝本，本地 `F:\projects\hermes\dpm-nbe`） | 依赖模式匹配五例：`sym` / `trans` / `cong` / **`H`（`Id Nat n (plus m zero)` 型精化链）** / **`C`（`Id Nat (suc zero) zero -> A` 荒谬前提）**；外加 `transN` 生成器式规模回归（N 跳传递链一次生成） |
| [Agda](https://github.com/agda/agda)（test/Succeed、test/Fail、test/Interaction 等） | **succeed / fail 双目录**心智模型：每个特性域同时登记"应通过"与"应报错（钉首条错误 + 位置）"两个半区；按特性分目录（Universe、DupFields、Pragma…） |
| [mini-agda](https://github.com/andreasabel/miniagda)（test/succeed、test/fail 等） | 同上双目录；且证明**错误用例也要随实现演进持续跑**（小目录、每文件一个独立断言点） |
| [Lean 4](https://github.com/leanprover/lean4)（tests/lean） | **issue 编号命名回归文件**（`3284.lean` 式）——本仓 docs 下已有 7 份 bug 报告，可平移为"报告→回归钉"约定；unification（isDefEq）专项负载单独成文件 |
| [Idris 2](https://github.com/idris-lang/Idris2)（tests/idris2/{basic,coverage,…}） | **golden `.err` 文件**：错误输出整体落盘比对；coverage（覆盖性）单列一个目录 |
| [Aya](https://github.com/aya-prover/aya)（TyckTest / DistillTest / ParserTest / CliTest） | **distill 往返测试**：elab 产物 pretty 后重新解析再 elab，输出必须幂等；显示格式（distill）与类型检查分开测 |
| guest0x0/normalization-bench（已吸收为 L01 负载） | **基准即正确性测试**：先断言结果再计时 |

---

## 0. 断言金字塔与 harness 约定

每个用例按四级断言组织（本仓已有基建，新用例直接套用）：

1. **parity（最外层）**：参考版与孪生版同源码互检。L02–L05 用
   `L0X::main_with(mode, src)` vs `L0X::bump_spine_iter::main_with(mode, src)`
   （nf/type/elab 各模式逐字节）；L06–L08 用 `run` vs `run_fast`（Ok 逐字节、
   Err 只比判定——**建议升级**为 L09–L13 的 `norm_err` 归一化正文比对，见 §4 缺口）；
   L09–L13 用 `run` vs `run_fast` + `norm_err`（剥 offset/path_id 数字后比正文）。
2. **golden（钉显示）**：只钉参考版 `run` 的 Ok 输出（双实现一致性由 parity
   另行锁定，`tests/l09_fast_parity.rs:1145` 注释即此约定）。显示格式**分时代**：
   L07/L08 空格血统（`Vec::cons([Nat::zero] Nat::zero Vec::nil)`）、
   L09–L13 comma 血统（`Nat::succ(Nat::zero)`、`Vec[Bool]::cons(1, Bool::false, Vec[Bool]::nil)`）、
   L08 struct `Point::Point.mk(…)` 空格式。golden 不得跨时代互贴（a4-r2 事故）。
3. **负向（钉判定 + 关键文案 + 位置）**：`Err` 判定 + `{:?}` 文案
   `starts_with/contains` + 报错位置。L13 首个错误与位置；L06+ 的
   `display_error` 是 megaparsec 风格 `(stdin):line:col` + caret。
4. **压力/终止**：超时内完成 + fuel/effort 上限触达时的可诊断降级文案
   （`(fuel exhausted)` 尾注、effort≤1000 上限）。

**harness 选择速查**：

| 章节 | 入口 | 测试文件形态 |
|---|---|---|
| L01 | 23 变体各自 bench 断言（先验正确后计时） | `src/L01_nbe` 内嵌 |
| L02–L05 | `#[path]` 独立编译 + `main_with(mode, src)` | `tests/l0X_blackbox*.rs` |
| L06–L08 | `elaboration_zoo_lsp::L0X::run` / `bump_spine_iter::run_fast` | `tests/l0X_blackbox*.rs` + `l0X_fast_parity.rs` |
| L09–L13 | 同上 + `norm_err` Err 正文 parity | `tests/l0X_fast_parity.rs` |
| L13 全语言（含 prelude） | `run_with_prelude` / LSP Backend | `src/L13_namespace/legacy_tests.rs`、`tests/twin_engine_tests.rs` |
| HDL/示例 | `test_examples_hdl_dir`（include_str 全量） | `src/L13_namespace/legacy_tests.rs:1441` |

> 方言分界（写用例前必读）：
> **L02–L05** 是 elab-zoo 方言——`let x : T = e;`、λ 写 `\x. e` 或 `λ x. e`、
> 隐式用 `{}`、宇宙只有 `U`（且 `U : U` 合法，不做宇宙负例）。
> **L06 起**是 typort 方言——顶层 `def`/`println`、λ 写 `binder => body`、
> 隐式用 `[]`、有字符串字面量。**隐式实参调用自 L06 起同时支持逐槽
> `f[A][B]` 与逗号合写 `f[A, B]`**（2026-09-19 起全章统一；此前 L06–L10
> 仅逐槽，L11 起才有逗号合写）。**L07** 加 `enum`/`match`，**L08** 加 `struct`/`new`，
> **L09** 加 `Type N` 分层宇宙（comma 显示），**L10** 加 `trait`/`impl`/`this`，
> **L11** 加 `macro_rules`，**L12** 无新语法（canonical 机制），**L13** 加
> `package`/`import`/`module`/`class`/`calc`/prelude/整数字面量糖。
> L13 的 enum 构造子/match case 必须**换行分隔**（单行 enum 是两版同错形态，
> 有专门的钉子用例，勿当 bug）。
>
> **可跑性声明**：G6 组核心片段（dpm-nbe 五例、strict η、类型层 match、
> 覆盖负例、方言陷阱）已于 2026-09-19 在 L07 参考版 `run` 下实际运行验证
> （15 个临时校验用例全过，校验件即验即删）；标注 ⚠ 的片段仍需落地时校准。

---

## 1. 用例组总目录与章节适用矩阵

图例：● 完全适用（该章起）｜◐ 适用但显示格式/语义有时代差异（见该组注）｜○ 不适用。

| 组 | 主题 | L02 | L03 | L04 | L05 | L06 | L07 | L08 | L09 | L10 | L11 | L12 | L13 | 适用起点（一句话） |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| G0 | 求值/conv/遮蔽骨架 | ● | ● | ● | ● | ● | ● | ● | ● | ● | ● | ● | ● | L02 起（η 为 L02 βη conv 的一部分） |
| G1 | 双向检查走廊（正/负） | ● | ● | ● | ● | ● | ● | ● | ● | ● | ● | ● | ● | L02 起 |
| G2 | 元变量/holes/pattern unification | ○ | ● | ● | ● | ● | ● | ● | ● | ● | ● | ● | ● | L03 起 |
| G3 | 隐式参数 | ○ | ○ | ● | ● | ● | ● | ● | ● | ● | ● | ● | ● | L04 起；L04/L05 用 `{}`，L06 起用 `[]` |
| G4 | typed metas + pruning | ○ | ○ | ○ | ● | ● | ● | ● | ● | ● | ● | ● | ● | L05 起；L04↔L05 判定反转成对用例仅此两章可辨 |
| G5 | 字符串/builtin/decl 表 | ○ | ○ | ○ | ○ | ● | ● | ● | ● | ● | ● | ● | ◐ | L06 起；builtin 注册表 L09 起缺席（时代缺口），L13 由 prelude 承接 |
| G6 | enum/match/依赖模式匹配 | ○ | ○ | ○ | ○ | ○ | ● | ● | ● | ● | ● | ● | ● | L07 起；显示 comma 化自 L09；覆盖诊断口径 L11 起收窄 |
| G7 | struct/记录/投影 | ○ | ○ | ○ | ○ | ○ | ○ | ● | ● | ● | ● | ● | ● | L08 起（L09+ 保留，脱糖为单构造子 enum） |
| G8 | 分层宇宙/大消去 | ○ | ○ | ○ | ○ | ○ | ◐ | ◐ | ● | ● | ● | ● | ● | L09 起（L07/L08 有 `U` 但无层级） |
| G9 | typeclass/trait | ○ | ○ | ○ | ○ | ○ | ○ | ○ | ○ | ● | ● | ● | ● | L10 起 |
| G10 | 宏 | ○ | ○ | ○ | ○ | ○ | ○ | ○ | ○ | ○ | ● | ● | ● | L11 起 |
| G11 | canonical 搜索/Val::Call | ○ | ○ | ○ | ○ | ○ | ○ | ○ | ○ | ○ | ○ | ● | ● | L12 起（机制单测层为主） |
| G12 | package/import/module/class/calc | ○ | ○ | ○ | ○ | ○ | ○ | ○ | ○ | ○ | ○ | ○ | ● | L13 起 |
| G13 | prelude 证明/数据套件 | ○ | ○ | ○ | ○ | ○ | ◐ | ◐ | ◐ | ◐ | ◐ | ◐ | ● | 语义自 L07 起可自带定义跑，prelude 形态仅 L13 |
| G14 | 健壮性/终止/栈安全 | ◐ | ● | ● | ● | ● | ● | ● | ● | ● | ● | ● | ● | occurs/unify 终止 L03 起；fuel L07 起；effort L10 起 |
| G15 | HDL | ○ | ○ | ○ | ○ | ○ | ○ | ○ | ○ | ○ | ○ | ◐ | ● | 完整形态 L13；L12 `Val::Call` 是铺垫 |

各章"新增语义"一句话：L01 归一化变体对比；L02 双向检查+βη；L03 洞+pattern
unification；L04 icit 穿线+插入+命名隐式；L05 typed metas+剪枝；L06 字符串+
decl 表+builtin+decl 序列；L07 enum/GADT/match（dpm-nbe 显式替换精化）；L08
struct/投影；L09 MLTT 再定基（宇宙层级，comma 显示）；L10 trait/实例求解；
L11 宏+decl 表世界；L12 canonical 搜索+Val::Call；L13 命名空间+module/class/
calc+prelude+HDL。

---

## 2. 用例目录

每条用例：ID、源码（该章方言，尽量可跑）、期望、出处。标 ⚠ 的片段是
"形态示意"，落地时按既有同族测试校准精确文案/输出。

### G0 求值 / conv / 遮蔽骨架 —— **L02 起**

| ID | 名称 | 源码（L02–L05 方言） | 期望 | 出处 |
|---|---|---|---|---|
| G0-01 | church 数求值 | `let two : U -> U -> U = \A s. \z. s (s z);` nf 模式 | 输出 `\A s. \z. s (s z)` 型规范形 | elab-zoo 02 / normalization-bench |
| G0-02 | β conv | `(λ f. f z) (λ x. x)`（church 变体） | 归约到 `z` | elab-zoo 01/02 |
| G0-03 | η 吸收 | `let eta : (A : U) -> (f : A -> A) -> A -> A = \A f. f;` | 通过（βη conv；L02 起） | elab-zoo 02 conv |
| G0-04 | let 透明 | `let t : U = U; let u : U = t;` nf | 体按 decl/let 语义展开（逐章口径） | elab-zoo 02 ex1/ex2 |
| G0-05 | 遮蔽换位 | `(\x. \y. x)` 应用于两个不同 church 数 | 取**内层绑定前**的正确变量（de Bruijn 换位不串） | mini-agda test/succeed（conv 族） |
| G0-06 | 深度求值 | church 翻倍链 n=2^k（k=10） | 栈线程内完成，nf 节点数断言 | normalization-bench / L01 church 负载 |
| G0-07 | distill 往返 | 任意正向用例：elab 输出 quote→pretty→重解析→再 elab | 幂等（输出二相同） | Aya DistillTest（**建议新增**，目前无） |

> G0 在 L06+ 方言的等价形态：`def id[A : U](x: A): A = x` +
> `println (id two)`。每个正向用例都应同时过三种模式（L02–L04：nf/type；
> L05 起：+elab）与双实现 parity。

### G1 双向检查走廊 —— **L02 起**

| ID | 名称 | 源码（L02–L05 方言） | 期望 | 出处 |
|---|---|---|---|---|
| G1-01 | 注解 λ 检查 | `let id : (A : U) -> A -> A = \A x. x; id`（ex0 前半） | Ok | elab-zoo 02 |
| G1-02 | 自应用负例（ex0） | `let bar : U = id id;` | Err：`Expected U, got U -> U` 类（首错位置在第二实参） | elab-zoo 02 ex0 |
| G1-03 | 未注解 λ 不可推断 | `(\x. x) (\y. y);` | Err：`Cannot infer type for lambda` | elab-zoo 02（infer 走廊） |
| G1-04 | 非函数应用 | `let bad : U -> U = \x. x x;` | Err：非函数/域不匹配（文案按章） | Agda test/Fail（application 族） |
| G1-05 | 作用域错误 | `let bad : U = y;` | Err：`Name not in scope: y` + 位置 | elab-zoo Errors.hs / mini-agda test/scope |
| G1-06 | Π 域/值域不匹配 | `let bad : U -> U = \x. zero;`（无 zero 的章用 church 替身） | Err：域失配 | Agda test/Fail |
| G1-07 | check vs infer 走廊 | `(\x. x)` 作实参（check 位）vs 作函数头（infer 位） | 前者 Ok 后者 Err（G1-03 的对照面） | elab-zoo 02 |

L06+ 方言等价（L06 起所有章通用）：`def bad(x: Nat): Nat = x x;`、
`def f = (x => x) (y => y);`（⚠ 未注解 λ 报错形态按章校准）。

### G2 元变量 / holes —— **L03 起**

| ID | 名称 | 源码（L03 方言） | 期望 | 出处 |
|---|---|---|---|---|
| G2-01 | 洞由合一解出 | `let id2 : (A : U) -> A -> A = λ A x. id _ x;`（配套 `id`） | Ok，洞解为 `id` 的实参类型 | elab-zoo 03 EX |
| G2-02 | 洞解引用局部变量 | `let k : (A B : U) -> A -> B -> A = λ A B x y. _;`（elab 模式） | 未解洞的显示**抽象掉全部局部**（pattern unification 核心）：`?m A B x y : A` 形 | elab-zoo 03 |
| G2-03 | 洞解逃逸作用域（scope check） | ⚠ 洞的解需引用不在其 bds 里的变量——形态族见 `tests/l05_blackbox_v3.rs` occurs 全谱组 | Err：scope error / can't unify | elab-zoo 03 rename scope check |
| G2-04 | occurs check | ⚠ 解中出现 meta 自身——形态族同上 | Err：occurs（不得死循环） | elab-zoo 03 / Agda test/Fail |
| G2-05 | 未解洞呈现 | L03–L05：elab 模式尾部 `displayMetas`（L05 起带类型 `let ?m : A = v;`）；L06+：unsolved meta Err | 按章口径 | elab-zoo 03/05、docs/syntax.md §3.7 |
| G2-06 | η + Flex 合一 | `?m` 对 `λ x. f x` 经 η 解出 | Ok（flex-rigid η 解） | elab-zoo 03/04 |

### G3 隐式参数 —— **L04 起**

方言注：L04/L05 用 `{}`（`{A : U}`、`const {B = U} U`、`\{B = B} a b c. a`）；
L06 起用 `[]`（`[A : U]`、`f [B = U]`、`[B = x] => body`）。以下给 L04 原生形态。

| ID | 名称 | 源码 | 期望 | 出处 |
|---|---|---|---|---|
| G3-01 | 隐式自动插入 | `let id : {A : U} -> A -> A = \x. x;` 应用 `id church2` | Ok（插入 `?A` 并解出） | elab-zoo 04 |
| G3-02 | 位置隐式实参 | `let argTest1 = const {U}{U} U;` | Ok（按 icit 对位） | elab-zoo 04 EX |
| G3-03 | 命名隐式实参 | `let argTest2 = const {B = U} U;` | Ok（`insert_until_name` 定位） | elab-zoo 04 |
| G3-04 | 命名隐式未命中 | `const {C = U} U;` | Err：`No named implicit argument with name C` | elab-zoo 04 Errors |
| G3-05 | 命名隐式 λ | `let namedLam : {A B C} -> A -> B -> C -> A = \{B = B} a b c. a;` | Ok（`B` 为体内可见本地名） | elab-zoo 04 |
| G3-06 | icitness mismatch | 显式 Π 函数收 `{u}` 实参 | Err：`Function icitness mismatch: expected explicit, got implicit` | elab-zoo 04 |
| G3-07 | inserted binder 不可见 | 非 λ 项 check 到隐式 Π（自动补 binder），体内尝试引用补的 binder 名 | 该名不可见 | elab-zoo 04（NameOrigin::Inserted） |
| G3-08 | 命名隐式 λ 不可推断 | `(\{A = A} x. x)` 处于 infer 位 | Err：`Cannot infer type for lambda with named argument` | elab-zoo 04 |
| G3-09 | unify 的 icit 纪律 | Π 比较要求 icit 相等；spine 实参比较忽略 icit | 正反各一条（⚠ 文案按章） | elab-zoo 04 Unification |

### G4 typed metas + pruning —— **L05 起**

| ID | 名称 | 源码（L05 方言） | 期望 | 出处 |
|---|---|---|---|---|
| G4-01 | typed meta 显示 | `let m : (A : U)(B : U) -> U -> U -> U = _;`（elab） | 尾部 `let ?m : (A : U)(B : U) -> … = …;`（**带类型**形态，L05 起） | elab-zoo 05 displayMetas |
| G4-02 | 剪枝掩码求解 | ⚠ 同一 meta 以互异变量实参出现在方程两侧、部分槽需剪除——形态组已覆盖于 `tests/l05_blackbox_v3.rs`「剪枝掩码」 | Ok（L05）；同一形态在 L04 判不可解 | elab-zoo 05 pruneVFlex/pruneTy |
| G4-03 | **L04↔L05 判定反转对** | 取 G4-02 中最简一例，同源码分别在 L04、L05 harness 下跑 | L04 Err / L05 Ok（反向钉死剪枝的价值面） | **建议新增**（成对用例，最直白的章节间差异证明） |
| G4-04 | pruneTy 的 RevPruning | 外→内掩码与 Π 层配对的用例（历史 bug 回归） | Ok 且解形正确 | 本仓历史 TODO 修复（已修，需保钉） |
| G4-05 | 陈旧值引读 | 状态化角落：meta 演化后旧值引读 | Err 判定稳定（真 bug 回归） | `l05_blackbox_v3` 已有，保留 |

### G5 字符串 / builtin / decl 表 —— **L06 起**

时代注：L06–L08 有 builtin 注册表；L09/L10 README 明记"无 builtin 注册表/可
变全局/文件 IO"（时代缺口）；L11 恢复 decl 表世界；L13 由 prelude 承接。
本组用例 **仅对 L06–L08、L11–L13 开**，L09/L10 跳过。

| ID | 名称 | 源码（L06 方言） | 期望 | 出处 |
|---|---|---|---|---|
| G5-01 | 字面量与转义 | `def s = "a\nb\\c"; println s` | 转义解释正确；`""` 合法；未知转义原样保留 | elab-zoo 06 程序形态（本仓自研延伸） |
| G5-02 | 字面量内的注释符号 | `def s = "http://x"; println s` | `//` 不当注释（strip 感知字符串） | 本仓历史 bug |
| G5-03 | prim 全元数触发 | `println (string_concat "a" "b")` / `str_eq "a" "b"` | 归约输出 / 得布尔 | L06 builtin |
| G5-04 | 部分应用保持卡住 | `println (string_concat "a")` | 打印卡住 Decl 头（不 panic、不误归约） | L06 语义 3 |
| G5-05 | decl 查表 miss 卡住 | 引用未注册 builtin 名并应用 | 卡住 Decl 头（`get_global` 缺名同口径） | L06 语义 2 |
| G5-06 | 重定义负例 | 同名 `def` 两次 / `def` 撞 builtin 名 | Err：`redefine {名}`；类型错误先于重定义报 | L07 语义（L13 fake_bind 前传） |
| G5-07 | 可变全局 | `def g = let gid = create_global "g" two; get_global "g"; change_mutable …` 链 | 连续更新链语义正确（黑盒 v2 有契约） | L06/L07 |
| G5-08 | 文件 IO 失败降级 | 指向不存在路径的文件 prim | 卡住降级而非 panic（`v2_file_*_stuck_not_panic` 契约） | 2026-09-17 评审轮 |
| G5-09 | decl 流残余 token | 顶层 decl 后带 `;` 或残余 token | 解析整体报错并**带首个残余 token 内容与偏移**（不静默截断） | L06 README 语法要点 |

### G6 enum / match / 依赖模式匹配 —— **L07 起**（dpm-nbe 五例为核心）

公共底座（L07 方言，L09+ 原样可用）：

```typort
enum Nat {
    zero
    succ(n: Nat)
}
def add(x: Nat, y: Nat): Nat =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }
def two = succ (succ zero)
enum Id[A](x: A, y: A) {
    refl(a: A) -> Id a a
}
```

| ID | 名称 | 源码（追加到上述底座） | 期望 | 出处 |
|---|---|---|---|---|
| G6-01 | ADT 基础 | `def four : Nat = add two two` + `println four` | L07：`Nat::succ([Nat] Nat::succ(...))` 空格系；L09+：`Nat::succ(Nat::succ(Nat::succ(Nat::succ(Nat::zero))))` comma 系 | elab-zoo 07 骨架 / dpm-nbe |
| G6-02 | **dpm-nbe sym** | `def sym[A : U](a: A, b: A)(e: Id[A] a b): Id[A] b a = match e { case refl(x) => refl x }` | Ok（refl 特化：`b =?= a` 双向精化；已验证） | dpm-nbe ex0 |
| G6-03 | **dpm-nbe trans** | `def trans[A : U](a: A, b: A, c: A)(e1: Id[A] a b, e2: Id[A] b c): Id[A] a c = match e1 { case refl(x) => match e2 { case refl(y) => refl a } }` | Ok（已验证） | dpm-nbe ex1 |
| G6-04 | **dpm-nbe cong** | `def cong[A : U, B : U](f: A -> B, a: A, b: A)(e: Id[A] a b): Id[B] (f a) (f b) = match e { case refl(x) => refl (f a) }`；调用写 `cong[Nat, Nat] (n => add n zero) two two (refl two)` 或逐槽 `cong[Nat][Nat] …`（两形态等价，2026-09-19 起 L06 起统一支持） | Ok（已验证；括号 λ 作实参亦验证通过） | dpm-nbe ex2 |
| G6-05 | **dpm-nbe H（索引算术精化链）** | `def H(m: Nat, n: Nat)(e1: Id[Nat] n (add m zero), e2: Id[Nat] m zero): Id[Nat] n zero = match e1 { case refl(x) => match e2 { case refl(y) => refl zero } }` | Ok（`n := add m zero`、`m := zero` 后目标归约；已验证）——这是旧"改写式精化" add_assoc 一族 bug 的教科书复现面 | dpm-nbe ex3 |
| G6-06 | **dpm-nbe C（荒谬前提，零臂 match）** | `def C[A : U](h: Id[Nat] (succ zero) zero): A = match h {⏎}`（零臂） | Ok（refl 特化方程 `zero ≡ succ zero` 冲突 → 无可达构造子，零臂即完备；ex falso；已验证） | dpm-nbe ex4；本仓 `l07_blackbox_v3` 零臂组 |
| G6-07 | GADT/索引族 | Vec 声明 + `def t[len]`（README §2 原例）与 `def head[T, L](x: Vec[T] (succ L)): T` | Ok（`succ L` 精化） | L07 README §2 |
| G6-08 | 类型层 match（大消去） | `def TyOf(b: Bool): U = match b { case true => Nat  case false => Bool }` + `def dep(u: TyOf true): Nat = u` | Ok（ scrutinee 归约后依赖类型成立） | `l07_blackbox_v2` 类型层 match |
| G6-09 | 覆盖缺失负例 | `def bad(x: Nat): Nat = match x { case zero => zero }` | Err：match 不完整（文案按章）；**覆盖粒度分时代**：L07/L08 路径感知（嵌套路径缺失也报，实测文案 `match 不完整：模式位置 succ#1 缺少构造子 zero`）；L11/L12 顶层-only（README 登记的收窄）——同一源码两段时代期望不同，成对登记 | Idris2 tests/coverage |
| G6-10 | 通配臂遮蔽 | 通配臂之后的臂 | Err/告警：Unreachable（L11 起只认通配臂——**收窄口径**） | L11 README 诊断收窄 |
| G6-11 | 卡住 match 显示 | 表面触发面 = 类型位（`T n` 族，`v3_match_result_type_depends_on_ctor` 形）与 def 链（bench match 负载）；**注意**："看似卡住"的表面打印例（如 `half` 缺 succ^1 路径）会被 L07 路径感知覆盖检查拦截，不是卡住用例 | 卡住显示 golden 锚既有：L09+ `(unsolved match n)` 简形（`golden_stuck_match_display`、l13 legacy） | L09 显示形态（刻意分歧） |
| G6-12 | 卡住 match 的合一（strict η） | `def use_eta(n: Nat): Id[Nat] n (match n { case x => x }) = refl n`（底座 Id） | Ok（已验证）——strict η 的分支体必须是**模式绑定器本身**（内核条件 `Tm::Var(Ix(0))`）；`case _ => n` 不构成 eta（实测 `can't unify`） | L07 README §3.3 + unification.rs:1091 |
| G6-13 | 卡住 match 再应用（splice） | 卡住的 match 值继续被应用 | L07/L08：实参 splice 进分支体；L09+：**不可再应用**（时代缺口，η 臂 `v_applicable` 守卫改判 Err）——**同一用例两段时代期望相反，按章分开登记** | L09 README 时代缺口 1 |
| G6-14 | 嵌套模式 + 深精化 | `bits_adder`（Vec[Bool] 递归全加器，legacy test7 迁移件） | Ok | L07 tests.rs |
| G6-15 | 索引等式负例 | 对 `Vec[Nat] zero` 给 `cons` 分支（方程失配） | 臂不可达/报错 | l07_blackbox_v3 |
| G6-16 | fuel 耗尽可诊断 | 深嵌套模式负载（`test_deep_pattern_fuel_budget_regression` 形态） | 有界降级 + `(fuel exhausted)` 尾注，不挂起不假 absurd 于预算内负载 | L07 README §7.2 |
| G6-17 | **transN 规模生成回归** | 生成器：N 跳 `Id` 传递链（dpm-nbe `genTransN`，N∈{3,10,50}） | 全 Ok；N=50 下燃料/深度不失控 | dpm-nbe genTransN（**建议新增**，参数化生成） |
| G6-18 | 隐式模式子臂 | `case cons[_](x, xs) => …` / 隐式绑定器缺省通配 | Ok（按 icit 对齐，隐式可缺省） | L07 README §4.1 |
| G6-20 | **隐式实参两形态（跨章回归钉）** | `f[Nat][Nat]`（逐槽）与 `f[Nat, Nat]`（逗号合写，2026-09-19 回移植 L06–L10，此前仅 L11+ 支持） | 两形态 elaboration 产物**逐字节相等**；参考↔孪生 parity——回归套件 `tests/implicit_comma_args.rs`（L06–L12 逐章钉住） | 本轮实测（2026-09-19） |

### G7 struct / 记录 —— **L08 起**

| ID | 名称 | 源码（L08 方言） | 期望 | 出处 |
|---|---|---|---|---|
| G7-01 | 声明/构造/投影 | `struct Point[T] { x: T  y: T }`（换行分隔）+ `def px[T](p: Point[T]) = p.x` + `new Point(one, two)` | Ok；投影类型正确 | docs/syntax.md §2.3 |
| G7-02 | `new` 与 `.mk` 双构造 | `new Point(a, b)` 与 `Point.mk a b` | 等价 | docs/syntax.md |
| G7-03 | 值显示（时代分叉） | `println p` | L08：`Point::Point.mk(...)` 空格系；L09+：comma 系——**不得互贴** | a4-r3 定案 |
| G7-04 | 中性投影 | 对卡住值取字段 | 卡住投影参与 unify（不证等、不 panic） | l07_blackbox_v3 卡住投影 |
| G7-05 | 单构造子 enum 脱糖 | L09+：struct 声明脱糖为 `{Name}.mk` 单构造子 enum | 行为与 L08 原生一致（parity 面） | L09 README 保留面 |
| G7-06 | 依赖字段 | `struct DPair[A](B: A -> U) { fst: A  snd: B fst }`（⚠ 支持度待验证） | 若支持则 Ok；若不支持登记为限制/分歧 | mini-agda Σ 族（**待验证项**） |

### G8 分层宇宙 / 大消去 —— **L09 起**

| ID | 名称 | 源码（L09 方言） | 期望 | 出处 |
|---|---|---|---|---|
| G8-01 | Type 0 : Type 1 | `def t0 : Type 1 = Type 0` | Ok（已有 `test0`） | mini-agda test/succeed（universe 族） |
| G8-02 | Girard 负例 | `def bad : Type 0 = Type 0` | Err（宇宙层级失配） | mini-agda test/fail；Agda test/Fail |
| G8-03 | 累积性 | `def lift(x: Type 0): Type 1 = x`；`Nat : Type 1` | Ok（README 宣称 cumulative——若无累积需登记为分歧） | Agda cumulativity |
| G8-04 | 宇宙多态恒等 | `def id1[A : Type 1](x: A): A = x` + `id1[Type 0] Nat` | Ok（大实例化） | elab-zoo 06 first-class-poly 精神 |
| G8-05 | 大消去组合 | G6-08 的 `TyOf` 配 `Type 0` 返回位 | Ok | L09 重定基保留面 |
| G8-06 | comma 显示锚点 | `println two` | `Nat::succ(Nat::zero)`（comma 血统 golden） | L09 golden（l09_fast_parity 既有锚） |

### G9 typeclass / trait —— **L10 起**

```typort
enum Nat {
    zero
    succ(n: Nat)
}
def natadd(x: Nat, y: Nat): Nat =
    match x {
        case zero => y
        case succ(n) => succ (natadd n y)
    }
```

| ID | 名称 | 源码（追加） | 期望 | 出处 |
|---|---|---|---|---|
| G9-01 | 实例合成 | `trait Semi[T] { def append(that: T): T }` + `impl Semi[Nat] for Nat { def append(that: Nat): Nat = natadd this that }` + `def d[T][s: Semi[T]](x: T): T = x.append x` + `println (d two)` | Ok（约束位实例求解） | Lean typeclass tests / Aya |
| G9-02 | outParam（关联类型） | `trait Add[T, O: outParam(Type 0)] { def add(that: T): O }` + `impl Add[Nat, Nat] for Nat { … }` + `def four = two.add two` | Ok（O 由 impl 推出，不参与匹配） | prelude Add / L10 README |
| G9-03 | this 与方法调用糖 | `x.append x`（接收者风格）desugar 为 trait_wrap | 与 `s.append` 显式约束位语义一致（双写对照用例） | L10 trait_wrap |
| G9-04 | 无实例负例 | `def g[T](x: T): T = x.append x`（无 Semi[T] 约束、无实例） | Err：实例求解失败（effort 上限内报错，不挂起） | Idris2/Lean 负例 |
| G9-05 | 两跳实例链 | 泛型 impl（`impl Semi[List[T]] for List[T][s: Semi[T]]` 形态，⚠ 按章语法）+ 嵌套调用 | Ok（依赖子目标搜索；`traitchain` 基准负载形态） | Lean/Coq instance chains |
| G9-06 | 不可达搜索终止 | 构造无法满足的自指目标 | effort≤1000 上限触发 Err（有界），子目标缓存不爆炸 | L10 typeclass.rs 护栏 |
| G9-07 | 接收者类型剔除边界 | `Val::to_typ` 对 LiteralType/Prim 返回 None 的路径（trait_wrap 接收者） | 判 Err 而非 panic | L10 README 恢复项 |

### G10 宏 —— **L11 起**

| ID | 名称 | 源码 | 期望 | 出处 |
|---|---|---|---|---|
| G10-01 | 基本展开 | `def x = 42` + `println (stringify t123)` | `t123` 输出 | l11_fast_parity 既有 |
| G10-02 | 生成声明 | `macro_rules make_bool { (yes) => { enum Yes { y } } }` + `make_bool yes` + `def b = y` | Ok（展开产物注册） | l11 既有 |
| G10-03 | 片段类（ident/raw/params） | 三类 fragment 各一条（⚠ 按章语法） | 按类匹配；错类报错 | Rust macro_rules 语义参照 |
| G10-04 | 自递归展开深度 | 宏自递归 | 深度上限触发报错（既有 probe 覆盖，固化） | l11 probe |
| G10-05 | u64 溢出 | 展开/计数字面量溢出路径 | Err 而非 panic（既有） | l11 probe |

### G11 canonical 搜索 / Val::Call —— **L12 起**

机制章（无新语法），用例以机制单测 + parity 为主：

| ID | 名称 | 说明 | 期望 | 出处 |
|---|---|---|---|---|
| G11-01 | iddfs 预算调度 | Err 重试路径 `1,3,5,…` 步进预算；`target_limit=6` 时预算恰 6 的实例不可达（README 登记的完备性缺口） | 按登记口径（如要修，先加钉） | L12 README |
| G11-02 | canonical Err 重试等价 | Err 重试路径上 iddfs 不改变 Ok 判定（孪生侧不移植 iddfs 的对照面） | 两版 Ok 判定一致 | L12 README（孪生不移植项） |
| G11-03 | pretty_nat 守卫臂 | Nat 值显示走 `pretty_nat` 时不出格 | 不 panic、格式稳定 | L12 README |
| G11-04 | Val::Call（regNext 泛型） | HDL 泛型延迟寄存的 Val::Call 路径 | 归约/卡住语义正确（完整 HDL 用例归 G15） | L12 README |

### G12 package / import / module / class / calc —— **L13 起**

| ID | 名称 | 源码 | 期望 | 出处 |
|---|---|---|---|---|
| G12-01 | package 前缀 | `package mylib.utils` + `def helper(x: Nat): Nat = x` | 声明自动带前缀；绝对路径不叠加 | docs/syntax.md §2.6 |
| G12-02 | 单名/花括号导入（S1/S3） | `import mylib.MyType.member` 后 `MyType` 不可用（负）；`import mylib.{x, y}` 后 `mylib` 本体不可用（负） | 按 S1/S3 语义判定 | namespace_tests.rs 语义 + syntax.md S1/S3 |
| G12-03 | 通配导入 | `import mylib._` 把 `MyType` 本体带入 | Ok | syntax.md |
| G12-04 | prelude 裸名优先（D1） | `mylib.zero` 与 prelude `zero` 同名冲突 | 裸名恒解析 prelude；限定名解析 mylib（**无警告**，golden 钉行为） | syntax.md D1 |
| G12-05 | 后缀 fallback 限域 | 裸 `mux` 解析到 `Expr.mux` 仅当首段是 decl key/可见命名空间 | 越域候选不解析（负例） | syntax.md |
| G12-06 | 查找顺序 | `局部 → 全局精确（含 prelude 裸别名）→ import 别名 → namespace 限定 → 后缀 fallback` 全序 | 每序一例（⚠ 逐条 golden） | syntax.md §8 |
| G12-07 | module 宏 | `module counterDemo { … }` 端口/reg/when/for 展开（`module_tests.rs` 39 测已覆盖） | 展开/错误按既有 golden | L13 module |
| G12-08 | class 语法 | `class Point { let x: Nat = succ zero  def sum: Nat = this.x + this.y }` + `println (Point.create.sum)` | Ok | L13 class_tests |
| G12-09 | calc 链（正/误） | `def zero_add_comm_calc(n: Nat): Eq (0 + n) (n + 0) = calc { 0 + n = n by add_zero_left n  n = n + 0 by symm (add_zero_right n) }` | Ok；步骤错误时 Err 且 span 正确 | L13 calc_tests |
| G12-10 | 单行 enum 同错形态 | `enum Nat { zero succ(n: Nat) }`（单行） | 两版同错（**行为钉子**，非 bug；防止未来"顺手修掉"漂移） | l13_fast_parity 头注 |
| G12-11 | 尾部声明静默丢弃（Bug 1） | docs/l13-known-bugs-2026-08.md Bug 1 复现源码 | **当前行为：静默丢弃（未修）**——先加行为钉子锁住现状，修复后翻转期望 | **缺口：无测试锚点**（P0） |

### G13 prelude 证明 / 数据套件 —— **L13 起**（语义形态自 L07 起可自带定义）

prelude 仅在 `run_with_prelude` / LSP 路径加载（L02–L12 章节测试不加载）。
本组是"标准库 + 标准证明"的集成半区：

| ID | 名称 | 源码（L13，可用 prelude） | 期望 | 出处 |
|---|---|---|---|---|
| G13-01 | Eq 消去器 | `def transport[A](P: A -> Type 0, x: A, y: A)(e: Eq x y, p: P x): P y = match e { case refl(_) => p }` | Ok（⚠ K 层面无保护是既定教学取舍） | mini-agda / dpm-nbe |
| G13-02 | 引理直引 | `def comm(n: Nat, m: Nat): Eq (n + m) (m + n) = add_comm n m` | Ok（prelude 预证引理签名稳定） | prelude core/nat |
| G13-03 | calc 组合 | G12-09 全链 + 一条带 `cong` 步的链 | Ok | calc_tests |
| G13-04 | List 程序族 | `list_map`/`list_foldr`/filter 组合（prelude data） | Ok + println 输出 golden | prelude data |
| G13-05 | Vec 依赖程序 | `Vec[A](len)` 的 append/index（legacy `test_index` 形态） | Ok + comma 显示 golden | legacy_tests.rs:604 |
| G13-06 | Option/Result/Either | 三族构造+match（prelude data） | Ok | prelude |
| G13-07 | prelude 单元级回归 | prelude 文件逐个 `load_prelude_skip_hdl` 后跑一条 smoke（**建议新增**：目前 prelude 只有 LSP/examples 间接覆盖） | 全部 Ok | **缺口：prelude 盲区**（P1） |

### G14 健壮性 / 终止 / 栈安全（跨章，按轴适用）

| ID | 名称 | 适用轴 | 说明 | 出处 |
|---|---|---|---|---|
| G14-01 | occurs/unify 终止 | L03 起 | G2-04 的全谱组（l05_blackbox_v3 已有），任何章新增 unify 臂都要复跑 | elab-zoo |
| G14-02 | fuel 边界 | L07 起 | 深嵌套模式/多 pending 卡住 match 带超时；`(fuel exhausted)` 文案 | l07_blackbox_v3 性能悬崖 |
| G14-03 | 深值栈安全 | L07 起（2026-09-18 后） | 默认 2MB 栈下 10 万层 occurs/结构比较、1 万层 rename 收集器（`deep_value_iterative_under_default_stack` 等三钉）；深值**释放**递归 Drop 与 quote/pretty 深路径是登记残留（§7.6） | L07 README §6 末行 |
| G14-04 | σ 跨轮回收 | L07 起（孪生） | `fast_substv_reclaimed_across_rounds`：两轮复用后 `SUBSTV_ALIVE` 回落基线 | L07 README §7.7 |
| G14-05 | effort 上限 | L10 起 | G9-06；实例求解/子目标缓存在上限内收敛 | typeclass.rs |
| G14-06 | 解析残缺不 panic | L02 起 | 截断源码、CRLF、非 ASCII、臂间注释行（L07+ `EndLine+` 放宽）、中文 offset（LSP） | parser_error_tests 91 测 + l07 v3 解析残缺组 |
| G14-07 | 并发/隔离 | L06 起 | 跨 run 隔离、path_id、`FILE_IO_LOCK`、large didOpen 不挂起 | l06/l07 blackbox v2 |
| G14-08 | transN 生成器 | L07 起 | G6-17（规模参数化，dpm-nbe 做法） | dpm-nbe |

### G15 HDL —— **L13 起**（L12 `Val::Call` 为铺垫）

现状已覆盖较好（`test_examples_hdl_dir` 全量 include_str + twin parity +
sim_tests + emit_tests），目录化动作只有三条：

1. **10+11 组合回归缺口**：`11-bundle-deep` 单文件安全，但与 10 系列同文件
   的深嵌套组合无回归钉（docs/l13-force-recursion-stack-overflow.md 的绕行
   面）——新增一条组合文件用例（P1）。
2. HDL004 宽度冻结（typeclass-instance-nat-param Bug B，未修）：补一条
   "警告出现即通过"的行为钉子（P1）。
3. 其余以 examples 目录为 golden 源，不在本目录展开。

---

## 3. 现状对照与缺口（按优先级）

现状（2026-09-19 探索盘点）：`tests/` + `src/` 内嵌合计 ~1800 个 #[test]；
L02–L08 有成体系 blackbox（含错误位置/文案 golden + parity）；L07 系测试最厚
（blackbox ×3 轮 + fast_parity 70）；L09–L13 黑盒负向很薄；golden 全部内嵌
（无外部快照）；`tests/parser_error_tests.rs` 是不变量式（不 panic 即过），
对文案质量无约束。

**P0（体系性缺口，建议先做）**

1. **L09–L13 负向半区补齐**（G1/G2/G6/G8/G9 的负向列，每章 ≥8 条 Err
   golden：判定 + 关键文案 + 位置）——Agda/mini-agda"fail 半区"平移。
2. **L07/L08 fast_parity 的 Err 升级为 `norm_err` 正文比对**（对齐 L09–L13），
   消除"错误文案漂移只能靠零散 contains"的状态。
3. **已知未修 bug 加行为钉子**：known-bugs Bug 1（G12-11）、typeclass
   Nat-param Bug B（G15-2）；Bug 2（lvl2ix 下标 panic 缓解面）补一条
   `should_panic` 式锚点。Lean 的 issue-编号回归文件惯例：报告文档名 ↔ 测试
   名一一对应。
4. **dpm-nbe 五例成套化**（G6-02..06 + G6-17）：sym/trans/cong 已散在
   tests.rs，补 H、C（零臂）与 transN 生成器，统一命名 `dpm_sym` 等。

**P1（覆盖补强）**

5. prelude 单元级回归（G13-07）；`load_prelude_skip_hdl` 下逐文件 smoke。
6. G4-03 判定反转对（L04 vs L05 同源码期望翻转）——最直白的"章节差异"测试。
7. G8 宇宙负例与累积性钉子（G8-02/03，顺带验证 README 的 cumulative 宣称）。
8. distill 往返幂等（G0-07）——Aya 经验，防显示/解析漂移（a4-r2 事故的
   通用疫苗）。
9. 深值残留路径（quote/pretty 深递归、递归 Drop）的定深拒绝或迭代化后补钉
   （G14-03 的登记残留）。
10. 探针/临时文件清理：`tests/zz_tmp_l13_debug.rs`、`probe_macro_bugs.rs`、
    `l13_into_probe.rs`（自述临抛件）移出测试编译面或转正。

**P2（整理与一致性）**

11. golden 统一化：共享 parser/pretty 的显示断言目前散在 25+ 文件；建议
    显示格式锚点集中在各章 fast_parity 的 golden 区（L09 已自带锚注释），
    新用例一律引用锚点不另立文案。
12. 三份 L07 tests.rs 拷贝（`src/L07`、`src/L08` 前置、`src/bench_pre`）的
    单一来源化（include 或生成）。
13. `parser_error_tests.rs` 从不变量式升级为"错误类别 golden"（首错类别 +
    位置行，不必钉全文案）。

---

## 4. 新用例落地模板

```rust
// tests/l0X_fast_parity.rs 追加（L09–L13 形态；L07/L08 同型，Err 暂比判定）
const SRC_DPM_H: &str = r#"
enum Nat {
    zero
    succ(n: Nat)
}
def add(x: Nat, y: Nat): Nat =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }
enum Id[A](x: A, y: A) {
    refl(a: A) -> Id a a
}
def H(m: Nat, n: Nat)(e1: Id[Nat] n (add m zero), e2: Id[Nat] m zero): Id[Nat] n zero =
    match e1 {
        case refl(x) =>
            match e2 {
                case refl(y) => refl zero
            }
    }
"#;

#[test]
fn parity_dpm_h_index_arithmetic_refine() { assert_parity(SRC_DPM_H); }

#[test]
fn golden_dpm_h_index_arithmetic_refine() {
    assert_eq!(run_basic(SRC_DPM_H).unwrap(), "<comma 血统输出，先跑参考版取值>");
}
```

约定：**每个正向用例至少过 parity + golden 两级；每个负向用例过 parity
（Err 归一化正文）+ 文案 contains**。章节适用性存疑时（如显示格式分时代、
语义时代缺口 G6-13），把同一源码在两段时代的期望**并排登记成两条**，不共享
断言。

---

## 5. 出处速查（用例 ↔ 上游）

- elab-zoo 02 `EX0/EX1/EX2` → G1-01/02、G0-04（本仓 `src/L02_tyck/mod.rs` 同名常量）
- elab-zoo 03/04/05 示例 → G2/G3/G4（本仓 L03–L05 `EX*_SRC`）
- dpm-nbe `ex0..ex4`、`genTransN` → G6-02..06、G6-17（本地 `F:\projects\hermes\dpm-nbe\src\Main.hs:16-50`）
- mini-agda test/succeed、test/fail → G0-05、G8-01/02（双目录心智模型整体）
- Agda test/Succeed、test/Fail → G1-04/06、G8-02（fail 半区 + 特性分目录心智模型）
- Idris2 tests/coverage 与 golden `.err` → G6-09、§0 断言金字塔第 3 级
- Lean 4 tests/lean issue-编号回归 → §3 P0-3（报告↔测试命名对应）
- Aya TyckTest/DistillTest → G0-07、显示/检查分离原则
