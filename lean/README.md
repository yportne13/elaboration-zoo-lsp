# Typort 类型论的 Lean 4 形式化

把本仓库（`elaboration-zoo-lsp`，Rust）实现的类型论抽取成一个自足的谓词演算，
用 Lean 4 写出它的语法、转换关系、判型规则，并证明一批基础引理。

* 工具链：**Lean 4.34.1**（`leanprover/lean4:v4.34.1`），**不依赖 Mathlib**（只用 core / Std）。
* 规模：8 个模块、1029 行、57 条已证明的定理/引理，**无 `sorry`、无 `axiom`、无 `admit`、无 `unsafe`**。
* 抽取规格（本形式化的依据，逐条带 `file:line` 锚点）在仓库 `docs/` 下：
  [`tt-spec-l09.md`](../docs/tt-spec-l09.md)（L09 内核）、
  [`tt-spec-l07-l08.md`](../docs/tt-spec-l07-l08.md)（归纳族 / 积类型 / match）、
  [`tt-spec-metas-typeclass.md`](../docs/tt-spec-metas-typeclass.md)（元变量 / 隐式参数 / 类型类）。

## 构建与校验

Lean 工具链未装在 PATH 上（本机 `~/.elan` 是 2021 年的 elan 1.0.7，只认 Lean 3）。
本目录用的是官方 release 解压出来的 4.34.1：

```powershell
$L = "$env:USERPROFILE\.lean4-toolchain\lean\lean-4.34.1-windows"
$env:PATH = "$L\bin;$env:PATH"
Set-Location lean
lake build            # 构建整库（默认目标 Typort），应输出 Build completed successfully
```

如果装了可用的 elan（≥ 3.x）或 `lean` 在 PATH 上，直接 `lake build` 即可；
本目录未放 `lean-toolchain` 文件，以便使用本地已有的 4.34.1 工具链
（如需固定版本，加一个内容为 `leanprover/lean4:v4.34.1` 的 `lean-toolchain`）。

## 模块 ↔ 仓库章节

| Lean 模块 | 形式化内容 | 对应 Rust |
|---|---|---|
| `Typort/Basic.lean` | `Name` / `Ix` / `Lvl` / `Icit` | `L02_tyck/mod.rs:26-43`（`Ix`/`Lvl`/`Name`）、`L09_mltt/parser/syntax.rs`（`Icit`） |
| `Typort/Syntax.lean` | 核心项 `Tm`（de Bruijn）、臂链 `Arms`、上下文 `Ctx`、telescope 折叠 | 各层核心 `Tm`：`L02_tyck/mod.rs:47`、`L09_mltt/mod.rs:63-84`（含 `Sum`/`SumCase`/`Match`/`Meta`/`Prim`） |
| `Typort/Subst.lean` | 重命名 `ren` / 替换 `subst` / `lift` / `subst0` 及其代数律（`ren_id`、`ren_ren`、`subst_id`、`subst_ren`、`ren_subst`、`subst_subst` …） | 元运算层；实现侧的显式替换 `Subst` 见 `L07`/`L09` 的 `subst.rs`（语义不同，见下「实现层 vs 声明层」） |
| `Typort/Conversion.lean` | `Step`（β / ζ / ι + 同余）、`EtaStep`（λ-η 展开）、`Conv`（等价闭包）及其同余律 | βη-转换：`L02_tyck/mod.rs:135-171`；`unify`：`L09_mltt/unification.rs:542-759`；β/ζ/ι 的求值点见 `L09_mltt/mod.rs:705-812`、`pattern_match.rs:361-411` |
| `Typort/Signature.lean` | 归纳族/构造子声明 `IndDecl`/`CtorDecl`、签名 `Sig`、由声明算出的族类型/构造子类型/motive 类型/臂类型、覆盖谓词 | `enum` 声明与构造子类型：`L07_sum_type/elaboration.rs:268-443`；`check_ctor_wf`：同文件 `:383-443`；参数/索引按 icit 区分见 `docs/tt-spec-l07-l08.md` §1 |
| `Typort/Typing.lean` | 声明式判型 `HasType`（`u`/`pi`/`lam`/`app`/`letE`/`ind`/`ctor`/`matchE`/`convTy`）、上下文良构 `WF`、平移/重命名/覆盖性引理 | 双向走廊 `check`/`infer`：`L09_mltt/elaboration.rs:296-376`、`:624-917`；非累积宇宙 `:822` 与 `unification.rs:569`；`check_universe` `:246-295` |
| `Typort/Prelude.lean` | 仓库 prelude 的**真实声明**：`Nat`、`Boolean`、`Eq`、`Vec`、`Void` 及其签名表 | `src/prelude/core/nat.typort:11-16`、`core/bool.typort:16-21`、`core/eq.typort:8-11`、`data/vec.typort:4-9`、`core/void.typort`；清单顺序 `L13_namespace/mod.rs:4095-4111` |
| `Typort/Examples.lean` | 在演算内部构造的判型推导（恒等函数、`Nat`/`Boolean`/`Eq` 的族类型）与归约步（β/ζ/ι） | 对照 `L02_tyck` 的 `ex1`/`ex2`（`mod.rs:605-623`）与 prelude 的 `Eq` 组合子 |

## 形式化的类型论（摘要）

**核心语法**（de Bruijn 索引，`Tm`）

```
Tm ::= var i | Type n | Pi ic A B | lam ic t | app ic f a | let A t u
     | ind D | ctor D c | match s P arms
Arms ::= nil | cons ci body rest          -- 臂链（构造子下标, 臂体）
```

* `ind D` / `ctor D c` 是**族常量**与**构造子常量**：它们的类型由签名给出
  （族：`(params) → (indices) → Type level`；构造子：`(params) → (tele) → D params retIndices`），
  应用统一走 `app`。这与实现一致：L09 起 enum 本体与构造子经 `fake_bind` /
  `define_global` 登记后就是按 Π 类型当函数用的（`L09_mltt/README.md` §2）。
* `match s P arms` 把 **motive 显式写成项**（Agda 式消去子）；臂体写成 λ telescope。

**判型规则**（`HasType`，节选）

| 规则 | 前提 → 结论 |
|---|---|
| `u` | `Γ ⊢ Type n : Type (n+1)`（**非累积**） |
| `pi` | `Γ ⊢ A : Type l₁`、`Γ.A ⊢ B : Type l₂` ⇒ `Γ ⊢ (x : A) → B : Type (max l₁ l₂)` |
| `lam` | `Γ ⊢ A : Type l`、`Γ.A ⊢ t : B` ⇒ `Γ ⊢ λx. t : (x : A) → B` |
| `app` | `Γ ⊢ f : (x : A) → B`、`Γ ⊢ a : A` ⇒ `Γ ⊢ f a : B[x := a]` |
| `letE` | `Γ ⊢ A : Type l`、`Γ ⊢ t : A`、`Γ.A ⊢ u : B` ⇒ `Γ ⊢ let x : A := t; u : B[x := t]` |
| `ind` / `ctor` | 查签名得 `D.type` / `ctorType`（在空上下文中定义，按 `Γ.length` 平移） |
| `matchE` |  scrutinee `s : D p̄ ī`、motive `P : (ī) → D p̄ → Type l`、覆盖全部构造子、每臂 `b : (tele_c) → P ī_c (c …)` ⇒ `Γ ⊢ match s P arms : P ī s` |
| `convTy` | `Γ ⊢ t : A`、`A ~ B`、`B` 是类型 ⇒ `Γ ⊢ t : B` |
| `var` | 查 `Γ[i] = (x : A)`，且 `A` 在其**尾部上下文**（= 更早的绑定）中是类型 ⇒ `Γ ⊢ x : shiftN (i+1) A` |

变量规则里「绑定类型在其尾部上下文中是类型」这一额外前提是刻意的：
它保证畸形上下文无法凭空判型，同时让 `HasType` 保持**非互归纳**——
Lean 4 的 `induction` 对互归纳类型不可用（实测报
`The induction tactic does not support the type … because it is mutually inductive`），
而元定理必须对判型推导做归纳。

**转换**（`Conv`）：`Step`（β / ζ / ι + 同余）与 `EtaStep`（λ-η 展开）的等价闭包。
实现里 η 只有 λ-η，且带 `v_applicable` 守卫（`L09_mltt/mod.rs:324-330`），
形式化只取 λ-η 发生器；**没有** sum/struct 的 η（与实现一致）。

**已证明的内容**（选定）

* 重命名/替换代数：`ren_id`、`ren_ren`、`subst_id`、`subst_ren`、`ren_subst`、`subst_subst`、
  `subst0_lift`、`subst_subst0`、`shiftN_zero`、`shiftN_succ`（`Subst.lean` / `Typing.lean`）。
* `Conv` 是等价关系，且对 `pi`/`lam`/`app`/`let`/`match` 各位置同余（`Conversion.lean`，9 条）。
* 覆盖性与臂查找：`Arms.find?_isSome_of_hasCtor`（`Signature.lean`）、
  `Arms.find?_renArms`、`Arms.hasCtor_renArms`（`Typing.lean`）。
* 具体的判型推导：恒等函数 `λA x. x : (A : Type 0) → A → A`、
  `Nat`/`Boolean`/`Eq` 的族类型、以及 β/ζ/ι 三条归约步与 `Conv` 吸收（`Examples.lean`）。

## 诚实边界（未形式化的部分）

形式化的范围是**声明式类型论**（语法 / 转换 / 判型 / 一批基础引理）。
以下是明确**没有**形式化的内容，以及原因：

1. **match 的索引精化 / 上下文精化（最重要的一处）**。实现把模式匹配的方程
   （头部索引 ≐ 构造子返回索引）**解成替换 σ 并作用到整个环境上**
   （`L07/pattern_match.rs:350-396` 的 `unify_indices` + `cxt.rs:333-352` 的
   `subst_cxt` + `subst.rs` 的 `Subst`/`frcs`），因此它接受的字面写法比 Agda 式
   「显式 motive + λ telescope 臂」**严格更强**：prelude 里
   `def trans[A,x,y,z](e1: Eq x y, e2: Eq y z): Eq x z = match e1 { case refl(a) => e2 }`
   （`src/prelude/core/eq.typort:30-33`）与 `subst`（同文件 `:49-52`）在标准规则下
   **不可判型**（臂的期望类型是 `Eq a z` / `P a`，而 `e2` / `p` 的类型是
   `Eq y z` / `P x`，除非把上下文里的 `x`、`y` 替换掉），但实现接受。
   本形式化的 `HasType.matchE` 是标准规则（`armType`），能覆盖 `cong`、`symm`
   这类臂（`Eq` 的 motive 取 `λ i₁ i₂ _. Eq (f i₁) (f i₂)` / `λ i₁ i₂ _. Eq i₂ i₁`），
   **不覆盖** `trans`/`subst` 的字面写法。要形式化精化，需要 Cockx 式的
   dependent pattern matching 统一化理论（方程求解 + 上下文替换的健全性），
   远超本轮范围。
2. **元变量 / 合一 / 剪枝 / fuel**。`Val::Flex`、`solve`、`invert`（要求 spine 是
   互异裸 rigid 变量）、occurs check、`prune_meta`、`UNIFY_FUEL=4096` 的有界降级
   都没有形式化；抽取规格在 `docs/tt-spec-metas-typeclass.md` §1-2。
   连带地，实现的 `conv` 是**值层** βη-比较（不是项层 `Conv`），本形式化只取项层关系。
3. **NBE 引擎**：`Val`（13 个构造子）、`eval`/`quote`/`force`/`frcs`、闭包与
   spine、卡住 match 的重选、`VSub` 显式替换、`struct_eq` 快路径、fuel 都没有形式化
   （`docs/tt-spec-l09.md` §2-4）。因此**没有**「算法健全性」
   （`eval`/`unify` 的结果与声明式关系一致）这类定理。
4. **顶层声明层与 δ 归约**：`fake_bind` 占名 + 递归 def（`L09_mltt/elaboration.rs:393-405`）、
   global 值表（哨兵 `1919810`）都没有形式化。形式化把全局名字当作**上下文里的变量**
   （`Sig` 只含归纳族），所以没有「def 展开」这条归约，prelude 的
   `add_zero_right : Eq (n + 0) n = rfl`（靠 `nat_add n 0` 定义性归约到 `n`）
   在本形式化里无法直接重演（缺 δ/primop 层）。
5. **类型类 / trait / impl / 实例求解**（`L10`/`L12`，字典传递 + 表驱动 SLD +
   `effort>1000` panic）没有形式化；规格见 `docs/tt-spec-metas-typeclass.md` §3-5。
6. **隐式参数与自动插入**（`insert`/`insert_until_name`、`[A, B]` 合写、
   隐式域默认 `U(0)`）没有形式化：`Icit` 作为标记保留在语法与规则里，
   但「什么时候插隐式实参」这层 elaborator 逻辑没有建模。
7. **模式编译器**：决策/逐臂下钻、嵌套位置覆盖检查、不可达臂、`#[derive(Bundle)]`、
   `struct` 脱糖、投影（`L08`）都没有形式化。`Signature.lean` 只保留声明与
   臂-类型计算；`Covers` 是**覆盖性要求**的谓词，但没有实现里的
   `probe_accessible`（可达性/absurd 臂）机制。
8. **HDL / Verilog 生成**（`L13` 的 `module`/`reg`/`blackbox` 等）是代码生成层，
   不是类型论，不在范围内；`UInt[w]` 这类依赖类型本身已由 `ind`/`ctor` + Pi 覆盖。
9. **元定理的进一步目标**：替换引理（`HasType Γ a A → HasType (Γ.A) t B →
   HasType Γ t[a] B[a]`）与**主体归约**（subject reduction）尚未证明。技术障碍是
   两处：(a) π/λ 规则在**头部**插入 binder，而替换引理的归纳必须在
   「上下文同态」下做（需要把 `CtxMor` 的 `matchE` 情形补齐：`motiveType` /
   `armType` 对重命名的交换律）；(b) Lean 的 `induction` 不支持互归纳，
   变量规则的「尾部类型」前提已按此调整。这两条是有明确路线的下一步。

## 实现层 vs 声明层：为什么不是逐行移植

实现（`src/L01..L13`）是一台带元变量、合一、显式替换精化、arena/bump 分配的
**elaborator**；类型论本身只是它的声明式骨架。本形式化选择：

* **保留**：de Bruijn 索引与层级、`icit` 标记、telescope 约定、非累积宇宙、
  `Type n : Type (n+1)`、Π 层级取 `max`、β/ζ/ι 三条归约、λ-η、
  构造子返回类型的参数位必须是族参数（`check_ctor_wf`）、覆盖性要求。
* **替换**：全局声明表 → `Sig` + `ind`/`ctor` 常量（等价于实现里
  「登记后按 Π 类型当函数用」）；变长实参列表 → 统一的 `app`；
  模式 → 逐构造子的 λ telescope + 显式 motive。
* **省略**：元变量、合一、精化、fuel、NBE 引擎、类型类、HDL（见上节）。

## 后续工作

1. 补 `CtxMor` 的 `matchE` 情形（`motiveType`/`armType`/`appAll` 对 `ren` 的交换律，
   `Arms.find?_renArms` 已在 `Typing.lean` 里备好），得到完整重命名引理 →
   弱化 → 替换引理 → **主体归约**（β/ζ 先做，ι 需要 telescope 实例化引理）。
2. 把 `Typort.Signature` 的 `Sig` 扩成含 def 的全局表，加 δ 归约，
   以便在演算内重演 `src/prelude/core/nat.typort` 的 `add_zero_right` 等 `rfl` 引理。
3. 形式化精化式 match（依赖模式匹配的统一化），使 prelude 字面写法的
   `trans`/`subst` 可判型——这是与实现对齐的最大缺口。
4. 形式化 `unify` 及其健全性（成功 ⇒ 两值在 `Conv` 下相等），以及
   `prune_meta`/occurs check 的语义。
