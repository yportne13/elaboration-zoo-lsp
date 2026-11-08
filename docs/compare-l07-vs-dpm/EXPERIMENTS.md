# 实证补件：三侧实测（L07 / dpm-nbe-rs / Haskell 原版）

> 目的：把总报告里标【推断】的两条关键行为跑实，并顺带测原始 Haskell 实现。
> 时间：2026-10-30。环境：Windows 10，Rust 1.9x debug/release，GHC 9.10.2。
> 结论摘要：**修正 2 条推断，新增 1 条 L07 健壮性退化，实证 dpm 的 1 条移植偏离**。

## 0. 一句话结论

同一组 5 个程序喂给三个实现：自指索引**三侧全部接受**（02 文档"L07 会拒绝"是错的）；卡住索引方程上 **L07 花 256 s 后报"分支不可达"（假不可达）**，而 Haskell 原版与 dpm 都在 ~10 ms 内报 `not sure`；Haskell 原版对**任何 λ 的 nf/打印**都发散（`NOTES.md` 偏离 1 的实证），dpm 已修复。

## 1. 方法

| 侧 | 做法 |
|---|---|
| L07 | 临时 `examples/l07_probe.rs`（约 20 行：读文件 → 64 MB 栈线程里调 `L07_sum_type::run` → 打印 `== OK ==`/`== ERR ==`），`cargo build --example` 后按文件跑。**测完已删除该文件。** |
| dpm | `cargo build --release`（仓库自带旧二进制早于源码，会把 `Nat` 报成未绑定变量，必须重编译），`dpm-nbe nf` 从 stdin 读程序。 |
| Haskell | 机器有 GHC 9.10.2（stack 的 `programs` 目录）但**无 megaparsec 包**。因此：① 写一个 `Text.Megaparsec` 桩（只提供 `SourcePos/Pos/initialPos`，项目里仅 Syntax/Context/Main 用到这三个名字）；② 绕过 `Parse.hs`，**直接构造 `Raw` AST**；③ 用 cabal 的 default-extensions 手工编译（含 `StrictData`）。等价于 CLI 的 `nf`/`type` 两种模式。 |

超时控制：`System.Diagnostics.Process.WaitForExit(ms)`，超时即 Kill；L07 分别给 90 s（debug）/120 s（release）/300 s（长测），其余 12–15 s。

## 2. 用例

| # | 程序（三侧语义相同） | 意图 |
|---|---|---|
| c1 | `λ x refl . zero : (x : Nat) → Id Nat (suc x) x → Nat` | 自指索引 `x := suc x`（经模式变量中转） |
| c1b | 同上但索引对调：`Id Nat (suc x) x` → 单步内即可形成 `x := suc x` | 检验 occurs 是否逐方程 |
| c2 | `λ x y refl . zero : (x y : Nat) → Id Nat (plus x zero) (plus y zero) → Nat` | 两个**递归** def 的卡住索引方程 |
| c2b | 把 `plus` 换成非递归的 `g`（`g x` 仍卡住） | 隔离"递归"是否是触发条件 |
| c2c | `Id Nat (add zero x) (add zero y)`（scrutinee 可归约） | 隔离"卡住 scrutinee"是否是触发条件 |
| c3 | `λ A (!) : (A : U) → Id Nat (suc zero) zero → A` | 荒谬消去 |
| c4 | H 例：`λ m n refl refl . refl` 作用在两个等式上 | 双重精化（dpm README 的主例） |
| c5 | `λ f x . f x : (Nat → Nat) → Nat → Nat` | 打印 λ（Haskell 偏离 1 的触发面） |

L07 侧全部用 `enum Nat`/`enum Eq[A](x: A, y: A){ refl(a: A) -> Eq a a }` 表达（`Eq` 对应 `Id`），`add` 是递归 `def` + `match`。

## 3. 结果（判定 + 实测耗时）

| 用例 | L07（release） | dpm-nbe-rs | Haskell 原版（infer） | Haskell（nf） |
|---|---|---|---|---|
| c1 | **接受**，81 ms | **接受**，13 ms | **接受**，12 ms | 发散（15 s 超时） |
| c1b | **拒绝**（分支不可达），8 ms | 未测 | 未测 | — |
| c2 | **假不可达**（"分支不可达"），**256 197 ms** | 报 `not sure`，5 ms | 报 `not sure`，11 ms | 同左（错误先于打印） |
| c2b | 接受，13 ms | 未测 | 未测 | — |
| c2c | 接受，8 ms | 未测 | 未测 | — |
| c3 | 接受，9 ms | 接受，6 ms | 接受，11 ms | 发散（15 s 超时） |
| c4 | 接受，8 ms | 接受，5 ms | 接受，11 ms | 发散（15 s 超时） |
| c5 | 接受，8 ms | 接受，5 ms | 接受，11 ms | 发散（15 s 超时） |

打印产物（仅 c5 三侧可比）：L07 `f => x => f x`；dpm `λ f x . f x`；Haskell 打不出。
c1/c3 的 dpm 输出：`λ x refl . zero : (x : Nat) → Id Nat (succ x) x → Nat`、`λ A (!) . ⊥ : (A : U) → Id Nat (succ zero) zero → A`。

## 4. 结论

### F1（修正 02 §4-A）自指索引：三侧**全部接受**，L07 的 occurs 是逐方程的、不传递的

02 文档推断"L07 会以分支不可达拒绝"——**错**。L07 实测接受 c1。机制：特化方程依次是 `x = a` 与 `succ x = a`（`a` 是构造子字段的 fresh 模式槽）：

1. `x := a`（x 可解、无环）；
2. `succ x` 在当前 acc 下变 `succ a`，与 `a` 合一 → `a := succ a`？**不**——实际是先命中 `(SumCase, Rigid a)` 臂解出 `a := succ x`（`succ x` 不含 `a`，occurs 通过）。

每一步的浅 occurs 都通过，组合出循环 σ `x := a, a := succ x`。变体 **c1b**（索引对调，使第二步直接是 `x vs succ x`）立刻被拒（"分支不可达"，8 ms）——**证明 L07 的浅 occurs 只挡单步环，挡不住经模式变量中转的链式环**。按理论，c1 的方程 `x = suc x` 无解，该子句应当不可达；L07 接受属于"解出循环替换"的健全性缺口（与 dpm 缺 occurs 殊途同归，但 L07 有检查却没做到传递闭包）。

> **修复后（2026-10-31）**：分支 `fix/l07-match-unify` 的四个 commit 已把该行为改为「**无法判定**」（278 ms），详见 [`L07-RISKS.md`](L07-RISKS.md) §0.1。本文其余实测记录保持修复前口径（用于对照）。
### F2（修正 02 §4-C）卡住索引方程：L07 不是"可能接受"，而是**假不可达 + 4 分钟**

02 推断"L07 可能接受"。实测：release 下 **256.2 s** 后返回 `分支不可达：模式 Con("refl"…)` —— 即把"解不出来"报成了"矛盾"，正是 README §7.2 说的 fuel 有界降级，但本例只有 4 个 `def`（`Eq`/`Nat`/`add`/`f`），完全不是"极深嵌套负载"。同题 Haskell 11 ms、dpm 5 ms 都干净地报 `I am not sure if there should be a pattern 'refl'…`。

### F3 触发条件被隔离到"递归 def × 刚性 scrutinee"

- **c2b**（`g x`/`g y`，`g` 非递归，仍是卡住 match）：13 ms 接受 → 说明 Match/Match 合成本身没问题。
- **c2c**（`add zero x`/`add zero y`，scrutinee 立即归约成 `x`/`y`）：8 ms 接受 → 说明"卡住"是必要条件。
- **只有 c2**（递归 `add` + 刚性 scrutinee `x`/`y`）爆炸。

机制推断（与 03 文档 D5、README §1.4 一致）：unify 的 Match/Match 臂先合一 scrutinee（`x := y` 本来可解），但**槽位只包裹不物化**（design doc §4 纪律），两份卡住 match 的捕获 env 各带不同的 `VSub` 实例；`struct_eq` 的 VSub 分支只对**同一 `Rc` 实例**短路（`struct_eq.rs:82-88`），于是快路径不命中，回落到"逐分支在 fresh rigid 下重求值"；递归 def 的分支体又产生新的卡住 match，层级每层递增，永不结构收敛，直到 fuel 池耗尽。每层都要 eval/quote，4000 次调用因此要数百秒。**这正是 README §1.4 说"期望类型重锚"要解决的问题——但覆盖探测/特化方程路径没有 rebase，快路径在这里失效。**

### F4（实证 NOTES 偏离 1）Haskell 原版打印任何 λ 都发散

c1/c3/c4/c5 的 `nf` 全部 15 s 超时且无输出，而同一程序的 `infer` 全部 11 ms 通过。`NOTES.md` 偏离 1 描述"frc 一个裸 λ 用空 spine 调 napp 自旋"完全属实。dpm 已修（偏离 1/3）；L07 不涉及（它的 `Lam` 值不带 spine，应用在 `v_app` 里 β）。

### F5 打印口径确实是跨侧 golden 的第一道坎

同一 λ：L07 `f => x => f x`、dpm `λ f x . f x`、Haskell 无法产出。三侧输出**不能直接逐字节对比**。

## 5. 对现有文档的修订

| 文档 | 位置 | 修订 |
|---|---|---|
| `FINAL.md` | §5 行 1（自指索引） | "L07 拒绝【推断】" → **三侧均接受**；补 c1b 说明 occurs 不传递 |
| `FINAL.md` | §5 行 3（卡住索引方程） | "L07 可能接受【推断·未验证】" → **L07 假不可达 256 s**（Haskell/dpm ~10 ms 报 not sure） |
| `FINAL.md` | §5 新增行 11–13 | 打印发散、L07 假不可达耗时、c1/c1b 对照 |
| `02-pattern-unify.md` | §4-A、§4-C、存疑 1/2 | 以本文件的 F1/F2 为准 |
| `01-subst-force.md` | S1 的 L07 侧 | 同上（L07 接受；对调顺序才拒绝） |
| `03-value-quote.md` | D3/D8 | 结论不变，仅补打印口径实测（F5） |

## 6. 复现

### L07 探针（`examples/l07_probe.rs`，已删除，可原样重建）

```rust
use elaboration_zoo_lsp::L07_sum_type::run;

fn main() {
    let path = std::env::args().nth(1).expect("usage: l07_probe <file>");
    let src = std::fs::read_to_string(&path).expect("read source file");
    let h = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || run(&src, 0))
        .expect("spawn");
    match h.join().expect("join") {
        Ok(out) => println!("== OK ==\n{out}"),
        Err(e) => println!("== ERR ==\n{e}"),
    }
}
```

```sh
cargo build --release --example l07_probe
cargo run  --release --example l07_probe -- c2.l07
```

### Haskell 侧

```sh
# 1) 桩：<tmp>/Text/Megaparsec.hs 只提供 SourcePos/Pos/initialPos
# 2) <tmp>/Probe.hs 直接构造 Raw（绕过 Parse.hs），getArgs 选用例
# 3) 编译（cabal 的 default-extensions 手工传入）：
ghc -v0 -XLambdaCase -XNoMonomorphismRestriction -XOverloadedStrings \
    -XPatternSynonyms -XRecordWildCards -XStandaloneDeriving \
    -XStrict -XStrictData -XTupleSections -XDerivingVia -XViewPatterns \
    -XFunctionalDependencies -XFlexibleInstances -XScopedTypeVariables \
    -XMultiParamTypeClasses \
    -i<tmp> -iF:/projects/hermes/dpm-nbe/src -outputdir <tmp>/out \
    <tmp>/Probe.hs -o <tmp>/probe.exe
```

用例源码与运行脚本保留在 `%TEMP%\dpmhsprobe\`（`l07_c*.l07`、`Probe.hs`、`run_all.ps1` 等），本仓库未留任何探针源码。

## 7. 残留与影响

- 已删除 `examples/l07_probe.rs`；仅剩构建产物 `target/{debug,release}/examples/l07_probe.exe`（不影响仓库，可忽略或 `cargo clean`）。
- L07 的 256 s 结果说明：**README §7.2 的"有界降级"在实践中可能昂贵到等同挂起**，且本例不需要"极深负载"。若要给 L07 排期，这是优先级最高的可修项（候选修法：Match/Match 直接比较捕获 env 时先做 `wrap_sub` 的规范化，或对"同一递归 def + 不同槽位"的卡住 match 加结构指纹/共享 σ 短路）。
