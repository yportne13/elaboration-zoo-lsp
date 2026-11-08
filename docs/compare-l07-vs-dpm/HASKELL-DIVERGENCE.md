# Haskell 原版 dpm-nbe 的"打印/比较 λ 就发散"：是什么、是否 bug、修法

> 对象：`F:\projects\hermes\dpm-nbe`（`KonjacSource/dpm-nbe`，GHC 项目，HEAD `ed5fa07` 2026-08-30 "typo"）。
> 结论：**是真实缺陷**，但它只暴露在"force 一个裸 λ"的路径上（打印 normal form、或对函数类型的项做转换判定）；对仓库自带的示例无影响，因为它们的程序总以 `; U` 结尾、结果永远不是 λ。
> 本文件同时给出可直接提交的 issue 草稿（[`ISSUE-haskell-frc-lambda.md`](ISSUE-haskell-frc-lambda.md)）。

## 1. "发散"具体指什么

三种含义要分清：

| 说法 | 含义 | 本仓库实测 |
|---|---|---|
| 类型检查发散 | `infer`/`check` 不停 | **否**。c1/c3/c4/c5/h1/h2/h3 的 `infer` 全部 11–13 ms 返回 |
| 打印发散 | `nf`/`print` 不停 | **是**。c1/c3/c4/c5 的 `nf` 15 s 无输出（被 kill） |
| 转换判定发散 | `conv` 不停 | **是**。h2/h3（`refl : Id (Nat→Nat) (λx.x) (λx.x)`、`refl : Id ((n:Nat)→Nat) h h`）10 s 无返回 |

也就是说：**求值器/打印器在"值是一个 λ"时死循环**，而类型检查本身（只要不进行比较或打印）是正常的。

## 2. 根因（`src/Eval.hs`）

```haskell
-- Eval.hs:106-113
napp v sp = case frc v of
  v | len sp == 0 -> progress v          -- ← 位置太晚：先 frc 了 v
  VNe (NVar n sp') -> block $ VNe $ NVar n (sp' +++ sp)
  VNe (NLam ps n cl sp') | len sp + len sp' >= n -> match ps n cl (sp' +++ sp)
                         | otherwise -> block $ VNe $ NLam ps n cl (sp' +++ sp)
  v -> error $ "napp: impossible ..."

-- Eval.hs:78-83
frc = \case
  NSub n sb       -> frcS sb n
  NVar v sp       -> VNe $ NVar v (frc sp)
  NLam ps n cl sp -> frc $ napp (VNe $ NLam ps n cl Sp) (frc sp)   -- ← 自旋点
  NPlus u v       -> frc $ plus (frc u) (frc v)
```

自旋链：
`frc (VNe (NLam … Sp))` → `frc (NLam … Sp)` → `frc (napp (VNe (NLam … Sp)) Sp)`
→ `napp` 的 `case frc v of` 先求值 `frc (VNe (NLam … Sp))` → **回到起点**。

注意 `v | len sp == 0 -> progress v` 这条守卫写在 `case frc v of` 的**分支位置**，所以"空 spine 直接返回"的意图**永远执行不到**——它依赖的值已经被 force 过了。

为什么打印会触发：`nf = quote 0 (eval …)`，`quote` 对 `VNe` 调 `frc`（`quoteNe`），于是打印任何 λ 都进入自旋。
为什么转换会触发：`conv` 同样先 `frc` 两侧，于是比较两个函数值也自旋（h2/h3 实证）。

## 3. 影响面（实测）

| 程序（官方 CLI 语义） | 未打补丁 | 打补丁后 |
|---|---|---|
| `let pr : (Nat -> Nat) -> Nat -> Nat = \ f x . f x; pr` 的 `nf` | 死循环 | `λ f x . f x`（12 ms） |
| `let f : Id (Nat -> Nat) (\ x . x) (\ x . x) = refl; f` | 死循环 | `refl : Id (Nat → Nat) (λ x . x) (λ x . x)` |
| `let h : (n : Nat) -> Nat = \ n . n; let e : Id ((n : Nat) -> Nat) h h = refl; e` | 死循环 | `refl : Id ((n : Nat) → Nat) (λ n . n) (λ n . n)` |
| `plus (suc zero) (suc zero)` 的 `nf`（不含 λ） | `succ (succ zero)`（正常） | 同左 |
| 仓库自带 README 示例（全部以 `; U` 结尾） | 正常（从不打印 λ） | 同左 |
| `let C … = λ A (!); C`（荒谬消去） | 死循环 | **`eval: impossible`**（暴露第二个缺陷，见 §5） |

推论：**任何"结果里含 λ 的 normal form"都打不出来**，任何"函数类型项之间的等式"都证不了。这不是"打印好看不好看"的问题，而是编译器能力缺口（`Id (A→B) f g` 这种类型在这种实现里无法被消去）。

## 4. 最小补丁（已验证）

```haskell
-- Eval.hs:78-84 —— 空 spine 的 λ 本来就是值
instance Force Ne Val where
  frc = \case
    NSub n sb       -> frcS sb n
    NVar v sp       -> VNe $ NVar v (frc sp)
    NLam ps n cl sp | len sp == 0 -> VNe $ NLam ps n cl sp
                    | otherwise   -> frc $ napp (VNe $ NLam ps n cl Sp) (frc sp)
    NPlus u v       -> frc $ plus (frc u) (frc v)
```

在**源码副本**上打此补丁后重新编译（`-i` 指向副本，未改原仓库），上表全部由"死循环"变为正常返回。这也验证了根因判断。

补丁的语义安全性：`frc` 只负责把"延迟替换/中性项"推到 WHNF；一个空 spine 的 `NLam` 已经是 WHNF，短路不改变任何可观测语义（Rust 移植版的 NOTES 偏离 1 用的正是这条）。

## 5. 补丁之后暴露的第二个缺陷：`Bot` 没有值

```haskell
-- Eval.hs:137-152 片段：eval 没有 Tm.Bot 的分支
```
打印 `λ A (!)` 需要 `eval Bot`，原版直接 `error "eval: impossible"`（`CallStack` 可见）。Rust 移植版为此加了 `Val::Bot`（NOTES 偏离 7）。两处可以合成一个 issue，也可以拆两个（推荐拆：一个是 force 自旋，一个是缺失值构造）。

## 6. 是不是"已知问题"？

- 本仓库 README/NOTES **没有**这条记录（README 只列语法与设计动机）；
- 但 Rust 移植版 `dpm-nbe-rs/NOTES.md` 的 **偏离 1** 原文写道："With an empty spine, `napp` forces its argument, which is again this lambda, so `frc` of a *bare* lambda value diverges (a lambda wrapped in a delayed substitution goes through the `frcS` arm instead and blocks). Since `conv` and `quote` force their arguments, the original cannot even compare or print a lambda." —— **移植作者（很可能就是同一批人）已经知道并修了，但上游 Haskell 仓库里没有对应 issue/commit**。
- 所以：这是"上游未修的已知缺陷"，提 issue 是合适的；也可以直接把移植版的 NOTES 当依据。

## 7. 关于"拉最新版本"

本机**无法联网**：`origin` 指向 `https://ghfast.top/https://github.com/KonjacSource/dpm-nbe`，`git fetch` 与直连 `github.com` 均超时；`web_fetch/web_search` 在本次会话中不可用（provider 配置报错）。因此只能确认：

- 本地工作区干净、HEAD = `ed5fa07`（2026-08-30，"typo"），`git rev-list --left-right --count HEAD...origin/HEAD` 为 `0 0`（以本地 refs 为准）；
- 该缺陷位于 `napp`/`frc` 的定义中，属于 elaboration-zoo 的原始代码（README 明说 "base code is directly copied from András Kovács' elaboration-zoo"）；除非上游重写求值器，否则不会自行消失。

若你能联网，请先 `git pull` 再复核；issue 草稿已按"对 HEAD `ed5fa07`"的口径写好，若上游已变请顺手改 commit 号。

## 8. 交付

- issue 草稿（英文，可直接粘贴）：[`ISSUE-haskell-frc-lambda.md`](ISSUE-haskell-frc-lambda.md)
- 复现脚本与探针：`%TEMP%\dpmhsprobe\`（`Probe.hs`、`probe.exe`、补丁副本 `hs\`、`probe_patched.exe`）；仓库内未留任何源码改动。
