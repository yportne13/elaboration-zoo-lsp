# L07 收尾：let 洞快路径 + 孪生封印 + 源码注解渲染（2026-11-23）

> 分支 `feat/l07-let-fastpath-and-twin-seal`（从 `master 17b2058f` 拉出，3 个提交）。
> VUnfold 那套（`Val::Fold` / `UnfoldMode` / `FoldMode`）**不在本分支**——留在
> `exp/l07-vunfold` 作研究记录。

## 1. 无注解 let 的推断类型不再物化（`01e4194a`）

`check` 的 Let 臂、无类型注解（`Raw::Hole`）时，原来 `a_checked = quote(ty)` 把 2^n 的类型
树写成项。该 Tm 是**死代码**：

| 消费者 | 是否读它 |
|---|---|
| `eval(Tm::Let)` | 不读（只求值 `t`，再把结果推进 env） |
| `Locals::Define` | 只存 |
| `close_ty`（唯一真读点） | 拼 meta 类型的 `Tm::Let` |
| `prune_ty` / `lams_go` | 只在值层 `Val::Pi` 上工作（Let 在 eov 后已消失） |
| 显示层（hover/inlay） | 用名字表里的 `Val`，不是 `Locals` 的 Tm |

改为占位 `Tm::U`（永不求值/打印）。实测：

| pairtest | 改前 | 改后 | 倍数 |
|---|---|---|---|
| 10 层 | 5,026 µs | **2,902 µs** | 0.58× |
| 15 层 | 174,028 µs | **85,034 µs** | 0.49× |
| 20 层 | 5,679,699 µs | **2,841,543 µs** | 0.50× |

其它负载无回退（natadd 8.70 / church 1.40 / strchain 7.46 / global 14.38 ms @k=11）。

理论风险只有一条：**未来若新增"打印未求值体"的入口**，会看到 `let x: U`。当前入口都不会
（`println`/`nf` 先 eval；hover 用值）。

## 2. 孪生封印（`7a68abc7` + `28a9371b`）

- `Cargo.toml` 加 feature `l07-twin`（默认关）；
- `tests/l07_fast_parity.rs` 整文件 `#![cfg(feature = "l07-twin")]`（默认 0 测试）；
- `tests/l07_blackbox_v3.rs` 的 3 个纯 parity 测试整例 gated，redex 系列 4 例**保留参考版
  golden**、只 gated 孪生侧（默认 115 = 118 − 3）；
- `src/L07_sum_type/bump_spine_iter.rs` 顶部 SEALED 说明；模块仍编译（bench 可显式用）。
- 复核：`cargo test --features l07-twin`（fast_parity 99 / v3 118 全绿）。

## 3. 源码注解渲染（方案 4，本分支核心产品价值）

新增 `src/L07_sum_type/raw_pretty.rs`（~200 行）：把 def 的**签名**（params + ret_type，都是
`Raw`）打成源码形态的类型串；`elaboration.rs` 的 def 登记处，在有显式返回类型注解时用它，
否则回落到值渲染。

效果（实测，`tests/l07_source_render.rs` 3 例钉死）：

| 场景 | 旧（值渲染，展开态） | **新（源码渲染）** |
|---|---|---|
| `def g(n: Nat): T n` | `(n: Nat) → (match n { case zero => Bool; case succ(m) => Nat })`（65 字符） | **`(n : Nat) → T n`** |
| `def mkx … : Box[Nat](add (add n zero) zero)` | 189 字符（展开的 match 链） | **`(n : Nat) → (a : Nat) → Box [Nat] (add (add n zero) zero)`**（60 字符） |
| `def h(n : Nat) = g n`（无注解） | 值渲染 | 值渲染（不变） |

**代价：零**（不打时间——只在 `lsp_collect` 打开且光标落在 def 名上时拼一次字符串）。

## 4. 门禁

| 套件 | 结果 |
|---|---|
| `l07_blackbox` | 48 passed / 1 ignored |
| `l07_blackbox_v2` | 51 passed / 2 ignored |
| `l07_blackbox_v3` | 115 passed / 1 ignored（默认，孪生已封印） |
| `l07_fast_parity` | 0 passed（`l07-twin` feature 关闭） |
| `l07_lsp_surface` | 83 passed |
| `l07_source_render`（新） | 75 passed（含内嵌 lib + 3 例自有） |
| `lib L07_sum_type` | 72 passed |

口径：`CARGO_PROFILE_TEST_DEBUG=0`（本机 MSVC 的 `LNK2019 anon.llvm.*` 规避）。

