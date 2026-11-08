# 审计：迭代化重写（2309e2a4）的遍历面完整性

> 对象：L07 参考版 `src/L07_sum_type`（分支 `fix/l07-match-unify`）。
> 起因：P15（`struct_eq` 漏比卡住 match 的 pending 值，S1）暴露了一类错误——
> **把递归遍历改写成任务栈时漏掉某个部件**。审计目标：同一轮改写涉及的所有
> 遍历器，逐 case 对照旧递归版，找出同类漏项。
> 方法：`git show 2309e2a4^:<file>` 取旧版，与当前实现逐分支比对"旧版扫到
> 哪些字段 / 新版压了哪些任务"；不看注释（P15 正是注释正确、实现漏项）。

## 结论

| 遍历器 | 改写形态 | 旧版位置 | 结论 |
|---|---|---|---|
| `struct_eq::val_eq/tm_eq/env_eq` | `EqTask` 任务栈 | `2309e2a4^` `val_eq_go/tm_eq_go/env_eq_go` | **1 处漏项 = P15**（pending 值），已修（`0c73b65d`） |
| `val_mentions_lvl` | `InlineStack` 工作栈 | 旧 `mod.rs` 同名递归 | **无漏项**（14 个 Val 变体逐一对应） |
| `rename / rename_deep / rename_arm` | 帧式收集器 + 原位 lift | 旧 `rename`/`rename_sp` 递归 | **无漏项**（详见下节） |

即：这类错误在 L07 参考版**只有 P15 一处**，其余两处改写是忠实的。

## 1. struct_eq（已修复）

旧 `val_eq_go` 15 个臂 / `tm_eq_go` 16 个臂 / `env_eq_go` / `closure_eq` 与
新版 `EqTask::{V,T,Env,Spine,Closure}` 一一对应。唯一差异是 Match 臂：

- 旧版：`xp.len() == yp.len() && zip.all(|((xv,xi),(yv,yi))| xi == yi && val_eq_go(xv,yv))`
- 新版（修复前）：只比 `xi == yi`，**未压 `EqTask::V(xv, yv)`**
- 修复后：先压 pending 值任务（LIFO ⇒ 最后弹出，符合注释访问序）。

其余臂的边界语义也已核对：`Obj` 比名字 + 内层 + spine；`Sum` 比名字 + 逐参数
`(icit, val, ty)`；`SumCase` 比 `case_name` + `typ` + 逐 datas `(icit, val)`；
`Lam/Pi` 比 icit + 闭包（env 与体）；`Spine` 比 icit + 值；预算只在 V/T 入口烧
（Env/Spine/Closure 展开不烧），与旧版一致。

## 2. val_mentions_lvl（无漏项）

旧递归 14 个臂 vs 新迭代 14 个臂，逐臂对应：

`Rigid`（自层 + spine）、`Flex/Decl/Prim`（spine）、`Obj`（内层 + spine）、
`VSub`（只扫内层，**不扫 σ 映射值**——注释明示的语义）、`Sum`（参数 val+ty）、
`SumCase`（typ + 逐 datas）、`Match`（scrutinee + env 槽 + pending）、
`Lam/Pi/U/LiteralType/LiteralIntro`（不进入，与旧一致）。

无字段遗漏；迭代化只改了栈结构，未改遍历面。

## 3. rename（无漏项，但值得记录几处等价性）

旧 `rename` 递归 14 臂 vs 新 `rename → rename_deep(Sum/SumCase/Obj) / rename_arm(其余)`：

1. **深链分派**：`Sum/SumCase/Obj` 走帧式收集器，其余回落 `rename_arm`；
   `rename_arm` 对这三种保留防御性 `Err`（入口已分派），`VSub` 保留 `Err`（不变式）。
2. **Sum 帧**：pending 逐参数压 `[val, ty]`，组装按同序取回 —— 与旧版
   "每参数 `rename(v)` 后 `rename(t)`" 一致。
3. **SumCase 帧**：pending = `[typ, datas…]`，组装先 typ 后 datas —— 与旧版
   先 rename typ、再逐 datas 一致。
4. **Obj 帧**：pending = `[被投影者, spine 实参（头→尾）]`；组装先 `Obj(inner)`，
   再把实参**逆序**折叠成 App 链。实测与旧 `rename_sp` 的应用序等价
   （spine 头 = 最后应用 ⇒ 最外层 App）。
5. **Lam/Pi 的 lift**：旧版 `lift(&pren)` 克隆表；新版 `ren.insert(pren.cod, pren.dom)`
   原位插入 + 回滚。插入键值、body 求值用的 `vvar(pren.cod)`、以及 Pi 先 ren
   定义域后 ren 余定义域的顺序均与旧版逐点一致；Err 路径也回滚。
6. **Match**：顺序 val（未 lift）→ 每分支 `env.prepend(vvar(cod))` + `lift_in_place`
   → 分支体在简化 decl 表下重求值后 rename → pending（未 lift）。与旧版一致。

## 4. 残留与边界

- **孪生版**（`bump_spine_iter`）的同类遍历（`struct_val_eq` / `mentions_level` /
  `rename_iter`）未审计——按当前决定"孪生版先不管"。P15 恰好证明两版可以独立
  出错，因此这仍是后续风险点。
- 本轮未改写的遍历（`quote`、`pretty`、`prune_*`、`invert`）仍是递归实现，
  不属于"改写漏项"类；它们的风险是深值爆栈（P11），另一类问题。
- **方法可复用**：`git show <rewrite-commit>^:<file>` 作为 oracle，逐臂对照
  "旧扫字段 / 新压任务"。这类审计成本低（约 2 小时），建议列入每次大改写的 checklist。

## 5. 复现清单

```sh
git show 2309e2a4^:src/L07_sum_type/struct_eq.rs   # 旧递归版
git show 2309e2a4^:src/L07_sum_type/mod.rs         # 旧 val_mentions_lvl
git show 2309e2a4^:src/L07_sum_type/unification.rs # 旧 rename/rename_sp
```

P15 的反例与回归钉见 `L07-RISKS.md` 的 P15 小节。
