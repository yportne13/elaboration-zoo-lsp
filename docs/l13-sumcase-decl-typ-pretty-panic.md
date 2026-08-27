# L13 调研报告：`SumCase expected Tm::Sum, but got Decl("Nat")` pretty panic

> 定位日期：2026-08-27。已定位、已最小复现、**已于同日修复**（见 §7）。
> 回归测试：`tests/repro_sumcase_panic.rs`（最小 5 行复现 + 01-basics 全标识符 hover）。

---

## 0. TL;DR

`Tm::SumCase.typ` 字段**没有单一不变量**：elaboration 存的是"引用形态"
（`Tm::Decl("Nat")` / `Tm::App` / `Tm::Var` / `Tm::Meta`），quote 存的是"展开形态"
（`Tm::Sum`）。所有消费者（pretty、`Frame::Obj` 投影、`tm_to_raw_type`）都假定展开形态。

2026-08-06 的 two-phase class elaboration（`647d1e9`，`tm_to_raw_type`）开始把
**未标注类型的 module/class 字段**的推断类型经 `quote → Raw::SumCase → 重新
elaborate` 往返，产出的字段类型 Tm 里带 `typ: Tm::Decl("Nat")`（引用形态），存进
decl 表；2026-08-25 的 hover 成员列表（`8925a60`，`render_pi_member`）开始对
decl 表里的**原始类型 Tm** 直接 pretty —— 两个日期之间埋着的污染被引爆，
hover 直接 panic（会崩掉整个 LSP server 的 hover handler）。

**运行期语义不受影响**：`eval(Tm::Decl("Nat"))` 会查回 `Val::Sum`，值层面的
`typ` 总是被"治愈"。这是 Tm 层的表示卫生 bug，受害面是显示与以 Tm 为输入的工具路径。

---

## 1. 复现

5 行 HDL（`tests/repro_sumcase_panic.rs` 内嵌）：

```
module m {
    input a = UInt[8]
    let x = a + a
}
```

hover 模块名 `m` → hover 弹出成员列表 → panic：

```
panicked at src\L13_namespace\pretty.rs:417:30:
SumCase expected Tm::Sum, but got `Decl("Nat" @ 6,9)`
  at pretty_tm(prec=3, indent=0)
```

完整 hdl 示例压力路径：`examples/hdl/01-basics.typort` 的 `exprLet` 模块
（hover 其 println 里的 `exprLet` 标识符即触发），与 `probe-out.txt` 的场景一致。

## 2. 触发链（按执行顺序，含代码位置）

1. **宏脱糖**：`input a = UInt[8]` 脱糖为**带标注**的
   `let a: UInt[8] = newUIntInput(8)`（`src/prelude/hdl/hdl-macros.typort:85`）；
   `let x = a + a` 是**无标注**字段。这是同模块内 a 健康、x 被污染的唯一差异。
2. **Phase A 推断**（`elaboration.rs:1890-1898`）：无标注字段的推断类型
   `force` + `quote` 后交给 `tm_to_raw_type` 转回 Raw 注解。
   - `a + a` 的宽度值是具体的 `Val::Nat(8)`；`quote` 把它展开成
     `succ^8 zero` 的 `Tm::SumCase` 链，此时 `typ = quote(decl.get("Nat").2)`
     = `Tm::Sum("Nat")`（**健康**，`mod.rs:3057 quote_nat`）。
3. **tm_to_raw_type 往返**（`elaboration.rs:2027-2042`）：`Tm::SumCase` 映射为
   `Raw::SumCase { typ: <typ 的 Raw>, case_name, datas }` —— 具体数字 8 变成了
   `Nat::succ (… zero)` 的 **Raw 构造器链**（而不是恢复成 `Raw::Nat(8)`）。
   `Raw::Var("Nat" @6,9)` 的 span 来自 quoted `Tm::Sum` 的名字 span
   （nat.typort 定义点）——这就是 panic 消息里 `Decl("Nat" @ 6,9)` 的出处。
4. **Phase B 重 elaborate**（`expand_class_decls` → `infer_after_prefix` →
   `Decl::Enum` arm，`elaboration.rs:2622-2657`）：合成 struct 的字段注解重新
   过 checker，`Raw::SumCase` arm 存
   `typ: typ_checked = infer_expr(Raw::Var("Nat")) = Tm::Decl("Nat")`
   （**引用形态**，`elaboration.rs:2652-2654`）。这个 Pi 链作为 mk 构造器的
   类型存入 decl 表（`.3`，`cxt.rs:857`）。
5. **hover 消费**（`lib.rs:416 hover_def_block` → `mod.rs:1366
   pretty_sum_definition` → `mod.rs:1253 render_pi_member`）：成员列表对 decl 表
   里的**原始类型 Tm**（从未 nf/quote 过）直接 `pretty_tm`；
   `pretty.rs:397-429` 的 `SumCase` arm 要求 `typ` 必须是 `Tm::Sum`（Nat 数字
   特化 + 构造器名查找都依赖它），遇到 `Tm::Decl` → `panic!`（`pretty.rs:417`）。

实测确认（插桩后 Debug dump）：同一个 `exprLet.mk` 构造器里，
`a/b/y: UInt[succ^8 zero (typ=Sum)]` 健康，`x: UInt[succ^8 zero (typ=Decl)]` 被污染。

## 3. 根因：`typ` 字段的双形态（设计层面）

`Tm::SumCase.typ` 的生产者有四类，形态不统一：

| 生产者 | 位置 | 存入形态 |
|---|---|---|
| `Raw::SumCase` elaborate | `elaboration.rs:2652` | 引用（`Decl`/`App`/`Var`/`Meta`） |
| Enum 构造器 body 合成 | `elaboration.rs:1233` | 引用（声明返回类型的 elaborate 结果） |
| `quote(Val::SumCase)` | `mod.rs:2967/2982` | 展开（quote 值层的 typ） |
| `quote_nat` | `mod.rs:3060/3067` | 展开（`decl.get("Nat").2` 的 quote；decl 缺 Nat 时退化 `U(0)`） |

消费者却统一假定展开形态：

- `pretty.rs:397-429` —— Nat 数字特化与 `index → case_name` 查找都要 `Tm::Sum`，
  否则 panic（`pretty.rs:417`，复审报告 `docs/L13-code-review.md` §3.1 早已记为"低"，
  现已实际触发）。
- `eval` 的 `Frame::Obj` 投影：`_ => panic!("impossible {typ:?}")`
  （`mod.rs:2757-2760`，值层同款假定）。
- `tm_to_raw_type`：`_ => return None`（`elaboration.rs:2028-2031`，优雅退化，
  但意味着恢复注解悄悄退化成 Hole）。

注意：**值层在正常 decl 下会被治愈**——`eval(Tm::Decl("Nat"))` 查回
`Val::Sum`（`mod.rs:2637`），所以 unify/match/emit 等值层路径不受影响。
问题只在"原始 Tm 不经 eval+quote 就被消费"的路径上。

## 4. 受害面盘点（当前实际可达的）

1. **hover 成员列表**（本次 panic）：`render_pi_member` / `render_pi_signature`
   pretty 原始 decl 类型。任何模块里有**无标注且推断宽度为具体 Nat 的字段**
   （`let x = a + b`、`sel.mux(...)` 这类）都会污染其 class 的 mk 类型。
   hdl 示例里 `01-basics` 起多个文件命中。
2. **hover_def_block fallback**（`lib.rs:468`）：`typ_pretty` 为空的 decl 表项
   直接 pretty 原始 body `.1`——而**所有 Enum 构造器的 body 本来就是**
   `SumCase{typ: 引用}`（`elaboration.rs:1233`）。目前构造器表项都带
   typ_pretty 所以未触发，但这是同款地雷。
3. **次级生产者（同症状、未单独复现）**：`quote(Val::Match)` / `rename` 在
   `simpl_decl` 下求值 case body（`mod.rs:3033` / `unification.rs:430`）。
   simpl decl 把所有定义值换成 `Val::Decl`（`mod.rs:983-999`），于是：
   - `nat_succ_shape`（`cxt.rs:108-116`）在 declb 下用 `decl.get("Nat").2 =
     Val::Decl("Nat")` 构造 SumCase；
   - case body 里内嵌的 `Tm::SumCase{typ: Tm::Decl}` 在 declb 下求值出
     `Val::SumCase{typ: Val::Decl}`。
   这些值再用**原 decl** quote 回 Tm 时，`typ` 就成了 `Tm::Decl` ——
   任何后续 pretty（println 的 nf、错误消息、hover 类型）同样 panic。
4. **性能次生影响**：污染的类型把宽度 `8` 存成 9 节点的 succ 链（每个字段
   一次），且 `tm_to_raw_type` 恢复的 Raw 链再 elaborate 又逐节点重建——
   宽度本应是 O(1) 的 `Raw::Nat`。

## 5. 修复方向（计划；§7 已全部落地）

1. **修生产者（推荐先做）**：`tm_to_raw_type` 对 Nat 的 `succ^k zero` 链
   （`typ` 为 `Tm::Sum(name=="Nat")`）先数链恢复 `Raw::Nat(k)`
   （与 `pretty_nat`/`count_nat` 同款遍历），而不是逐节点 `Raw::SumCase`。
   一次修复同时消除：本 panic 的主要来源、恢复注解退化成 Hole 的隐患、
   存储类型的 succ 链膨胀。
2. **pretty 全量化（兜底，防 server 崩溃）**：`pretty.rs` 的 SumCase arm 对
   非 `Tm::Sum` typ 不再 panic —— Nat 特化同时接受 `Tm::Decl("Nat")`
   （succ 链照常打印数字）；一般情形退化为 `<pretty(typ)>::<#index>(args)`
   （与 `go_app_pruning` 的越界降级同一哲学，`pretty.rs:115-121` 已有先例）。
   hover/错误路径永远不允许 panic 是 `f62e2c2` 压力测试立下的约束。
3. **不变量收口（根治，二选一或并行）**：
   - `Raw::SumCase` arm（`elaboration.rs:2628-2654`）存 typ 前先
     `eval + quote` 强制展开形态（或直接存已求出的 `typ_val` 的 quote），
     使"存进 decl 表的 Tm 里 typ 恒为 Tm::Sum"成立；
   - 或在类型上给 `SumCase` 加构造约定注释 + `debug_assert!`，把隐式契约
     显式化（复审报告 N2 对 `Tm::Call` 提过同款建议）。
4. **次级生产者**：`simpl_decl` 保留 sum 类型表项的 `Val::Sum` 定义值
   （sum 定义不是递归 def，保留不会引起重展开），可整类消灭 declb 下的
   `typ=Val::Decl` 污染；`Frame::Obj` 的 `panic!("impossible")` 顺手降级。

## 6. 时间线（修复前）

| 日期 | 提交 | 作用 |
|---|---|---|
| 较早 | `1b380d5` | pretty 的 SumCase panic 就存在（复审记为"低"） |
| 2026-08-06 | `647d1e9` | two-phase class elaboration 引入 `tm_to_raw_type` —— **生产者**埋入 |
| 2026-08-25 | `8925a60` | hover 成员列表 `render_pi_member` —— **消费者**接通，panic 显性化 |
| 2026-08-26 | `f62e2c2` | "hover 永不 panic" 压力测试只覆盖了 4 个小文件，未含 HDL 模块的无标注宽度字段，故漏检 |

## 7. 修复（2026-08-27，同日完成）

按 §5 的 1/2/3/4 全部落地，核心是**收口不变量 + pretty 全量化**：

1. **生产者（`elaboration.rs`）**：
   - `tm_to_raw_type` 的 SumCase arm 先用 `nat_chain_len`（数 `succ^k zero`
     链，`checked_add` 防溢出）识别具体 Nat，恢复为 `Raw::Nat(k)`，不再
     生成逐节点 `Raw::SumCase` 链（宽度从 k+1 节点回到 1 个字面量）。
   - `Raw::SumCase` elaboration arm 改存**展开形态** typ：
     `typ: self.quote(&cxt.decl, cxt.lvl, &typ_val)`。该 arm 本来就要求
     `typ_val` 是 `Val::Sum`（index 查找），所以存进 decl 表的
     `SumCase.typ` 从此恒为 `Tm::Sum`。Enum 构造器 body（`elaboration.rs`
     `Decl::Enum` 合成的 `Raw::SumCase`）同被治愈。
2. **pretty 全量化（`pretty.rs`）**：新增 `is_nat_typ`（同时接受展开
   `Tm::Sum("Nat")` 与历史泄漏的引用形态 `Tm::Decl("Nat")`）；Nat 字面量
   特化与 `pretty_nat` 的链式游走都改用它。一般 arm 对非 `Tm::Sum` typ
   不再 `panic!`，降级渲染 `<typ>::#<index>(datas)`——hover/错误显示路径
   永不崩 server（与 `go_app_pruning` 越界降级同一哲学）。
3. **次级生产者（`mod.rs` `simpl_decl`）**：定义值本身是 `Val::Sum` 的
   表项（Nat/Boolean 等无参 sum）保留原值，不再替换成 `Val::Decl`。
   `Val::Sum` 是 WHNF 叶子、不会重展开，安全性不变；但 declb 下的
   `nat_succ_shape`/构造器求值从此产出 `typ: Val::Sum` 的 SumCase，
   不再经 quote 回灌 `Tm::Decl`。顺带修复了 declb 下 primop 的
   `is_nat_sum` 判定失灵（`nat_concrete` 等此前在 simpl decl 下悄悄
   退化为不归约）。
4. **投影降级（`mod.rs` eval `Frame::Obj`）**：`Val::SumCase` 的 typ 非
   `Val::Sum`（stuck meta/rigid 头）时降级为通用 stuck 投影
   `Val::Obj(a, name, [])`，删掉 `panic!("impossible")`。

**验证**：
- `tests/repro_sumcase_panic.rs` 两条回归：最小复现的 hover 成员列表现在
  渲染 `struct m(_prev: ModuleTree, a: UInt [8], x: UInt [8], _res:
  ModuleTree, _: Unit)`（无标注字段宽度恢复为字面量 `8`）；
  01-basics 全标识符 hover 无 panic、无降级占位。
- `pretty.rs` 新增单测：`Decl("Nat")` 引用形态的 succ 链照常打印数字；
  非 Sum typ 降级为 `T::#1(Nat)` 而非 panic。
- 全量测试与修复前基线一致：lib 49 个失败均为 L07–L12 旧课程既有失败
  （干净 HEAD 复核相同），L13 与全部集成套件（hover/emit/sim/completion…）
  除既有的 2 个 completion 失败外全绿，无新增失败。

