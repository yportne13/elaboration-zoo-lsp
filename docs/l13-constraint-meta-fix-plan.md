# 立项前置分析：约束 meta 的消费点参数化（方向 3）

> 状态：立项前置分析（2026-08-26）。
> 关联：`docs/l13-typeclass-instance-nat-param-bug.md` §修复方向 3、
> `docs/for-hdl-blocker.md`（for 循环阻塞，三次排查记录）。
> 结论先行：for 循环转绿没有第二个修复面——唯一路径是方向 3 的
> 「约束 meta 延迟解 / 消费点参数化」。本文件给出最小验证用例、
> 改动面清单、分步建议与风险。

## 1. 背景

两处已知缺陷最初表现为不同症状，本次深挖确认它们是**同一簇相互依赖的
约束 meta**，且**只能整体求解**：

| 症状 | 场景 | 现状 |
|---|---|---|
| `find unsolved meta with type ModuleTree/Type 0` | 类体内 `let _ = <调用>`、`let f = i => unit`、for 循环体 | 检查期诊断（master 基线可复现） |
| `lvl2ix: level N is out of scope … leaked into a quote` | 同上（更早触发时） | panic，消息可诊断 |
| `v_app: impossible apply U(0)` | 对余留 meta 做「oty 确定自解」后 | 运行期 panic（错解值已污染） |
| 复现 B：参数化 module 字段宽度退化 1 位 | module 宏 + `[w: Nat]` | HDL004 显式警告（静默已修） |

`docs/l13-typeclass-instance-nat-param-bug.md` §修复方向 3 的定义：
> 让约束 meta 的解能表达**消费点参数化**——例如 `MetaEntry::Solved` 支持
> Tm/延迟形态，或 class Phase B 组装字段 Tm 时对 `Tm::Meta(约束)` 做 Tm
> 展开（消费点 eval 时以自己的 env 构造实例应用的 spine）。

## 2. 已排除的路径（勿重复）

1. **def 尾部「oty 确定自解」**：把悬挂 meta 的 oty 当解——检查期诊断消失，
   但暴露错解值 `Val::U(0)`（Type 0）挂在 spine（`MetaEntry::Solved` 化一个
   类型级 meta 后仍被当函数应用）→ `v_app` panic。**净退化，已回退**。
2. **Phase A 逐 item 局部闭合**（item 检查后 solve_multi_trait + 自解）：
   无效——meta 不是单个悬挂，是**相互引用的一簇**（每个目标类型内仍含
   未解 meta），单点闭合条件永不满足。**已回退**。
3. **`let _ =`/lambda 转写形态择形**（for-arm 三种形态分别踩三类失败）：
   只改变触发路径，不改变系统缺陷。**已记录，勿再花时间**。
4. **无注解 Hole metaa 显式 pin**（保留在 `14c0805`）：只解决 Hole 推断层，
   够不到隐式参数簇。**保留，不属于本立项**。

## 3. 机制证据（最小复现链）

```typort
// A. 母版场景（无 for）
module uM {
    let a = UInt[8]
    let _ = whenEnd(unit)          // 或 let _ = unit / nat_add(0, 1)
    a := a
}
println(moduleTreeVL(uM.create.tree))
// B. for 场景（现成的 ignore 测试即验证器）
module forDemo {
    let a = UInt[8]
    for i in 0 until 4 {
        let x = UInt[8]
        x := a
    }
}
println(moduleTreeVL(forDemo.create.tree))
```

诊断现场（插桩定位）：

```
meta[33971] = Unsolved(
  Pi("bn" @ .. BindingName ..                      ← 记录 cxt.lvl=6，类型引用 bn 级
    Closure(..0, Let("_" @ 20835,
      AppPruning(Meta(MetaVar(33942)), [Some(Expl)]),   ← dependent 隐式参数
      App(Decl("change_mutable_default"), LiteralIntro("ModuleTree"), ...))))
meta[34024] = Unsolved(Pi("this" @ .. Sum("forDemo" ...), ... change_mutable_default ...))
no_metas 报告的第一个 Unsolved: cxt_lvl=6，span=(11783,11783,28)（宏展开恢复处）
```

- 来源：`change_mutable_default/get_global` 的**内建注册类型**经
  `string_to_global_type`（`cxt.rs:593-630`）——返回类型依赖首参；
- 隐式参数占位由 `fresh_meta`（`mod.rs:2148-2167`）建为
  `Tm::AppPruning(Meta(m), cxt.pruning)`；
- Phase A 的检查在 **bn 语境**（create 隐式参数），Phase B 的 create/tree
  在消费点重建（`build_class_chain_tm`/`maybe_prechecked_method_body`，
  `parser/mod.rs:2581`/`:2700`）——**创建点与消费点的 env 不同**；
- 该 meta 的求解锚点缺失：既无 trait 约束（`solve_multi_trait` 不覆盖），
  值检查对依赖返回又不 unify meta 本身（`check` 只解目标）。

## 4. 最小验证用例（作为方向 3 的验收门）

```
cargo test module_for_loop -- --ignored          # 期望：4 passed
cargo test L13_namespace::module_tests            # 期望：22 passed（回归）
```

另加两个手工用例（加进 module_tests 后在验收时摘掉 ignore）：正文 §3 的 A
（`let _ = whenEnd(unit)` / `let _ = unit`）；B 中的嵌套循环
（`module_for_loop_nested`）验证 `x_i_j` 命名与多级 meta 簇。

## 5. 改动面清单（按推荐顺序）

### 5.1 Phase B 组装对约束 meta 展开（改动小，先做）

- `src/L13_namespace/parser/mod.rs`
  - `build_class_chain_tm`（`:2581`）：注解/值复用 `Raw::Tm` 前，对含
    `Tm::Meta(约束)` 的 prechecked term **按消费点展开**（或暂不复用、保留
    raw 重检查——但 raw 重检查目前仍会触发缺陷，需要配合 5.3）；
  - `maybe_prechecked_method_body`（`:2700`）：同上，方法链复用条件
    （`tm_is_closed`）扩展为「无未解 meta」。
- 风险：低-中。局部、parser 侧；破坏面 = 类展开的行为差异；
  回归由 §4 验收门覆盖。

### 5.2 `MetaEntry::Solved` 支持延迟/Tm 形态（架构级，单独一步）

- `src/L13_namespace/mod.rs`：`MetaEntry` 定义（`:302`）、`new_meta`
  （`:2148`）、`lookup_meta`（`:2166`）、`val_no_metas` 的 quote 分支
  （`:2185-2193` 的 `NM_QUOTE_LVL`——自解实验的 panic 即该路径）。
- `src/L13_namespace/elaboration.rs`：solve 后 meta 消费点（no_metas 遍历、
  `check` 的 `Raw::Tm` 分支 `:624-637`、`insert_go` 的隐式插入 `:178-230`）。
- `src/L13_namespace/unification.rs`：`solve_trait` Phase 1/2 实例化后
  （现有「re-eval 修复」即 `l13-typeclass-instance-nat-param-bug.md` §2），
  把延迟形态在消费点 eval——本路线与「Phase 2 后重新 eval」共用同一钩子。
- 风险：**高**。影响 quote/eval/meta 全链路；**必须与 5.1 分批验收**。

### 5.3 内建 dependent 类型注册（可选加固）

- `src/L13_namespace/cxt.rs`：`string_to_global_type` 三条内建
  （`create_global/change_mutable/change_mutable_default/get_global`，
  `:593-630`）的注册类型——考虑在检查期直接对依赖泛型做**求值优先**，
  减少运行期 Dependent spine 的生成频率。
- 风险：中（改内建签名影响面大，需全量测试；优先 5.1/5.2，本项后置）。

## 6. 建议路线

1. **5.1 先落地**（低风险、immediate 价值：即使不完全转绿，也能把
   for 测试的错误从「meta 簇」推进为「逐个可诊断」）；
2. 提交并跑 §4 验收门；
3. **5.2 立项为独立变更**（架构级、评估对 wasm/LSP 缓存的影响；
   与「实例 Nat 参数冻结 re-eval 修复」共用钩子，压缩实现成本）；
4. 5.3 待 5.2 稳定后评估。

## 7. 完成定义（DoD）

- [ ] `cargo test module_for_loop -- --ignored` 4/4 通过；
- [ ] `cargo test L13_namespace::module_tests` 22/22（不回归）；
- [ ] §3-A 手写用例不再报 meta/lvl2ix/v_app 三类错误；
- [ ] 相关文档撤回「阻塞」表述（for-hdl-blocker.md 改「已解决」）。
