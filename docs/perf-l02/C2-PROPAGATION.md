# C2「尾任务寄存器化」全链下沉规程（L02–L13）

> Lead 制定。**已验证原型**：`docs/perf-l02/raw/exp9-c2.patch`（L02，3 站点），
> 实测 church **−6.42/−5.77%**、conv **−7.42/−5.70%**，独立复核自跑
> **−6.53/−5.60/−7.71/−6.45%**，符号检验 p ≤ 7e-5（见 `docs/perf-l02/03-verification.md`）。
> 本轮把它下沉到 **L02–L13 全链**（该模式在 12 层的 `eval_iter` 里都有）。

## 1. 背景：为什么有效

`eval_iter` 是双栈迭代求值的主循环；`work: Vec<W>` 是显式任务栈（L02 实测
`size_of::<W>() == 40B`）。有些臂把任务 `work.push(...)` 之后**立刻**回到循环头，
于是该任务在下一轮**必被 pop**——这一 push/pop 对是纯浪费：
40 B store + 40 B load + 两次 `Vec` len 更新 + 一次 jump-table 分发。

改法：加一个循环局部寄存器 `cur: Option<W<'a>>`；循环头先取 `cur`，空了再
`work.pop()`；把这些"必被立刻弹出"的 push 改成 `cur = Some(...)`。
**语义严格等价**：LIFO 顺序完全不变（`cur` 在下一轮被最先取走，与"刚 push 上去、
下一轮被 pop"是同一件事）。

## 2. 循环头改写（`W` 的 lifetime 名以**本文件实际签名**为准）

```diff
-    while let Some(w) = work.pop() {
+    let mut cur: Option<W<'a>> = None;
+    loop {
+        let w = match cur.take().or_else(|| work.pop()) {
+            Some(w) => w,
+            None => break,
+        };
         match w {
```

## 3. 转换条件：一条 `work.push` 只有同时满足 (a)(b)(c) 才可改

- **(a)** 该 push 之后、控制回到**主循环头**之前，没有其它 `work.push`；
- **(b)** 该 push 之后、控制回到主循环头之前，没有 `work.pop`（包括 `work.pop()`）；
- **(c)** 控制确实回到主循环头：该 `match` 臂结束，或内层 `loop { … break; }` 的
  `break` 落回主循环。

等价说法：**它是这条控制路径上最后一个 `work.push`**。

## 4. 易错点（必须逐站点读代码，**不要**用正则批量替换）

1. **同臂多个 push 只改最后一个**：
   ```rust
   work.push(W::PiBody(name, cod, env));
   work.push(W::Tm(dom, env));          // ← 只有这一行可改
   ```
   `PiBody` 必须留在栈上，否则执行顺序颠倒。
2. 条件 push 后面还有 push 时它不是最后一个：
   ```rust
   if heads > 0 { work.push(W::ChainWrap(heads)); }   // ← 不改
   work.push(W::Tm(base, env));                        // ← 这个才是最后一个
   ```
3. 内层下钻环里 `work.push(W::Tm(base, env)); break;` → **可改**（break 回主循环头）。
4. push 之后还有**不碰 `work`** 的语句（如 `vals.push(...)`）时，理论上仍可改
   （只要没有 `work.push`/`work.pop`），但为降低风险：
   **优先只改"push 之后紧接块结束 / `break`"的站点**；若你要改带非 work 语句的站点，
   必须在 justification 里单独论证。
5. **不得**改动任何其它逻辑、注释风格、格式——diff 要最小。

## 5. 每层必须交付的验证

| 项 | 命令 | 要求 |
|---|---|---|
| 层单测 | `cargo test --lib <层模块名>`（如 `L03_holes` … `L13_namespace`） | 全绿 |
| 黑盒/parity | `cargo test --test l0X_blackbox` / `_v2` / `_v3` / `l0X_fast_parity`（按实际存在的文件） | 全绿 |
| bench 冒烟 | `cargo build --release --bin l0Xbench && ./target/release/l0Xbench --max-k 11 --rounds 3 --only fast`（l13bench 建议 `--workload church`） | 内置断言全过，**结果/节点数与改动前一致**（只有时间不同） |
| 站点清单 | 报告里逐站点给 before/after 行号 + 一行等价性理由 | 完整 |

## 6. 纪律

- 只改你写范围内的文件；**`src/L02_tyck/**` 由 Lead 负责**，不要碰其他层。
- **bench 运行必须持锁**：`mkdir docs/perf-l02/.benchlock`（释放
  `rm -f docs/perf-l02/.benchlock/pid; rmdir docs/perf-l02/.benchlock`）；编译不必持锁。
  拿不到锁就 sleep 5–10 s 重试；pid 已死可接管。
- 每层 `git diff --stat` 应该只有 1 个文件；不要顺手格式化。
- 不需要做 A/B（性能 A/B 由 Lead 统一安排），只要正确性 + 冒烟。
