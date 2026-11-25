# L13 架构级升级（语义前提层）：结构快路径回灌（2026-11-24）

> 用户要求：「语义前提层那套架构级的变动也要落到 L13 上」。
> 本轮落地的是 **FINAL §4 #2 的 `struct_eq` 结构快路径**（B 档机制对齐），
> 精化载体 σ 与名字世界两项按 `docs/wip/README.md` 的 5 轮失败记录**不做**（理由见 §4）。
> 工作分支 `feat/l13-sigma-carrier`（worktree `F:/projects/hermes/ezl-l13-sigma-arch`），
> **未合入 master**，master 上的 A 档改动保持不动。

## 1 做了什么

| # | 项 | 文件 | 说明 |
|---|---|---|---|
| 1 | 新建 `struct_eq` 模块（403 行） | `src/L13_namespace/struct_eq.rs` | 按 L13 的 `Rc<Val>` 值表示**重写**，不是照抄 L07：无 `VSub` 臂、无 `Prim` 臂；新增 `Nat(u64)` / `Call` / `SumCase{is_trait,index}` 三条臂；`U` 变体改比层级；`Pi`/`Sum` 按 L13 真实字段；`PatternDetail` 用 `PartialEq`；`Tm` 覆盖 `Call`/`OpCall`/`AppPruning` |
| 2 | 新增 `InlineStack`（内联容量 16 的任务栈） | `src/L13_namespace/mod.rs` | L07–L09 都有、L13 独缺；结构比较与深值遍历的浅路径零堆分配 |
| 3 | `unify` 的 `(Match, Match)` 臂接入快路径 | `src/L13_namespace/unification.rs` | **先试结构相等**（scrutinee + 捕获 env + 模式 + 分支体），命中即 `Ok(())`；只有快路径失效、真要逐分支重求值时**才**计入 64 次 `MATCH_CMP_BUDGET`（L07 2026-11-08 口径） |
| 4 | 新增回归钉子（2 例） | `tests/l13_struct_eq_fastpath.rs` | 钉住：同一递归函数的卡住 match 自比较能证；相等值合一成功、不等值必须失败 |

## 2 为什么这是「语义前提层」的改动

回报的是本层的**判定能力**，不是性能：

- 改前：`(Match, Match)` 自比较只能逐分支重求值，每次重求值又展开一层新的卡住 match，
  fresh rigid 层级递增、**永不结构收敛**；唯一兜底是 64 次预算，耗尽后记 `UnifyKind::Fuel`
  并报 `can't unify`。⇒ **L07 能证的等式，L13 证不出。**
- 改后：结构相同直接判等，预算只用于真正需要重求值的情形。判定从「保守失败」回到「可证」。

这正是 FINAL §4 #2 记录的分叉，也是 `02-unify.md` 标为 **E3** 的那一条。

## 3 验证

| 项 | 命令 | 结果 |
|---|---|---|
| 层内 lib | `cargo test --release --lib L13_namespace::` | **622 passed / 0 failed / 13 ignored**（与 master 基线一致） |
| 新钉子 | `cargo test --release --test l13_struct_eq_fastpath` | **2 passed** |

## 4 没有做的两项，以及为什么

| 项 | 决策 | 依据 |
|---|---|---|
| **精化载体 σ**（换掉 `update_cxt`） | **不做** | `docs/wip/README.md` 记录了 5 轮完整尝试：语义面基本正确、GADT 覆盖修复完成，但留下 prelude 加载 21s（基线 9.3s 口径仍在 28× 纯 elaboration）、12k 层 meta 解链栈溢出、`FRCS_MEMO` 长跑内存到 GB 级、孪生镜像未完成。第五轮补丁 `git apply --check` 对本 HEAD **已不适用**（基准提交是 2026-08-28 `3957f3bf`，之后 L13 改了 3.4 万行），等于按现有架构重做一遍——不是「落地」，是「重写核心 + 重新踩已知的 4 个坑」。 |
| **名字世界换回 decl 表** | **不做** | 同一份审计把 L13 的 package/import 全限定键判为**产品必需面**（LSP hover/goto/completion、HDL 模块树全部依赖它）；换回裸键会打断 LSP 产品路径，属 C 档重定基。`l13-rebase-decision-2026-11-17` 已明确否决。 |

## 5 合入建议

本分支可以独立验收后合并：改动**只增不减**（新建 1 个模块 + 1 个辅助结构 + 1 处调用 + 2 个测试），
不触碰精化载体、名字世界、值表示。若不想合入，master 的 A 档改动不受影响。

## 6 如果确实要推进 σ（下一步的实际起点）

不要拿 round5 补丁直接 apply。按 `docs/wip/README.md` 的「接续建议」从 **round 6 第 1 项**开始：
孪生编译器的逐列精化镜像（`Arm` 加 σ 字段、6 个构造点带精化、探测点 `wrap_sub`），
因为那是当前**唯一已知的 REF/TWIN 语义分歧**；在此之前任何覆盖索引类型 match 的 parity 都会分叉。
