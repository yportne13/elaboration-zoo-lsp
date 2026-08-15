# 执行计划（已获用户确认）

## 1. 记录分析文档
- 写 `docs/module-redesign-analysis.md`：现状机制、实测实验结论（check 求值 ~3 次/restore 抹平/task2 35x 退化根因）、问题清单、优化方案（modulePush/modulePop/mkInstanceIfParent + 单 arm 宏 + 去特例 + when 去重）、task2 教训对照、验证计划。

## 2. module 优化实现（主工作区，按已确认方案）
- hdl-core.typort：modulePush/modulePop/mkInstanceIfParent + createPortExpr 支持 Bool
- hdl-macros.typort：module 宏单 arm（cd 可选 + 宽度可选）、Expr 宏删 `$m.create` 特例、when arm 去重
- 新增 module_tests.rs；性能基准对比；全量 `cargo test --lib L13` 回归

## 3. git worktree + 子 agent 并行三任务
- **wt-pretty**：pretty 优化——`foo({xxx}, xx, xxx)` → `foo[xxx](xx, xxx)`（隐参应用方括号显示）
- **wt-hover**：tuple hover 按元素定位（鼠标指向 tuple 的哪个元素显示哪个元素的 hover）
- **wt-calc**：Lean4 calc / Agda reasoning 链式证明机制——子 agent 先设计使用方式，交用户确认后再实现

三个任务各自独立分支 + worktree，子 agent 并行执行，完成后汇报结果。