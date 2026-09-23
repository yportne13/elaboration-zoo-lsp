# L13 性能深挖第三轮（2026-09-23 加场）：未落地补丁与证伪存档

本目录保存 2026-09-23 加场轮（见 `docs/perf-l13-round-2026-09-23b.md`）
**未落地**的补丁：实现与验证都已完成，因收益未达门槛（<3%）或符号
不一致而按纪律回退。全部补丁对干净 HEAD（9dbf99f）+ 已落地的本轮
三项改动可独立应用（`git apply --check` 验证过）。

## 产物

- `l13-matchidx-backlog2.patch`（eval.rs +164 / force.rs +4）：宽表
  match 的 **per-node 懒建分派索引**（backlog #2 原样）。实现健全、
  语义逐点等价、门禁全绿、内存中性，A/B 实测 **−0.2~3.4%**（低噪声
  窗 8 行中 7 行符号一致，默认口径 ≤1.4%），未达 <3% 门槛。**证伪
  结论**：wide_enum k=11 的主成本不在值层分派（0.4-1.4%），在编译期
  覆盖检查（已由本轮 `compiler.rs` CoversIndex 单独落地）。保留本
  补丁供"分派占比更高的负载形态出现"时复用。
- `p4a-item1-app-clone-lazy.patch`（machine.rs）：`infer_expr` /
  `infer_expr_pm` 应用臂 Raw 双深克隆惰性化（tuple_head 免克隆 +
  clone 移进非 Π 头分支）。A/B：prelude-core fast **+3.1%** / fast_ss
  −1.7%（符号不一致）⇒ 回退。建议静窗重跑后再定（prelude-hdl 方向
  一致轻微为正）。
- `s8-scratch-reuse.patch`（quote.rs / eval.rs / force.rs，294 行）：
  size-32 草稿栈复用（帧内复用形态 + LIFO TLS 池形态）。实测两形态
  **0% / −0.02%**（l06l13mem 计数不动）⇒ 证伪。教训：S3 的逐点栈
  归因（quote/force/eval CallAsm/export 六站点）在官方计数口径下
  不复现——8269 个 size-32 首块另有出处；下轮先移植 `l07whoalloc`
  的分配点回溯再定池化目标。
- `s7-task2-compact-casesmap.patch`（compact.rs +19）：压实期共享
  cases 切片去重（`Copier::casesmap`，键=旧切片指针+长度）。语义
  中性、门禁绿，但实测**零命中**（cases 切片按节点新分配，一份切片
  天然单引用者；仅 `machine.rs:4589` 的 splice 复用形态可能共享，
  现有负载未触达）⇒ 不落地，作"防退化护栏"备查。

## 相关已落地项（不在此目录）

- `compiler.rs` 覆盖检查索引化（CoversIndex，wide_enum k=11 −89.8%）
- `mod.rs` Tm/Val 迭代析构漏字段修复（27 处 release_owned，
  wide11 每轮泄漏 2.69GB→2.36MB）
- `src/bin/l06l13mem.rs` TRACE≤32 重入死锁修复

证据日志（A/B raw、探针输出、OS 峰值）留在 `target/tmp/`（gitignored，
可再生产物）。
