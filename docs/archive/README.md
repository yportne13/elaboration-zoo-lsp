# `docs/archive/` —— 历史评审归档区

本目录存放**已结束的历史评审轮次**（2026-09 至 2026-11）的完整报告快照。归档的目的是
保留当时的结论、证据链与未采纳项，供回溯；**不代表当前代码状态**。

## 归档规则

1. **只读**：本目录内容为历史快照，**不再更新、不再补充结论**。若发现路径/链接失效，
   只做机械性链接修正（如 `docs/review-*` → `docs/archive/review-*`），不改实质内容。
2. **新评审不放这里**：正在进行或新发起的评审写到仓库级 `docs/<当前评审目录>/`（如
   `docs/optimal-design/`、`docs/compare-*/`）；该轮评审结束、结论已被上游文档吸收后，
   再整体 `git mv` 迁入本目录。设计类结论优先落在 `docs/optimal-design/`。
3. **引用方式**：其他文档指向归档请用绝对仓库路径 `docs/archive/review-*/...`；
   归档内部文件互相引用保持相对链接（整树移动后 sibling 相对关系不变，无需改写）。
4. **迁移纪律**：迁移用 `git mv`（保留文件历史），迁入后跑一次
   `grep -rn "docs/review-" --include=*.md` 修引用，迁移记录写入 `docs/optimal-design/`
   的清理报告。归档不等于删除：结论页（`FINAL.md`）与分报告都应保留。

## 目录清单

| 目录 | 文件数 | 内容 | 时点 |
|---|---:|---|---|
| `review-2026-10-11/` | 11 | 全仓多维评审总审计（十轮、~330 项实验；r01–r10 分报告 + `FINAL.md`） | 2026-10-11 |
| `review-cont/` | 18 | L01–L13 跨章节承接连续性评审（续评，a1–a6 多轮 + `FINAL.md`） | 2026-09 |
| `review-continuity/` | 16 | L01–L13 跨章节承接连续性评审（另一轮，a1–a7 + `BRIEF.md`/`FINAL.md`） | 2026-09 |
| `review-l01l12/` | 23 | L01–L12 多轮系统评审（a1–a5、cross + `BRIEF.md`/`FINAL.md`） | 2026-09 |
| `review-l07-hardening-2026-11-08/` | 4 | L07 2026-11 加固轮（P1–P11）的独立 review 终报 + 3 份 findings | 2026-11-08 |
| `review-l07l12/` | 11 | 显式替换（σ）重构后 L07–L12 多维并行评审（d1–d6 + `BRIEF.md`/`FINAL.md`） | 2026-09-15 |
| `review-l13/` | 22 | L13 生产层 + 共享基础设施多轮评审（a1–a7、交叉审计 + `BRIEF.md`/`BASELINE.md`/`LEAD-probes.md`/`FINAL.md`） | 2026-09 |

合计 7 个目录 / 105 个文件。

## 迁移记录

- **2026-11-09（P1 基线清理，分支 `p0-p1-baseline-cleanup`）**：7 个目录自 `docs/review-*`
  `git mv` 至 `docs/archive/review-*`；仓库内 47 个文档的 103 处旧路径引用改为
  `docs/archive/review-*`（详单与验证见 `docs/optimal-design/P1-docs-archive-report.md`）。
