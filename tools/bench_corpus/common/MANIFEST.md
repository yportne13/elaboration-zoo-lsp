# common/ — L07–L13 跨层「严格同一文件」语料

用途：在**完全相同的源文件**上横比 L07–L13 的参考版性能（`docs/bench-crosslayer-ref-2026-11-11.md`）。

## 来源与筛选

从 `tools/bench_corpus/L07/` 的 27 个文件中筛选「只用 L07 核心语言子集、且 L07–L13 全部可跑」的 6 个：

| 文件 | 来源 | decls | 说明 |
|---|---|---:|---|
| ex_block_comments.typort | L07 抽取 | 3 | 块注释词法（最小用例） |
| ex_even_odd.typort | L07 抽取 | 6 | 互递归 Nat→Bool |
| ex_line_comments.typort | L07 抽取 | 3 | 行注释词法（最小用例） |
| ladder_l07_small.typort | L07 阶梯 | 48 | 解释器前端流水线（50 decls 档） |
| ladder_l07_medium.typort | L07 阶梯 | 198 | 同上（200 decls 档） |
| ladder_l07_large.typort | L07 阶梯 | 798 | 同上（800 decls 档） |

筛选过程：把 L07 全部 27 个文件复制到本目录，逐层跑 `realbench --layer L0X --corpus tools/bench_corpus/common --validate`（L13 用 `l13bench --file ... --with-prelude none`），取 7 层都 PASS 的交集。被淘汰的主因是层间语言面演进：

- L09 起 `U` 改为 `Type N`（`U` 不再在 scope）；
- L12 起对 universe 注解更严格（大量 L07 风格 `enum`/`def` 报 `expected universe`/`can't unify`）；
- L10 参考版与孪生版在部分 GADT/Vec 程序上 nf 不一致（本目录要求闸门通过）。

## 验证结果

```text
realbench --layer L07..L12 --corpus tools/bench_corpus/common --validate  → pass=6, skip=0（六层一致）
l13bench --file <每个文件> --with-prelude none                             → 6/6 通过（nf 与参考版一致）
```

## 注意

- L11/L12 的 `basic` 是全流程 `run`（含 parse+pretty+stdout），其余层是 parse 外 `bench_check_nf` 口径；本目录文件 nf 最大 1406 节点、源码最大 37 KB，口径差估计 <5%。
- 本目录只服务跨层横比，不替代各层自己的真实语料（`tools/bench_corpus/L0X/`）。
