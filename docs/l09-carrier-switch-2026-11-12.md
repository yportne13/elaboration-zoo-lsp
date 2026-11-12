# L09 参考版载体切换：把顶层声明移出类型检查上下文（2026-11-12/13）

> 触发：`docs/l09-perf-gap-2026-11-12.md` 的定位结论——L09 参考版相对 L07/L08
> 的慢不是"少了一行优化"，而是 L09 定基把顶层 def/enum/构造子做成了 **Cxt
> 上下文条目**（env/lvl/locals/pruning 随声明数 D 增长），导致：
> ①每次引用老全局 `eval` 在 Rc 单链 env 上线性 `iter().nth` → O(D)；
> ②`fresh_meta` 无条件 `close_ty(&cxt.locals, …)` + 求值 D 长 Let 链 → 每次 O(D²)。
> 用户决策：「没有可取之处就照搬 L07/L08 的设计」——**采纳 L08 的核心载体设计**
> （顶层声明不进上下文、全局 O(1) 取用），但保留 L09 的宇宙语义/parser/显示/错误/
> 测试面（不整层复制 L08 引擎，避免重做宇宙增量；用户批准方案 A 的实现层细化）。
>
> - HEAD `ae8ccb6c`；改动仅 `src/L09_mltt/{mod,cxt,elaboration,pretty,struct_eq}.rs` + 本层 README
> - 改动规模 **+260/−121 行**（对比整层重定基 ~5k 行）；`bump_spine_iter`（孪生）与 tests 未动
> - 语义门禁：`l09_fast_parity` **46/46**、`l09_blackbox` **82/82**、lib **17/17**、`--validate` 与基线完全一致

## 1. 改动内容

### 1.1 载体（`mod.rs`）

| 项 | 切换前 | 切换后 |
|---|---|---|
| 顶层值的家 | `Cxt.env` 的 define 槽 + `Infer.global` | 只在 `Infer.global`（键 = `global_idx`，O(1) 直查） |
| 顶层声明对 Cxt 的影响 | `env.prepend` + `lvl+1` + `Locals::Define` + `pruning.prepend(None)` | **无**（Cxt 四条链只随局部 binder 增长） |
| 全局引用项形 | `Tm::Var(Ix(小下标))`（经 env 槽） | `Tm::Global(Ix(id + 1919810))`（哨兵直查） |
| 递归检查期自身占位 | `Tm::Var(Ix(id + 1919810))`（fake_bind 哨兵） | 保持 `Tm::Var(哨兵)`，用 `in_progress_globals` 集合与已定名引用区分 |
| 中性全局视图 | 只中和哨兵（递归占位） | 只中和 `Var(哨兵)`；`Global` 照常展开（与旧版 env 槽语义逐点一致） |
| `benck_check_nf` 末值 | `cxt.env.head()` | `Infer.global[末 def 的 id]` |

- `define_global` 现在只做三件事：`in_progress_globals.remove`、`global.insert(id, 值)`、
  `global_names.insert(名, (id+BASE, 类型))`（+ `shadow_local` 内建撞名处理）。
- `eval` 的 Var 臂**先判哨兵**再扫 env；局部 de Bruijn 下标照旧走 env（长度 = 局部深度）。
- `Tm` 新增 `Global(Ix)` 变体（+ 配套 `eval`/`quote` 不涉及/`tm_size_ref`/`pretty`/`struct_eq`）。
- `pretty_tm_g(names, global_names, tm)`：错误文案对**未 quote 的项**做显示时反查全局名
  （否则 `p.zzz` 会显示成 `recursive_5`，与孪生错误正文分叉；普通显示路径行为不变）。

### 1.2 语义等价的三个关键点

1. **值和类型事实不变**：全局值仍是检查完覆盖的终值；类型事实仍在
   `src_names`（局部）/`global_names`（全局）两张表。
2. **哨兵 vs 定名的两分法复刻旧语义**：旧版只有 fake_bind 自身引用是哨兵
   （中性视图中和），其余全局引用走 env 槽（照常展开）。新版用 `Tm::Global`
   vs `Tm::Var(哨兵)` 精确复刻该二分——这是 parity/黑盒错误文案能逐字节对齐的原因。
3. **显示/错误面**：names 列表与局部层级同步收缩，本地变量位次不变；`recursive_N`
   仍只用于递归占位；错误里 `find/expected` 的 quote 路径不受影响。

## 2. A/B 验收（同一台机、HEAD↔NEW 交替 3 轮取 min；`target/perf09/baseline/` 原始日志）

| 场景（`basic`，min ms） | HEAD | NEW | 变化 |
|---|---:|---:|---:|
| L09 common（6 文件，L07 风格代码） | 112.691 | **96.544** | 1.17×（−14.3%） |
| L09 自有真实语料（34 文件） | 1777.941 | **11.371** | **156.4×** |
| Eq 证明阶梯单文件（801 decls） | 1691.850 | **3.567** | **474.3×**（L07 2.497 → 差距 686×→**1.43×**） |
| strchain k=11（4096 defs） | 61.171 | **9.121** | 6.71×（L08 8.6 → 1.06×） |
| struct k=10（2048 decls） | 48.07* | **6.50** | ~7.4×（L08 5.60 → 1.16×） |
| match k=11 | 0.120 | **0.105** | 1.14× |
| 控制层 L07/L08/L10（源码未动） | — | — | common +1.7%/−1.2%/−1.1%，单文件 ≤±0.6% |

`*` struct 的 HEAD 值取今日跨层基准同窗口数据（基线脚本未跑该 workload）。

- 测试：HEAD 46/82/17 → NEW 46/82/17，全绿。
- validate：L09 common 6 PASS/0 SKIP、L09 自有语料 34 PASS/0 SKIP，与基线逐项一致；
  跨层对照（L09 语料喂 L07/L08/L10）PASS/SKIP 数不变。
- 审计噪声：首轮 AFTER 单跑曾出现控制层 +17~24% 的瞬时负载污染，已用 HEAD↔NEW
  交错 3 轮复测收敛（≤±1.7%），单轮数据保留在 `after/logs/` 附录 A。

## 3. 仍存差距（非量级问题，后续可选）

载体切换后 L09 ≈ L07/L08 的 1.0–1.7×，剩余常数项来源已定位但未在本轮处理：

| 缺口 | 现象 | 锚点/原因 | 可选修法 |
|---|---|---|---|
| common 1.43× | L07 风格 798-decl 代码 96.5 vs 65 | L09 每份类型注解都走完整 `check_universe`（infer + insert + 宇宙层级判定）；L07/L08 有结构预检 `ty_precheck` 捷径 | 给明显结构化的注解加快速宇宙判定（不动语义） |
| church 1.7×、enum 1.7× | β/构造子路径的常数 | `Tm::Lam/Pi` 体仍是 `Box<Tm>`（L07/L08 已 `Rc`；借用版 `eval_ref` 建 Closure 时深拷） | 同步 85b9c87e 的 Tm 侧 Rc 化（G3） |
| strchain 常数 | 已 1.06× L08 | 内建 `string_concat` 走普通 β + `Tm::Prim`（无 PrimFunc/eta） | 可选移植 PrimFunc（收益小） |

这些都不改变结论：**L09 参考版已回到 L07/L08 性能量级**，且保留 L09 的
「无名字键 decl 表、值表按下标存」的简化载体与全部宇宙语义。

## 4. 回退与复验

- 回退：`git checkout -- src/L09_mltt/{mod,cxt,elaboration,pretty,struct_eq}.rs src/L09_mltt/README.md`
  （切换前 HEAD 版本同时导出在 `target/perf09/baseline/l09_*_head.rs`）。
- 复验命令：
  ```powershell
  cargo test --release --test l09_fast_parity --test l09_blackbox
  cargo test --release --lib L09_mltt::
  target/release/realbench.exe --layer L09 --corpus tools/bench_corpus/L09 --validate
  target/release/realbench.exe --layer L09 --corpus tools/bench_corpus/L09 --rounds 3 --only basic
  target/release/realbench.exe --layer L09 --corpus tools/bench_corpus/common --rounds 3 --only basic
  target/release/l09bench.exe --workload strchain --max-k 11 --rounds 3 --only basic
  ```
- A/B 脚本与原始数据：`target/perf09/baseline/{run_*.ps1,ab_recheck/,after/}`；
  汇总报告 `target/perf09/baseline/after/ab_compare.md`、`.deltawork/perf09/baseline.md` §13。

## 5. 相关文档

- 差距定位（历史）：[l09-perf-gap-2026-11-12.md](l09-perf-gap-2026-11-12.md)（§7 记录本轮落地）
- 跨层基准（切换前历史值）：[bench-crosslayer-ref-2026-11-12.md](bench-crosslayer-ref-2026-11-12.md)
- 实现对应物：`src/L09_mltt/README.md` §2（载体）、§4（与孪生对齐）、§5（新基准表）
