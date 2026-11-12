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
> - HEAD `ae8ccb6c`；**第一批（2026-11-12）**：载体切换，改
>   `src/L09_mltt/{mod,cxt,elaboration,pretty,struct_eq}.rs`（+260/−121 行）；
>   **第二批（2026-11-13）**：从 L08 继承 G3 `Tm::Lam/Pi` 体 Rc 与重定义报错，
>   改 `mod.rs/cxt.rs/elaboration.rs/unification.rs/syntax.rs/struct_eq.rs/
>   bump_spine_iter/{machine,entry}.rs` + `tests/l09_blackbox.rs`。
>   两批均不整层复制 L08（保留宇宙/parser/显示/错误/测试面）。
> - 语义门禁（最终）：`l09_fast_parity` **46/46**、`l09_blackbox` **82/82**、
>   lib **17/17**、`--validate` 与基线逐项一致（L09 common 6/0、自有语料 34/0）。

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

## 3. 第一批后的剩余差距（历史记录；第二批已关闭大部分）

载体切换（第一批）后 L09 ≈ L07/L08 的 1.0–1.7×。下表是当时的错误/待定归因，
**保留为诊断记录**：其中 common 1.43× 当时猜「ty_precheck 快路径缺失」，第二批
实测证明主因是 `Tm::Lam/Pi` 体仍是 `Box`（G3）——改 Rc 后 common 直接到 1.01×。

| 缺口 | 第一批现象 | 当时的（部分错误）原因假设 | 第二批结论 |
|---|---|---|---|
| common 1.43× | 96.5 vs L07 65 | 猜 check_universe 全推断/ty_precheck 缺失 | **G3（Tm Box 深拷）为主因**，Rc 化后 1.01× |
| church 1.7×、enum 1.7× | β/构造子常数 | `Tm::Lam/Pi` 体 `Box`（G3） | G3 落地：church 0.95×、enum 1.33× |
| strchain 1.06× L08 | 内建走普通 β | PrimFunc/eta（G4） | 判定**不合入**（理由见 §6） |

## 4. 回退与复验

- 回退：`git checkout -- src/L09_mltt/ src/L09_mltt/README.md tests/l09_blackbox.rs`
  （第一批切换前 HEAD 版本同时导出在 `target/perf09/baseline/l09_*_head.rs`；
  第二批前的中间版本在 git 历史 `568c65c5`。）
- 复验命令：
  ```powershell
  cargo test --release --test l09_fast_parity --test l09_blackbox
  cargo test --release --lib L09_mltt::
  target/release/realbench.exe --layer L09 --corpus tools/bench_corpus/L09 --validate
  target/release/realbench.exe --layer L09 --corpus tools/bench_corpus/L09 --rounds 3 --only basic
  target/release/realbench.exe --layer L09 --corpus tools/bench_corpus/common --rounds 3 --only basic
  target/release/l09bench.exe --workload strchain --max-k 11 --rounds 3 --only basic
  ```
- A/B 脚本与原始数据：`target/perf09/baseline/{run_*.ps1,ab_recheck/,ab_recheck2/,after/,after2/}`；
  最终报告 `target/perf09/baseline/after2/ab_compare.md`、
  `target/perf09/baseline/ab_recheck2/ab_recheck.md`、`.deltawork/perf09/baseline.md` §13/§14。

## 5. 相关文档

- 差距定位（历史）：[l09-perf-gap-2026-11-12.md](l09-perf-gap-2026-11-12.md)（§7 记录落地）
- 跨层基准（切换前历史值）：[bench-crosslayer-ref-2026-11-12.md](bench-crosslayer-ref-2026-11-12.md)
- 从 L08 继承的侦察与取舍：`.deltawork/perf09/l08-inherit-recon.md`
- 实现对应物：`src/L09_mltt/README.md` §2（载体）、§4（与孪生对齐 + G3）、§5（新基准表）

## 6. 第二批（2026-11-13）：从 L08 继承 G3 与重定义检查

用户口径：「项目最初目的就是下一章节继承上一章节然后添加新特性……该从 L08
合过来的东西就合入吧」。按 `l08-inherit-recon.md` 的逐项判定，第二批合入两项、
明确不合入三项：

### 6.1 合入：G3 `Tm::Lam/Pi` 体 Rc（性能主项）

- `Tm::Lam` 体 `Box<Tm>`→`Rc<Tm>`；`Tm::Pi` 域/余域 `Box<Ty>`→`Rc<Ty>`
  （与 L07/L08 表示一致）。同步 eval / `eval_ref`（建 `Closure` 由深拷变
  `Rc::clone`）/ quote_arm / `lams_go` / `tm_size_ref` / struct_eq / `close_ty` /
  `Cxt::new` 内建 / 孪生 `CTm` 导出。
- 语义零变化（parity/黑盒/validate 全绿）；增益：relative to 第一批
  common −30.5%、L09 自有语料 −19.8%、Eq 阶梯单文件 −16.2%。

### 6.2 合入：重定义报错（L07/L08/L13 语义）

- 顶层 `def`/`enum` 重名（含撞 `Cxt::new` 内建、撞构造子裸名）→
  `redefine {名}`；顺序 = 先检查类型、后查重定义（与 L07/L08/L13 同序）。
  参考版与孪生同轮同步（twin 的 `prime_round` 把内建注册在 `global_names`，
  同表判定）。
- `tests/l09_blackbox.rs` 的 `bb_redefinition_silent_overwrite` 翻面为
  `bb_redefinition_rejected`（5 个反向用例：同名 def / 撞 enum / 撞构造子裸名 /
  撞内建 String / enum 撞先前 def）；README §1/§6 同步。

### 6.3 不合入（判定与证据）

| 候选项 | 判定 | 证据/理由 |
|---|---|---|
| B `ty_precheck`（L08 类型注解预检） | **不合（性能项）** | L08 `ty_precheck`（elab:150-183）是零副作用**诊断预检**，`check_ty` 预检后仍完整 `check`——不存在"跳过推断的快路径"；common 1.43× 的第二批归因已证实是 G3，与预检无关。仅可作 P3 诊断移植（不宣称性能收益） |
| C PrimFunc/eta（L08 builtin 机制） | **不合** | `eta` 在 L08 参考版是只写不读的死字段（真正生效的是 `prim_names` 的 quote η 展开）；L09 载体无名字键 decl 表/全局层级值表，移植需新增 `Val::Prim(name, spine)` + registry + prim_reduce（8+ 文件、20+ 匹配臂、翻 golden），并推翻 A4-R2 §2-2「Prim 无 spine 故无 fuel 宿主」论证；而 strchain 已 1.15× L07 / 1.06× L08，主体是 O(n²) 字符串拷贝 |
| E L08 builtin/可变全局/文件 IO 语言面 | **不合（语言面）** | A4-R2 正式登记为「再定基层刻意保留的时代缺口」；L10 README 明写「与 L09 相同，不修」；L09/L10 语料零依赖；L11+ 以新特性（`Tm::Prim(typ, PrimFunc)` 口径）恢复，不是 L09 该继承的机制 |

### 6.4 最终 A/B（4 轮 HEAD↔NEW2 交替、逐项 min；`ab_recheck2/`）

| 场景 | HEAD `ae8ccb6c` | NEW2 | 变化 | 相对 L07/L08 |
|---|---:|---:|---:|---|
| L09 common（6 文件） | 115.321 ms | **67.055 ms** | −41.9% | L09/L07=1.007×、L09/L08=0.981× |
| L09 自有语料（34 文件） | 1763.739 ms | **9.116 ms** | **193.5×** | — |
| Eq 阶梯单文件（801 decls） | 1678.524 ms | **2.988 ms** | **561.8×** | 1.199× L07（原 660×） |
| strchain k=11 | 65.033 ms | **9.106 ms** | 7.14× | 1.15× L07 / 1.06× L08 |
| church k=11 | 2.461 ms | **1.367 ms** | 1.80× | 0.95× L07 |
| natadd k=11 | 4.221 ms | **3.360 ms** | 1.26× | 0.97× L07 |
| enum k=9 | 0.677 ms | **0.222 ms** | 3.05× | 1.33× L07 |
| struct k=10 / universe k=11 | — | 6.286 / 4.541 ms | — | 1.12× L08（struct） |

- 测试：HEAD 46/82/17 → NEW2 **46/82/17，全绿**；validate 8 条一致
  （L09 common 6/0、L09 自有语料 34/0）；控制层 L07/L08/L10 无变慢
  （−4.2%~+0.8%），其中 L07 common −2.8%、L10 单文件 −4.2% 为「新版更快」的
  重建布局效应，已接受（非回退）。
- 结论：**L08→L09 的机制继承补齐完成**；L09 参考版性能回到 L07/L08 量级
  （common 1.01×、单文件 1.20×、church/natadd ≤1.0×），量级差距清零。

