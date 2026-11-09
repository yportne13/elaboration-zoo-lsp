# L13 参考引擎（非 twin）性能优化清单与有效性判定

> 范围：`src/L13_namespace` 的参考版（排除 `bump_spine_iter/**` 孪生、共享 parser/pretty 的跨层优化、
> 以及用户明确排除的原生 Nat 相关项 `Val::Nat`/nat primops/`quote_nat`/`NAT_CHAIN_LIMIT`）。
> 行号口径：`[System.IO.File]::ReadAllLines` 的**数组下标 +1**（不用 Get-Content/Select-String，本仓二者会漏/错行）。
> 证据档位：`[历史实测]`（仓库既有 A/B，注明日期与口径）/`[未量化]`（有代码与设计论证、无可信数字）/
> `[合因]`（收益与相邻项捆绑、无分离数字）。跨窗口绝对值只作量级参照（09-23 轮的 ±10% 漂移教训）。

## 1. 清单（参考版当前 HEAD 仍在生效的项 + 两项已失效/负结果）

| # | 优化 | 代码锚点 | 机制一句话 | 证据（日期/出典） | 复杂度 / 移植 |
|---|---|---|---|---|---|
| 1 | decl 表 COW 就地写 + `&mut Cxt` + `drop(fake_cxt)` | `cxt.rs:1240`(fake_bind) `:1303`(decl) `:1310`(make_mut)；`elaboration.rs:1663`,`:1826`(drop) | `fake_bind`/`decl` 改收 `&mut Cxt`，`Rc::make_mut` 计数=1 时就地 insert；登记前 `drop(fake_cxt)` 把计数打回 1，消灭"先 clone 再 make_mut"的两次整表深拷 | `[历史实测 2026-09-20]` bench-matrix-2026-09-20 附录 B：L13 basic `strchain 4537→18.6ms(244×)`、`struct 7490→85.2ms(87.9×)`（同窗口统一复测；与 #2 合因） | M；无 unsafe；→ L07–L12（L11/L12 同模式未修） |
| 2 | `scan_def_replay` 记忆化 | `mod.rs:1486`(memo 字段) `:3120`/`:3128`(读/写) `:3152`(fn) | def replay 副作用扫描按名 memo；**截断守卫**（环/超限结果不入表）避免脏缓存 | 同 #1（附录 B 修法表②，"两条必须同修"，无分离数字）`[合因]` | S；→ L07/L08（同 replay 概念） |
| 3 | decl 表表示：`FxHashMap` + `SmolStr` 键 + `Span<()>` | `mod.rs:432`(`type Decl = FxHashMap<SmolStr,(Span<()>,…,Option<PrimFunc>,String)>`) | 热路径 `decl.get` 用 FxHash；短名 SmolStr 内联零堆分配；span 不携源串 | `[未量化]` 设计论证（prelude 装载 ~4M 次 decl.get，README §1.1）；对照数据：09-20 附录 A "L07/L08 每条目 ~7ns vs L13 ~893ns" | S；→ L09–L12（L11 仍 `String` 键） |
| 4 | **FORCE_MEMO**（指针键 force 记忆化） | `mod.rs:163`(static) `:194`(CAP) `:211`(clear) `:2662`(force) `:2713`(force_inner) | 只对 `SumCase/Call/Obj` 复合形状走表：keepalive 持输入 Rc、taint 传播（meta/副作用 prim 不入表）、`PRIM_VERSION` 惰性失效；1M 上限；每文件/每 kick `force_memo_clear` | `[历史实测 2026-08-22]` l13-perf-review-4 §16.4：prelude 固定成本 22.4s→**6.0s(3.7×)**、force 调用 636.6M→**4.41M(144×)**；用户文件 ±0（冗余只在跨 def 共享图） | M（~157 行跨 3 文件）；三支柱正确性风险；→ L07–L12（需 PRIM_VERSION/prim 白名单接口） |
| 5 | force 形状门控 + `Val::Sum` 叶子 | `mod.rs:2664-2672`(dispatch) `:2715-2723`(unary gate) `:2897`(`Val::Sum => t.clone()`) | 非 compound 值直进 `force_inner`（省哈希）；`Val::Sum` 直接作 WHNF 叶返回；只有一元 SumCase 链才走 `force_chain`，省其 `clone+match` | `[未量化]` 代码注释：常见形状省一次 clone+match；属 FORCE_MEMO 后的微调 | S；→ L07–L12 |
| 6 | `simpl_decl` 简化表共享缓存 | `mod.rs:1252`(`DECLB_CACHE`) `:1268`(fn) | `quote/rename/unify` 处理 `Val::Match` 时共用的"body→Decl 引用"简化 decl 表按 decl 地址缓存 | `[历史实测 2026-08-05]` l13-perf-review §2.4：与 #7 共同作用 adder_proof（无分离数字）`[合因]` | S（~40 行）；→ L07–L12 |
| 7 | unify 的 Call/Call 无-Flex 预检 | `unification.rs:71`(val_has_no_flex) `:89`(spines_contain_flex) `:1008`(用法) | 两 spine 全 ground 时免 meta+trait_metas 快照直接 `unify_sp`（成功路径原本也整表 clone） | `[历史实测 2026-08-05]` l13-perf-review §2.2：adder_proof 1.470→**0.895s(−39%)**（min-of-5，±20% 噪声窗） | S（~30 行）；→ L09–L12 |
| 8 | `trait_wrap` 惰性 meta 快照 | `elaboration.rs:3527-3543` | `ns_entries` 为空（~97% 成员访问）直接返回；只有存在候选条目时才取 meta/trait_metas 快照 | `[历史实测 2026-08-05]` §2.1：09-hierarchy −29%（0.304→0.217s）、10-bundle −21%（0.825→0.66s） | S（~15 行）；→ L10–L12（各层有 trait_wrap） |
| 9 | 实例 `head_index` 桶 + 桶空早退 | `typeclass.rs:98`；`unification.rs:745-751` | `(trait, head) → instance 下标`，O(1) 筛候选；两桶皆空即免全实例 `val_match` | `[未量化]` 规范文述（typeclass-syntax.md:250 "head_index O(1) 筛选候选"）；无 A/B | S/M；→ L10–L12 |
| 10 | `no_metas` 改 visited-set 图遍历 | `mod.rs:693`(fn) `:706`(no_metas_seen) `:735`(no_metas_rc) `:2616`(val_no_metas) | Rc 指针去重的 Tm 图遍历 + 直接在 Val 图检测未解 meta（不 quote 已解图） | `[历史实测 2026-08-14]` l13-perf-review-4 §7.4：11-bundle-deep 4.400→**1.461s(3.0×)**、10-bundle 1.7× | M（+87/−13）；依赖指针稳定假设；→ L09–L12 |
| 11 | `eval_aux` 只 force 非构造子头 | `pattern_match.rs:608-635` | 构造子头直接取 `index/datas`；只对 meta 等非构造子头 force，避免每步重走深链（O(n²)） | `[未量化]` 注释给 `nat_add_helper` 大字面量动机 | S；→ L07–L12 |
| 12 | class Phase A 结果复用（`Raw::Tm`） | `parser/syntax.rs:113-118`(`Raw::Tm`)；`elaboration.rs:2552`(Phase A) `:2592`(PrecheckedItems) | Phase A 检查过的字段值/类型包成 `Raw::Tm`，Phase B 的 create/tree 复用之而非重新 infer | `[历史实测 2026-08-13]` review-4 §6.2：HDL 用户侧 **2.0–2.5×**（02-arithmetic 1.23→0.49s、01-basics 0.30→0.19s）；3× 回退基本消除 | L（elaboration+parser 跨文件；`bn_refs`/配对安全门）；→ L13 专有（L11/L12 无 class） |
| 13 | `PRELUDE_CACHE` + `clone_prelude_state` | `mod.rs:3981`(static slot) `:4381`(fn) `:4410`(clone) | prelude 的 `(Infer,Cxt,macros)` 进程内缓存一次，后续装载改深克隆而非重 elaborate 24 文件 | `[历史实测 2026-08-07]` L13-code-review:57：debug 126s→**3.9s**；review-2 §5.4：CLI 2.94→**1.9s(−35%)**、prelude 2.4→1.6s、macro_goto_tests 20.1→9.8s | M；→ 各层 test/CLI（prelude 宿主仅 L13 有） |
| 14 | `PreludeSlot` / `PreludePool`（TLS 槽+进程池） | `mod.rs:4009`/`:4011`(pool) `:4021`(struct) `:4058`(Drop) | 线程退出把 prelude 状态推池、新线程取池；`Drop for PreludeSlot` 清 FORCE_MEMO/DECLB_CACHE 以维持"推池时持最后引用" | `[历史实测 2026-09-11]` l13-parallel-test-uaf §3：`TYPORT_NO_PRELUDE_POOL=1` 下 -j4 parity suite **31s→9m42s**（每线程重 elaborate）；README §3.3 libtest 每测试线程 ≈1.5s | M；测试/宿主面收益；→ 仅 L13（无 prelude 的层无意义） |
| 15 | `ctor_hover_memo` 构造子 hover 渲染缓存 | `mod.rs:1499`(field)；`elaboration.rs:2837-2848` | 构造子 hover 值是 decl 闭合值，push 期渲染一次后按 decl 键缓存（无未解 meta 才缓存） | `[历史实测 09-19/20]` README §3.2：每 Con 模式 ~22µs→**~0.5µs**；L13 match basic 0.338→0.215（矩阵 09-20，与 `448775c`/`ba90f96` 合窗） | S（~30 行）；→ L13 only（需 hover） |
| 16 | def-site `typ_pretty`（decl 第 7 槽） | `mod.rs:432`/`:446`；`cxt.rs:1235`/`:1293`/`:1303`；`elaboration.rs:1621`/`:1665` | def 登记期算一次类型渲染串，hover 直读、免查询期无上下文 re-pretty | `[未量化]` 收益；成本有数：~893ns/entry 一次（cxt.rs:1235；09-20 附录 A 对照） | S；→ L13 only |
| 17 | owned 观察表 + push 期渲染 | `mod.rs:1413`(`HoverEntry=(Span<()>,Span<()>,String)`)；`elaboration.rs:2826`(push_hover) | 观察面存 owned 串而非 live `Val`，push 时 quote+pretty 定稿 | `[未量化]` 参考版净收益；契约主要服务双引擎（lsp-twin-wiring §0/阶段 0）；参考版 prelude 期仍在付费（master 无总闸，wip 补丁才有） | M；→ L13 only |
| 18 | bench 入口补 `force_memo_clear`（**仅 bench 口径**） | `mod.rs:4869`(bench_check_nf_bounded) `:4948` | 参考版 bench 入口此前漏清 FORCE_MEMO，表只涨不中；补齐后恢复真实命中 | `[历史实测 2026-09-22]` perf-l13-round-22 §2.7：修复后 basic `struct −19%`、`prelude-core −30%` ⇒ **此前 basic 数字被污染**，不是产品优化 | S；仅测量口径 |
| 19 | ~~Sum 臂 eval 记忆化~~（**已撤销，负结果**） | 无（HEAD 不存在） | `eval(Tm::Sum, env)` 点级缓存（曾完整实现并验证） | `[历史实测 2026-08-14]` review-4 §9：全语料**净损失**（01-basics +22%、02-arithmetic +33%、hdl_ops +21%、adder_proof +30%、10-bundle +12%）；原因：一次性求值占 60%，守卫/锁成本 > 重复节省 | —；不要抄 |
| 20 | ~~filter_accessible_constrs 快照只包慢路径~~（**已失效**） | 无（`448775c` 逐臂重写删除该路径） | 决策树时代优化：快照/恢复只包索引探测循环 | `[历史实测 2026-08-05]` §2.3：hdl-verilog infer −9~13%、01-basics −13%；2026-09-18 决策树→逐臂后代码不存在 | —；历史项，勿按旧路径移植 |
| 21 | （已吸收）Def 体不做 eager nf+pretty | `elaboration.rs:1621`（只算 `vtyp_pretty`，无 body 串） | 只保留类型渲染；body_pretty 不预算 | `[历史实测 2026-09-12]` opt-name-table-cow §1：L10 同类删除 6.8×/29.4×；L13 早已如此（`elaboration.rs:975` 旧注释）→ 无新收益 | —；说明"L13 先行正确"，非可抄项 |

## 2. 有效性判断（4 档）

- **真有效（可信数值、非负载/窗口假象）**：#1+#2（组）、#4、#7、#8、#10、#12、#13、#14（仅测试/宿主面）、#21（跨层已吸收）。
  其中 #4 的强证据还说明一个反直觉事实：**用户文件侧收益 ±0，全部收益来自 prelude 固定成本**。
- **有效但被夸大/归因合并**：#6（与 #7 合因，adder_proof 的 −39% 不能单记给它）、#15（与两个 commit 合窗；
  单点 22µs→0.5µs 可信，match 总收益不可全归它）、#9（"O(1)"是机制描述，无 A/B）、#14（对产品运行时≈0，
  收益在 test 二进制/进程生命周期）。
- **存疑（窗口/口径/未量化）**：#3、#5、#11、#16、#17、#18（#18 是**测量口径修复**：它让 basic 变快，
  但反过来证明此前 basic 数字失真，不能当优化宣传）。
- **无效或已回退**：#19（净损失，已撤销）、#20（被逐臂重写取代，代码已不存在）。

## 3. S/M/L 与可移植目标（初筛）

| 等级 | 项 | 目标层 |
|---|---|---|
| **S**（≤~50 行、无 API 破坏、无 unsafe、可独立验证） | #2、#5、#6、#7、#8、#11、#15、#16 | #2→L07/L08；#5/#6/#11→L07–L12；#7→L09–L12；#8→L10–L12；#15/#16→仅 L13（hover） |
| **M**（改签名/局部状态或多文件；需门禁+parity） | #1、#4、#9、#10、#13、#14、#17 | #1/#4/#10→L07–L12；#9→L10–L12；#13/#14/#17→L13 宿主 |
| **L**（跨子系统语义门） | #12 | 仅 L13（class 专有） |

## 4. 结论

**Top 5「真正有效且简单可抄」**（按"可抄性×收益"排序）：
1. **#7 unify Call 无-Flex 预检**（S，−39% adder_proof，L09–L12 合一器同形即可移植）。
2. **#8 trait_wrap 惰性 meta 快照**（S，−29%/−21%，L10–L12）。
3. **#6 simpl_decl 共享缓存**（S，与 #7 合因的证明/复杂模式负载）。
4. **#1+#2 decl 表就地 COW + replay memo**（M，244×/87.9%（合因），L11/L12 的"先 clone 再 make_mut"同模式明确未修）。
5. **#10 no_metas visited-set**（M，3.0×，L09–L12）。
> 附注：绝对收益最大的单项其实是 **#4 FORCE_MEMO（3.7×/144×）**，但三支柱正确性使其不算"简单"；
> 若目标是 L13 prelude 固定成本，应优先它，移植时必须带 keepalive/taint/PRIM_VERSION 与 per-file epoch。

**Top 3「别抄 / 只在 L13 有用」**：
1. **#19 Sum 臂 eval 记忆化**——已实测净损失 +5~+33%，勿重试。
2. **#20 filter_accessible_constrs 惰性快照**——决策树时代的优化，`448775c` 逐臂重写后路径已删除；按旧文档移植会做死代码。
3. **#15/#16/#17 观察面三件套**（ctor_hover_memo / typ_pretty / owned hover 表）：只在有 LSP 的 L13 有意义；
   参考版自身净收益未量化，且 master 参考版在 prelude 期仍在付渲染成本（总闸只在 wip 补丁）——要抄先带"prelude 期总闸"。

## 5. 边界：这些**不算**参考版优化（易混淆）

- **孪生独占**（不计入本清单）：bump arena/打包值 `V`/迭代内核/复合环境/`name_map+trail`/覆盖检查 `CtorIndex`/
  meta journal/`FORCE_PRIM_MEMO`/force 叶子快路径（09-25）/摊平链三刀（09-26）/`prime_resident`+`compact`/
  `case_spans`/后缀倒排索引/14 表归还档。注意 `case_spans` 只在孪生（参考版无该符号）。
- **共享设施**（不计入引擎）：`preprocess` 单遍（`mod.rs:4651`）是共享前端；pretty 增量 builder 属 L11/L12。
- **未落地的"机会"**（不是已做优化）：参考版 `covers` 仍 n³（09-23 §4/§7 有意留作对照）、
  后缀倒排索引未移植（09-22 §3.3/09-23 §4，上限 k=13 约 600ms）、参考版每 def 双渲染合一未合并、
  prelude 期 LSP 表总闸未进 master（仅 `docs/wip/` 补丁，21.1s→9.3s）。
- **原生 Nat 项全部排除**：`Val::Nat`、nat primops、`quote_nat`、`NAT_CHAIN_LIMIT`/`guard_nat_chain`。

## 6. 数据口径提醒

1. 08-05/08-13/08-14/08-22 的数字来自 `l13-perf-review*.md`（min-of-3/min-of-5，±20% 噪声窗，部分窗口未交错 A/B）；
   09-20 附录 B 是**同窗口统一复测**（0.91–1.06× 无回归对照），可信度更高；09-23 轮起规定"同窗交错 A/B"。
2. #15/#16 的收益与 `448775c`（逐臂）、`ba90f96`（unify_pm 孪生臂）、`b3b1700`（hover 缓存）同窗，**不可拆分归因**。
3. #18 说明"bench 变快"也可能只是口径修复；引用 basic 数字时须注明是 09-20 之后（修复后）的窗口。
4. 参考版的定位是"可读规格实现"：多处 O(D²)/O(n³) 被业主**有意保留**（#1 类修法在 L05/L06/L09/L10 已搬运，L11/L12 未动）。
