# L13 参考版性能优化 → L11/L12 参考版移植可行性

> 口径：master（`f09e4dfe`，2026-11-09），工作树干净；**只读分析，未跑 cargo/bench**。
> 行号 = `[IO.File]::ReadAllLines` 的 1-based 行号（本次逐一核对）；标签 `[码]`/`[文档]`/`[推断]`。
> 范围：L11_macro / L12_canonical 的**参考版**，trait 面连带 L10_typeclass（同一段 `trait_wrap` 代码）。
> 按用户要求**排除 built-in Nat**（`Val::Nat`/`nat_*` prim/`quote_nat`/`nat_step_value` 等一律不列）。
> 与并行产出 `docs/optimal-design/L13-ref-perf-inventory.md`（analyst-l13）对齐：其 #1/#2/#4/#6/#7/#9/#10 对应本表 #1/#4/#5/#6/#7/#11；本文件只补"在 L11/L12 参考版是否落得下"的判断。

## 0. 速览

| 排名 | Top 3 简单可抄 | 改动量 | 预期收益（依据） | 验证 |
|---|---|---|---|---|
| T1 | **decl 表插入就地化**：`Cxt::fake_bind/decl` 改 `&mut self` + `infer_in_place` + `drop(fake_cxt)`（L13 `cxt.rs:1231-1315`、`elaboration.rs:1381/1658-1665`） | ≈35–45 行（3 文件） | **2–5×** `[推断]`：下界=插入路径残留 O(D²) 实测 3.5–4.0×/翻倍；上界=孪生平铺化 macro 28.6×。L13 侧 #1+#2 同窗口复测 strchain 4537→18.6 ms、struct 7490→5.2 ms（244×/87.9×，含 replay，不可全归 decl）`[文档 L13-ref-perf-inventory #1]` | `l11/l12_fast_parity` + `l11bench macro/struct`、`l12bench strchain` A/B |
| T2 | **删死代码 `typ_pretty`/`body_pretty`**：无任何消费方（L11 `mod.rs:48`+`elaboration.rs:420`；L12 `mod.rs:50`+`elaboration.rs:467`） | ≈10 行 | 0–3% `[推断]`；L10 同类删除（含 body）church k13 199.4→6.78 ms（29.4×）可作上界参照 `[文档 docs/opt-name-table-cow-2026-09-12.md §1]` | lib+parity（Ok 逐字节） |
| T3 | **`trait_wrap` 去掉整表 `.clone()`**：字段级拆分借用 + `can_satisfy` 式预筛（L13 `elaboration.rs:3521-3633`；L10 `:1011-1012`、L11 `:1114-1115/:1147-1148`、L12 `:1174/:1211-1212`） | ≈10–20 行/层 | L12 traitchain **5–20%** `[推断]`；L10/L11 trait 面小 | parity + L10/L12 traitchain ref 侧 A/B |

**三个特别问题的直答**：① `FORCE_MEMO` → **不值得**（L13 的收益来自 prelude 重放的长生命周期，L11/L12 单次 run 无此结构，且 L11 `force` 烧 fuel，缓存会跳过燃料账）；② decl COW → L11/L12 **已做**（`Rc<Decl>`，实测 3.2–6.4×），差距只剩**插入路径**（每次 2 次整表深拷贝），L13 的 `&mut` 就地写正是下一刀；③ `head_index` → 机制可复用到 L12 Val 级求解器，但**单独收益低**，应作为 T3 的预筛使能一起做，且必须带 L13 `9b238e00` 的 stale 下标回退。

## 1. L13 候选 × L11/L12 现状矩阵

| # | L13 参考版优化（锚点/证据） | L11 参考版现状 | L12 参考版现状 | 判断 |
|---|---|---|---|---|
| 1 | `Cxt::fake_bind/decl` 收 `&mut self`，`Rc::make_mut` 直接就地写；调用侧 `drop(fake_cxt)` 后登记（`cxt.rs:1231-1246`、`:1300-1315`；`elaboration.rs:1381`、`:1658-1665`；注释自证旧形态 ~893 ns/entry、O(D²)）`[码]` | `fake_bind(&self)` 先 `self.decl.clone()` 再 `make_mut`（`cxt.rs:392-408`）⇒ 强计数恒 ≥2、**每次整表深拷贝**；`decl(&self)` 同（`cxt.rs:438-454`）；Def 臂 `:370`/`:425` 无 `drop(fake)` | 同构：`cxt.rs:248-265`（fake_bind）、`:294-310`（decl）；elaboration `:389`/`:472` | **T1（最大收益）** |
| 2 | decl 表 `Rc<Decl>` 写时复制（`mod.rs:432`；`cxt.rs:308`） | **已有**：`type Decl = HashMap<String, 5 元组>`、`pub decl: Rc<Decl>`（`mod.rs:22`、`cxt.rs:23`），`53e8adb` 实测 3.2–3.5× | **已有**：键已 `SmolStr`（`mod.rs:24`、`cxt.rs:21`），同修复 3.4–6.4× | 已落地，只剩 #1 的插入路径 |
| 3 | `typ_pretty` 在 L13 有消费方（hover，`elaboration.rs:1621`+`DecEntry` 串）——**不是可移植"缓存"** | `DeclTm::Def.typ_pretty` 每 def 做 `nf+pretty` 但 `run` 只读 `Println`（`elaboration.rs:420`；全仓无读点） | 同（`elaboration.rs:467`；`mod.rs:50`） | **T2：删，不缓存** |
| 4 | `FORCE_MEMO`：只记 `SumCase\|Call\|Obj`，`Rc` 指针键 + epoch/taint/prim 版本（`mod.rs:163-2712`）；实测 prelude 装载 636M 次 force / 188,292 个不同输入（≈3400× 冗余）`[文档 l13-perf-review-4.md:728]`，无 memo 时 11.0 s（3.4×）`[文档 l13-twin-bench-2026-09.md:12]`；**用户文件侧收益 ±0，全部收益来自 prelude 固定成本**（22.4→6.0 s / force 636.6M→4.41M）`[文档 L13-ref-perf-inventory #4]` | 无 memo；`force` 只有 Flex/VSub/Obj 三扩展臂（`mod.rs:561-581`），且展开**烧 `unify_fuel`**（`:567`） | 无 memo；`force` 递归 Obj/Call/VSub（`mod.rs:686-...`），同样烧燃料 | **不建议**（见 §3/Q1） |
| 5 | `simpl_decl` 单条指针键缓存（`mod.rs:1268-1302`，`DECLB_CACHE`） | 中性表已在分支循环外重建（`mod.rs:1009-1017`；`unification.rs:361`、`:780`），`perf-l08l13-followup §4` 实测**无差别**（0.98–1.04×） | 同（`mod.rs:1150-1166`；`unification.rs:364`、`:822`） | 不建议（见 §3） |
| 6 | `FxHashMap` + `SmolStr` 全链（`mod.rs:5/432`） | decl 键为 `String`（`mod.rs:22`）；换 `SmolStr` 只省条目克隆的堆分配 | 已是 `SmolStr` | 尾部清理，非第一波 |
| 7 | `head_index`：`Synth` 里 `(trait, head) → 下标桶`（`typeclass.rs:98/177-215`），`solve_trait` 先查桶再线性扫（`unification.rs:706-765`；stale 回退 `9b238e00`） | 无：`class_instances: HashMap<String, Vec<Instance>>` 线性扫（`typeclass.rs:130`；`unification.rs:491`+`:537`） | 无（`typeclass.rs:87/107`；`unification.rs:508`+`:552`）；`docs/tt-spec-metas-typeclass.md` 明记 L10/L12 无头索引 | 见 Q3：与 T3 合并，不单抄 |
| 8 | `scan_def_replay`/`def_needs_replay`（`mod.rs:3119-3200`，prelude/全局副作用重放判定） | 无 replay 概念（可变全局只在 builtin 内，无 namespace/prelude 装载） | 无（`run_with_prelude` `mod.rs:1290` 只是 6 个 core 文件的线性装载，非 replay） | **不适用** |
| 9 | `Span<()>` 降低错误值携带成本（`mod.rs` 多处） | decl 元组**已** `Span<()>`（`mod.rs:22`）；`Span<String>` 仅名字/错误定位需要 | 名字全 `SmolStr`（`mod.rs:24`） | 已等价，无动作 |
| 10 | force 复合形状 memo（`SumCase/Call/Obj` 递归 walk 才值得 memo，`mod.rs:2664-2672`） | L11 `force` 的 `SumCase` 是叶子（不递归，`:580`）⇒ 无对应冗余 | L12 递归 `Call` 体（`mod.rs:705-706/765`），但调用值多为内联体、复用低 `[推断]` | 不进 Top3 |
| 11 | `trait_wrap`：命名空间探测惰性快照（`:3531-3591`）、`can_satisfy` 头预筛（`:3550/3563`）、**去整表 clone**（`:3626` 直接迭代） | `trait_definition.clone()` 自证 TODO（`elaboration.rs:1114-1115`、`:1147-1148`），候选 `synth` 在克隆表上跑 | 同：`:1174`、`:1211-1212`（L10 `:1011-1012` 同病） | **T3** |
| 12 | `filter_accessible_constrs` 快照只包慢路径（L13 早期 -9~-13%） | L11 值级探测已只快照 `infer.meta`（`pattern_match.rs:124`） | 同（`pattern_match.rs:114`） | 已等价 |
| 13 | unify 的 `Call/Call` 无-Flex 预检（L13 早期 -39% adder_proof） | L11 无 `Tm/Val::Call` | L12 已有 `Call` 但 unify 直接取 body 合一（`unification.rs:678-679`），无 meta 快照 | 不适用 |
| 14 | namespace/hover/LSP/prelude-pool/effect/replay | 无对应设施 | 无 | 不建议（L13 专有） |
| 15 | `trait_wrap` 命名空间探测的**惰性 meta/trait_metas 快照**（`elaboration.rs:3531-3591`；`ns_entries` 空则零成本，97% 成员访问走空分支）`[历史实测 2026-08-05 l13-perf-review §2.1：09-hierarchy −29%、10-bundle −21%]` | **无快照**：namespace 探测里 `fresh_meta` + `unify_catch` 失败后不回滚（`elaboration.rs:1132-1145`）——这是**正确性缺口**（meta 泄漏），不是单纯性能差 | 同（`elaboration.rs:1196-1209`） | 与 T3 同函数；建议作为正确性修复跟进（条件快照+L13 门控），不单算 perf 收益 |
| 16 | `no_metas` 改 visited-set 图遍历（`mod.rs:693/706/735`，Rc 指针去重，直接查 Val 图）`[历史实测 2026-08-14 l13-perf-review-4 §7.4：11-bundle-deep 4.400→1.461 s（3.0×）、10-bundle 1.7×]` | L11/L12 的 `no_metas` 走 quote 后遍历（无 visited set）；大值/深图有重复工作，但 L11/L12 单次 run 图规模远小于 L13 prelude | 同 | **值得但不够"简单"**（M：L13 +87/−23 行、依赖指针稳定假设）；列入第二波而非 Top3 |

## 2. Top 3 详情（改哪里 / 怎么验证 / 收益量级）

**T1 decl 表插入就地化（≈35–45 行）**
1. `cxt.rs`：`fake_bind`、`decl` 签名 `&self → &mut self`；删掉函数内 `let mut decl = self.decl.clone()`，直接 `Rc::make_mut(&mut self.decl).insert(..)`；保留 `fake_bind` 的 `redefine` 错误（**必须用 `contains_key` 前置判定**以保持 Err 文案/顺序，L13 `cxt.rs:1242-1245` 同款）；返回 `Ok(self.clone())`（浅克隆）。
2. `elaboration.rs`：`infer(&mut self, cxt: &Cxt, ..)` → 新增 `infer_in_place(&mut self, cxt: &mut Cxt, ..)`（原函数体）；旧 `infer` 保留为 `let mut c=cxt.clone(); self.infer_in_place(&mut c, t)`（L13 `:1396-1401` 同款，API 零破坏）；Def 臂在 `solve_multi_trait` 与 `no_metas` 检查之后、`ret_cxt.decl(..)` 之前加 `drop(fake_cxt)`（L13 `:1658-1665`）。
3. 驱动：`run` 的 `infer.infer(&cxt, tm)` → `infer.infer_in_place(&mut cxt, tm)`（L11 `mod.rs:1109`；L12 `mod.rs:1271`，`run_with_prelude` 的两处 `:1332/:1360` 同改）。Enum 臂（L11 `:455/542/545`、L12 `:502/602/605`）可第二批；ctor 注册（L11 `:588`、L12 `:648`）同理。
- 验证：`cargo test --lib L11_macro` / `L12_canonical`；`l11_fast_parity` / `l12_fast_parity`（Ok 逐字节、Err span+`?N` 归一化）；bench `l11bench --workload macro,struct --max-k 11 --only basic`、`l12bench --workload strchain --only basic`（同窗口交错 A/B，rounds=3 min）。
- 收益：`[推断]` 2–5×（L11 basic macro 911.9 ms、struct 887.5 ms、strchain 707.6 ms（09-20 矩阵）；L12 strchain 645.0 ms——这些负载 k=11 时有 ~2^12 个 def，插入路径是 O(D²) 主导项之一；`perf-l08l13-followup §3.4` 记录残留缩放 3.5–4.0×/翻倍、末次 5.5×）。风险：`make_mut` 在表被共享时仍深拷贝 ⇒ 隔离语义不变；不要再叠加 #5 的指针键缓存（F3，`docs/review-2026-09-29.md` P1-?：指针键 + 原地变更 ⇒ 陈旧命中）。

**T2 删除 `typ_pretty`/`body_pretty`（≈10 行）**
- 改：L11 `mod.rs:44-50` 的 `DeclTm::Def` 删两字段；`elaboration.rs:360/420-421/428/433-438` 删 `vtyp_pretty`/`vt_pretty` 与 `nf+pretty` 计算。L12 `mod.rs:46-52`、`elaboration.rs:379/467/475/480-485` 同。L11/L12 内 `DeclTm::Def` 只有构造点、无读点（grep 复核：两层的 `run` 只匹配 `Println`；L13 有 hover 消费方，不在本移植面）。
- 验证：lib + parity（输出面只有 `Println`，Ok 应逐字节不变）。
- 收益：`[推断]` 0–3%（每 def 一次类型 nf+pretty；L10 同类删除的 29.4× 是 body 主导，不可直接外推）；价值主要是删死代码/降复杂度。

**T3 `trait_wrap` 去整表 clone（≈10–20 行/层）**
- 改：把 `self.trait_definition.clone().iter()..` 换成**字段级拆分借用**：
  `let defs = &self.trait_definition; let solver = &mut self.trait_solver;`（必要时另取 `&mut self.completion_table`），在迭代里用 `solver.clean(); solver.synth(..)`；Rust 允许不相交字段借用，语义零变化。第一处 completions 分支（L11 `:1114-1130`、L12 `:1172-1194`、L10 `:1011-1030`）与第二处方法候选分支（L11 `:1147+`、L12 `:1211+`）各一处；L13 已示范无 clone 迭代（`elaboration.rs:3626`）。
- 可选增强（同轮）：仿 L13 `can_satisfy` 头预筛（`:3550/3563`）在 `synth` 前挡掉明显不匹配候选；这依赖 Q3 的 head_index，可后置。
- 验证：L10/L11/L12 lib + parity；L12 traitchain 目前孪生 parity 失败（FACTS/bench §4），故用 **ref 侧 A/B**（改前/改后二进制同窗口交错）+ 非 trait 负载无回归。
- 收益：`[推断]` L12 traitchain 5–20%（每成员访问一次克隆 `trait_definition`：条目含方法表 Vec，克隆是 O(#traits×#methods)）；L10/L11 的 trait 用例体量小，收益接近噪声。

## 3. 不建议抄

1. **`FORCE_MEMO`**（Q1）：L13 的 3.4×/11.0 s 是 **HDL prelude 重放**（同节点跨轮/跨 decl 反复 force，636M/188k 冗余；analyst-l13 审计亦记"用户文件侧收益 ±0，全部收益来自 prelude 固定成本"，见 `L13-ref-perf-inventory #4`）；L11/L12 `run` 每次新建 `Infer`、单遍、无 prelude replay，节点生命周期短。且 L11 `force` 的 meta 展开是**烧 fuel** 的（`mod.rs:567`），memo 命中会跳过燃料消耗 ⇒ 与"有界降级"语义冲突，需额外 fuel/taint 守卫。移植 ≈50–80 行 + 语义评审，预期 <5% `[推断]`。若要做，先以 env 开关在 macro/strchain/natadd 上 A/B，而不是直接进默认路径。
2. **`simpl_decl`/`DECLB_CACHE`**：L11/L12 已把中性表提出分支循环且实测无差别（`perf-l08l13-followup §4` 0.98–1.04×）；再加快捷缓存收益面只有"多次 Match 值 quote/unify"，且指针键与 T1 的原地 COW 直接冲突（F3 类陈旧命中），风险>收益。
3. **`head_index` 单独移植**（Q3）：L11/L12 实例数小、trait-heavy 基准只有 L12 traitchain 且孪生侧已坏；单独加索引只省线性 filter，收益小，还引入刚在 L13 触发 OOB 的 stale-bucket 维护面（`9b238e00`）。等 T3 需要预筛时一并做。
4. **`scan_def_replay`/`def_needs_replay`**：为 L13 的 namespace/prelude/全局副作用重放服务；L11/L12 无 replay 语义，硬搬=无消费者代码。
5. **`Span<()>`/`SmolStr` 全量化**：L11 decl 元组已 `Span<()>`；`SmolStr` 在 L12 已是全链，L11 换键只是尾部微优化（~30 行触点多），留给后续清理。
6. **`force Sum/Call 复合 memo`**（#10）：L11 `SumCase` 是叶子、无递归冗余；L12 `Call` 递归但内联体复用低；不是可测收益点。
7. **L13 专有设施**：namespace、hover/LSP 观察面、prelude 池化/常驻/compact、effect/IO replay —— 依赖 L13 宿主工程，带不进 L10–L12 的"简单参考实现"目标。

## 4. 验证方案、顺序与风险

- **门禁**：`cargo test --lib L11_macro` / `--lib L12_canonical`；`cargo test --test l11_fast_parity` / `l12_fast_parity`（判据：Ok 逐字节、Err 剥 span+`?N`，L11/L12 已如此）；改动 T1 后额外跑一次 `l11/l12_fast_parity` 的深负载段（macro/struct/strchain）。
- **性能 A/B**：按 FRAMEWORK §2（`CARGO_TARGET_DIR=C:\ezl-target`，独立进程、同窗口交错、≥3 轮 min，报告比值而非绝对值）；L11 主测 `macro/struct`，L12 主测 `strchain/macro`；trait 项测 L12 traitchain（ref 侧改前/改后，不依赖孪生）。
- **顺序建议**：T3（最小、独立）→ T2（零风险收尾）→ T1（最大、需 bench 复核）；T1 与 #2 的 `Rc<Decl>` 已就位，不需要动 `Decl` 表示/parity 判据。
- **主要风险**：① `fake_bind` 的 redefine 判定顺序/文案必须与旧一致（Err parity）；② `make_mut` 共享回退路径不能省（trait/enum 递归里 cxt 会被 clone），否则语义变；③ 不要与指针键缓存（DECLB/FORCE_MEMO）同轮落地；④ L12 traitchain 孪生 parity 既有失败，T3 验证不要把它当门禁；⑤ T2 删字段后若 L11/L12 的测试/探针匹配 `DeclTm::Def` 需同步（grep 目前只有构造点）。

## 5. 给 Lead 的一句话

**L13 参考版真正能"简单抄"给 L11/L12 的是两处结构性小刀——`&mut Cxt` 就地插 decl（最大收益，2–5× 推断）与 `trait_wrap` 去整表 clone（trait 面）；FORCE_MEMO/DECLB_CACHE/head_index 要么依赖 L13 prelude/LSP 生命周期，要么与原地 COW 冲突，不建议第一波。**
