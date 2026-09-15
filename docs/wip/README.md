# L13 显式替换移植：未落地尝试的证据存档

L13（生产层）的显式替换移植**代码已完成且裸语言语义正确**，但因
prelude/calc 路径的规模放大未通过验收，**已回退到 HEAD 状态**。
本目录保存历次尝试的补丁与结论，供后续接续。

## 产物

- `l13-explicit-subst-round1.patch`：第一轮移植（参考版 + 孪生版，8 文件
  / +1599−452）——裸语言语料 65 例逐字节 diff = 0，但 prelude 挂起。
- `l13-explicit-subst-attempt.patch`：第二轮修复尝试（= round1 + `frcs`
  入口 `mentions_level` 快路径、`wrap_sub` 展平、`compose` 去重、
  `quote_sp` 迭代化 + 顶层 quote 记忆化、`subst_cxt` 条件包裹；对干净
  HEAD 可独立应用，是 round1 的累积超集）——挂起缓解为"可完成但慢"，
  calc 单测 74s（默认测试栈直接 STATUS_STACK_OVERFLOW，即 parity 崩因）。
- `l13-explicit-subst-round3-perf-probes.patch`：第三轮（2026-09-15），
  **= attempt 累积补丁 + 三项性能修复 + 全套诊断探针**，对干净 HEAD 可
  独立应用（`git apply --check` 已验证）。见下文"第三轮结论"。

## 第三轮结论（2026-09-15）：根因已定位到函数级

复现与方法：应用 attempt 补丁后，`TYPORT_PRELUDE_PROF=1`（逐文件/逐
decl 计时）+ `L13_DIAG=1`（FUNC_PROF WATCH + [DIAG8] 计时探针）跑
`typort check`（等价于测试的 `run_with_prelude` 全路径），与 stash 后的
基线同法对照。

### 画像一：耗时分这不是 eval，是"每个操作变贵"

prelude 全量加载（含 HDL）：**基线 ~4.5s → 移植后 ~30s**。逐 decl 热点
（移植后）：`portLineSingle` 2.26s（基线 0.010s）、`collectRegLines`
2.48s（0.013s）、`collectInitLinesCd` 2.28s（0.025s）、
`wrapWithWhenContext` 1.78s、`createSignalExpr` 1.63s——全部是
`hdl-verilog.typort`（file[30]，移植后单文件 15.5s / 基线 0.93s）里
**大枚举 match（15–30 case）+ 字符串 List 处理**的函数。

### 画像二：elaboration 结构完全没变，是单次操作成本爆炸

prelude 加载期间 FUNC_PROF 对比（同机同构建参数）：

| 函数 | 基线 | 移植后 | 倍率 |
|---|---|---|---|
| infer_expr 调用数 | **118 304** | **118 304（完全相同）** | 1× |
| infer_expr 独占 | 0.441s | 13.4s | 30×（113µs/次） |
| quote | 0.202s / 1.12M 次 | 8.5s / 4.2M 次 | 42× |
| eval | 3.035s / 5.68M | 4.414s / 6.54M | 1.4× |
| check | 0.153s / 44 292 次 | 2.363s / 44 292 次（次数相同） | 15× |
| force | 0s / 5.18M | ~0s / 10.9M（memo 生效后） | — |

调用次数逐一对齐 ⇒ 模式编译器/检查器的**递归结构没变**，是 σ 载体让
每步（每次 force/quote/方程重锚）贵了 30–100×。

### 画像三：[DIAG8] 独占计时分解（移植后 ~30s）

- **hover ≈ 11.0s**：`push_hover` 在每次变量引用时 quote+pretty 该变量的
  类型值；σ 机制下类型带 VSub 包裹、且 meta 求解使类型值每次引用都是
  **新指针**——按指针键的渲染缓存全 miss，每个引用都重走"force（frcs
  重建）→ 全树 quote → pretty"。基线同样每引用都渲染，但类型值稳定且
  小，总计仅 ~0.2s。
- **unify_pm ≈ 2.5s**：每条方程入口 `force(VSub(f, acc))` 的重包裹重建。
- **eval ≈ 4.2s（1.4×）**：可接受。
- **模式编译器为最大子树**（compile_aux 含递归的 inclusive 计时 143s，
  双计但量级指示明确）：每分支的构造子探测 `check_pm`、臂体 `ret_type`
  的 quote→eval 重锚（对 σ 包裹值 quote 会展开出巨型树）都在分支循环里。

### 画像四：σ 身份漂移击败一切按指针键的缓存

- frcs 慢路径实测 **~9.8e5 个不同 σ 指针、~1.3e6 个不同 (v,σ) 对**
  （对 ≈ 调用数，几乎无重复）——每次 `extend`/`compose` 都是新 Subst，
  每次包裹都是新 VSub cell；嵌套 match 的上下文被逐臂 `subst_cxt`
  逐层再包裹。
- 因此"巨型卡住应用"的旧定性需要修正：不存在字面 7.8 万实参的应用。
  quote 树扇出 77 811 节点/深 12 287 层，是**σ 逐节点包裹的长 List 值**
  （Verilog 字符串行列表）在 quote 时被逐单元展开；σ 链本身很短
  （实测 maxsublen=4），force 后顶层从不是 VSub（DEEP2 零命中）。

### 第三轮已落地的修复（在 round3 patch 内，74s → 26.6s）

1. `Subst::compose` 恒等快路径：`Rc::ptr_eq(outer, inner)` 时原指针返回
   （读点反复自组合不再新分配内容相同的 Subst）。
2. `FRCS_MEMO`：frcs **顶层入口**（深度 1）的 (结构, σ) 对 memo——输入
   持 `Weak`（不延长生命、无 ABA）、结果持强引用（产物指针稳定 ⇒ 下游
   FORCE_MEMO/QUOTE_MEMO 键恢复命中）；taint + fuel 水位 + PRIM_VERSION
   + epoch 四重守卫。**注意选型教训**：输入强 keepalive 会钉住重建图
   （实测 8 GB）；结果持 Weak 则跨调用全 miss（更慢）。
3. `push_hover` 渲染串缓存：键 (值指针, locals 身份, PRIM_VERSION)，
   输入 Weak + 渲染串 Rc——但只对"同一类型值被重复引用"生效，prelude
   加载期类型值多为新指针，命中率低（见接续 a）。

### 语义状态（第三轮实测）

- `calc_err_by_no_proof` / `calc_err_by_wrong_position`：**通过**（第二轮
  存档所称"报错文案改变"在 attempt + round3 状态不复现，round 4 可独立
  复核）。
- 裸语言 65 例 diff = 0 的结论仍属 round1，round3 未重跑全量。

## 接续建议（round 4 工作清单，按预期收益排序）

1. **hover 惰性化**：hover 表存 (Val Rc, 名字表, decl) 元组，
   `hover_entry_at` / JSON 序列化时按需渲染一次（RefCell 缓存）。孪生版
   本就有 `push_hover_cached`，参考版照做即可对齐。预期回收 ~11s。
2. **unify_pm 方程入口**：`mentions_level` 判定 acc 对两侧无作用时跳过
   `force(VSub(·, acc))` 重包裹。预期回收 ~2.5s。
3. **σ 内容寻址内化（关键解锁项）**：为 `Subst`/`VSub` 包裹建 thread-local
   内容寻址 canonical 表，使"逻辑相同的 σ/包裹"共享指针——此后
   FRCS_MEMO、quote memo、渲染缓存全部开始跨分支命中。这是把"按指针键
   缓存全部失效"的死结解开的唯一结构项。
4. **模式编译器分支缓存**：ret_type 重锚（quote→eval）与构造子探测结果
   按 (臂, canonical σ) 缓存；`checked_ret` 跨分支复用口径复核。
5. **孪生版同批**：孪生 frcs/XCell 尚无 FRCS_MEMO 等价物，round 3 未动
   孪生，parity 未跑（首测即栈溢出的行为由 1+2 缓解后应可跑完）。
6. 验收口径不变：`l13_fast_parity` / `l13_into_probe` / 全量 `cargo test`
   / examples `typort check` / 65 例裸语言 diff / l13bench ≤1.5×（基线
   prelude-core basic 22.4ms / fast 12.8ms，prelude-hdl 3080ms / 1321ms，
   见 `docs/bench-matrix-2026-09-12.md`）。

## 历史根因记录（第二轮回退时的定性，部分已被第三轮修正）

1. ~~"一个 meta/中性头被累积应用到约 7.8 万个 VSub 包裹的实参上"~~
   → 第三轮修正：是长 List 值逐节点 VSub 包裹后的 quote 展开树，见上。
2. 参考版 quote 无记忆化且 `quote_sp` 递归 ⇒ 8MB 测试栈爆栈；迭代化 +
   记忆化后能跑完但慢——**仍成立**（默认测试栈下 parity 崩因）。
3. ~~calc_err_* 报错文案回归~~ → 第三轮实测不复现。
4. "frcs 重建 + memo 失效"是次因——**仍成立**，round3 的 FRCS_MEMO 即
   针对此项。

## 附带发现（对文档的订正）

`docs/pattern-match-refinement-analysis.md` 的复现程序经移植前后对照：
**显式替换未使任何"失败→成功"发生**，且其中 weak01/02/04 与文档的
`vtail` 控制例本身即类型错误（文档基线也自认"正确拒绝"），weak03 现状
已通过。该文档的"一般性缺陷"论断过度概括，已在
`docs/explicit-subst-refactor-status.md` 记录订正。
