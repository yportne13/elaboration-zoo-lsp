# L07–L12 评审修复轮记录（2026-09）

对应 [FINAL.md](FINAL.md) §7 的建议处置顺序。规模：39 文件、+1091/−373。
全部改动经六层 parity + blackbox + 各层 lib 测试复验（见 §3）。

## 1. 已修（代码）

| 发现 | 处置 | 验证 |
|---|---|---|
| D2 P1：孪生 `vapp1` Clo 臂尾调 `eval_iter` 清空宿主循环的共享 work/vals/icits（外层 pending 项静默丢失） | 六层孪生改 `mem::take` 暂存/还原 | 各层 parity 加 `parity_vsub_slot_nested_let_workbuf`；L07 先红（ref Err / twin Ok 分裂）后绿 |
| D4 F1：frcs 解析应用守卫 λ 分叉（ref 排除 `Lam` / twin `vapp_ok` 放行） | 六层参考版对齐放行 λ（只改 frcs 守卫，不动共用于 η 臂的 `v_applicable`） | 守卫逐点等价 + 六层 parity 绿 |
| D4 F2：L10/L11 漏移 `bbcf214`（quote 的 VSub 防御臂） | 补 `Val::VSub(v, _) => self.quote(.., v)`（对齐 L07/L08/L09/L12 及各层孪生） | 六层 parity + lib 绿 |
| D3 P1-3：typeclass 求解器 `panic!("Too much effort :(")` | L10/L11/L12 改返回 `None`（调用点已按 `is_some()` 过滤，降级为常规 can't-solve） | lib 测试绿 |
| D3 P1-4：文件 IO 内建对 IO 失败 panic | L07/L08 参考版+孪生改为卡住降级（与"实参非字面量"同口径） | blackbox v2 三个 panic 契约用例改写为降级契约并绿（`v2_file_*_stuck_not_panic`） |
| D3 P1-5：`eval_aux` typ 非 Sum（L10–L12 孪生 panic；L09 双版 panic） | 统一空表降级（Con 模式全按变量模式命中） | 六层 parity + lib 绿 |
| D3 P1-2：卡住 match 被应用 → `panic!("impossible apply")` | **未根治**（pending 实参吸收是功能级移植）；L10/L11/L12 模块头补 L09 同款已知限制说明 | 文档 |
| D3/D1：燃料护栏缺口 | L09 `unify` 入口回植 burn（孪生按 `UItem::Pair` 烧同一 `PM_FUEL` 池）；L10–L12 参考版 `check_pm*` 入口补 `refuel()` | 六层 parity + lib 绿 |
| D3：`lvl2ix` 裸减法下溢（L11/L12） | 补 L07 同款护栏（`debug_assert!` + release 降级 `Ix(0)`） | 编译 + 测试绿 |
| D3：值层投影 `find().unwrap()` / panic（L09–L12） | 参考版改全函数（查不到 / typ 非 Sum / 形态不合 → 中性 `Obj`，对齐 L07 `project()`） | 六层 parity + lib 绿 |
| D1 P2 + D5 P2-1：L12 canonical 读点未 force；HashMap 迭代序泄漏 | 候选类型与闭包应用结果逐次 force；decl 候选按名排序（跨进程确定）；逐候选 refuel 提到循环开头 | L12 parity + lib 绿 |
| D2 P2-2：L07 孪生 10 处 transmute 无 SAFETY 注释 | 全部补 SAFETY 注释（记录真实不变式与借出期纪律）；**未**加借出点 clear——L07 共享 workbuf 架构下与内核入口 clear 重复、盲目清有风险，该纪律现由回归测试守 | 编译 + parity 绿 |
| D6 P2-5：L07 parity 的 Err oracle 只判同型不比正文 | 移植 L12 `norm_err`，Err 正文归一化后逐字节比对 | **64 例全绿**——两版 Err 正文本就一致（NV-2 得到正面结论），oracle 与其余五层同级 |
| D4 F4 / D6 P2-3：§9.5 钉死测试未复刻 | L08 `tests.rs` 补 `test_fn_typed_index_slot_applied_after_refine` 与 `test_deep_pattern_fuel_budget_regression`（d=400），均绿 | lib 绿 |
| D6 P3-2 / D1 P3-3 / D6 P2-4：文档滞后 | L09/L10/L11 README 燃料条订正；L11/L12 孪生模块头机制段重写（update_cxt/refresh → 显式替换）；L09 孪生两处陈旧注释；顶层 README/README.zh 架构表给 L08–L12 补显式替换标注；测试计数订正（v3 86→47、L07 44→45、L08 77→80/81、design doc §7） | 文档 |

## 2. 新发现并登记（本轮实测；`git stash` 基线对照确认**非本轮改动引入**）

- **L09–L12 在 §9.5 两个哨兵程序上非终止**（L07/L08 同程序正常）：
  - ① "已解 rigid + 非空 spine"解析应用：`enum Foo(f: Nat -> Nat) { mk -> Foo (n => n) }`
    + `def t(g: Nat -> Nat, w: Foo g): (P : Nat -> U) -> P (g zero) -> P zero`；
  - ② 深嵌套模式 + 通配兜底（`case cons(h0, cons(h1, …))` + `case _`）：
    实测 d=10 亦超 150s（疑与决策树编译的抛空 pats / 覆盖判定缺陷同源）。
  两程序**不入 L09–L12 的 parity 套件**（会挂住进程），各套件内留解释注释；
  登记于 `docs/explicit-subst-refactor-status.md` §3。后果：§9.5"各层移植
  必须复刻"在该四层无法兑现，需专项定位（不终止的输入类）。
- **D3 P1-2（卡住 match 被应用）保持文档化不修**：根治需给 `Val::Match`
  加实参吸收（pending），属功能级移植；已在 L10/L11/L12 模块头登记。
- **L11/L12 parity 剔除的 GADT/依赖索引族**：原"另案跟踪"在仓库中无案，
  现登记于 status doc §3（与上述两项挂起同源的可能性待查）。

## 3. 验收（本轮实测）

| 目标 | 结果 |
|---|---|
| `l07_fast_parity` | 64 通过 |
| `l08_fast_parity` | 81 通过 |
| `l09/l10/l11/l12_fast_parity` | 32 / 33 / 38 / 37 通过 |
| `l07_blackbox` (+v2/v3) | 48 / 51 / 91 通过（各 1–2 ignored） |
| `l08_blackbox` (+v2) | 57 / 51 通过 |
| `--lib` L07/L08/L09/L10/L11/L12 | 45 / 51 / 5 / 14 / 22 / 23 通过 |

## 4. 未做（留给后续）

1. 卡住 match 的 pending 实参吸收（L09–L12，功能级移植）；
2. L09–L12 §9.5 两项非终止的根因定位与修复；
3. L09–L12 最小 blackbox 契约套件；L09/L10/L11 `mod.rs` 零断言 `test*`
   补断言；
4. L11/L12 parity 剔除族的 walk 用例补测；
5. bench 补 σ 深链负载（D5 P2-4）；L09/L10 参考版 `Infer::clone` →
   `simpl_decl`（D5 P2-2）；L07/L08 force 卡住 Match 臂的 scrutinee 深拷贝
   （D5 P2-3）；
6. D2 P2-1 `Rc<SubstV>` 跨轮泄漏（bump 不跑 Drop）——需表示层改造，或
   至少在文档标注泄漏上界。
