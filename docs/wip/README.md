# L13 显式替换移植：未落地尝试的证据存档

L13（生产层）的显式替换移植**代码已完成且裸语言语义正确**，但因
prelude/calc 路径的规模放大未通过验收，**已回退到 HEAD 状态**。
本目录保存该尝试的补丁与结论，供后续接续。

## 产物

- `l13-explicit-subst-round1.patch`：第一轮移植（参考版 + 孪生版，8 文件
  / +1599−452）——裸语言语料 65 例逐字节 diff = 0，但 prelude 挂起。
- `l13-explicit-subst-attempt.patch`：第二轮修复尝试（在上者基础上加
  `frcs` 入口 `mentions_level` 快路径、`wrap_sub` 展平、`compose` 去重、
  `quote_sp` 迭代化 + 顶层 quote 记忆化、`subst_cxt` 条件包裹）——挂起
  被缓解为"可完成但 ~198s（移植前 5.34s）"，`l13_fast_parity` 仍红。

## 根因（两轮诊断的最终结论）

1. **真正的放大源**：移植后 calc/prelude 路径会构造出**巨型卡住应用**
   ——单次顶层 `quote` 扇出 77,811 节点、祖先链 12,287 层（形状画像
   `Flex=1, Rigid=4, VSub=77,806`），即一个 meta/中性头被累积应用到约
   7.8 万个 VSub 包裹的实参上。`calc_two_step`（226 字节源码）触发
   force 2.06e7 次 / quote 1.11e7 次 / frcs 1.0e7 次。
2. **参考版 quote 无记忆化且 `quote_sp` 递归**（孪生版有 memo + 迭代），
   沿长 spine 逐项吃原生栈帧 ⇒ 8MB 测试栈爆栈；迭代化 + 记忆化后能跑完
   但慢（198s）。
3. **语义回归**：`calc_err_by_no_proof` / `calc_err_by_wrong_position`
   报错文案在移植后改变（移植前 `name not in scope: calc`，移植后 unify
   报错）——parser/macros/preprocess 逐字节一致，差异只在 elaboration
   层。即显式替换改变了 calc 宏展开后的报错走向。
4. 上一轮诊断的"frcs 重建 + memo 失效"是**次因**：`frcs` 入口
   `mentions_level` 快路径命中约 58%，剩余 4M 次慢路径仍是主开销，但
   单独加它不消除挂起。

## 接续建议

1. 先定位"为何 calc 展开在 σ 机制下累积出 ~7.8 万实参的卡住应用"——
   这是与 L07–L12 的本质差异（那些层的 prelude 规模未暴露此病理）。
   重点检查 `v_app`/`unify` 入口 `Rc::new(Val::VSub(...))` 与 `unify_pm`
   回退路径的实参累积。
2. 参考版补 quote 记忆化 + `quote_sp` 迭代化（本身是独立收益，注意
   memo 必须持有输入 `Rc<Val>` 的 keepalive——缺它地址复用会给出错误
   结果，第一版曾因此假绿）。
3. 若要缩小移植面：先只移植"载体"、保留 L13 既有 `infer_expr_pm` /
   `is_refined` 路径，分步对齐。
4. 验收仍需：`l13_fast_parity` / `l13_into_probe` / 全量 `cargo test` /
   examples `typort check` / `l13bench` / 65 例裸语言 diff。

## 附带发现（对文档的订正）

`docs/pattern-match-refinement-analysis.md` 的复现程序经移植前后对照：
**显式替换未使任何"失败→成功"发生**，且其中 weak01/02/04 与文档的
`vtail` 控制例本身即类型错误（文档基线也自认"正确拒绝"），weak03 现状
已通过。该文档的"一般性缺陷"论断过度概括，已在
`docs/explicit-subst-refactor-status.md` 记录订正。
