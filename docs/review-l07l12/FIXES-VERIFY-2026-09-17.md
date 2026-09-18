# FIXES.md 落地核验（2026-09-17）

> 本文件是对 [FIXES.md](FIXES.md)「已修」清单的**代码核验记录**，并登记当轮
> 实际落地的修复。起因：2026-09-17 L07 代码评审发现 FIXES.md 声称的部分
> 修复在工作区不存在，逐项复核后确认**整个修复轮未落在本仓库任何 ref 上**
> （`git log --all -S "parity_vsub_slot_nested_let_workbuf"` 零命中、
> `git log --all -S "v2_file_read_missing"` 只命中引入 panic 契约的
> `2e9efcc`、`git stash list` 无相关条目、无同名分支）。

## 1. 核验结论：三处「已修」与工作区不符（评审前状态）

| FIXES.md 声称 | 核验结果（master @ 8dabd63 + 未提交工作区） |
|---|---|
| D2 P1 孪生 `vapp1` Clo 臂 workbuf 清空已修（`mem::take` 暂存/还原 + 回归测试 `parity_vsub_slot_nested_let_workbuf`） | 回归测试不存在；`vapp1` 路径无 `mem::take`（仅 conv scratch 有）。**同类问题经 VSub→闭包路径仍可复现**（见 §2-①，ref Ok / twin Err） |
| D3 P1-4 文件 IO panic 改卡住降级（"blackbox v2 三个用例改写为降级契约 `v2_file_*_stuck_not_panic`"） | `mod.rs` 四个文件臂仍 `panic!`；v2 现行用例是 `v2_file_read_missing_panics` / `v2_file_delete_missing_panics` / `v2_file_write_bad_path_panics`，**钉的是 panic 契约** |
| D4 F1 frcs λ 守卫对齐（"六层参考版对齐放行 λ，只改 frcs 守卫"） | 参考版 frcs 仍用共用的 `v_applicable`（不含 `Val::Lam`）；孪生 `vapp_ok` 对 Clo tag 放行——**分叉仍在**（被"期望类型重锚"纪律大面积掩盖，parity 照绿） |

其余各条（L09–L12 燃料护栏、`lvl2ix` 下溢、typeclass effort panic、投影
全函数化等）未逐条核验；按上表结论，**该轮修复整体应按"未落地"处理**，
需要时重做。

## 2. 2026-09-17 L07 评审轮实际落地的修复

① **孪生 `vapp1` VSub→闭包重入清栈（P0，ref/twin 判定分裂）**：
臂上下文 `subst_cxt` 把 let 绑定的 λ 槽包成 VSub → `Tm::Var` 的 tag-1
快路径把 tag-7 值当"非闭包"压进 vals → `ChainWrap`/`Apply`/`AppPrunOne`
带本循环在飞的 work/vals 调 `vapp1` → VSub 臂 force 出闭包 → 闭包臂用
**调用方的缓冲**重入 `eval_iter`，入口 `clear()` 静默截断外层任务
（注解求值拿到部分应用闭包 `(y => y)` 而非 `zero`，快版误报 can't
unify）。修：VSub→闭包 β 改用本次私有草稿栈（`force` 同款纪律，:1390
注释既是同款先例）。回归钉 `parity_vsub_slot_applied_closure_workbuf`
（`tests/l07_fast_parity.rs`，Ok 期望值断言，非双盲）。

② **frcs 头可应用守卫放行 λ（D4-F1 补落地）**：参考版 frcs Rigid 臂
`!v_applicable(&head)` → `!matches!(head, Val::Lam(..)) && !v_applicable(&head)`
——解值是 λ 且读点带实参是良型形态（β），η 臂共用的 `v_applicable`
语义不变（λ 与不可应用值相遇仍不展开）。

③ **文件 IO 失效降级（D3 P1-4 补落地）**：`file_read/write/append/delete`
四个臂改 `None`（卡住），与"实参非字面量"同口径；参考版 + 孪生同步。
v2 三个 panic 契约改写为 `v2_file_*_stuck_not_panic`（读缺失物化卡住
prim；写/删失败断言 Ok + 文件不存在），`check_panic` 辅助函数随之删除。

④ **`eval(Tm::Prim)` 零元头（评审新发现）**：旧实现把**现场 env 全槽**
收进 spine，只在 builtin λ 链体的正典路径下正确；quoted Prim 在其它
env 下重求值（`fresh_meta` 的 close_ty 闭包体、`solve` 的 `lams`、
`prune_meta` 的类型重求值）会捕获无关 env 槽、spine 长度失真 → unify_sp
长度失配误报。修：`Tm::Prim` 改零元卡住头，builtin 值体 = λ 链 →
`((Prim 名 p1) p2 …)` App 链，实参一律经 App 到达；参考版 `cxt.rs
add_builtin` + `mod.rs eval`、孪生 `prime_round` + `eval_iter` 同步。

⑤ **孪生 Match/Match 交错序对齐（评审新发现）**：旧实现把分支数/模式/
pending 长度与 icit 检查整体**前置**，而参考版是惰性交错（scrutinee 合一
→ 分支数 → 逐分支模式+体 → pending 长度 → 逐 pending icit+值）；spec
合一的 Err 经 `unify_indices` → `Walk::Unreachable` 后**编译继续**，Err
路径上 scrutinee 合一的 meta 副作用可观测（"unify 错误均致命"的论证
不成立）。修：新增 `UItem::MatchPrecheck` / `MatchPendingLen` /
`MatchPending` 三个屏障任务 + `MatchBranch` 携带模式引用，逐点对齐。

⑥ **探测独立充值燃料（评审新发现）**：`probe_accessible` 入口
`meta_refuel()` / `fuel.set(UNIFY_FUEL)`（双版同点）——多构造子枚举的
逐 ctor 探测不再互相挤占；探测状态本已回滚，只有燃料单向消耗。

### 文档/登记项

- README §6 增「代码评审轮（2026-09-17）」行；§7 增已知限制 6（深值原生
  递归吃栈，双版同形）与 7（孪生 σ 的 Rc 跨轮不回收）；§7.2/§8 计数与
  契约表述同步。
- 孪生模块头：σ 生命周期表述改为"仅**可读性**上单轮"（bump `reset()`
  不跑 Drop，arena 内 `XCell::VSub` 的 Rc 克隆跨轮不递减）；`env_len`
  注释去掉已移除的 Prim env 收集。
- `parser/mod.rs` 删除恒等函数 `extract_base`（两臂都原样返回）；
  `elaboration.rs` `ty_precheck` 错误文案由 `Val` 的 Debug 转储改
  `pretty_tm` 渲染（`"expected universe"` 前缀被 v3 钉住，保持）。
- 误报澄清：评审子 agent 报的孪生 `typ_tm` 未使用（:6121/:6232）不成立
  ——两处随后都用于 `self.eval(..., typ_tm)`。

## 3. 验收（本轮流后实测）

| 目标 | 结果 |
|---|---|
| `--lib L07_sum_type` | 45 通过 |
| `l07_fast_parity` | 66 通过（含新回归钉） |
| `l07_blackbox` / `_v2` / `_v3` | 48+1ignored / 51+2ignored / 91+1ignored 通过 |

## 4. 仍未做（本仓库待办）

1. §1 表中未核验的其余 FIXES 条目（L09–L12 侧）——若确认未落地需重做；
2. 深值原生递归的迭代化（README §7.6，LSP 接入前置）；
3. 孪生 `Rc<SubstV>` 跨轮回收（README §7.7，需表示层改造或热路径登记）。
