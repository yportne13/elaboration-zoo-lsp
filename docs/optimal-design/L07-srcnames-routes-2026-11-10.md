# L07 `src_names` 两条路线实测对比（2026-11-10）

> 基线 `master` @ `1f382a2a`（decl COW + FxHash 已落地）。两条路线均在独立 scratch worktree
> 实现，**未 commit**；同一台机器、release、`l07bench` 标准负载 + 自建深作用域探针。
> 路径：A = `C:\ezl-src-own`，B = `C:\ezl-src-trail`；二进制在 `C:\ezl-src-bench\`。

## 0. 结论

| 路线 | 实现 | diff | 深作用域（lam/let） | 现有 l07bench | 判定 |
|---|---|---|---:|---:|---|
| **A：所有权/`&mut Cxt`** | `push_bind/pop_bind` 系列 + `check/check_ty/infer_expr` 改 `&mut Cxt`；8 处 binder scoped push/pop，`locals` 用 move 入链/恢复 | **+306/−67**（4 文件） | **−55%~−58%（≈2.3×）** | 中性（±5% 散点） | **只推荐 A**；需补 pattern_match 7 处 binder + unification η 1 处（0.5–1.5 人日）才完整 |
| **B：L08 name_map+trail** | `Cxt` 内共享 `NameState{map,trail}` + `name_mark`，bind/define O(1)，lookup 前按 mark 惰性 unwind | **+132/−34**（3 文件） | −6%~−13% | 中性（±5%） | **不推荐**：仅拿到名字表那一份，剩余 O(n²) 在 `Locals` Box 链；引入 RefCell/作用域纪律风险 |

**一句话**：两条路线都不改善现有 L07 语料；但深嵌套 binder 上 A 是 **2.3×**、B 只有 **~10%**。
若必须选一条落地，选 **A**，并把 pattern_match 的 7 个模式 binder 收尾；B 单独做性价比不够。

## 1. 路线 A（所有权/`&mut Cxt`）

- `Cxt` 新增 `push_bind/push_new_binder/push_define/pop_bind`（`&mut self`；`BinderUndo` 只保存
  O(1) 的 env/lvl/pruning/key/prev；`locals` 用 `mem::replace` move 入链、pop 时解包恢复——连
  `Box<Locals>` 的 O(深度) 深 Clone 也消掉；prev 用于同名遮蔽回写）。
- `check/check_ty/infer_expr` 全链路 `&mut Cxt`；Lam/隐式 Π/Let/Pi/Lam 推断/App 隐式 fallback
  **8 处 binder** 改 scoped push+pop；错误路径统一"先 pop 再 `?`"。
- 覆盖：`L07_BINDER_STATS=1` 实测覆盖路径 `Rc::strong_count==1` **100%**（demo 32/32、
  church 50/50、bits_adder 52/52），`pop_shared=0`；总覆盖（calls/(calls+legacy)）60–91.4%，
  未覆盖为 pattern_match walk/walk_con 的 **7 处模式 binder** 与 `unification.rs:947` η 1 处。
- 验收：lib 70；blackbox 48+1 / 51+2 / 116+1；`l07_fast_parity` 97；l07bench 节点断言全过；
  期间修过同名遮蔽 pop 未写回 prev 的真 bug（blackbox 兜住）。

## 2. 路线 B（L08 name_map + name_trail）

- `Cxt.src_names: Rc<FxHashMap>` → `NameState { map: FxHashMap, trail: Vec<(name, old)> }` +
  `Cxt.name_mark`；bind/define = unwind(摊销 O(0)) + 1 insert + 1 trail push = **O(1)**；
  lookup 仍 O(1)（多 2 次 RefCell borrow）；每次访问前把 trail 裁回本上下文 mark（惰性作用域退出）。
- 覆盖全部 bind/define/new_binder/subst_cxt 与 lookup；`new_binder` 不进表；`subst_cxt` 走轨迹。
- 风险：stale binding 依赖"深度优先作用域纪律"（release 无断言）；RefCell 重入 panic 面；
  错误路径靠惰性回退。测试全绿（lib 70 release+debug、blackbox、parity 97、bench 断言）。
- 根因限制：深作用域剩余 O(n²) 在 `Locals` Box 链（`syntax.rs:10-14`），本路线只消掉名字表一项，
  所以只有 ~10%。

## 3. 性能数据（min-of-3，两次顺序交错，ms）

### 3.1 深作用域探针（N 层嵌套 λ / let）

| 负载 | n | base | A | A Δ | B | B Δ |
|---|---:|---:|---:|---:|---:|---:|
| lam | 250 | 33.479 | **14.236** | **−57.5%** | 30.253 | −9.6% |
| lam | 500 | 158.133 | **68.239** | **−56.8%** | 143.284 | −9.4% |
| lam | 1000 | 638.247 | **287.394** | **−55.0%** | 601.367 | −5.8% |
| let | 250 | 26.366 | **11.628** | **−55.9%** | 22.865 | −13.3% |
| let | 500 | 113.195 | **48.069** | **−57.5%** | 102.470 | −9.5% |
| let | 1000 | 466.594 | **196.799** | **−57.8%** | 423.285 | −9.3% |

- A 在两种深链都是 **2.3×**；但 T(2n)/T(n) 仍 ≈4.1–4.8×，说明还有第三方 O(n²)（A 已消掉
  `src_names` map 复制与 `Locals` Box 深拷两项，仍未到线性，需再 profile）。
- B 的 T(2n)/T(n) 同样 ≈4.1×，与"只拿名字表 ~15%"的预期一致。

### 3.2 现有 `l07bench` 负载（k=9..13，basic）

两条路线与 base 的差异全在 **±5–7% 散点**内，无一致方向：A 在 church k13 +6.3%、global k11
−4.9%、strchain k11 −5.0%；B 在 church k13 +9.8%、match/strchain 基本 0；其余噪声。
**现有负载作用域浅（K≲5），两条路线都没有可复用收益。**

## 4. 复现与产物

```powershell
# A: C:\ezl-src-own, target C:\ezl-target-own
# B: C:\ezl-src-trail, target C:\ezl-target-trail
# 深探针（临时 bin，已拷入三个 worktree）：deepbench.exe <n> <rounds>
C:\ezl-target-deep-base\release\deepbench.exe 1000 3   # base
C:\ezl-target-own\release\deepbench.exe 1000 3         # A
C:\ezl-target-trail\release\deepbench.exe 1000 3       # B
```

产物：`ROUTE-OWN.md` / `ROUTE-TRAIL.md`；patch `C:\ezl-src-bench\l07-name-trail.patch`；
二进制 `l07bench-own.exe` / `l07bench-trail.exe`；A/B 原始日志 `C:\ezl-src-bench\ab2\`。

## 5. 建议

- 若目标只是**现有 L07 课程负载**：两条都不落地（保持现状，避免 RefCell/API 改动）。
- 若目标覆盖**深嵌套 λ/let**（教学/生成语料可能出现）：选 **A**，并完成 pattern_match 的 7 处
  binder 与 unification η 1 处，再做 N=200–2000 的计时钉；预计完整收益仍非严格线性（第三方
  O(n²) 需另行定位）。
- **B 不单独落地**；若未来做 `Locals` Rc 化，可把 B 的 name_map/trail 作为其中一部分一起上，
  单独做只有 ~10% 且引入风险。
