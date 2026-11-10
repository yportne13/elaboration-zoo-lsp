# L08-PORT：把 L07 已验证的性能优化移植到 L08 参考版

> 分支 `feat/l08-hardening`（worktree `C:\ezl-wt-l08`）· 基线 `feat/all-layers-hardening` @ `deef97f7`
> （含 `07f737d6` L08 merge 残留编译修复 + `deef97f7` L07 Pi-move）· **未 push**
> 构建：`CARGO_TARGET_DIR=C:\ezl-target-all-l08` · 时点 2026-11-10 05:00–06:30

## 0. 结论（TL;DR）

- 已按 L07 模板在 L08 参考版落地 **4 项**（每项独立 commit）：Locals Box→Rc、FxHashMap、
  decl COW 就地写、**name_map+trail**。
- **全部 L08 套件绿**：lib 60（release + debug 各 60）/ blackbox 57(+1 ignored) /
  blackbox_v2 51(+2) / fast_parity 95；`l08bench` 节点数断言（闭式 + 双实现互检）全部通过。
- **大幅提速**（`l08bench --only basic`，k=11，5 对交错、中位数，相对 `deef97f7`）：
  **strchain 127.1→9.6 ms（13.2×）、global 141.4→18.0 ms（7.8×）、struct 138.6→17.7 ms（7.8×）**。
- item4（name_map+trail）在标准 l08bench 上**中性**（7 对交错 A/B 中位数 0.96–1.05，噪声内），
  但在**深作用域探针**上显著：deep-let n=500/1000 **−24.9% / −22.3%**（与 L07 `d411debe` 同量级）。

## 1. 提交清单

| # | commit | 对应 L07 模板 | 内容 | diff |
|---|---|---|---|---|
| 1 | `535bb4be` | `65d4512a` Locals Box→Rc | `syntax.rs` `Bind/Define(Rc<Locals>)` + `close_ty` 改 `mcl.as_ref().clone()`；`cxt.rs` 3 处 `Box::new`→`Rc::new` | +13/−8（2 文件） |
| 2 | `9f159a97` | `72f12101` FxHashMap | `cxt.rs`：`Decls` 别名 / `src_names` / `empty()`；`mod.rs`：`mutable_map`、import | +11/−8（2 文件） |
| 3 | `5c56d27c` | `c2fffd3f` decl COW 就地写 | `Cxt::decl_insert_mut` + `decl_insert` 包装；`Cxt::new`/`add_builtin` 用 mut；`Infer::infer_owned` + `infer` 兼容包装；Def/Enum 占位与注册就地写；`run`/`bench_check`/`bench_check_nf` 改用 owned 链 | +56/−39（3 文件） |
| 4 | `a3652630` | `d411debe` name_map+trail | `NameState{map,trail}` + `Cxt.name_mark`；`bind/define/new_binder/subst_cxt` 改 O(1) 轨迹写；`lookup_src`/`has_src` 惰性 unwind；elaboration 3 个查表点 | +135/−24（3 文件） |
| 合计 | 4 commits | — | 5 文件（cxt/elaboration/mod/pattern_match/syntax） | **+215/−79** |

均基于 `deef97f7`（前 3 个已由 Lead merge 进 `feat/all-layers-hardening`），工作树干净；未改 L07、
未改 master/main worktree、未 push。

## 2. 逐项说明与依据

### 2.1 Locals Box→Rc（`535bb4be`）
- L08 `syntax.rs` 的 `Locals` 仍是 `Box<Locals>` 链；`Cxt::bind/define` 每次
  `self.locals.clone()` 深拷 O(深度)，n 个嵌套 binder ⇒ O(n²)。
- 照 L07/L13 改为 `Rc<Locals>`：clone O(1)，`close_ty` 克隆尾链 Rc。
- 现有 7 个 l08bench 负载上收益 −3~−5%（与 L07 同为"深作用域负载才显著"）。

### 2.2 FxHashMap（`9f159a97`）
- L08 三张热表仍是 std `HashMap`（SipHash）：decl 表（`Decls` 别名）、`src_names`、`mutable_map`。
- 换 `rustc_hash::FxHashMap`（key 全是 `SmolStr`/`String`，无 map 顺序依赖——`simpl_decl` 只重建表）。
- L08 无 `simpl_cache`（L07 的 `ver` 旁表缓存属另一项，未移植）；`unification.rs` 的 `ren: HashMap`
  未动（与 L07 的 Fx 移植范围一致，留待单独评估）。

### 2.3 decl COW 就地写（`5c56d27c`）
- L08 `Cxt::decl_insert(&self)` 先 `self.decl.clone()` 再 `Rc::make_mut`：强计数恒 2 ⇒ **每个顶层
  def/enum/构造子都深拷整张 decl 表**；strchain/global/struct 各生成 2^(k+1) 个 def ⇒ O(D²)。
- 照 L07：`decl_insert_mut(&mut self)`（无前置 clone）+ `decl_insert(&self)` 浅克隆包装；
  `Cxt::new`/`add_builtin` 改就地；`Infer::infer_owned(Cxt, Decl)` 接管所有权（`RC=1`），
  `Infer::infer(&Cxt, Decl)` 保留为兼容包装；`run`/`bench_check`/`bench_check_nf` 改 `cxt = new_cxt` 链。
- 语义注意（与 L07 同）：占位与最终条目现在写进同一张表（不再扔进克隆表）；无消费者依赖此差别
  （`Decls` 在本基线无 `ver` 计数）。

### 2.4 name_map+trail（`a3652630`）
- L08 `Cxt.src_names` 是**按值** `FxHashMap<String,(Lvl,VTy)>`：每次 `bind`/`define` `clone()` 整表
  （O(作用域名数)，且每条 `(Lvl,VTy)` 会深拷 `VTy` 的 `Val` 树）⇒ n 个绑定器 O(n²)。
- 照 L07：`Cxt` 改持 `Rc<RefCell<NameState{map, trail}>>` + `name_mark: u32`；条目改
  `Rc<(Lvl,VTy)>`（lookup 克隆 = 一次引用计数）；`bind/define` 先 `unwind(name_mark)` 再
  insert+trail push（O(1) 摊销）；`lookup_src`/`has_src` 每次访问前惰性回退；`new_binder` 不进表；
  `subst_cxt` 走轨迹逐条包 `VSub`（可逆）。
- 作用域纪律：所有访问前先把轨迹裁回本上下文 mark（深度优先假设）；`unwind` 里
  `debug_assert!(mark <= trail.len())`。L08 侧 bind/define 调用点已按 L07 同口径审计
  （elaboration 7 / pattern_match 8 / unification 1 + `subst_cxt`），debug 档 lib 测试通过。

## 3. 门禁（全绿）

| 套件 | 结果 |
|---|---|
| `cargo test --release --lib L08_product_type` | ✅ **60 passed** |
| `cargo test --lib L08_product_type`（debug，校验 `unwind` 的 debug_assert） | ✅ 60 passed |
| `cargo test --release --test l08_blackbox` | ✅ 57 passed / 0 failed / 1 ignored |
| `--test l08_blackbox_v2` | ✅ 51 passed / 2 ignored |
| `--test l08_fast_parity` | ✅ **95 passed** |
| `l08bench` 节点数断言（church/strchain/global/struct 闭式 + match/enum/natadd 双实现互检） | ✅ 全部 k 通过 |
| `cargo build --release --bin l08bench` | ✅ |

原始日志：`C:\ezl-src-bench-l08\{item1,item3,item2,final,item4}-tests.txt`、`item4-debug-tests.txt`。

## 4. 性能（l08bench，`--only basic`，k=11，`--rounds 3`）

### 4.1 逐项 A/B（相对 `deef97f7` 基线，3 对交错、每侧 3 轮 min）

| workload | baseline | +Locals Rc | +FxHash | +decl COW（= final，item1–3） |
|---|---:|---:|---:|---:|
| church | 3.35 ms | 0.962 | 0.990 | **0.953** |
| strchain | 127.1 ms | 0.982 | 0.925 | **0.076（13.2×）** |
| global | 141.4 ms | 0.956 | 0.941 | **0.128（7.8×）** |
| struct | 138.6 ms | 0.967 | 1.106* | **0.127（7.8×）** |
| match | 0.144 ms | 0.952 | 0.830 | **0.868** |
| enum (k=9) | 0.284 ms | 0.969 | 1.015 | **0.912** |
| natadd | 9.61 ms | 1.115* | 0.954 | **0.856** |

\* 单点噪声（该 batch 期间有其他 agent 构建/bench 干扰；`struct` 的 +10.6% 与 `natadd` 的 +11.5% 未复现）。

### 4.2 最终 A/B（`l08bench-baseline.exe` vs `l08bench-final.exe`，5 对**反向交错**，中位数/最小值）

| workload (k=11) | baseline (ms) | final (ms) | ratio |
|---|---:|---:|---:|
| church | 3.346 | 3.189 | 0.953 |
| strchain | 127.109 | 9.607 | **0.076** |
| global | 141.384 | 18.035 | **0.128** |
| struct | 138.637 | 17.663 | **0.127** |
| match | 0.144 | 0.125 | 0.868 |
| enum (k=9) | 0.284 | 0.259 | 0.912 |
| natadd | 9.613 | 8.228 | 0.856 |

### 4.3 item4 专项（`l08bench-final.exe` = item1–3 vs `l08bench-item4.exe`，7 对交错、中位数）

| workload (k=11) | pre-item4 (ms) | item4 (ms) | ratio |
|---|---:|---:|---:|
| church | 3.662 | 3.606 | 0.968 |
| strchain | 10.490 | 10.593 | 1.021 |
| global | 20.096 | 20.128 | 0.994 |
| match | 0.125 | 0.128 | 1.024 |
| enum (k=9) | 0.267 | 0.259 | 0.963 |
| struct | 18.545 | 18.370 | 1.017 |
| natadd | 9.294 | 10.214 | 1.051 |

→ **标准负载中性**（与 L07 `d411debe` 的 "existing corpus neutral" 一致）。

**深 let 链探针**（临时测试，已删除；`run()` 端到端、min-of-4、256MB 栈）：

| n | pre-item4 (ms) | item4 (ms) | Δ |
|---:|---:|---:|---:|
| 250 | 17.098 | 15.524 | −9.2% |
| 500 | 69.588 | 52.294 | **−24.9%** |
| 1000 | 273.441 | 212.428 | **−22.3%** |

（L08 无深 λ/let bench 负载；L07 同探针 item4 增量 −18~−25%，量级一致。比值仍有 >2×/翻倍，
剩余平方项在 parser/递归检查路径，不在名字表——与 L07 巡检结论一致，属另一议题。）

### 4.4 口径与归因

- 归因：strchain/global/struct 的 6.5–13× 全部来自 **decl COW**（O(D²)→O(D)）；Locals Rc + FxHash
  贡献常数级 −3~−5%；item4 只在深作用域路径上显著（标准负载中性，符合 L07 结论）。
- 口径：同机隔离进程、`--rounds 3`、每侧取多次运行的中位数/最小值、A/B 反向交错。
  **机器为共享环境**（其他 route 的 agent 同时在构建/bench，绝对 ms 有 ±20–30% 窗口漂移），
  故以**同窗口交错比值**为准。首轮 item4 A/B（05:57 窗口）出现 strchain/global +9%，
  5 分钟后重测（7 对）回到 +2%/0%——判定为首轮窗口被 l12 bench 干扰，记录在案。
- 基线/各阶段 exe 与原始日志均在 `C:\ezl-src-bench-l08\`。

## 5. 风险与注意事项

1. **语义**：四项均无语义变化（表示/哈希/所有权/名字表实现），但 decl COW 改变"占位只存在于
   克隆表"的实现细节——占位与最终值现在落在同一张表；本基线无 `Decls::ver`/simpl 缓存，故无可观测
   差别；若后续回移 L07 的 `ver` 缓存需重新审（占位会造成两次 ver 递增，L07 亦然）。
2. **`infer_owned` 的移动语义**：调用方（`run`/`bench_check*`）在 Err 分支直接返回，Ok 分支重新绑定
   `cxt`；`infer(&Cxt)` 保留兼容包装（tests 未直接用它）。
3. **name_map 作用域纪律（item4 主要风险）**：惰性回滚依赖"深度优先、不在访问浅 Cxt 后再用深
   Cxt"；L08 调用点已审计，`unwind` 有 `debug_assert`，debug 档 lib 测试通过。但 release 无断言：
   未来若新增"保存深 Cxt 跨兄弟作用域复用"的代码会静默读错表。建议保持该纪律并在 review 时检查。
4. **RefCell 重入面（item4）**：持有 `names.borrow()` 期间回调精化会 panic；现实现 lookup 克隆后
   立即释放、`subst_cxt` 的 wrap 闭包不回调；新增访问点需遵守。
5. **FxHashMap**：无顺序依赖（`simpl_decl` 只构建表、无迭代语义）；若未来有"按 map 序输出"的诊断需复查。
6. **未覆盖**：`l08bench` 的 `fast_ss/fast`（孪生）未受影响，本报告只报 `basic`（参考版）。
7. **机器干扰**：见 §4.4；如需发表级数字，建议 Lead 在安静窗口用保存的
   `l08bench-baseline.exe` / `l08bench-final.exe` / `l08bench-item4.exe` 重跑 5–7 对反向交错。

## 6. 与 L07 的差异（为什么 L08 收益更大）

- L07 的 strchain/global k=13 在 `c2fffd3f` 时是 33×/25×；L08 这里 k=11 为 13.2×/7.8×（规模更小），
  但 **L08 的 struct 负载（特色）同样 7.8×**——L08 的 struct 生成 2^(k+1) 个顶层 def，正撞 COW 放大器。
- L08 的 `src_names` 比 L07 移植前更原始（**按值 HashMap**，非 Rc），item4 在 L08 补的改进更彻底
  （连 VTy 深拷一并消掉）；深作用域探针 −22~−25% 与 L07 的 −18~−25% 同量级（Rc/Locals 已在 item1 完成）。

## 7. 后续建议（已无未做项）

1. **（可选）把深作用域探针固化为 bench 负载**：L08 `l08bench` 目前没有 deep lambda/let 负载，
   无法在标准套件里体现 item4 收益；建议新增 `deep` workload（生成 n 层 let/lambda），并用
   `bench_check_nf` 节点数做闭式断言（末值节点数固定）。
2. **（可选）`unification.rs` 的 `ren: HashMap`**：同属 rename 热路径，可换 FxHashMap，先做 A/B。
3. **（可选）回移 L07 的 `Decls::ver` + simpl 缓存**：L08 目前每次消费卡住 match 都重建简化表；
   回移可再拿一份收益，但需与 item3 的"占位两次写入"一起重新审 ver 语义。
4. **合并**：`feat/l08-hardening` 的 4 个 commit 已可由 Lead 直接 merge/快进（前 3 个已在
   `feat/all-layers-hardening`，第 4 个 `a3652630` 待合）。

## 8. 复现

```powershell
cd C:\ezl-wt-l08
$env:CARGO_TARGET_DIR='C:\ezl-target-all-l08'
cargo build --release --bin l08bench
cargo test --release --lib L08_product_type
cargo test --release --test l08_blackbox
cargo test --release --test l08_blackbox_v2
cargo test --release --test l08_fast_parity
cargo test --lib L08_product_type            # debug：校验 name_map unwind 断言
# A/B（安静窗口；每侧 3 轮，5–7 对反向交错）
C:\ezl-src-bench-l08\l08bench-baseline.exe --workload all --max-k 11 --rounds 3 --only basic
C:\ezl-src-bench-l08\l08bench-final.exe    --workload all --max-k 11 --rounds 3 --only basic
C:\ezl-src-bench-l08\l08bench-item4.exe    --workload all --max-k 11 --rounds 3 --only basic
```

产物：`C:\ezl-src-bench-l08\`（`l08bench-{baseline,final,item1,item3,item2,item4}.exe`、
`i*/i3/i4*/fin-*.txt` 原始日志、`*-tests.txt` 门禁日志）。


## 9. 2026-11-10 follow-up: L07 check_ty + unannotated-let ports

- Commit `2a1f378f`: port L07 `deef97f7` (check_ty destructure Raw::Pi by value,
  no `*a.clone()`/`*b.clone()` per level) and `87924b00` (unannotated let infers
  the binder type via `infer_expr` instead of creating a closed hole meta).
- Standard L08 workloads are neutral (same-window interleaved A/B):
  strchain k11 1.009x, struct k10 1.014x, church k10 1.004x, match k13 1.014x,
  natadd k11 0.996x.
- Deep-scope probe (n=1000, check_nf, interleaved A/B min):
  deep lambda **310.7 -> 246.2 ms (0.792x, -20.8%)**;
  deep let **171.2 -> 1.283 ms (0.007x, -99.3%)**.
- Gates after the port: lib 60, blackbox 57(+1)/51(+2), parity 95; check all-targets 0 error.
- Remaining L07-only item not ported: `Tm::Lam/Pi` body `Rc<Tm>` (L08 still has
  `Box`; mechanical but touches Obj arms) and any L07 hardening not yet mirrored.
