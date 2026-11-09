# L08-PORT：把 L07 已验证的性能优化移植到 L08 参考版

> 分支 `feat/l08-hardening`（worktree `C:\ezl-wt-l08`）· 基线 `feat/all-layers-hardening` @ `deef97f7`
> （含 `07f737d6` L08 merge 残留编译修复 + `deef97f7` L07 Pi-move）· **未 push**
> 构建：`CARGO_TARGET_DIR=C:\ezl-target-all-l08` · 时点 2026-11-10 05:00–06:05

## 0. 结论（TL;DR）

- 已按 L07 模板在 L08 参考版落地 **3 项**（每项独立 commit）：Locals Box→Rc、FxHashMap、decl COW 就地写。
- **全部 L08 套件绿**：lib 60 / blackbox 57(+1 ignored) / blackbox_v2 51(+2) / fast_parity 95；
  `l08bench` 节点数断言（闭式 + 双实现互检）全部通过。
- **大幅提速**（`l08bench --only basic`，k=11，5 对交错、中位数）：
  **strchain 127.1→9.6 ms（13.2×）、global 141.4→18.0 ms（7.8×）、struct 138.6→17.7 ms（7.8×）**；
  match/enum/natadd 也各快 ~9–14%（Locals Rc + FxHash 的副作用）。
- 未做：**name_map+trail（L07 `d411debe`）**——L08 的 `src_names` 仍是**按值 HashMap**
  （每次 bind 深拷整张表，比 L07 移植前的 Rc 表更差），可移植但需同时引入
  `NameState{map,trail}`+Rc 条目（lookup 返回 `Rc` 否则 VTy 深拷），估计 +120 行/1 个 commit；
  因时间与风险（深度优先作用域纪律）留给后续，见 §7。

## 1. 提交清单

| # | commit | 对应 L07 模板 | 内容 | diff |
|---|---|---|---|---|
| 1 | `535bb4be` | `65d4512a` Locals Box→Rc | `syntax.rs` `Bind/Define(Rc<Locals>)` + `close_ty` 改 `mcl.as_ref().clone()`；`cxt.rs` 3 处 `Box::new`→`Rc::new` | +13/−8（2 文件） |
| 2 | `9f159a97` | `72f12101` FxHashMap | `cxt.rs`：`Decls` 别名 / `src_names` / `empty()`；`mod.rs`：`mutable_map`、import | +11/−8（2 文件） |
| 3 | `5c56d27c` | `c2fffd3f` decl COW 就地写 | `Cxt::decl_insert_mut` + `decl_insert` 包装；`Cxt::new`/`add_builtin` 用 mut；`Infer::infer_owned` + `infer` 兼容包装；Def/Enum 占位与注册就地写；`run`/`bench_check`/`bench_check_nf` 改用 owned 链 | +56/−39（3 文件） |
| 合计 | 3 commits | — | 4 文件 | **+80/−55** |

均基于 `deef97f7`，工作树干净（`git status` 空）。未改 L07、未改 master/main worktree、未 push。

## 2. 逐项说明与依据

### 2.1 Locals Box→Rc（`535bb4be`）
- L08 `syntax.rs` 的 `Locals` 仍是 `Box<Locals>` 链；`Cxt::bind/define` 每次
  `self.locals.clone()` 深拷 O(深度)，n 个嵌套 binder ⇒ O(n²)。
- 照 L07/L13 改为 `Rc<Locals>`：clone O(1)，`close_ty` 克隆尾链 Rc。
- 现有 7 个 l08bench 负载上收益 −3~−5%（与 L07 同为"深作用域负载才显著"；L08 无深 lambda 探针，
  预期与 L07 的 lam/let n=1000 −48~−56% 同量级）。

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

## 3. 门禁（全绿）

| 套件 | 结果 |
|---|---|
| `cargo test --release --lib L08_product_type` | ✅ **60 passed** |
| `cargo test --release --test l08_blackbox` | ✅ 57 passed / 0 failed / 1 ignored |
| `--test l08_blackbox_v2` | ✅ 51 passed / 2 ignored |
| `--test l08_fast_parity` | ✅ **95 passed** |
| `l08bench` 节点数断言（church/strchain/global/struct 闭式 + match/enum/natadd 双实现互检） | ✅ 全部 k 通过 |
| `cargo build --release --bin l08bench` | ✅ |

原始日志：`C:\ezl-src-bench-l08\{item1,item3,item2,final}-tests.txt`。

## 4. 性能（l08bench，`--only basic`，k=11，`--rounds 3`）

### 4.1 逐项 A/B（相对 `deef97f7` 基线，3 对交错、每侧 3 轮 min）

| workload | baseline | +Locals Rc | +FxHash | +decl COW（= final） |
|---|---:|---:|---:|---:|
| church | 3.35 ms | 0.962 | 0.990 | **0.953** |
| strchain | 127.1 ms | 0.982 | 0.925 | **0.076（13.2×）** |
| global | 141.4 ms | 0.956 | 0.941 | **0.128（7.8×）** |
| struct | 138.6 ms | 0.967 | 1.106* | **0.127（7.8×）** |
| match | 0.144 ms | 0.952 | 0.830 | **0.868** |
| enum (k=9) | 0.284 ms | 0.969 | 1.015 | **0.912** |
| natadd | 9.61 ms | 1.115* | 0.954 | **0.856** |

\* 单点噪声（该 batch 期间有其他 agent 构建/bench 干扰；`struct` 的 +10.6% 与 `natadd` 的 +11.5% 未复现于 final）。

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

口径与局限：同机隔离进程、`--rounds 3`、每侧取多次运行的中位数/最小值；**机器为共享环境**
（其他 route 的 agent 同时在构建/bench，绝对 ms 有 ±20–30% 窗口漂移），因此以**同窗口交错比值**
为准（5 对 A/B 反向交错）。基线 exe 与 final exe 均在 `C:\ezl-src-bench-l08\`。

### 4.3 归因

- strchain/global/struct 的 6.5–13× 全部来自 **decl COW**（O(D²)→O(D)），与 L07 同因；
- Locals Rc + FxHash 贡献常数级 −3~−5%（+ 小负载噪声内的 match/enum/natadd 改善）；
- church 以 λ/应用为主、顶层 def 少 → COW 收益小，与 L07 一致。

## 5. 风险与注意事项

1. **语义**：三项均无语义变化（表示/哈希/所有权），但 decl COW 改变"占位只存在于克隆表"的实现细节
   ——占位与最终值现在落在同一张表；本基线无 `Decls::ver`/simpl 缓存，故无可观测差别；
   若后续回移 L07 的 `ver` 缓存需重新审（占位会造成两次 ver 递增，L07 亦然）。
2. **`infer_owned` 的移动语义**：`buf` 调用方（`run`/`bench_check*`）在 Err 分支直接返回，Ok 分支
   重新绑定 `cxt`；本地所有调用点已改为该模式；`infer(&Cxt)` 保留兼容包装（tests 未直接用它）。
3. **FxHashMap**：无顺序依赖（已核对 `simpl_decl` 只构建表、无迭代语义）；若未来有"按 map 序输出"
   的诊断需复查。
4. **未覆盖**：`l08bench` 的 `fast_ss/fast`（孪生）未受影响，本报告只报 `basic`（参考版）；
   孪生侧如需同窗口数据可由 perf 统一复测。
5. **机器干扰**：见 §4.2 口径；如需发表级数字，建议 Lead 在安静窗口用保存的
   `l08bench-baseline.exe` / `l08bench-final.exe` 重跑 5–7 对反向交错。

## 6. 与 L07 的差异（为什么 L08 收益更大）

- L07 的 strchain/global k=13 在 `c2fffd3f` 时是 33×/25×；L08 这里 k=11 为 13.2×/7.8×（规模更小），
  但 **L08 的 struct 负载（特色）同样 7.8×**——这是 L08 独有的显著增量（L07 无 struct 负载；
  L08 的 struct 生成 2^(k+1) 个顶层 def，正撞 COW 放大器）。
- L08 的 `src_names` 比 L07 移植前更原始（**按值 HashMap**，非 Rc），所以 **item4（name_map+trail）
  在 L08 的潜在收益比 L07 更大**；未做，见 §7。

## 7. 未做项与后续建议

**item4 name_map+trail（L07 `d411debe`）未做**，原因与估计：
- L08 `Cxt.src_names: FxHashMap<String,(Lvl,VTy)>`（按值）：每次 `bind/define` `clone()` 整表 O(名字数)，
  `subst_cxt` 也整表重建；深作用域/宽 match 臂下是剩余的主要平方项。
- 移植成本估计：`NameState{ map: FxHashMap<String, Rc<(Lvl,VTy)>>, trail: Vec<(String, Option<Rc<...>>)> }`
  + `Cxt.name_mark` + `unwind/lookup/has_src` + `bind/define/new_binder/subst_cxt` 改写（~120 行），
  3 个 lookup 调用点；需 Rc 条目避免 lookup 克隆 VTy 深树。
- 风险：惰性回滚依赖"深度优先作用域纪律"（L07 侧已审计 17 个 bind 点并加 `debug_assert`）；
  L08 的 pattern_match 结构同源，但需重新审计 + debug 档跑测试。
- 建议：作为下一个独立 commit 做，先跑 debug 档 lib 测试验证 `mark<=trail.len()` 断言。

## 8. 复现

```powershell
cd C:\ezl-wt-l08
$env:CARGO_TARGET_DIR='C:\ezl-target-all-l08'
cargo build --release --bin l08bench
cargo test --release --lib L08_product_type
cargo test --release --test l08_blackbox
cargo test --release --test l08_blackbox_v2
cargo test --release --test l08_fast_parity
# A/B（安静窗口；每侧 3 轮，5 对反向交错）
C:\ezl-src-bench-l08\l08bench-baseline.exe --workload all --max-k 11 --rounds 3 --only basic
C:\ezl-src-bench-l08\l08bench-final.exe    --workload all --max-k 11 --rounds 3 --only basic
```

产物：`C:\ezl-src-bench-l08\`（`l08bench-baseline.exe`、`l08bench-final.exe`、item1/3/2 exe、
`i*/i3/fin-*.txt` 原始日志、`*-tests.txt` 门禁日志）。
