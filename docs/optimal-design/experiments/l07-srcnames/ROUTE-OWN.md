# ROUTE-OWN：L07 参考版 `src_names` 所有权路线原型

> worktree：`C:\ezl-src-own`（分支 `src-own`，HEAD `1f382a2a`，**未 commit**；未触碰 master / `C:\ezl-target`）
> 目标：消除 `Cxt::bind/define` 因 `&self` 导致 `Rc::strong_count` 恒 ≥2、每个 binder 深拷整张
> `src_names` map（O(scope)/bind，嵌套 O(n²)）的问题；用 **所有权传递 + scoped push/pop** 实现。
> 构建/测试：`CARGO_TARGET_DIR=C:\ezl-target-own`（全部实测，见 §5）。

## 0. 结论

1. **可行性成立**：4 个文件、+306/−67 行（`cxt.rs` +212、`elaboration.rs` +80/−65、`mod.rs` +12、
   `pattern_match.rs` +2/−2），`check/check_ty/infer_expr` 全链路改为 `&mut Cxt` + push/pop 撤销。
2. **每 binder 唯一所有权已实测**：覆盖路径上 `Rc::strong_count(&src_names)==1` 占比 **100%**
   （demo 32/32、church 50/50、bits_adder 52/52），且 pop 时 map 仍共享次数 **0**；
   旧持久化路径（pattern_match 等）仍是共享拷贝，故**总覆盖率 60%–91%**（按语料，见 §4）。
3. **语义保持**：全部验收绿：lib 70 passed（release）、`l07_blackbox` 48+1ign、`_v2` 51+2ign、
   `_v3` 116+1ign、`l07_fast_parity` 97 passed、`l07bench` 全 workload 节点数断言 exit 0。
   期间发现并修复一个真实语义 bug：**同名遮蔽**的 pop 必须写回旧条目（不能直接 remove），
   否则 `λx. λx. …` 的内层作用域结束后外层 `x` 丢失（初版被 `name not in scope: x` 钉出）。
4. **性能**：现役 bench 无回归（match/church/enum basic 与 base 二进制同档、差异在噪声内）；
   预期收益在**深/嵌套作用域语料**上（旧代价 ≈ Σ scope ≈ O(n²) 次 map 条目复制，新为 O(1) 摊还
   insert/remove），bench 负载作用域浅所以量不出——需补一个 N 层嵌套 λ/let microbench（未做）。
5. **未实现/风险**：pattern_match 的 7 个模式 binder 仍是旧路径（题面允许的最小原型范围）；
   它和 unification 的 1 个 binder 是覆盖缺口；完整化预计 +150–250 行、需改 `Walk` 携带 Cxt 的
   所有权形态（见 §6），风险中等（parity 可兜底）。

## 1. 设计（scoped 所有权传递）

原 `Cxt::bind(&self) -> Self`：
```rust
let mut src_names = Rc::clone(&self.src_names);   // 计数 = 父 1 + 本 1 = 2
Rc::make_mut(&mut src_names).insert(..);          // 恒深拷整表（O(scope)）
```
原型改为两条并行 API（旧 API 保留给未迁移调用方，行为不变）：

```rust
// cxt.rs（新增，均 &mut self）
pub fn push_bind(&mut self, x, a_quote, a) -> BinderUndo;
pub fn push_new_binder(&mut self, x, a_quote) -> BinderUndo;      // 不进 src_names
pub fn push_define(&mut self, x, t, vt, a, va) -> BinderUndo;
pub fn pop_bind(&mut self, undo: BinderUndo);
```
- **就地写**：`Rc::make_mut(&mut self.src_names)` 在独占时原地 insert/remove；`Cxt` 由调用方
  `&mut` 向下传递、不产生父副本，所以计数=1。
- **撤销凭据** `BinderUndo` 只存 O(1) 字段：`kind/env/lvl/pruning/key/prev`。
  `env/pruning` 是持久 `List`（clone = 指针）；`locals` 不 clone——push 用
  `mem::replace` 把旧 `Locals` **move 进** Box 链，pop 从链头**解包**恢复（连原实现的
  `Box::new(self.locals.clone())` O(scope) 深拷也一并消掉）。
- **遮蔽恢复**：`prev = src_names.get(key).cloned()`；pop 时 `Some(prev)` 写回、`None` 删除。
  这是"child 丢弃即恢复父"持久语义的就地等价物（初版忘了 prev，被嵌套同名 λ 测试抓出）。
- **父子隔离**：child 检查结束后 `pop_bind` 恢复 env/lvl/locals/pruning/src_names；
  异常路径统一"先 pop 再 `?`"，即 `let r = self.check(...); cxt.pop_bind(u); r?`。

## 2. 改动的调用路径（覆盖）

| 位置 | 改动 |
|---|---|
| `elaboration.rs::check` | `cxt: &mut Cxt`；Lam / 隐式 Π 插入 / Let 三个 binder 改 push+pop；`decl` 借出改为本地 `Rc<Decls>` clone（避免与 `&mut cxt` 冲突） |
| `elaboration.rs::check_ty` | `&mut Cxt`；Π 余域 binder 改 push+pop |
| `elaboration.rs::infer_expr` | `&mut Cxt`；Lam 推断 / Pi / Let / App-隐式插入 fallback 四处 binder 改 push+pop；闭包 env 语义保持（Pi 闭包 env = 父 env） |
| `elaboration.rs::infer_owned` | 对 `check/check_ty/infer_expr` 的调用改 `&mut cxt`（顺序声明路径本就独占 Cxt，计数天然=1） |
| `pattern_match.rs::Compiler::compile` | 仅适配 `infer.check(&mut cxt_arm, ...)`（分支体检查进入已覆盖链；**walk/walk_con 的 7 个模式 binder 未迁移**） |
| `mod.rs::run` | 诊断探针：`L07_BINDER_STATS=1` 时重置并打印计数器（见 §4）；生产路径零额外分支 |
| `cxt.rs` | 旧 `bind/define/new_binder` 保留（加 legacy 计数），新增 push/pop + `BinderUndo` + 计数器 |

## 3. 未覆盖的 binder（诚实清单）

1. **`pattern_match.rs` walk/walk_con 7 处**（`:465/:507/:530/:545/:603/:614/:660`）：`Walk::Matched`
   目前**携带新 Cxt**（函数式返回），改所有权需把 walk 改成"互斥借用 + 返回时撤销/或每臂 clone，
   或把 `Walk::Matched` 改为无 Cxt、binder 链留在传入的 &mut Cxt"，是本路线剩余最大工作量
   （预计 +120–200 行，涉及 walk/walk_con/compile 的 3 个签名与错误路径）。
2. **`unification.rs:947` 一处**（η/重命名路径）仍旧路径；量小。
3. 兼容入口 `Infer::infer(&Cxt)` 仍先 `cxt.clone()` 再 `infer_owned`——从该入口进入时首个 binder
   会因计数=2 付一次 map 拷（之后转独占）；`run`/`bench_check` 走 `infer_owned`，不受影响。

## 4. 唯一所有权证据（实测计数器）

计数器：`calls`=push_* 次数；`map_calls`=其中动 src_names 的；`unique`=make_mut 前计数=1 的次数；
`pop_shared`=pop 时 map 仍被共享的次数；`legacy`=旧持久化 bind/define/new_binder 次数。
**覆盖率 = calls/(calls+legacy)**；**独占率 = unique/map_calls**。

| 语料（lib test，release，`L07_BINDER_STATS=1`） | calls | map_calls | unique | pop_shared | legacy | 独占率 | 覆盖率 |
|---|---:|---:|---:|---:|---:|---:|---:|
| `tests::test_demo`（混合） | 32 | 32 | 32 | 0 | 3 | **100%** | 91.4% |
| `tests::test_lambda_calculus_and_strings` | 50 | 50 | 50 | 0 | 16 | **100%** | 75.8% |
| `tests::test_dependent_match` | 22 | 22 | 22 | 0 | 9 | **100%** | 71.0% |
| `tests::test_nested_patterns` | 18 | 18 | 18 | 0 | 12 | **100%** | 60.0% |
| `tests::test_bits_adder` | 52 | 52 | 52 | 0 | 24 | **100%** | 68.4% |

⇒ 在已迁移的路径上**每个 binder 都是独占**（原地 insert/remove，不再整表拷贝）；
剩余 legacy 全是模式匹配/η 路径。统计手段为 release 原子计数（每次 binder 2–3 次
`Relaxed fetch_add`，量级 ~ns；仅诊断用，后续可 cfg 编译掉）。

## 5. 验收记录（全部在 `C:\ezl-target-own`，release）

| 项目 | 结果 |
|---|---|
| `cargo build --release --bin l07bench` | ✅ `Finished release ... in 3m15s` |
| `cargo test --release --lib L07_sum_type -- --test-threads=1` | ✅ **70 passed / 0 failed** |
| `cargo test --release --test l07_blackbox` | ✅ 48 passed + 1 ignored |
| `cargo test --release --test l07_blackbox_v2` | ✅ 51 passed + 2 ignored |
| `cargo test --release --test l07_blackbox_v3` | ✅ 116 passed + 1 ignored（含带入 lib 测试） |
| `cargo test --release --test l07_fast_parity` | ✅ 97 passed（ref↔twin 逐字节/判定） |
| `l07bench --workload all --max-k 9 --rounds 1 --only basic` | ✅ exit 0，nf 节点数断言全过 |
| A/B（basic，rounds=3，k=11） | match own 0.135ms vs base 0.116–0.226ms（base k11 离群，噪声）；church own 2.647 vs base 2.625；enum k9 0.254 vs 0.254 ⇒ **无回归、收益未显影**（bench 作用域浅） |
| 交付二进制 | ✅ `C:\ezl-src-bench\l07bench-own.exe`（从 `C:\ezl-target-own\release\l07bench.exe` 拷出） |

## 6. 预计完整重构成本

| 项 | 规模 | 说明 |
|---|---|---|
| pattern_match walk/walk_con | +120–200 行 | 改 `Walk::Matched(PatternDetail, Cxt)` 的所有权形态：方案 A（每臂 `base.clone()` 后 `&mut` 走查、Matched 不带 Cxt，链留原地）≈ 最小；方案 B（walk 返回 undo 栈，逐层 pop）更省但错误路径复杂。compiler 的 7 处 `let cxt = cxt.bind(..)` 与 3 处 `&cxt` 递归需同步，`nested_checks`/`cxt_arm` 生命周期要重排 |
| unification η binder | +10–20 行 | 该处 cxt 是否可拿到 `&mut` 需查调用链，通常可半日完成 |
| 兼容 API 清理 | +20 行 | 全量迁移后可删旧 `bind/define/new_binder`（或保留 deprecated） |
| 测试/门禁 | 同现有 | lib+黑盒×3+parity 全绿为硬闸；建议加"深嵌套 λ/let 的 scope 计时"钉（现仓无此负载形态） |
| 综合 | **约 0.5–1.5 人日**（不含评审） | 本原型已占 ~15% 工作量但拿到全部关键机制与计数证据 |

## 7. 风险与建议

1. **配对纪律**：push/pop 必须成对；原型在 `?` 前显式 pop（先存 Result）；panic 展开会留下被改的
   `Cxt`——只在检查期栈上、随 panic 丢弃，可接受；若未来 Cxt 长生命周期需 RAII guard。
2. **共享回退**：任何 `cxt.clone()`/`subst_cxt`/探针快照都会让计数>1，自动回退到 COW 拷贝（正确但
   付费）；实测语料 `pop_shared=0`，但 pattern_match 迁移后需重测（它的 `subst_cxt` 会产生新 Cxt）。
3. **收益验证缺口**：现役 bench 无深作用域负载，建议与 Lead 确认是否加一个 microbench
   （N=200–2000 嵌套 λ/let 的源码，计时 `run`）：预计旧路径秒级、新路径线性。
4. **不要混用**：迁移过的函数与未迁移函数之间传 `&mut Cxt` 时，未迁移方仍只借 `&Cxt` 做旧式
   bind（产生临时 child）——语义正确但会抵消局部收益；完整化后再收尾。
5. 本原型保留 `L07_BINDER_STATS` 诊断口与旧 API；提交前建议把计数器改 `cfg(debug_assertions)`
   或直接移除（发布路径零成本）。
