# ROUTE-TRAIL：L07 参考版 `src_names` → `name_map` + `name_trail`（共享表 + 惰性回滚）

> 路由：两条 `src_names` 优化路线之二 · worktree `C:\ezl-src-trail` · 基线 HEAD `1f382a2a`
> （master 同 commit；**未 commit/push**，未动 master 与 `C:\ezl-target`）
> 构建：`CARGO_TARGET_DIR=C:\ezl-target-trail` · 2026-11-10 00:00–00:50

## 0. 结论（TL;DR）

- **实现完成、语义等价、全部门禁绿**：70 lib + 48/51/116 黑盒 + 97 parity，共 **382 passed / 0 failed / 4 ignored**；
  `l07bench` 的节点数断言（闭式 + 双实现互检）全部通过。
- **性能结论：现有 6 个负载上中性**（交错 A/B：−1.9%…+3.7%，噪声带内）；只在**深作用域合成负载**上稳定
  **−14.8%**（n=250/500/1000 均为 −14.8~−14.9%），但该负载的剩余二次方**不是名字表**（见 §5）。
- **建议：不为性能单独落地**。若要做"参考版去 O(n²)"，必须同时把 `Locals` 链 Rc 化（本次已定位，
  见 §5），否则只赚 15%。本 patch 留档供回滚/参考，不进 master。
- 交付物：`C:\ezl-src-bench\l07bench-trail.exe`（SHA256 `E440FD0E…5D0315`）、
  `l07-name-trail.patch`（288 行 / 22,940 B）、A/B 原始日志 `ab-{base,trail}-r{1,2,3}.txt`。

## 1. 设计选型（任务允许的 A/B 两形态）

采用 **B 形态：`Cxt` 内共享可变表 + 撤销轨迹 + 按 mark 惰性 unwind**。

理由（相对 A 形态 "`Infer` 级 name_map + Cxt 只带 mark"）：
1. 调用面最小。参考版 17 个 `bind`/`define`/`new_binder` 调用点都是 `&cxt.bind(…)` 形态；
   A 形态需把 `bind` 移进 `Infer`（`&mut self`），在 `self.check(&self.bind(..))` 这类实参位置
   会触发借用冲突，需改写成先 `let c = self.bind_name(...)` 再调用——波及 `elaboration.rs`
   10 处以上；B 形态保持 `Cxt::bind(&self)` 签名不变，只改 `cxt.rs` 内部 + 3 个查表调用点。
2. 与"参考版可读性优先"定位一致：状态收敛在一个 `NameState` 里，语义论证只需 §4 一条。
3. 可选回滚：表与轨迹都在 `Cxt` 树内，不污染 `Infer`（参考版 `Infer` 仍是纯 meta/decl 状态）。

## 2. 变更清单

| 文件 | 行数 | 内容 |
|---|---|---|
| `src/L07_sum_type/cxt.rs` | +125 / −27 | 新增 `NameState { map, trail }`（`trail: Vec<(String, Option<Rc<(Lvl,VTy)>>)>`）；`Cxt` 字段 `src_names: Rc<HashMap>` → `names: Rc<RefCell<NameState>>` + `name_mark: u32`；新增 `unwind_names`/`lookup_src`/`has_src`；`bind`/`define` 改为 insert+trail（O(1)）；`new_binder` 不动表只带 mark；`subst_cxt` 改走轨迹包 `VSub` |
| `src/L07_sum_type/elaboration.rs` | +6 / −6 | `Var` 解析、`Enum.case` 局部遮蔽判定、`ty_precheck` 三处改走 `lookup_src`/`has_src` |
| `src/L07_sum_type/pattern_match.rs` | +1 / −1 | 注释同步（src_names→名字表） |
| **合计** | **+132 / −34（3 文件）** | patch 288 行 |

无新依赖、无 `unsafe`、无公开 API 变化（`Cxt` 仍是 `pub`，字段本就 `pub`→名字表字段改私有；
仓库内无外部访问 `.src_names` 的点，已 grep 核实）。

## 3. bind / lookup 复杂度

**旧（持久表）**：`bind` = `Rc::clone`（强计数 2）+ `Rc::make_mut` ⇒ **深拷整张表**：
K 个源码名 ⇒ K 次 `String` 堆分配 + K 次 Rc 递增 + 哈希桶重建，O(K)；n 个嵌套绑定器总代价
**Σ K = O(n²)**（K = 作用域内名字数，深作用域最坏 = 层号）。lookup O(1)。

**新（共享表 + 轨迹）**：
- `bind`/`define`：`unwind(self.name_mark)`（摊销 O(0)：每条轨迹只被弹一次）+ 1 次 hash insert
  + 1 次 trail push = **O(1)**；仅一次键 `String` clone（与旧版单条相同）。
- `lookup_src`/`has_src`：unwind 摊销 O(0) + hash get + `Rc` clone = **O(1)**；代价是每次多 2 次
  `RefCell::borrow` 检查（实证见 §5，噪声内）。
- `subst_cxt`：仍是 O(现有名字数) 一次（每 match 臂一次，与旧版同量级，只是由"新建表"改为
  "逐条改写入轨迹"）。
- 内存：旧版每次 bind 瞬时分配 K 个键字符串（垃圾量 O(n²) 字节）；新版每 bind 一条键 + 一条轨迹
  条目，表本身单例、命中缓存后稳态 O(1)。

## 4. 回滚机制与语义等价性论证

- **轨迹**：`(名字, 旧值)` 日志；`name_mark` = 轨迹长度。任何 `Cxt` 用 `(mark)` 唯一标识一个
  名字表版本；`unwind(mark)` 逆序弹日志（`Some(prev)` 复原、`None` 删除）即可恢复该版本。
- **惰性**：作用域退出不显式回滚；**每次访问前**调 `unwind_names()`（回退到本上下文基线）。
  深度优先遍历下这等价于"每个 Cxt 看到的名字集 = 创建时快照"，即与旧持久表**逐点等价**。
- `subst_cxt` 的可回滚性：把现有条目逐条换成 `VSub` 包裹版本，旧条目进轨迹；父上下文下次访问
  惰性复原——与 `bind` 同一机制（match 臂边界无需显式撤销。
- 走访审计（全部调用点）：`bind` 17 处（elaboration 7 / pattern_match 8 / unification 1 +
  `infer_owned` 链）、`define` 2 处、`new_binder` 1 处、`subst_cxt` 1 处；`infer_owned` 返回的
  `Cxt` 是"同 mark、decl 更新"的链式传递（`mod.rs` 三处 `cxt = new_cxt`），不产生深 mark 存活；
  pattern walk 是 `cxt = new_cxt` 严格顺序；`unify` 的 η 臂只在实参位置临时 bind，返回后即丢弃。
  **没有**"保存深 Cxt → 访问浅 Cxt → 再用深 Cxt"的模式（这正是惰性方案唯一会错的形态）。
- 防线：`unwind` 里 `debug_assert!(mark <= trail.len())`；debug 档 70 个 lib 测试全过（未触发）。

## 5. 实验结果

### 5.1 门禁（`--release`，C:\ezl-target-trail）

| 套件 | 结果 |
|---|---|
| `cargo build --release --bin l07bench` | ✅ Finished（2m23s，仅既有 warning） |
| `cargo test --release --lib L07_sum_type` | ✅ **70 passed**；debug 档同样 70 passed（`debug_assert` 未触发） |
| `cargo test --release --test l07_blackbox` | ✅ 48 passed / 0 failed / 1 ignored |
| `--test l07_blackbox_v2` | ✅ 51 passed / 2 ignored |
| `--test l07_blackbox_v3` | ✅ 116 passed / 1 ignored |
| `--test l07_fast_parity` | ✅ 97 passed / 0 failed（参考版 vs 孪生逐字节/判定一致） |
| `l07bench` 节点数断言（church/strchain/global 闭式 + match/enum/natadd 双实现互检） | ✅ 全 k 通过 |

原始日志：`C:\ezl-src-bench\l07-tests-trail.txt`、`l07-tests-trail-debug.txt`。

### 5.2 标准负载 A/B（basic = 参考版；3 对交错运行、每格 3 轮取 min、同 target/同窗口）

| workload (k=11) | baseline (ms) | trail (ms) | Δ |
|---|---:|---:|---:|
| church | 2.654 | 2.640 | −0.5% |
| strchain | 9.304 | 9.268 | −0.4% |
| global | 18.079 | 17.736 | −1.9% |
| match | 0.135 | 0.140 | +3.7% |
| enum (k=9) | 0.264 | 0.264 | 0.0% |
| natadd | 5.145 | 5.143 | 0.0% |

→ **中性**。原因：这些负载作用域深度小（K≤~5），旧版整表深拷的绝对成本被 parse/eval/unify 掩埋。

### 5.3 深 let 链探针（临时测试，已删除；`run()` 端到端含 parse，min of 4）

| 深度 n | baseline (ms) | trail (ms) | Δ |
|---:|---:|---:|---:|
| 250 | 31.920 | 27.173 | −14.9% |
| 500 | 135.713 | 115.561 | −14.8% |
| 1000 | 551.251 | 469.837 | −14.8% |

- 收益稳定 −14.8%（名字表 O(n²)→O(n) 的那一份），但 **T(2n)/T(n) 仍 ≈ 4.1× ⇒ 剩余二次方项仍在**。
- 定位：`Locals` 是 **Box 链**（`src/L07_sum_type/syntax.rs:10-14`：
  `Define(Box<Locals>, …)` / `Bind(Box<Locals>, …)`），`bind`/`define` 里
  `self.locals.clone()` 每次深拷 O(深度) ⇒ 另一个 O(n²) 源。`env`/`pruning` 用的 `List` 是
  Rc 链（`src/list.rs:5,39`），O(1)，不是瓶颈。
- 推论：只做 name_map 路线 ≈ 拿到深作用域开销的 ~15%；要线性需同时 `Locals` → Rc 链
  （或按层共享），属另一条改动（影响 `names()`/`close_ty`/`pretty` 的遍历方式）。

## 6. 风险清单

1. **stale binding（核心风险）**：惰性方案的正确性依赖"不在访问浅 Cxt 之后继续使用深 Cxt"的深度优先纪律。
   现有代码审计满足（§4），但未来新增"保存 Cxt 跨兄弟作用域复用"的代码会静默读错表；release 无断言。
   缓解：`unwind` 的 debug_assert + 该纪律写进 `NameState` 文档；CI 跑 debug 档 lib 测试可兜底。
2. **RefCell 重入 panic**：持有 `names.borrow()` 期间回调精化会 panic。现实现 lookup 克隆后立即释放、
   `subst_cxt` 的 `wrap` 闭包不回调；未来新增访问点需遵守。
3. **嵌套作用域/遮盖**：轨迹按 `(名字, 旧值)` 复原，同名 shadow 正确（blackbox/parity 全绿验证）。
4. **错误路径**：Err 冒泡时深 mark 残留，下一次访问自动回退（blackbox 错误族全绿）。
5. **性能回归面**：lookup 每次多 2 次 borrow 检查；标准负载噪声内（§5.2），未观测到回归。
6. **单线程假设**：`Rc`/`RefCell` 非 Send，与参考版现状一致（LSP 侧按需分线程，未见跨线程 Cxt）。

## 7. 建议

- **perf 结论：不落地**。现有负载中性、深作用域负载只有 15%，且引入内部可变性与作用域纪律风险；
  与"参考版=可读、可审计的教学实现"的定位相悖。
- 若 Lead 想消除该理论债：**一次做两件事**——(a) 本 patch（名字表 O(1)），(b) `Locals` Rc 化；
  合起来才能把深绑定器路径从 O(n²) 拉到 O(n)。单独 (a) 不改变渐进阶的观感。
- 若目标是"参考版/孪生机制同构"（优雅/单一事实来源）：本 patch 让参考版与孪生 `name_map+trail`
  结构对齐，但 D3 的结论更支持"删双引擎/抽公共核"，而非让参考版逐点模仿孪生——同构价值有限。

## 8. 复现

```powershell
cd C:\ezl-src-trail
$env:CARGO_TARGET_DIR='C:\ezl-target-trail'
cargo build --release --bin l07bench
cargo test --release --lib L07_sum_type
cargo test --release --test l07_blackbox --test l07_blackbox_v2 --test l07_blackbox_v3 --test l07_fast_parity
C:\ezl-src-bench\l07bench-trail.exe --workload all --max-k 11 --rounds 3 --only basic
# A/B：C:\ezl-src-bench\l07bench-baseline.exe 与 l07bench-trail.exe 交错跑（ab-*.txt 即原始输出）
```

未完成项：无（探针测试已删除；`git status` 仅 3 个源码文件 modified，无 commit）。
