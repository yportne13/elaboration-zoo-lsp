# L01–L06 硬化审计与低风险移植（branch `feat/l0106-hardening`）

> worktree `C:\ezl-wt-l0106`，基线 `f8d21e55`，目标 `CARGO_TARGET_DIR=C:\ezl-target-all-l0106`。
> 只动 L01–L06；未 push、未动 main/L07+。行号 = 当前分支源码。验收命令见 §5。

## 0. 结论

1. **Locals `Box→Rc` 在 L05/L06 基线已落地**（L05 `mod.rs:104-116`、L06 `syntax.rs:11-20` 已是
   `Rc<Locals>` + `Rc<Ty>/Rc<Tm>` 载荷）；L01–L04 无 `Locals` 结构（上下文用持久 `List`），**N/A**。
2. **L05 的唯一剩余大项已落**：`Cxt.src_names` 原本是按值 `std HashMap`，`Cxt::clone`/`bind`/`define`
   各整表克隆（chain 负载每声明 6–8 次 Cxt 克隆 ⇒ O(D)/次）。改为
   **`Rc<FxHashMap<SmolStr, (Lvl, Rc<VTy>)>>` COW**（与 L06/L07 同款），并把 unification 的
   `HashMap/HashSet` 换 FxHash。**实测 chain −50.8%、implicit −33.1%**。
3. **L06**：`src_names` 已是 `Rc<HashMap>` COW、`decls`/`mutable_map` 是 `Infer` 持有的当场
   `insert`（无 clone-before-make_mut 问题）；本轮只把 6 处 `HashMap`/`HashSet` 换 **FxHash**
   （`cxt.rs` / `mod.rs` / `unification.rs`），bench 中性（0.99–1.02×，符合预期）。
4. **L03/L04**：上下文是持久 `List`（无深拷名字表）、无 decl 表、无 `Locals`；唯一 hash 结构是
   unification 的 `ren`（`HashMap<u32,Lvl>`）——换 FxHash（各 −12 行/4 文件行）；bench 中性。
5. **L01/L02 仅审计（按 Lead 口径）**：L01 已用 `FxHashMap`（`bump_spine_memo.rs` 等），无 `Locals`/
   decl 表深拷；L02 上下文全持久 `List`（`types: List` `mod.rs:183-212`）。**无适用改动**。
6. **L05/L06 的 `NameState+trail`（L08 `a3652630` 配方）评估后未落**：能进一步消掉"父 Cxt 存活时
   bind 仍整表 COW 拷贝"，但需 Infer 持有 `Rc<RefCell<NameState>>` + `name_mark` + 惰性 unwind 纪律，
   并审计全部名字读点（L05/L06 各 ~150–250 行）；超出本轮 90 分钟低风险窗口，列为下一波（§6）。

## 1. 逐层审计（基线状态 + 适用性）

| 层 | Locals | 名字/类型表 | decl/global 表 | 适用项 | 处置 |
|---|---|---|---|---|---|
| L01 | 无（多 NBE 变体） | 无持久名字表；已 FxHash | 无 | 无 | 审计 N/A |
| L02 | 无 | `types: List<...>`（持久，`mod.rs:183-212`） | 无 | 无 | 审计 N/A |
| L03 | 无 | `types: List`（`:631-663`）；unif `ren: HashMap`（`:312,679`） | 无 | FxHash | ✅ dd10d59b |
| L04 | 无 | `types: List`（`:782-825`）；unif `ren: HashMap`（`:326,841`） | 无 | FxHash | ✅ 0cd81a42 |
| L05 | **已 Rc**（`Rc<Locals>`，`:111-116`） | **`src_names: HashMap` 按值**（`:252`，每次 Cxt clone/bind 整表克隆）；unif `ren: HashMap/HashSet`（`:339,605`） | 无 | src_names Rc COW + FxHash | ✅ dce5c61c |
| L06 | **已 Rc**（`syntax.rs:15-20`） | `src_names: Rc<HashMap>` 已 COW（`cxt.rs:271`）；unif `ren: HashMap/HashSet`（`unification.rs:25,60`） | `decls: HashMap`、`mutable_map: HashMap`（`mod.rs:155,158`；**Infer 就地 insert，无 clone-before-make_mut**） | FxHash ×6 点 | ✅ df2fde54 |

补充：L05/L06 的 `Locals` 载荷已 `Rc<Ty>/Rc<Tm>`，不再有 Box 链深拷；L06 `src_names` 的
`Rc::make_mut` 在"父 cxt 仍持有"时仍整拷一次（与旧版同价，语义需要），完整消除需 NameState。

## 2. 落地项（每项单独 commit）

| commit | 层 | 改动 | 行数 |
|---|---|---|---|
| `dce5c61c` | L05 | `src_names` 改 `Rc<FxHashMap>` COW（`Rc::make_mut` 插入，`new_binder` 只 clone Rc）；`invert_go`/`PartialRenaming`/`lift` 的 `HashMap/HashSet` → `FxHashMap/FxHashSet` | 12/12（1 文件） |
| `df2fde54` | L06 | `cxt.rs src_names`、`mod.rs decls/mutable_map`、`unification.rs ren/HashSet` → FxHash | 13/12（3 文件） |
| `dd10d59b` | L03 | `invert_go`/`PartialRenaming/lift` → `FxHashMap` | 4/4（1 文件） |
| `0cd81a42` | L04 | 同上 | 4/4（1 文件） |

## 3. Bench A/B（同批交错，base=基线二进制 vs own=改动后；k=9，rounds=3，min-of-2 配对，basic 列）

| 负载 | base min | own min | ratio | 判读 |
|---|---:|---:|---:|---|
| L03 church | 0.799 | 0.783 | 0.98× | 噪声内 |
| L03 chain | 19.755 | 19.982 | 1.01× | 噪声内 |
| L04 church | 0.855 | 0.805 | 0.94× | 噪声内 |
| L04 implicit | 26.097 | 25.858 | 0.99× | 噪声内 |
| **L05 church** | 0.843 | 0.812 | **0.96×** | 噪声内/略好 |
| **L05 implicit** | 61.387 | **41.041** | **0.669×（−33.1%）** | **显著** |
| **L05 chain** | 54.498 | **26.788** | **0.492×（−50.8%）** | **显著** |
| L06 church | 0.623 | 0.633 | 1.02× | 中性 |
| L06 strchain | 10.799 | 10.772 | 1.00× | 中性 |
| L06 global | 19.453 | 19.233 | 0.99× | 中性 |

口径：独立进程；同一时段交错 base/own 各 2 轮；机器共享负载未记录到 CPU 频率，但 base/own 同批
交替，比值可用；**prune 负载 L05/L06 基线各 ~31 s，为另一条 O(n²) 轴，未纳入本轮 A/B**（避免长跑）。

## 4. 门禁（`CARGO_TARGET_DIR=C:\ezl-target-all-l0106`，release）

| 套件 | 结果 |
|---|---|
| `cargo check --all-targets` | ✅ exit 0（dev profile，1m16s） |
| L03 lib / `l03_blackbox` / `_v2` | ✅ 28 / 136 / 81 passed |
| L04 lib / `l04_blackbox` / `_v2` | ✅ 30 / 75 / 73 passed |
| L05 lib / `l05_blackbox` / `_v2` / `_v3` | ✅ 23 / 41 / 54 / 62 passed |
| L06 lib / `l06_blackbox` / `_v2` / `_v3` | ✅ 13 / 41 / 23 / 81 passed |
| parity | **N/A**：本仓 `l0X_fast_parity` 自 L07 起才有（L03–L06 无 parity 套件；黑盒为闸门） |

**环境坑（基线已存在，非本轮回归）**：`l06_blackbox::workload_node_counts` 在 libtest 默认测试线程栈上
**STATUS_STACK_OVERFLOW（0xC00000FD）**；用 `git stash` 回退本轮 L06 改动后重编重跑，**基线同样溢出**
⇒ 与本改动无关。设置 `RUST_MIN_STACK=67108864` 后全部用例通过（本轮所有 L06/含 L05 套件即按此跑）。
`.cargo/config.toml` 只抬了主线程栈（linker `/STACK`），不覆盖 libtest 每测试线程；建议 CI/门禁显式设
`RUST_MIN_STACK`（或把该测试移入大栈线程）。

## 5. 复现

```powershell
git switch feat/l0106-hardening            # worktree C:\ezl-wt-l0106
$env:CARGO_TARGET_DIR='C:\ezl-target-all-l0106'
$env:RUST_MIN_STACK='67108864'
cargo check --all-targets
cargo test --release --lib L03_holes       # 同理 L04/L05/L06
cargo test --release --test l05_blackbox -test l05_blackbox_v2 ...
cargo build --release --bin l03bench --bin l04bench --bin l05bench --bin l06bench
# A/B：base 二进制为基线构建（f8d21e55，build 在改动前采集），own 为当前构建；
#      --workload {church,implicit,chain,strchain,global} --max-k 9 --rounds 3 --only basic
```

## 6. 未落地 / 下一波建议

1. **L05/L06 `NameState+trail`（照 L08 `a3652630`）**：`Cxt` 持有 `Rc<RefCell<NameState{map,trail}>>`
   + `name_mark`；bind/define 先按 mark 惰性 unwind 再一次 insert+trail push；读点先 unwind。
   可消掉"父 Cxt 存活时 bind 仍整表 COW 拷贝"（L05 chain 已 −50.8%，此项预计还能吃掉剩余
   深作用域项，L08 实测深 let n=1000 −22.3%）。成本：L05/L06 各 ~150–250 行 + 全名字读点审计 +
   `mark <= trail.len()` debug_assert；风险中（DFS 作用域纪律），建议带 L07/L08 的 parity 钉子。
2. **L05/L06 `prune` 负载 ~31 s**：与名字表无关的另一条轴（metas/pruning），需单独 profile；
   本轮未动。
3. **L01/L02**：无适用项（已 FxHash、持久 List 上下文），维持审计结论。
4. 建议把 `RUST_MIN_STACK` 写入门禁脚本；否则 L06 深负载测试在默认栈上会假红。
