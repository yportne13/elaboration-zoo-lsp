# L05/L06 `src_names` → `NameState{map,trail}` + lazy unwind

> worktree `C:\ezl-wt-l0506nm`，分支 `feat/l0506-name-map`，基线 `feat/all-layers-hardening` @ `421ca6b7`
> `CARGO_TARGET_DIR=C:\ezl-target-l0506nm`；只改 L05/L06 参考版；未 push、未动 main/L07+。
> 配方来源：L08 `a3652630` / L07 `d411debe`（bump 孪生 `name_map`+`name_trail` 的参考版对应物）。

## 0. 结论

1. **两层的 `src_names` 已从"持久 COW 表"改为"单表 + 撤销轨迹 + 按 mark 惰性回退"**：
   `bind`/`define` 从"整表 `Rc::make_mut` 拷贝（父 Cxt 存活时必拷）"变成 **O(1) 摊还**的一次
   哈希插入 + 一条轨迹；上下文退出不显式撤销，下一次访问名字表前把轨迹裁回本 Cxt 的
   `name_mark`。语义与持久表等价（每个 Cxt 看到创建时的名字快照）。
2. **A/B 实测（同批交错，base=421ca6b7 已含上一轮 L05 Rc COW / L06 FxHash）**：
   **L06 strchain 10.68→4.30 ms（0.403×，−60%）、L06 global 19.17→6.08 ms（0.317×，−68%）**；
   L05 chain 25.75→19.24（0.747×，−25%）、L05 implicit 41.02→29.78（0.726×，−27%）；
   L06 church 1.02×（噪声）。深作用域探针 chain k=11：0.707×。
3. 门禁全绿：L05 lib 23 + blackbox 41/54/62；L06 lib 13 + blackbox 41/23/81（`RUST_MIN_STACK=67108864`）；
   两层 debug lib 各 23/13（验证 `mark <= trail.len()` debug_assert）；`cargo check --all-targets` exit 0。
4. 无 API 破坏：L05 `Cxt` 私有，读点仅 1 处改为 `lookup_src`；L06 `Cxt` 字段 `src_names` 变私有
   `names+name_mark`，读点 2 处改 `lookup_src`（其余调用方只用方法）。孪生版未改（其 `name_map/trail`
   早已存在）。

## 1. 设计（照 L08 `a3652630`）

```
NameState { map: FxHashMap<Key, (Lvl, Rc<VTy>)>, trail: Vec<(Key, Option<旧值>)> }
Cxt { ..., names: Rc<RefCell<NameState>>, name_mark: u32, ... }
```
- `unwind(mark)`：逆序弹轨迹，`Some(prev)` 写回、`None` 删除；`debug_assert!(mark <= trail.len())`。
- `bind`/`define`：`borrow_mut` → unwind(self.name_mark) → insert（旧值入轨迹）→ 子 Cxt 的
  `name_mark = trail.len()`；`new_binder` 不进表，子 mark 继承父 mark。
- `lookup_src`/`has_src`：先 unwind 再 `get`/`contains_key`；条目值仍是共享 `Rc`，无 `Val` 深拷贝。
- 深度优先遍历下，"上下文退出"= 之后任何更浅上下文的访问会惰性撤销更深作用域残留；轨迹是
  单线程 DFS 日志，(mark, trail.len) 唯一标识名字表版本。
- 与 L08 的差异：L05/L06 **没有 σ/`subst_cxt`**（精化层从 L07 起），故不需要 L08 `subst_cxt`
  的"按轨迹逐条包 VSub + 重设 mark"路径；L05 键是 `SmolStr`（`type Name = Span<SmolStr>`），
  L06 键是 `String`，各自沿用原值类型 `(Lvl, Rc<VTy>)`。

## 2. 落地（每层单独 commit）

| commit | 层 | 改动文件 / 行数 | 内容 |
|---|---|---|---|
| `a4520491` | L05 | `src/L05_pruning/mod.rs` 89/11 | 新增 `NameState`；`Cxt.src_names` → `names: Rc<RefCell<NameState>>` + `name_mark`；`bind/define` 改插入+轨迹；`new_binder` 共享；`lookup_src/has_src/unwind_names`；1 处读点（`Raw::Var`）改 `lookup_src` |
| `dfd7ca92` | L06 | `cxt.rs` 85/11 + `elaboration.rs` 3/3 | 同上（键 `String`、`Cxt` 字段 `pub`→私有 `names`）；`ty_precheck` 与 `infer_expr` 两处 `src_names.get` 改 `lookup_src`（返回 owned 条目，省一次 Rc clone 的 `&` 适配） |

基线 `421ca6b7` 已含：L05 `src_names` `Rc<FxHashMap>` COW + FxHash unification、L06 FxHashMap
（上一轮 `c9f72a79`）；因此本轮增益是**在 COW 之上的纯增量**（消掉"父存活时 bind/define 仍整表 COW"）。

## 3. 门禁（`C:\ezl-target-l0506nm`，release）

| 套件 | 结果 |
|---|---|
| `cargo check --all-targets` | ✅ exit 0（`Finished dev profile`，最后一次 25s） |
| L05 `--lib L05_pruning`（release / debug） | ✅ **23 passed** / ✅ 23 passed（debug_assert 生效） |
| L05 `l05_blackbox` / `_v2` / `_v3` | ✅ 41 / 54 / 62 passed |
| L06 `--lib L06_string`（release / debug） | ✅ **13 passed** / ✅ 13 passed（debug_assert 生效） |
| L06 `l06_blackbox` / `_v2` / `_v3`（`RUST_MIN_STACK=67108864`） | ✅ 41 / 23 / 81 passed |
| parity | N/A：L05/L06 无 `l0X_fast_parity`（自 L07 起才有）；黑盒套件为闸门 |

## 4. Bench A/B（同批交错；base/own 各 3 次交替，min/median；`--only basic --rounds 3`）

| 负载 | k | base min/med (ms) | own min/med (ms) | ratio(min) |
|---|---:|---:|---:|---:|
| **L05 chain** | 9 | 25.751 / 26.126 | **19.240 / 19.699** | **0.747×（−25.3%）** |
| **L05 implicit** | 9 | 41.017 / 41.182 | **29.780 / 30.119** | **0.726×（−27.4%）** |
| L06 church | 9 | 0.627 / 0.646 | 0.641 / 0.657 | 1.022×（噪声） |
| **L06 strchain** | 9 | 10.680 / 10.793 | **4.302 / 4.418** | **0.403×（−59.7%）** |
| **L06 global** | 9 | 19.174 / 19.381 | **6.080 / 6.219** | **0.317×（−68.3%）** |
| **L05 chain（深作用域探针）** | 11 | 26.936 / 30.302 | **19.047 / 19.826** | **0.707×（−29.3%）** |

- Load：批次开始 CPU 平均 **8%**、结束 **6%**（`Win32_Processor.LoadPercentage` 采样），无重负载干扰；
  同批交替执行，比值可信。median 与 min 同向（无长尾假象）。
- 为什么 L06 strchain/global 收益最大：这两个负载是**顶层 def 密集**（每声明一次
  `define` 触发 `src_names` 插入）；旧 COW 下 map 随 def 数增长、每次 define 整表拷贝 ⇒ O(D²)；
  新实现每 define O(1)。L05 chain/implicit 是深作用域/深 let，受益于"父 Cxt 存活时的 bind 拷贝消失"。
- deep 探针口径：L05 chain k=11（n=4096，作用域/声明链更深），非新写 benchmark；本轮未额外加
  临时 probe 程序（chain k=11 已能体现随深度增长的趋势）。

## 5. 风险 / 注意

1. **DFS 作用域纪律**：`unwind` 的正确性依赖"访问名字表前先裁到本上下文 mark"；所有名字读点
   已改为 `lookup_src/has_src`（内部先 unwind），`Cxt::bind/define/new_binder` 也先 unwind。
   新增读点必须走方法，不能直接 `names.borrow()`。
2. **RefCell 借用**：`unwind_names` 与随后的 `borrow()` 是两次顺序借用，无嵌套借用；`bind/define`
   在同一个 `borrow_mut` 作用域内完成 unwind+insert+取 len，无重入。
3. `mark <= trail.len()` 的 `debug_assert` 已由两层 **debug lib** 各跑一次验证；release 无断言。
4. L05/L06 无 `subst_cxt`（无 σ），本轮无需轨迹改写；若未来引入精化，需照 L08 `subst_cxt`
   按轨迹逐条包 VSub 并重设 mark。
5. 文档：L05/L06 README 仍描述"写时复制"旧实现（本轮未改 readme，避免与代码 review 混在一起；
   建议合并时一并更新）。

## 6. 复现

```powershell
git switch feat/l0506-name-map
$env:CARGO_TARGET_DIR='C:\ezl-target-l0506nm'
$env:RUST_MIN_STACK='67108864'      # L06 深负载 blackbox 需要
cargo check --all-targets
cargo test --release --lib L05_pruning ; cargo test --lib L05_pruning
cargo test --release --lib L06_string  ; cargo test --lib L06_string
cargo test --release --test l05_blackbox --test l05_blackbox_v2 --test l05_blackbox_v3
cargo test --release --test l06_blackbox --test l06_blackbox_v2 --test l06_blackbox_v3
cargo build --release --bin l05bench --bin l06bench
# A/B：base 快照 = 基线 421ca6b7 构建；own = 当前分支构建
#   --workload {chain,implicit,church,strchain,global} --max-k {9,11} --rounds 3 --only basic
```

## 7. 给 Lead 的合并信息

- 待 merge：`feat/l0506-name-map` 上 `a4520491`（L05）、`dfd7ca92`（L06）、本报告 commit。
- 基线 `421ca6b7` 已含上一轮 L03–L06 硬化；本分支仅 L05/L06 两文件级增量，无构建配置改动。
- 合并后建议：更新 L05/L06 README 的"名字表写时复制"描述；把 `RUST_MIN_STACK=67108864` 带到
  L06 blackbox 的 CI 环境（基线已有该 CI 改动，确认未被覆盖）。
