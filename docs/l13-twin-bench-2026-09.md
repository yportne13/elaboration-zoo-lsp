# L13 双引擎基准（2026-09-08/09）——从"跑不完 prelude"到反超参考版

> 目的：L13 性能孪生 `bump_spine_iter.rs` 至今没有 bench（无 `l13bench`），
> ref vs twin 一次都没实测过。本轮补 `src/bin/l13bench.rs`，在合成负载与
> 真实 prelude 负载上量（`basic` 参考版 / `fast` 孪生一次性 /
> `fast_ss` 孪生稳态）。
>
> **核心结论（2026-09-09 更新）**：孪生原先**连核心 prelude 都跑不完**
> （trait 求解在 flex goal 上选错实例）；本轮连修 5 个阻塞点后，
> **跑通全部 943 个 HDL prelude decl**，且移植 force 记忆化后
> **1.83s vs 参考版 3.29s（反超 1.8×）**。此前"性能版在真实负载上反而更慢"
> 的推断被实测证实（无 memo 时 11.0s，慢 3.4×），force memo 由此从"可选
> 优化"变成接入 LSP 的前提。

---

## 0. 总览（截至 2026-09-09）

| 阶段 | 状态 |
|---|---|
| 核心 prelude（134 decls） | ✅ 通过，nf=25，**1.55×** 领先 |
| HDL prelude（943 decls） | ✅ 通过，nf=219，**1.8×** 领先（移植 force memo 后） |
| 合成负载（natadd/gadt/match/struct/strchain/moduletree） | ✅ 全部 nf 一致，1.2-1.6× 领先 |
| 已修阻塞点 | 5 个（见 §10 时间线） |
| 剩余阻塞 | church/enum 生成器语法面；LSP 接线（观察面 + prelude 加载） |

---

## 1. 合成负载（孪生自带生成器，两版都通过）

release，min/med（ms），`--rounds 3`：

| 负载 | k | decls | basic | fast | fast_ss | fast/basic |
|---|---|---|---|---|---|---|
| natadd | 11 | 14 | 6.745 | 4.612 | 4.517 | 0.67× |
| gadt | 9 | 10 | 0.484 | 0.304 | 0.299 | 0.62× |
| match | 11 | 15 | 0.285 | 0.251 | 0.250 | 0.88× |
| struct | 11 | 4101 | 8657 | 7107 | 7175 | 0.82× |
| strchain | 11 | 4096 | 5458 | 3898 | — | 0.71× |

即孪生在这些负载上稳定领先 ~1.2-1.6×，与 L02-L08 的结论一致。但：

- `church` / `enum` 两族**两版都返回 nf=0**（生成器语法超出 L13 语言面，
  非分叉）。需要修生成器或换成 L13 合法源，否则这两族在 L13 无意义。
- 这些负载**都不加载 prelude**，与 LSP 的真实负载（HDL 文件 + 24 个
  prelude 文件）相去甚远。

## 2. 真实 prelude 负载（决定性，修复前）

`--workload prelude-core`（15 个核心 prelude 文件，134 decls）：

```
-- prelude-core (134 decls) NF-DIVERGE basic=25 fast=0
   basic         22.861ms
   fast           1.206ms
```

`basic` 能算完（nf=25），`fast` 返回 0 = 失败。`L13BENCH_DIAG=1` 二分定位：

```
[diag] prelude-core: twin 首个失败在第 51/134 个 decl (def add_zero_right):
       "can't unify\n  expected: String\n      find: Nat"
```

`def add_zero_right(a: Nat): Eq (a + 0) a = rfl`——`a + 0` 的 trait 求解
把 **`Add[String, String] for String`** 错选成了 `Nat` 的 `+` 实例，于是
`expected: String, find: Nat`。

### 2.1 最小复现（已核实）

```typort
def outParam[A](a: A): A = a
trait Add[T, O: outParam(Type 0)] { def +(that: T): O }
impl Add[String, String] for String { def +(that: String): String = string_concat this that }
enum Nat { zero
           succ(n: Nat) }
def nat_add(x: Nat, y: Nat): Nat = match y { case zero => x
                                            case succ(n) => succ (nat_add x n) }
impl Add[Nat, Nat] for Nat { def +(that: Nat): Nat = nat_add this that }

def f(a: Nat): Nat = a + zero
```

- 参考版：`Ok`（输出 `a => a`）
- 孪生：`Err("can't unify\n  expected: String\n      find: Nat")`
- **实例登记顺序敏感**：把 `impl Add[Nat,Nat]` 放到 String 实例之前 → 孪生
  `Ok`；只有 Nat 实例（无 String）→ 孪生 `Ok`。

## 3. 根因（已定位并修复）

trait 求解的三个"参数仍 flex → 推迟"判据（`has_flex_non_out` /
`has_flex_out` / out 参数跳过）与 flex defaulting 全用了 **`v_tag(v) == 5`**
（只认裸 meta），而参考版用的是 **`Val::Flex(..)`**——后者还覆盖
**meta 头链** `?m x`（twin 里 tag 2 且 `hk == HK_FLEX`）。而 trait goal 的
参数形态恰恰常是后者（`Flex(22, [Rigid(0)])`），于是：

1. 判据漏判 → 不推迟；
2. Phase 1 `val_match` 拿到 `Flex` 侧 → **对每个实例恒真** → 候选集污染成
   全部实例；
3. Phase 2 按 `matching_lvls` 登记序取第一个 → `Add[String,String]` 先登记
   → 选中它 → 用 `Nat` unify `String` → 报错。

追踪证据（`L13_TRACE_TRAIT=1`）：

```
# 修复前（twin）：goal 参数全是未解 flex，判据漏判
[TP-X] trait=Add all=[spine(Flex22(unsolved), len=1), spine(Flex23(unsolved), len=1), ...]
# 参考版：逐步解出 Sum(Nat) 后不再推迟
[REF-X] trait=Add all=[Sum("Nat"...), Flex(MetaVar(23), [(Rigid(Lvl(0)), Expl)]), ...]
```

## 4. 修复

`bump_spine_iter.rs::solve_trait_ref` 四处 flex 判据改用 `is_flex(&spine, v)`
（裸 meta 或 meta 头链）：

- flex defaulting 的 `any/filter`
- out 参数在实例匹配里的跳过
- `has_flex_non_out` / `has_flex_out`（顺带把重复 force 合并成
  `forced_params` 一次，避免借用冲突）

另修 `v_to_ref_val` 的 spine 链解码：原先每步把累积值整体换成
`Flex(MetaVar(u32::MAX), [该实参])`，既丢头（`?A x` → 通配 `?_ x`）又丢
更早的实参；改为保留真实头并逐个 `prepend` 实参。

## 5. 修复后实测

`prelude-core`（134 decls）：

```
-- prelude-core (134 decls) nf=25
   basic         24.607ms
   fast          15.948ms*   (1.54×)
```

`L13BENCH_DIAG=1` 报"twin 全部 134 decls 通过"，nf 与参考版一致。

`prelude-hdl`（943 decls）仍停在 decl 136
（`impl $trait_name$Nat for Nat`，`error name not in scope: nat_to_dec`）——
这是**bench 未注册 nat 内建**（`register_nat_builtins` 在参考版里于
nat.typort 加载后调用；孪生无对应机制，属阶段 5 的 prelude 加载缺口），
非新分叉。

回归：`cargo test --lib` 647 全过；`l13_fast_parity` 372 全过。

## 6. 对后续阶段的影响

- **阶段 5（LSP 接线）仍被阻塞**，但阻塞点从"trait 求解分叉"推进到
  "prelude 加载机制缺失"（nat/width 内建注册、宏、`PreludePool`）。
- **阶段 2（force memo）现在可以测了**——孪生已能跑核心 prelude，可以在
  上面量 force 次数/指针冗余。HDL 负载要先补内建注册。
- 合成负载的 1.2-1.6× 领先真实；核心 prelude 1.54× 领先。

## 7. 阶段 2（nat 内建注册）进展与剩余阻塞

给孪生补了 `register_nat_builtins`（`nat_to_dec` / `width_range` /
`nat_is_ground` + 五则算术 primop，逐句移植参考版 cxt.rs 的规则表），并加
了 `bench_check_nf_bounded` / `run_decls_bounded`（按 decl 下标在
"nat.typort 文件边界"注册——参考版 `load_prelude_state_impl` 同款时机），
参考版侧也加了对称的 `bench_check_nf_bounded`（原先它的 `bench_check_nf`
同样不注册 nat 内建，导致 `basic=0` 的假失败）。

效果：孪生在 HDL prelude 上的推进 **136 → 171 / 943 decls**。

### 7.1 decl 171 已修（Obj 臂剥 mk 链的 U(0) 占位）

根因：孪生 `infer_expr` 的 Obj 臂剥 `.mk` 构造子类型链时，**显式** binder
以 `U(0)` 实例化；参考版（elaboration.rs 2380-2398）用**接收者自身**
`Obj(this)`。于是 `this.data` 的投影类型在孪生里是
`Vec[ModuleDef](U(0))` 而非 `Vec[ModuleDef](this.num)`，下游
`cons m this.data` 的隐式 len 被迫解成 U(0)，
`expected: Vec[ModuleDef](this.num + 1) find: Vec[ModuleDef](Type 0 + 1)`。
所有带依赖索引字段（`data: Vec[T] num`）的 struct 投影都命中。

修复后最小复现（新增 `l13bench --workload moduletree`，8 decls）两版一致
（nf=11），HDL prelude 冲过 decl 171。

### 7.2 新阻塞：`Into` out 参数求解 + 模块树巨链（未解）

修掉 7.1 后，阻塞推进到 `Add[Nat, UInt[width]] for UInt[width]` 的方法体
`this + that.into`：孪生在 Def 臂 `solve_multi_trait_ref(...).unwrap()` 处
panic（`solve trait failed: Into[Nat, UInt[...]]`）。

已核实的事实（`L13_TRACE_INTO` 探针，已移除）：

- `Into` 只有 out 参数（`out_param = [false, true]`，含前置 Self），
  goal 的 out 槽是**未解 flex 的巨链**（`spine(len=63606)`，头 `Flex`，
  `is_flex=true`）——这是模块树值链，形态正常。
- `has_flex_non_out` / `has_flex_out` 判据**都正确触发**推迟
  （`cand=4, has_flex_out=true` → `Ok(None)`），与参考版一致。
- 因此分叉不在推迟逻辑；错误解来自**推迟之后**由上下文补齐的路径
  （`Add` 的 `has_flex_non_out=true` 也推迟，之后重试）。
- 参考版同源能收敛，说明差异在 `unify` / `rename` / `prune` 某一臂对
  「flex 巨链」的处理，或 pretty 里 `Variable index out of bounds` 对应的
  那个坏解的产生点。

**下一步**：用 `l13bench --workload moduletree` 加 `Into` 自反实例与
`Add[Nat, UInt]` 的最小组合复现（自包含，不带巨链），二分是 rename 越界
还是 unify 选错实例。注意：曾尝试把 `has_flex_out` 的判据从二次 force 改成
复用 `all_params`，**实测无效且偏离参考版**（参考版就是二次 force），已回退。

## 8. 阶段 3：force 记忆化移植（2026-09-09，**决定性**）

### 8.1 实测动机

孪生跑通 HDL prelude 后（§7.2 的 308 处阻塞已由 meta_cxt 修复解决）实测：

| 口径 | HDL prelude（943 decls） |
|---|---|
| basic（参考版） | 3.29s |
| fast（孪生，无 memo） | **11.04s（慢 3.4×）** |

与参考版自己的记录吻合：force 记忆化把 prelude 从 22.4s 降到 6.0s
（`docs/l13-perf-review-4.md` §16），而孪生此前**明确不移植**它
（模块头"不移植"清单）。LSP 每键击全量重推，这 3.4× 直接否决了接入。

### 8.2 实现与结果

参考版三根正确性支柱在 bump 模型下的处置：

1. **keepalive 免了**——bump 同代内单调分配、地址不复用；每轮入口
   `force_memo_clear()`（4 个 `bump.reset()` 处）。
2. **taint**：未解 meta（裸 tag 5 / flex 链头）与有副作用 prim
   （`prim_is_pure` 白名单外）→ bump 线程局部计数器，动过的条目不插入。
3. **prim-ness 版本**：`decl_reg` 里 prim 槽有无变化即 `prim_version_bump`，
   条目记版本、不匹配即 miss。

结果：

| 口径 | HDL prelude | core prelude |
|---|---|---|
| basic | 3.29s | 26.8ms |
| fast（移植后） | **1.83s（1.8× 反超）** | 16.0ms（1.67×） |

## 9. 下一步（按优先级）

1. 修 `church`/`enum` 生成器（L13 语言面），恢复两族对照。
2. LSP 接线（阶段 5，最大）：观察面（hover/completion/inlay/accumulated_errors/
   defer_println）+ prelude 加载（PreludePool/宏）+ 跨请求数据面。
3. 扩 parity 覆盖到 namespace/class/trait/Nat 语言面。

## 10. 阻塞点修复时间线

| # | 问题 | 修复 |
|---|---|---|
| 1 | trait 求解漏判 meta 头链 flex → 核心 prelude 选错实例 | `is_flex` 替代 `v_tag==5`（019ac19） |
| 2 | 无 nat 内建注册 → HDL 首个 nat_to_dec 引用即失败 | 移植 `register_nat_builtins`（f166c4c） |
| 3 | Obj 臂剥 mk 链用 U(0) 占位 → 依赖索引字段投影类型退化 | 改用接收者自身（6c7f0bd） |
| 4 | Def 臂 solve_multi_trait 失败 unwrap panic | 改返回 Err（ec3eb6e） |
| 5 | 用调用方上下文求解 meta（层级错位）→ 越界变量 | 改用 meta 创建处快照（7fcb67c） |
| 6 | 无 force 记忆化 → HDL 慢 3.4× | 移植 FORCE_MEMO（d85a759） |

## 11. 复现命令

```bash
cargo run --release --bin l13bench -- --workload prelude-core --rounds 3 --only basic,fast
cargo run --release --bin l13bench -- --workload prelude-hdl --rounds 3 --only basic,fast
cargo run --release --bin l13bench -- --workload moduletree --rounds 3 --only basic,fast
L13BENCH_DIAG=1 cargo run --release --bin l13bench -- --workload prelude-hdl --rounds 1 --only fast
cargo run --release --bin l13bench -- --workload struct --max-k 11 --rounds 3 --only basic,fast,fast_ss
```

