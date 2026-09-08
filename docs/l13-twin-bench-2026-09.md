# L13 双引擎基准第一轮（2026-09-08）——性能孪生无法吃下核心 prelude

> 目的：L13 性能孪生 `bump_spine_iter.rs` 至今没有 bench（无 `l13bench`），
> ref vs twin 一次都没实测过。本轮补 `src/bin/l13bench.rs`，在合成负载与
> 真实 prelude 负载上量三口径（`basic` 参考版 / `fast` 孪生一次性 /
> `fast_ss` 孪生稳态）。
>
> **核心结论**：孪生原先**连核心 prelude 都跑不完**——trait 求解在 flex
> goal 上选错实例。本轮已修复（见 §6），修复后孪生跑完 134 个核心 prelude
> decl 且 nf 与参考版一致（25），耗时 **1.54×** 领先。合成负载上孪生
> 稳定领先 1.2-1.6×。HDL prelude 仍受"无 nat 内建注册"阻塞（阶段 5 的
> prelude 加载缺口）。

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

效果：孪生在 HDL prelude 上的推进 **136 → 171 / 943 decls**。剩余阻塞是
decl 171 的 `can't unify`（`impl $trait_name$ModuleTree`，struct 脱糖出的
inherent impl，涉及 class/module-macro 链）——属模块头"已知偏差 2"的
class/struct 接收者家族，**不是 nat 内建问题**（诊断确认失败时
`nat_to_dec` 在 decl 表中）。

最小复现/下一步：定位 decl 171 的 unify 失败（class 两阶段 + 宏展开链的
`Raw::Tm` 指针导入表与 trait 求解交互）。

## 8. 下一步（按优先级）

1. 定位并修 decl 171 的 unify 失败（class/module-macro 家族）。
2. 修 `church`/`enum` 生成器（L13 语言面），恢复两族对照。
3. 孪生能跑 HDL 负载后，测 force 次数/指针冗余，决定是否移植 force memo。
4. 之后才谈阶段 3-5。

## 9. 复现命令

```bash
cargo run --release --bin l13bench -- --workload prelude-core --rounds 3 --only basic,fast
L13BENCH_DIAG=1 cargo run --release --bin l13bench -- --workload prelude-core --rounds 1 --only fast
cargo run --release --bin l13bench -- --workload struct --max-k 11 --rounds 3 --only basic,fast,fast_ss
```

