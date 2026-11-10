# L08 natadd 2× gap：profiling 与 eval_aux 借用修复（2026-11-10）

## 问题

master/branch 上 L08 的 `natadd` 一直比 L07 慢约 28%（k10：3.19ms vs 2.61ms）。
之前的 phase probe 只能确认差距在 **check**（不是 nf/quote），但 check 内部没有定位。

## 定位方法：按源码形态做消融

用临时 dual-layer probe（L07/L08 同进程）构造 `natadd` 的几种变体，n=10（与 bench 的 k=10 一致），
每轮 `bench_check` 取中位数：

| p_i 定义 | L07 | L08 | L08/L07 |
|---|---:|---:|---:|
| `p{i-1}`（plain） | 0.111 ms | 0.103 ms | 0.93× |
| `succ p{i-1}` | 0.110 ms | 0.107 ms | 0.97× |
| `add p0 p0`（小常量） | 0.160 ms | 0.196 ms | 1.23× |
| `add p{i-1} p0`（大第一个参数） | 0.369 ms | 0.568 ms | **1.54×** |
| `add p0 p{i-1}`（大第二个参数） | 0.173 ms | 0.202 ms | 1.17× |
| `add p{i-1} p{i-1}`（真实负载） | 5.347 ms | 9.699 ms | **1.81×** |

结论：
- 差距不在 per-def 的 Cxt/decl 处理（plain 反而 L08 略快）；
- 不在 constructor 应用（succ 持平）；
- 只在 **递归 `add` 匹配第一个大 Nat** 时出现，且随第一个参数规模放大。

`add` 定义是：

```text
def add(x: Nat, y: Nat): Nat =
    match x { case zero => y; case succ(n) => succ (add n y) }
```

第一个参数是 size 2^n 的 Nat；对它递归做 match，分支选择次数也是 2^n 量级。

## 根因

L08 的运行时 `Compiler::eval_aux` 返回 **clone 后的分支体** `Tm`：

```rust
pub fn eval_aux(...) -> Option<(Tm, Env)> {
    ...
    PatternDetail::Any(_) | PatternDetail::Bind(_) => {
        return Some((body.clone(), env.prepend(head.clone())));
    }
```

L07 返回借用的 `&Tm`，eval 直接借用求值；L08 的 `eval` 按值消费 Tm，所以每个 match 步都要
clone 一次分支体。`add` 递归 2^n 步时就多出 2^n 次 `Tm` clone/分配，正好对应 2× 常数差。

## 修复

提交 `bc929dcc`：

- `Compiler::eval_aux` 改为 L07 形态：`Option<(&Tm, Env)>`，不再 clone 分支体；
- L08 `eval` 增加借用式 `eval_ref(&Tm)`，原有 `eval(Tm)` 作为 wrapper；
- `force` 的 `Val::Match` 臂也用 `eval_ref` 处理选中分支；
- 语义不变，只去掉每步分支体 clone。

## A/B

同一窗口、交错 A/B/B/A、min-of-6：

| workload | before | after | ratio |
|---|---:|---:|---:|
| natadd k10 | 3.192 ms | 2.514 ms | **0.788×（−21.2%）** |
| strchain k11 | 7.934 ms | 7.930 ms | 0.999× |
| match k13 | 0.118 ms | 0.119 ms | 1.008× |
| struct k10 | 7.607 ms | 7.483 ms | 0.984× |
| church k10 | 0.935 ms | 0.988 ms | 1.057×（噪声） |

natadd 现在与 L07 的 ~2.2ms 基本同量级，剩余差异只剩 L08 产品/Obj 扩展的常数项。

## 门禁

- L08 lib 60；blackbox 57+1 / 51+2；parity 95
- `cargo check --all-targets` 0 error
- 全量 lib（合并后）通过
