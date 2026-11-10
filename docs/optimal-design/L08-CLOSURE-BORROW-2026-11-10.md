# L08 残余 scaling 差距：closure_apply 借用修复（2026-11-10）

## 背景

修掉 `eval_aux` 分支体 clone 后，natadd k10 已从 3.19ms 降到 2.51ms，但还有：

- church k10：L08 0.99ms vs L07 0.72ms
- natadd k11：L08 5.30ms vs L07 4.28ms

而且差距随 `k` 缓慢放大（church k9→k11 比值 1.18→1.37），说明仍有一个“每次 β/递归都付费”的项。

## 定位

对比 `Infer::closure_apply`：

```rust
// L07（P0-1 第 2 步）
self.eval(decl, &closure.0.prepend(u), &closure.1)

// L08 旧实现
self.eval(decl, &closure.0.prepend(u), (*closure.1).clone())
```

L07 已经改成借用闭包体；L08 每次 **β 归约都 clone 整个 Rc<Tm> 闭包体**。
church 是 λ 演算数（大量 β），natadd 的递归 `add` 每次递归也 β 一次；这正好解释：
- 差距随规模线性增长；
- 不是 Cxt、不是 match 分支选择（那部分已修）。

## 修复

提交 `fd5a3a95`：

```rust
fn closure_apply(&self, decl: &Decls, closure: &Closure, u: Val) -> Val {
    self.eval_ref(decl, &closure.0.prepend(u), &closure.1)
}
```

语义不变，只去掉每次 β 的闭包体 deep clone。

## A/B

同窗口、交错 A/B/B/A、min-of-6：

| workload | before | after | ratio |
|---|---:|---:|---:|
| church k11 | 1.994 ms | 1.409 ms | **0.707×（−29.3%）** |
| natadd k11 | 5.304 ms | 3.983 ms | **0.751×（−24.9%）** |
| struct k10 | 7.646 ms | 7.051 ms | 0.922× |
| match k13 | 0.120 ms | 0.119 ms | 0.992× |
| strchain k11 | 8.215 ms | 8.536 ms | 1.039×（噪声） |

## L08 vs L07 当前（同 k，交错）

| workload | L07 | L08 final | L08/L07 |
|---|---:|---:|---:|
| church k11 | 1.431 ms | 1.409 ms | 0.985× |
| natadd k11 | 4.279 ms | 3.983 ms | 0.931× |
| strchain k11 | ~8.45 ms | ~8.54 ms | ~1.01× |
| match k13 | 0.125 ms | 0.119 ms | 0.952× |

L08 在 L07 共有的这些 workload 上已经持平或略快；残余只有 L08 独有的 struct/Obj 功能成本。

## 门禁

- L08 lib 60；blackbox 57+1 / 51+2；parity 95
- `cargo check --all-targets` 0 error
- 全量 lib **994 passed / 0 failed / 6 ignored**
