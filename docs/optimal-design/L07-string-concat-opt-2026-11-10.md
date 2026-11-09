# L07 `string_concat` 单次拷贝优化（F1a）：A/B 与不落地记录（2026-11-10）

> 背景：COW（`c2fffd3f`）、FxHash（`72f12101`）、深作用域（`65d4512a`/`d411debe`）之后，
> L07 参考版在 `strchain`/`global` 上仍比孪生慢约 2.2×。本文件记录该差距的一个候选：
> `prim_reduce` 的 `string_concat` 先去深拷旧串再 `format!`（同一次归约拷两遍）。
>
> **结论：单独落地收益只有 ~3–4%（strchain）/ ~0（global），不按性能项落地。**
> 若将来做下面的 F1c（`Val` 字面量载荷 `Rc<str>`）可以顺手合并——语义完全等价、零风险。
> 同轮 review 的另一项（覆盖探测 U1+U2）已落地 `a78daec7`，与本文件无关。

## 1. 候选改动（未合入）

位置：`src/L07_sum_type/mod.rs`，`Infer::prim_reduce` 的 `"string_concat"` 臂（当前主线 :1040 附近）。

改前（每个 concat 对旧串拷 2 遍：`a.clone()` 一次 + `format!` 写入一次）：

```rust
match (&args[0], &args[1]) {
    (Val::LiteralIntro(a), Val::LiteralIntro(b)) => Some(Val::LiteralIntro(
        a.clone().map(|x| format!("{x}{}", b.data)),
    )),
    _ => None,
}
```

改后（只 `format!` 一次；span 位置/path 原样保留——`Span::map` 语义等价）：

```rust
match (&args[0], &args[1]) {
    (Val::LiteralIntro(a), Val::LiteralIntro(b)) => Some(Val::LiteralIntro(Span {
        data: format!("{}{}", a.data, b.data),
        start_offset: a.start_offset,
        end_offset: a.end_offset,
        path_id: a.path_id,
    })),
    _ => None,
}
```

体量：11 insertions / 3 deletions，不改类型/API/判定。

## 2. 为什么收益小

`strchain` 每层 `def s_i = string_concat s_{i-1} "x"` / `global` 每层 `change_mutable "k" (s => string_concat s "x")`
在检查期对上一版长串做多次全长复制（串长随层数线性增长，总量 O(n²)）：

| 路径 | strchain | global |
|---|---|---|
| `eval(Tm::Var)` / `eval(Tm::Decl)` 的值 clone | 1 | 1 |
| `force(Val::Prim)` 把实参 `v.clone()` 进 `args: Vec`（`mod.rs:879`） | 1 | 1 |
| `mutable_map.get(...).cloned()`（global 特有） | — | 1 |
| **本候选：`string_concat` 旧串 clone + format 写入** | **2 → 1** | **2 → 1** |
| `format!` 生成新串（必要） | 1 | 1 |

本候选只省“每层若干份全长拷贝”里的 **1 份**；global 的耗时还受 `mutable_map` 读写/闭包 β 应用影响，
不是纯拷贝带宽瓶颈，所以看不到收益。

## 3. A/B 实测（release，交错多进程取 min）

测量方法：每个变体单独进程跑 `--workload <wl> --max-k 14 --rounds 5 --only basic,fast`，
新旧两进程按正/反序**交错 6 次**，每格取 min；同机同窗口；F: 盘不构建。

| 基线 | workload k=14 | 改前 (ms) | 改后 (ms) | Δ |
|---|---|---:|---:|---:|
| `1f382a2a`（旧主线） | strchain | 167.873 | 161.570 | **−3.8%** |
| `1f382a2a`（旧主线） | global | 160.860 | 160.988 | 0.0% |
| `9530205d`（新主线） | strchain | 167.233 | 162.506 | **−2.8%** |
| `9530205d`（新主线） | global | 149.280 | 150.890 | +1.1%（噪声） |

判读规则（与 review 一致）：**≥10% 才算信号**；本次 <5%，不达标。
twin `fast` 对照行在 A/B 中不变（改动只打在参考版）。

## 4. 语义与风险（若将来顺手合并）

- 与 `Span::map` 的输出等价：data 重算、`start_offset/end_offset/path_id` 原样保留
  （L07 的值 span 参与诊断/quote，不能用 `empty_span` 替换）。
- 无类型/API 变化；包含该项的等价分支跑过门禁：`--lib L07_sum_type` 70 passed、
  `l07_blackbox_v3` 116 passed + 1 ignored、`l07_fast_parity` 97 passed。
- 成本 1 个函数 11 行，风险接近 0；属“看到就顺手带”的 hygiene，不单独立项。

## 5. 真正值得做的后续（2.2× 的候选）

1. **F1b：`force(Val::Prim)` 字面量快路径**——当前每个 prim 触发都把实参 `clone` 进 `Vec`
   （`mod.rs:879`）；`string_concat` 的实参在 strchain/global 全是字面量，可按引用先判断/直接借
   `&sp` 归约，省掉另一份全长拷贝（~15 行）。
2. **F1c：`Val::LiteralIntro(Span<String>)` → `Rc<str>` 载荷**——`eval(Var/Decl)`、
   `force` 实参 clone、`mutable_map.cloned()` 全部退化为 O(1) 引用计数，只剩 concat 必须的一次
   `format!`。review 估计 strchain/global 可达 **1.5–2×**（30–60 行，需 parity 门禁；不做全量
   `Span<()>` 重构）。
3. 主线深作用域升级（`65d4512a`/`d411debe`）后仍有第三个 O(n²)：deep 探针 n 翻倍仍 4.4–4.75×
   （主线文档 §4.3 已记录未定位），与本节独立。

## 6. 复现

```powershell
# 在 C: 盘 worktree/目标目录（F: 不构建）：
#   git checkout <基线>；应用上文的 11 行改动；构建 l07bench
C:\ezl-target-l07fix\release\l07bench.exe --workload strchain --max-k 14 --rounds 5 --only basic,fast
C:\ezl-target-l07fix\release\l07bench.exe --workload global   --max-k 14 --rounds 5 --only basic,fast
# 旧/新进程交错 6 次，取各格 min 对比；twin 的 fast 行作对照。
```

> 测量用的 l07bench 增强行（`basic_check/fast_check/basic_setup/fast_setup`、`--workload empty`、
> `--workload manydefs`）属于临时 harness，未合入主线；A/B 时新旧两侧用同一份 harness 即可。
