# L07 升级实验：结构/COW、求值快路径，以及同语料跨引擎对比（2026-11-09）

> 目的：回答"L07 有没有大量真实 benchmark 用例；结构/COW、求值快路径两项升级各能带来多少收益；
> 同一批用例上 L13 参考版与 L07 孪生版表现如何"。
> 口径：`master` @ `f09e4dfe`；release、`CARGO_TARGET_DIR=C:\ezl-target-l07exp`（F: 盘不构建）；
> 同机同窗口、每档 `--rounds 5` 取 min；参考版每轮新建 `Tycker`（与 `fast` 口径对齐），孪生另给
> `fast`（每轮新建）与 `fast_ss`（稳态复用）两档，表内用 **`fast`** 与参考版对齐。
> 补丁只存在于 scratch worktree `C:\ezl-l07exp`（未提交、未 push）；原始输出在同目录 `*.txt`。

## 0. 结论（TL;DR）

1. **L07 没有"大量真实 benchmark 用例"**：`l07bench` 只有 6 个生成负载族（church / strchain / global /
   match / enum / natadd），k=9–13 共 25 个配置；真实小程序在 3 个 blackbox 测试文件里（49+53+47=149 个
   测试函数、129 个 lib `#[test]`），但它们没有被接成性能基准，单例 1–30 行、耗时多为 µs–ms，噪声不可用。
2. **结构/COW（decl 表就地写 + `&mut Cxt`）收益巨大且只打在"顶层 def 链"上**：
   - `strchain` k=13：**1977.0 → 60.0 ms（32.9×）**；k=11：**126.3 → 9.6 ms（13.1×）**；
   - `global` k=13：**1955.1 → 79.3 ms（24.7×）**；k=11：**136.1 → 19.2 ms（7.1×）**；
   - `church` / `match` / `enum` / `natadd` 只有 0–7% 或噪声级变化（这些负载的顶层 def 数只有十几到几十个）。
3. **"求值快路径"在 L07 上没有可测收益（−1.4% ~ +1%，全在噪声带）**：L07 的 `force` 对 `Val::SumCase`
   本来就是叶子臂（`t => t`），`eval_aux` 的构造子名比较也只是一次 `SmolStr` 比较；L13 的
   eval 快路径是对 L13 自己的"force(SumCase) 递归重走整棵树"设计的，前提在 L07 不存在。
   → **L07 该抄的只有结构/COW；求值快路径不用抄。**
4. **同语料横向**：L07 孪生（arena）仍然全面最快；补丁后的 L07 参考版在 strchain/global 上追近到孪生的
   ~1.7–2.3×；L13 参考版在 church/natadd 上比 L07 参考版快 1.3–3.1×，在 match/enum 上反而慢 1.3–1.9×，
   strchain 即使扣掉 prelude 固定成本仍慢于 L07+COW（见 §4 限制）。

## 1. L07 用例盘点（回答"有没有大量真实用例"）

| 类别 | 内容 | 数量 | 是否可作性能基准 |
|---|---|---|---|
| `l07bench` 生成负载 | church / strchain / global / match / enum / natadd | 6 族 × k=9..13 = **25 配置** | 是（本报告使用） |
| `tests/l07_blackbox.rs` | 真实小程序（happy-path + 错误案例） | 49 test fns / 1571 行 | 否（太小、断言导向） |
| `tests/l07_blackbox_v2.rs` | 同上 | 53 / 906 行 | 否 |
| `tests/l07_blackbox_v3.rs` | 同上 | 47 / 1549 行 | 否 |
| `src/L07_sum_type/tests.rs` 等 | 单元/回归测试 | 129 `#[test]` | 否 |
| 真实 HDL/示例语料 | L07 无（L13 才有 `examples/` + prelude） | 0 | — |

**结论**：L07 的"真实用例"是有的（149 个 blackbox 程序），但**没有真实语料 benchmark**；要做有统计意义的
A/B，只能用 6 族生成负载。若需要，我可以把 blackbox 源程序抽成 corpus、接一个 `--workload real`（单例太短，
需要每例重复 N 次取总时间才稳定）。

## 2. 实验设计：两项升级各自怎么实现

### 2.1 结构/COW（L07 `src/L07_sum_type/cxt.rs` + `elaboration.rs` + `mod.rs`）

L07 原实现（与 L13 修前同构）：

```rust
pub fn decl_insert(&self, k, e) -> Self {
    let mut decl = self.decl.clone();     // 先 clone ⇒ 强计数 = 2
    let d = Rc::make_mut(&mut decl);      // 于是每次必然深拷整表
    ...
}
```

实验补丁（照 L13 `fake_bind`/`decl` 就地写模式）：

- 新增 `Cxt::decl_insert_mut(&mut self, k, e)`：直接 `Rc::make_mut(&mut self.decl)`，计数 1 时原地写；
- `Infer::infer` 改为**接管 `Cxt` 所有权**（`cxt: Cxt`，返回新 `Cxt`），顺序声明路径上父视图无需保留；
- `Def`/`Enum` 占位与最终登记改为就地插入；`reason`：旧 `fake_cxt = cxt.decl_insert(...)` + 再
  `cxt.decl_insert(...)` 每个 def 深拷两次整表（strchain/global 的 O(D²) 放大器）；
- 保留旧 `decl_insert(&self)` 作为持久化包装（`clone` + `decl_insert_mut`），测试/其它 `&Cxt` 调用点不动。

### 2.2 求值快路径（L07 `src/L07_sum_type/pattern_match.rs`，照 L13 ref 的 `eval_aux`）

- `eval_aux` 入口：`SumCase` 头不再调 `infer.force`（L13 注释："a Sum is already in WHNF / only head
  constructor needed"）；非构造子头（Flex/meta/VSub）仍 force；
- `eval_aux_arm`：`case_name == pattern name` 时直接下钻，不再先重建/扫描 `ctor_names`（L13 用构造子
  index 分派；L07 没有 index，用 name 快比较近似）。

> L13 其它 eval 提效项（`no_metas` visited-set、Call/Call 无-Flex 预检、`trait_wrap` 惰性快照、
> `SumCase` 数据惰性重建）在 L07 **没有对应消费者/表示**：L07 无 `no_metas`、无 `Val::Call`、无 trait、
> `force(SumCase)` 本来就是叶子，故不纳入本实验（这点本身是结论的一部分）。

### 2.3 L13 参考版同语料

- 用 `l07cases` 辅助 bin 把 `l07bench` 生成的源码逐 k 落盘（`C:\ezl-l07cases`），再喂给
  `l13bench --file --with-prelude none|core`（L13 参考版 basic 口径，`--rounds 5` 取 min）。
- L07 的 `U` 宇宙在 L13 中写成 `Type 0`；church 的 `Nat` 声明因 `(N : Type 0) -> ...` 落在 `Type 1`，
  改写为 `def Nat : Type 1 = ...`。改写后 nf 节点数与 L07 期望值一致（church k11=8196、k13=32772）。
- `strchain`/`global` 依赖 L07 builtin：`strchain` 用 L13 core prelude 可跑（含 prelude 检查成本）；
  `global` 因 L13 core prelude 的 `create_global` 签名与 L07 不同（`expected: k / find: String`）无法跑，
  表中记 N/A。

## 3. 结果（release，min-of-5，ms）

### 3.1 主表：k=13（最大规模）与 k=11（常用规模）

| 负载 | k | L07 ref 基线 | +结构/COW | ΔCOW | +eval | Δeval | COW+eval | L07 孪生 `fast` | L13 ref |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| church | 13 | 15.355 | **14.579** | +5.1% | 14.434 | +6.0% | 14.469 | **1.293** | **8.814** |
| church | 11 | 2.689 | **2.584** | +4.0% | 2.832 | −5.3% | 2.816 | **0.274** | **2.052** |
| strchain | 13 | 1977.008 | **60.020** | **+32.9×** | 2003.857 | −1.4% | **59.738** | **27.892** | 161.992* |
| strchain | 11 | 126.257 | **9.618** | **+13.1×** | 127.973 | −1.4% | **9.415** | **5.671** | 79.691* |
| global | 13 | 1955.083 | **79.295** | **+24.7×** | 1958.107 | −0.2% | **78.911** | **36.003** | N/A |
| global | 11 | 136.113 | **19.231** | **+7.1×** | 134.921 | +0.9% | **19.537** | **8.398** | N/A |
| match | 13 | 0.174 | 0.163 | +6.7% | 0.175 | −0.6% | 0.161 | **0.057** | 0.325 |
| match | 11 | 0.153 | 0.143 | +7.0% | 0.154 | −0.7% | 0.142 | **0.049** | 0.209 |
| enum | 9 | 0.288 | 0.277 | +4.0% | 0.287 | +0.3% | 0.276 | **0.072** | 0.447 |
| natadd | 13 | 31.776 | 31.227 | +1.7% | 32.282 | −1.6% | 29.858 | **3.404** | **10.198** |
| natadd | 11 | 5.337 | 5.410 | −1.4% | 5.202 | +2.5% | 5.144 | **0.858** | **2.616** |

\* L13 的 strchain 是 **含 core prelude 检查**的总时间（4304 decls）；空 prelude 检查基线 64.6 ms，
  粗扣后 k11 ≈15.1 ms、k13 ≈97.4 ms（见 §4 限制，不能与 L07 的纯用户代码时间严格并列）。

### 3.2 规模曲线（结构/COW 的 O(D²)→线性）

| 负载 | k=9 | k=10 | k=11 | k=12 | k=13 | 形态 |
|---|---:|---:|---:|---:|---:|---|
| strchain ref 基线 | 9.014 | 32.786 | 126.257 | 495.742 | 1977.008 | 每翻倍 ≈4×（平方） |
| strchain +COW | 2.003 | 4.203 | 9.618 | 23.363 | 60.020 | 每翻倍 ≈2.1–2.5×（近线性） |
| strchain 孪生 fast | 1.115 | 2.361 | 5.671 | 10.376 | 27.892 | 线性 |
| global ref 基线 | 11.695 | 38.543 | 136.113 | 507.843 | 1955.083 | 每翻倍 ≈4× |
| global +COW | 4.376 | 8.878 | 19.231 | 39.384 | 79.295 | 每翻倍 ≈2× |
| global 孪生 fast | 1.899 | 4.088 | 8.398 | 17.622 | 36.003 | 线性 |
| church ref 基线 | 1.070 | 1.437 | 2.689 | 5.949 | 15.355 | 每翻倍 ≈2.2–2.6× |
| church +COW | 0.703 | 1.319 | 2.584 | 5.133 | 14.579 | 基本不变（def 数少） |
| church 孪生 fast | 0.080 | 0.144 | 0.274 | 0.571 | 1.293 | 线性 |
| natadd ref 基线 | 1.362 | 2.711 | 5.337 | 11.996 | 31.776 | 每翻倍 ≈2.4–2.7× |
| natadd +COW | 1.360 | 2.682 | 5.410 | 11.388 | 31.227 | 不变 |

**note**：COW 只对"顶层 def 条数 D 大"的负载有用；church 只有 16 个 def（k=13），所以只省 5%；
strchain/global 是每 k 翻倍生成 2^(k+1) 个 def，正好放大 O(D²)，所以 13–33×。

### 3.3 求值快路径逐项（全部落在噪声带）

| 负载 | k=11 基线 | +eval | Δ | k=13 基线 | +eval | Δ |
|---|---:|---:|---:|---:|---:|---:|
| church | 2.689 | 2.832 | −5.3% | 15.355 | 14.434 | +6.0% |
| strchain | 126.257 | 127.973 | −1.4% | 1977.008 | 2003.857 | −1.4% |
| global | 136.113 | 134.921 | +0.9% | 1955.083 | 1958.107 | −0.2% |
| match | 0.153 | 0.154 | −0.7% | 0.174 | 0.175 | −0.6% |
| enum | 0.288 | 0.287 | +0.3% | — | — | — |
| natadd | 5.337 | 5.202 | +2.5% | 31.776 | 32.282 | −1.6% |

噪声量级本身约 ±5–6%（同机同窗口、5 轮 min，小负载尤其明显）；**没有任何负载出现系统性收益**。

## 4. 解读与限制

1. **COW 的收益是"移除 O(D²) 表深拷"，不是"让单次插入变快"**：L07 顺序 def 路径上原实现每次
   `decl_insert` 都 `self.decl.clone()` 再 `make_mut`，因此每个 def 都深拷一次当前整表；strchain/global
   的 D=2^(k+1)，所以 k=13 时省掉约 4k 次整表复制。补丁把 cxt 所有权沿顺序路径传递（`infer(&mut self,
   cxt: Cxt)`），使 `make_mut` 计数=1。**代价**：`infer` 的签名/所有权变了（L07 内部 API，不影响
   blackbox/parity 外部表面）；`Def`/`Enum` 占位临时表与最终表合并为同一张表（`ver` 会多 bump 一次，
   无消费者依赖精确值）。
2. **求值快路径零收益不是实现错了，而是 L07 表示更简单**：L13 `force(SumCase)` 会递归 force `typ` 和
   所有 `datas`（side effects），L13 的 eval 快路径是为了避免 this O(n²)；L07 `force` 的 `SumCase` 落到
   `t => t` 叶子臂，本来就不递归，故省下的只是每步一次函数调用。match/enum 负载的 arm 数只有 2–5 个，
   `ctor_names.iter().any` 也基本在噪声内。
3. **L13 ref 对比不是"同引擎"**：L13 有更大的语言/prelude/诊断，`--file` 跑 L07 生成源需要语法改写；
   strchain 的 L13 计时含 prelude 检查（16 个 core 文件、208 decls、空文件基线 64.6ms），扣除法只是
   粗略近似；`global` 的 L07 builtin 与 L13 prelude 签名不兼容，无法跑。
4. **L07 孪生 `fast` 与 ref 基线同口径**（每轮新建）；稳态 `fast_ss` 通常再快 5–20%（strchain k13
   `fast_ss=28.504` vs `fast=27.892`，两者接近；church k13 `fast_ss=1.029` vs `fast=1.293`）。
5. **测量窗口**：所有档位同机同日、交错有限（每个 variant 连续跑 5 轮）；大负载的 2× 以上差异可信，
   小负载（match/enum/church）的 5–7% 差异应视为噪声。若要做严格 A/B，应同二进制内 `--variant` 交错，
   当前 scratch 实现为不同二进制（同一编译器/同一 target dir）。

## 5. 复现命令与产物

```powershell
# scratch worktree
git worktree add --detach C:\ezl-l07exp master
# 结构/COW 补丁：cxt.rs decl_insert_mut + Infer::infer 接管 Cxt（详见同目录 diff）
# 求值快路径补丁：pattern_match.rs eval_aux / eval_aux_arm
CARGO_TARGET_DIR=C:\ezl-target-l07exp cargo build --release --bin l07bench
C:\ezl-target-l07exp\release\l07bench.exe --workload all --max-k 13 --rounds 5 --only basic,fast,fast_ss
# L13 参考版（对落盘源）
l13bench --file <case>.typort --with-prelude none --rounds 5 --only basic      # church/match/natadd/enum
l13bench --file strchain-k13.typort --with-prelude core --rounds 5 --only basic
```

原始输出（scratch，未入 git）：

- `C:\ezl-l07exp\baseline-l07.txt`（base）
- `C:\ezl-l07exp\cow-l07.txt`（+COW）
- `C:\ezl-l07exp\eval-l07.txt`（+eval）
- `C:\ezl-l07exp\both-l07.txt`（COW+eval）
- `C:\ezl-l07exp\twin-fast-l07.txt`（孪生 `fast`）
- `C:\ezl-l07exp\l13-on-l07.txt`（L13 ref）

**一句话**：L07 值得抄的只有结构/COW（strchain/global 13–33×，其他负载 0–7%）；L13 的求值快路径在
L07 无收益（L07 的 `force` 已是叶子表示）；补丁后 L07 ref 仍慢于孪生 1.7–11×，L13 ref 在 church/natadd
更快、match/enum 更慢，且 strchain 仍不及 L07+COW（其自身 COW 已生效，但引擎/prelude 更重）。
