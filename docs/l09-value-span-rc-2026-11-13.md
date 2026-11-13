# L09 低成本增值两项的实验报告：rc_take unique-move vs Val 名字 span Rc 化（2026-11-13）

> 任务（用户）：「L09 可选低成本增值 这两点分别尝试一下，看看收益分别多少以及合起来多少」。
> 两项候选（来自 `docs/l10-perf-advantages-2026-11-13.md` §2.5）：
> ① 投影/match 抽取路径的 `rc_take`：`Rc<Vec>` 独占时 move 字段，避免共享分支深拷；
> ② `Val` 名字 span 从 `Span<String>` 改成廉价克隆句柄（本报告实测选 `Rc<Span<String>>`，
>    即 `VSpan`），让 Val 克隆热路径不再为每个构造子/绑定器名做 String 堆分配。
>
> **结论先行**：① 实测收益 ≈ **0（噪声内，已否决并回退）**；② 实测收益 **显著**
> （最重负载 common ladder −24.9%，`realbench` L09 common 67.06→50.39 ms；l09bench
> strchain −17.6%、natadd −21.0%、struct k10 −20.8%、match −13.6%、enum −6.3%、
> universe −9.0%、church ≈持平）；**合起来 = ②（① 增量在噪声内）**。

## 1. 方法与基线

- 快速迭代工具：临时 bin `l09probe`（口径与 `realbench` 的 L09 `basic` 一致：parse 在
  计时外，逐 Decl `bench_check_nf`；大栈线程；min/med 多轮）。**实验后已删除**（保留
  `realbench` 复现口径）。基线/变体各自 rebuild 后测，同一台机、同窗口、min-of-5。
- 官方复核口径：`target/release/realbench.exe`（改前/改后各 rebuild 一次）+
  `l09bench.exe`；与 `.deltawork/perf09/baseline/` 的 round-2 基线（`ab_recheck2`）对齐。
- 基线（改动前 = commit `fc5dfe92` 状态，`realbench --only basic --rounds 3`，ms）：
  common **67.055**；L09 自有语料 **9.116**；Eq 阶梯单文件 **2.988**；
  l09bench：church k11 1.367 / strchain 9.106 / match 0.103 / enum 0.222 /
  struct k10 6.286 / natadd 3.360 / universe 4.541。

## 2. 实验 ①：`rc_take` unique-move（收益 ≈ 0，否决）

先用临时计数探针（同一 fixture；计数后已移除）量出真实热路径：

| 计数（common ladder_l07_large，单轮） | 值 |
|---|---:|
| `Val::clone` 总次数 | **1,165,017** |
| ├ `SumCase`（构造子值） | 666,144 |
| ├ `Sum`（类型头） | 302,958 |
| ├ `Lam`（闭包） | 191,935 |
| `rc_take` 调用 | **1,405** |
| └ 其中独占 move / 共享深拷 | **0 / 1,405** |

即：**`rc_take` 不是热路径**（1.4k 次 vs Val 克隆 1.17M 次，最多 <0.2% 收益），
且共享分支的"深拷"实际是 Val 枚举浅拷贝+名字 String 分配（子值仍 Rc 共享）。
按任务要求仍实现了 unique-move 快路径（`Rc::strong_count(&datas)==1` 时
`Rc::try_unwrap` 后 `Vec::remove` move 字段；共享走回退），改两个投影抽取臂后实测：

| 文件（probe，min-of-5，µs） | 基线 | ①-only | 变化 |
|---|---:|---:|---:|
| common ladder_l07_large | 61,167 | 60,499 | −1.1%（噪声） |
| L09 Eq 阶梯 | 2,942 | 3,013 | +2.4%（噪声） |
| proofs_400 | 2,839 | 2,829 | −0.4% |
| plain_defs_800 | 610 | 603 | −1.1% |
| old_global_800 | 1,177 | 1,204 | +2.3%（噪声） |
| L09 自有语料 34 文件合计 | ≈9,030 | 9,029 | ≈0 |

**判定：① 收益 ≈ 0，放弃**（改动已回退；多一个 `try_unwrap().unwrap()` 分支不值得）。

## 3. 实验 ②：`Val` 名字 span Rc 化（收益显著，采纳）

### 3.1 实现

- `Val` 里 5 类名字 span（`Obj` 字段名、`Lam`/`Pi` binder 名、`LiteralIntro` 名、
  `Sum` 头名与参数名、`SumCase` 名与字段名）由 `Span<String>` 改为
  `VSpan(Rc<Span<String>>)`；`Deref<Target=Span<String>>` 让既有 `.data`/显示代码
  透明；跨表示比较（VSpan ↔ `Span<String>`）实现只看名字的 `PartialEq`；
  为 parity/错误正文保留**与内层 `Span<String>` 同形的 `Debug`**（否则双实现错误
  正文里的 span 形态会分叉，parity 首轮就是被它拦下的）。
- 构造点统一 `vspan(span)`；`quote`/`rename` 回写 Tm 时用 `tmspan(&vspan)`（非热路径）。
- 涉及 5 个文件 +127/−79 行；Tm 侧保持 `Span<String>`（项层克隆不在热路径，避免无谓扩散）。

### 3.2 结果

probe（同 fixture，min-of-5，µs）：

| 文件 | 基线 | ② | 变化 |
|---|---:|---:|---:|
| common ladder_l07_large（798 decls） | 61,167 | **44,627** | **−27.0%** |
| common ladder_l07_medium | 3,983 | **3,064** | −23.1% |
| L09 Eq 阶梯单文件 | 2,942 | **2,623** | −10.8% |
| proofs_400 | 2,839 | 2,430 | −14.4% |
| plain_defs_800 | 610 | 495 | −18.9% |
| old_global_800 | 1,177 | 965 | −18.0% |
| def_chain_800 | 1,483 | 1,170 | −21.1% |
| enum_match_200 | 1,713 | 1,537 | −10.3% |

官方口径（`realbench`/`l09bench`，`--rounds 3 --only basic`，ms；基线 = round-2）：

| 口径 | 基线 | ② 后 | 变化 |
|---|---:|---:|---:|
| `realbench` L09 common TOTAL（6 文件） | 67.055 | **50.393** | **−24.9%** |
| └ ladder_l07_large CASE | 63.1 | **46.4** | −26.5% |
| L09 自有语料（34 文件） | 9.116 | **8.938** | −2.0% |
| Eq 阶梯单文件（801 decls） | 2.988 | **2.735** | −8.5% |
| l09bench church k=11 | 1.367 | 1.39–1.40 | ≈持平（+1.5%，噪声内） |
| l09bench strchain k=11 | 9.106 | **7.502** | **−17.6%** |
| l09bench natadd k=11 | 3.360 | **2.654** | **−21.0%** |
| l09bench struct k=10 | 6.286 | **4.980** | **−20.8%** |
| l09bench match k=11 | 0.103 | **0.089** | −13.6% |
| l09bench enum k=9 | 0.222 | **0.208** | −6.3% |
| l09bench universe k=11 | 4.541 | **4.130** | −9.0% |

控制层（源码未改）：L07 common 66.56→65.09（−2.2%）、L08 68.36→65.01（−4.9%）、
L10 41.49→40.79（−1.7%）——全部无变慢（差异为重建二进制布局效应）。

### 3.3 为什么收益这么大

- ladder 上 **1.17M 次 Val 克隆**，每次克隆 `SumCase`/`Sum`/`Lam` 都要复制一个
  `Span<String>`（名字 String 堆分配）；`Rc` 句柄后克隆只是引用计数递增。
- 这与 L10 参考版快 1.67× 是**同一机制的廉价子集**：L10 整机 `Rc<Val>`（全值句柄），
  本项只把名字 span 句柄化，就吃到 ladder −24.9%、strchain/natadd/struct −18~21%。
- 注：上面「vs L07/L08」的数字是**合入 L07/L08 之前**的对照；同日稍后已把同一
  VSpan 机制**移植到 L07/L08 参考引擎**（见
  [bench-crosslayer-vspan-2026-11-13.md](bench-crosslayer-vspan-2026-11-13.md)），
  三层在 common 上收敛到 50.3–51.1 ms（彼此差 ≤1.6%），L09 用同一份 common
  代码从 67.06→50.35 ms。跨层定位改为：L07→L09 同水位；L10 仍是 40.97 ms
  （1.23×，整机 `Rc<Val>` 世代差），但旧载体在 801-decl ladder 上慢 454×。

## 4. 实验 ①+② 合起来

① 在 ② 之上再叠加后 probe：ladder 45.2 ms（vs ② 44.6，+1.3% 噪声）、
L09 自有语料合计 8,292 µs（≈② 水平）——**合起来 = ②，① 增量在噪声内**。
结论：只采纳 ②；① 的实验 patch 留在 `.deltawork/perf09/variantA_rc_take.patch`（不提交）。

## 5. 验收

- `cargo test --test l09_fast_parity` **46/46**、`--test l09_blackbox` **82/82**、
  `--lib L09_mltt::` **17/17** 全绿（② 落地后；含新增 `VSpan` Debug 形态 parity 修复）。
- `realbench --layer L09 --corpus tools/bench_corpus/{common,L09} --validate`：
  common **6 PASS / 0 SKIP**、自有语料 **34 PASS / 0 SKIP**（与基线一致）。
- `cargo check --all-targets` OK；`Tm`/孪生/其它章节零改动。

## 6. 复现

```powershell
cargo build --release --bin realbench --bin l09bench
target\release\realbench.exe --layer L09 --corpus tools\bench_corpus\common --rounds 3 --only basic
target\release\realbench.exe --layer L09 --corpus tools\bench_corpus\L09 --rounds 3 --only basic
target\release\realbench.exe --layer L09 --corpus target\perf09\corpus_real_l09\ladder_large_only --rounds 3 --only basic
target\release\l09bench.exe --workload all --max-k 11 --rounds 3 --only basic
```

> 备注：实验用的 `l09probe` bin、Val 克隆/`rc_take` 计数探针均为临时物，**未提交**；
> 相关原始输出在 `target/perf09/`（`valexp_build*.txt`、探针 patch 于 `.deltawork/perf09/`）。
