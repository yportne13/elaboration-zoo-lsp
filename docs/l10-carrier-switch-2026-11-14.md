# L10 参考版载体切换（P0）+ close_meta_ty / force-Obj（2026-11-14）

> 依据：`docs/l10-perf-advantages-2026-11-13.md` 的归因——L10 快 = 整机 `Rc<Val>`
> 世代（值复制常数 ~2×），慢 = 旧载体（顶层声明压进 `Cxt`：全局引用 O(D)、
> `fresh_meta` 的 `close_ty(locals)` O(D²)）。本 P0 把载体切换从 L09
> （`568c65c5`）移植到 L10 参考版，保留其 Rc 世代；另带两个便宜项。
> 未改孪生逻辑、未改其它层、未改 tests/docs（本文件除外）。

## 1. 改动

`src/L10_typeclass/{mod.rs, elaboration.rs, pretty.rs}`，**+255/−70**：

- **载体切换**（照 L09 `568c65c5` 设计）：新增 `Tm::Global(Ix)`（编码
  `global_idx + 1919810`）三态引用；`Infer.in_progress_globals` 区分「递归定义
  检查期自引用（`Tm::Var` 哨兵，中性视图中和）」与「已定名全局（`Tm::Global`，
  直查 `Infer.global`）」；`fake_bind` 只登记名字占位；`define_global` 只写
  `global`/`global_names`，**不再增长 Cxt**（env/lvl/locals/pruning 不动，返回
  O(1) 克隆）；`eval` 先判哨兵直查全局表；`infer_expr` 的 `Var` 三态编码；
  `bench_check_nf` 末值改从 global 表取；`pretty_tm_g`/`resolve_global` 为错误
  文案保留全局名反查。
- **两个便宜项**：`fresh_meta` 加 L06 `close_meta_ty` 快路径
  （`all_define_slots`+`env_independent` 守卫；载体切换后 locals 只剩局部，
  本项主要护 local let/隐式洞场景）；`force` 的 `Obj` 臂加 `Rc::ptr_eq` 早退。
- **typeclass 面零额外注册点**：`TraitDecl`/`ImplDecl` 复用 def/enum 的 `infer`
  路径（trait 本体 + `Trait.mk` 自动登记，impl 值作普通 def），`solve_trait`/
  `synth` 不变。
- 唯一 parity 适配层：`cxt.lvl` 改为「只计局部 binder」后，3 处错误文案里的
  `Lvl(n)` 用 `display_val` 平移回孪生旧口径（仅显示，语义值不变）——这是为了让
  `l10_fast_parity` 的**逐字节错误正文**继续对齐；彻底统一需孪生也换口径
  （独立工作，不在本 P0）。

## 2. 验收（全绿）

| 项 | 结果 |
|---|---|
| `cargo test --test l10_fast_parity` | **47 passed / 0 failed**（基线 47） |
| `cargo test --lib L10_typeclass` | **26 passed / 0 failed**（基线 26） |
| `cargo check --all-targets` | **0 error** |
| `realbench --layer L10 --corpus tools/bench_corpus/L10 --validate` | **22 PASS / 0 SKIP**（同基线） |
| `realbench --layer L10 --corpus tools/bench_corpus/L09 --validate` | **25 PASS / 9 SKIP**（skip 集合同基线） |

## 3. 性能（`realbench --only basic --rounds 3`，min，同机同窗口）

| 口径 | P0 前 | P0 后 | 变化 |
|---|---:|---:|---:|
| **common 6 文件 TOTAL** | 40.966 ms | **32.108 ms** | **−21.6%** |
| └ common ladder CASE | 37.888 ms | **29.331 ms** | −22.6% |
| **L10 自有语料（22 文件）** | 16.419 ms | **5.249 ms** | **−68.0%** |
| **Eq 阶梯单文件（801 decls）** | 1,078.871 ms | **2.128 ms** | **−99.80%（507×）** |
| **同文件 L09 语料喂 L10（25 PASS）** | 1,103.699 ms | **4.044 ms** | **−99.63%（273×）** |

**同轮跨层**：common L07 50.593 / L08 52.428 / L09 50.482 / **L10 32.108 ms**
（L10 现在全场最快，0.63–0.64×）；Eq 阶梯单文件 L07 2.417 / L08 2.417 /
L09 2.703 / **L10 2.124 ms**（L10 最快，0.79–0.88×）。

**机制验证（cause 实验 fixture，P0 前 → 后）**：

| fixture（此前 L10 超线性） | P0 前 | P0 后 | 变化 |
|---|---:|---:|---:|
| proofs_400（fresh_meta O(D²–³)） | 2,062,015 µs | **1,800 µs** | **1146×** |
| let_chain_800 | 3,394,305 | **5,170** | **657×** |
| meta_implicit_200 | 548,487 | **1,362** | **403×** |
| proj_chain_200 | 1,365,311 | **3,744** | **365×** |
| type0_only_1600 | 490,088 | **3,035** | **161×** |
| old_global_1600（env O(D)） | 15,250 | **1,502** | −90.2% |
| plain_defs_1600 | 6,535 | **876** | −86.6% |
| strchain_like_1600 | 9,838 | **2,326** | −76.4% |
| nat_value_s768（值复制主导） | 40,305 | 38,263 | −5.1%（保持 Rc 世代收益） |
| unfold_16（Rc 共享） | 3,256 | 3,363 | 持平 |

⇒ 此前归因完全被证实：P0 后所有「D 超线性」形状回到近线性/常数；值复制类
负载保持 L10 的 Rc 世代优势（相对 L07/L08/L09 仍快 1.4–2×，见 §3 跨层）。

### 3.1 l10bench micro 家族（**重建 l10bench 后**；同族负载，各层自家生成器）

> 重要勘误：P0 首轮记录的 l10bench strchain/struct/traitchain「仍慢」是**过期
> 二进制**所致——第一次测量时 `target/release/l10bench.exe` 还是 P0 前 22:05 的
> 构建（`realbench` 已重建、l10bench 没重建）。重建后三者的真实值如下：

| 负载 | k | L10（P0 后） | L09 同族 | L08 同族 |
|---|---:|---:|---:|---:|
| church | 11 | 1.398 ms | 1.399 | 1.323 |
| strchain | 11 | **7.151 ms** | 7.929 | 7.805 |
| match | 11 | **0.081 ms** | 0.093 | 0.095 |
| natadd | 11 | **2.039 ms** | 2.666 | 2.828 |
| struct | 10 / 11 | **3.524 / 6.958 ms** | 5.117 / 10.238 | 4.967 / 10.074 |
| universe | 11 | 4.320 ms | **4.012** | — |
| traitchain | 9 | **20.4 ms**（P0 前旧二进制 25.5s） | — | — |

即 P0 后 L10 在 strchain/struct/natadd/traitchain 上要么最大幅领先、要么回到
L09 同级；只剩 universe 比 L09 慢约 7.7%（每 def check_universe 的 trait 机械
常数，量级已正常）。**此前「strchain 57ms / struct 167ms / traitchain 25.5s」
是过期二进制读数，予以撤回。**

## 4. 剩余问题（P0 未覆盖，如实登记）

1. **l10bench enum 仍因孪生/参考 nf 节点数不一致 panic**（既有，非 P0 引入）：
   `realbench --layer L10 --corpus <enum_src 单文件>` 的 gate 给出
   `nf_parity ref=28 twin=6`；同一源在 **L09 通过（ref=twin=28）**。
   **已定位根因**（临时探针）：问题在 **L10 孪生 `bump_spine_iter`**，不在参考版——
   对 `rep` 的 `case cons(h, xs)` 臂，孪生 `Compiler::compile` 的
   `check_pm_final` 首轮 `unify_pm(cxt, cxt.lvl, …)` 返回 Err，该臂按「荒谬臂」
   被静默丢弃；于是 `Tm::Match` 只剩 `nil` 一臂，末值 quote 节点数 6（参考版
   保留两臂 = 28，与 L09 一致）。用户可见 `run` 输出/validate 语义正常，只影响
   该 bench 口径。修复需对齐 L10 孪生 `unify_pm(lvl)`/`check_pm_final` 与参考版
   （孪生 index 合一的既有缺陷，独立任务）。
2. **universe 比 L09 慢 7.7%**（4.32 vs 4.01ms，k=11），量级正常，属 L10 trait
   机械的每 def 常数；可留待后续微调。
3. **P0.5 未做**：L10 参考版无 `struct_eq`；`quote`/`rename` 仍递归（L09 的
   深链帧式化未移植）——深值栈风险与迁移前相同。
4. `cxt.lvl` 语义变为局部口径（错误文案靠 `display_val` 适配）；孪生仍是旧口径。


## 5. 复现

```powershell
cargo build --release --bin realbench --bin l10bench
target\release\realbench.exe --layer L10 --corpus tools\bench_corpus\common --rounds 3 --only basic
target\release\realbench.exe --layer L10 --corpus tools\bench_corpus\L10 --rounds 3 --only basic
target\release\realbench.exe --layer L10 --corpus target\perf09\corpus_real_l09\ladder_large_only --rounds 3 --only basic
target\release\realbench.exe --layer L10 --corpus tools\bench_corpus\L10 --validate
```

原始日志：`target/perf09/l10_p0_after/`；spike patch：`.deltawork/perf09/l10_carrier_spike.patch`。
