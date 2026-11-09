# A1 Round2 — 交叉只读审计：A2 切片（`src/L04_implicit/**`、`src/L05_pruning/**`、`src/L06_string/**`）

> 方式：`git diff -- src/L04_implicit src/L05_pruning src/L06_string` + grep + 直接阅读源码。
> 未修改 A2 任何文件。审计对象为审计时刻的**工作树快照**；期间 A2 仍在并发编辑
> （`mod.rs` 的改动在我首次 diff 之后才出现），结论以最后一次读取为准。

## 1. 结论（verdict）

- 对 A2 切片：**P0: 0  P1: 0  P2: 0**；P3: 0；needs-verify: 1（η 守卫行为变更的口径，见 §3）。
- A2 本轮的 A1（对齐）与 η 守卫工作**两版同步、无漏改拷贝、注释与代码相符**。
- 另发现**切片外**（A3 的 L07/L09）一个 P0/P1 级漏改拷贝，见 §4，供 orchestrator 转交。

## 2. A1 对齐修复核对（A2 切片）

逐个核对「被 `ptr|tag` 编码的类型 → 是否有足够对齐」：

| 文件 | 类型 | 打包 tag | 是否含 u64 | 64 位对齐 | wasm32 对齐 | A2 处置 |
|---|---|---|---|---|---|---|
| L04 `bump_spine_iter.rs:234` | `CloCell` | `ptr|1` / `& !7` | 否 | 8 | 4 | `#[repr(align(8))]`(:233) + assert `>=8`(:241) ✔ |
| L04 `:246` | `PiCell` | `ptr|4` / `& !7` | 是(`dom:V`) | 8 | 8 | assert `>=8`(:254) ✔ |
| L04 `:187` | `EnvCons` | 不编码 | 是(`val:V`) | 8 | 8 | assert `>=8`(:180) ✔ |
| L05 `:255` | `CloCell` | `ptr|1` / `& !7` | 否 | 8 | 4 | `#[repr(align(8))]`(:257) + assert `>=8`(:265) ✔ |
| L05 `:263` | `PiCell` | `ptr|4` / `& !7` | 是 | 8 | 8 | `#[repr(align(8))]`(:269) + assert(:278) ✔ |
| L05 `:191` | `EnvCons` | 不编码 | 是 | 8 | 8 | assert `>=8`(:199) ✔ |
| L06 `:210` | `XCell` | `ptr|7` / `& !7` | 否 | 8 | **4** | `#[repr(align(8))]`(:209) + assert(:216) ✔ |
| L06 `:303` | `CloCell` | `ptr|1` | 否 | 8 | 4 | `#[repr(align(8))]`(:302) + assert(:310) ✔ |
| L06 `:315` | `PiCell` | `ptr|4` | 是 | 8 | 8 | `#[repr(align(8))]`(:314) + assert(:323) ✔ |
| L06 `:236` | `EnvCons` | 不编码 | 是 | 8 | 8 | assert(:244) ✔ |

- 全切片 `grep "as \*const .* as u64"` / `& !7` 只命中上述三类单元，无第四类指针型
  打包（`Lvl/Spine/Meta/LiteralType` 均为立即数）→ **无遗漏拷贝**。
- L06 `XCell` 的 `#[repr(align(8))]` 注释（:204-208）准确描述了 wasm32 上
  `&str` align 4 → `& !7` 会清 bit2 → UB 的机制。
- 结论：ROUND2 §A1（A2 部分：L04/L05 全部 tagged 类型 + L06 `XCell`）**已正确落地**。

## 3. η 守卫核对

- **L06**：参考版 `unification.rs:16,476,481` 与快版 `bump_spine_iter.rs:833,1737,1756`
  都有 `v_applicable` 守卫（本轮 HEAD 已有，A2 未动）。
- **L04**：本轮 A2 新增参考版 `mod.rs:140-145`（守卫 `Flex|Rigid`）并在 η 臂
  `mod.rs:437,441` 加 `if v_applicable(...)`；快版新增
  `bump_spine_iter.rs:163-169`（`tag 0|5` 或 tag2 链头 `0|5`）并在 `:1008,:1020` 使用。
  两版语义等价（快版 tag0=Lvl/rigid、tag5=Meta/flex ↔ 参考版 Rigid/Flex）。
- **L05**：同 L04，参考版 `mod.rs:180,939,943`；快版 `bump_spine_iter.rs:181,1152,1164`。
- 未发现「参考版修了、快版没修」或反向分叉。

### [needs-verify] L04/L05 参考版新增守卫是「panic → Err」的行为变更
- 位置：`src/L04_implicit/mod.rs:437,441`；`src/L05_pruning/mod.rs:939,943`
- 证据：A2 的注释（`L04/mod.rs:134-139`）自述：守卫只改变原本走 `v_app` impossible
  panic 的分支，守卫为真时行为不变；并断言「L04/L05 无 decl/builtin，该分支不可达」。
- 机制/影响：若「不可达」成立则零行为变化；若不成立，这是 panic→Err 的合理 bug 修复。
  但 A2 未按 ROUND2 §C 附可运行探针（C 表未列 L04/L05，故非违规），该「不可达」目前
  仅为论证、无测试钉子。BRIEF §6.3 要求行为变更需触发用例或证明——建议 orchestrator
  让 A2 补一个「构造非 λ 的 U/Pi 侧 vs λ 侧」探针，或在报告中正式记录该不可达论证。
  因两版（参考/快）判定同步，不会造成 parity 裂缝；严重度不足以计 P1。
- 处置：仅报告（不强求修）。倾向接受，但请 A2 明确标注为 design-decision。

## 4. 切片外发现（供 orchestrator 转交 A3，非 A2 责任）

### [P0/P1·wasm soundness + 注释与代码不符] L07/L09 的 `CloCell` 缺 `#[repr(align(8))]`
- 位置：`src/L07_sum_type/bump_spine_iter.rs:386-391,408`、
  `src/L09_mltt/bump_spine_iter.rs:402-407,424`
- 证据：
  - 两层 `CloCell` 字段为 `name:&str, icit:Icit, env:Env, body:&Tm`，**不含 u64**，
    wasm32 上 `align_of == 4`。
  - 两处 `v_clo` 写 `ptr | 1`、`v_clo_of` 读 `v.0 & !7`（L07:`211-214`、L09:`209-212`），
    要求低 3 位为 0。
  - A3 本轮补了 `const _: () = assert!(align_of::<CloCell>() >= 8);`
    （L07:408、L09:424），但**没有给 `CloCell` 加 `#[repr(align(8))]`**
    （两文件的 repr 只加在 `XCell`：L07:265、L09:268）。
  - 邻近注释（L07:404、L09:420）称「其余类型通常含 `V`(u64) 已 ≥8」——对 `CloCell`
    不成立（它不含 u64）。
- 影响：wasm32 上该 `assert!` **直接编译失败**（比 UB 好，但 wasm 目标构建被破坏）；
  若为通过编译而删断言，则回退成 `& !7` 清 bit2 的 UB。x64 `cargo check` 无法发现
  （x64 上 align 本为 8）。
- 对照：A2（L04/L05/L06）与 A4（L08 `:400`、L10 `:433`）都已正确给 `CloCell` 加
  `#[repr(align(8))]`——这是典型的「同一拷贝修了、L07/L09 漏改」分叉。
- 建议修法：照 L08/L10 给 L07/L09 的 `CloCell` 加 `#[repr(align(8))]`，并订正注释
  「其余类型通常含 V(u64)」的措辞。请 orchestrator 转交 A3。

### 已知残留（共享文件，按约定不改）
- `src/L13_namespace/bump_spine_iter.rs:541` 的 `enum XCell` 仍无 `#[repr(align(8))]`，
  属共享文件，ROUND2 §A8 已明确本轮不改，仅记录。

## 5. 其它核对

- **改错/漏改**：A2 对 L04 `Machine.workbuf` 的 SAFETY 注释重写
  （`bump_spine_iter.rs:1493-1494`）与代码相符——`W`/`QJob`/`UItem`
  （`:445,:651,:920`）均为无可 Drop 字段的 Copy 枚举，故 `'static` 存放 + 按当次
  `'a` 重写指针类型不产生 Drop 悬垂。
- **注释与代码相符**：L04/L05 的 `v_clo_of`/`v_pi_of` SAFETY 注释已从「bump 分配
  （对齐 ≥8）」改为显式引用 `#[repr(align(8))]`（L04:136-138 等），与新增 repr 一致。
- **测试**：A2 本轮未改 `tests/l04_*.rs`/`l05_*.rs`/`l06_*.rs`；A1 对齐属编译期断言，
  无须运行时测试，符合 ROUND2 §C「XCell 对齐编译期断言即可」。
- 未发现 A2 引入的 `unwrap`/`panic!`/切片下标/新 unsafe。

## 6. 交叉审计计数

- A2 切片：P0 0 / P1 0 / P2 0 / P3 0 / needs-verify 1。
- 切片外（转 A3）：P1 1（`CloCell` wasm 对齐 + 注释不符）。
