# A5 交叉审计 Round2 — A1 切片（L01_nbe / L02_tyck / L03_holes）

> 只读审计，未改 A1 任何文件。依据：`git diff -- src/L01_nbe src/L02_tyck src/L03_holes`
> + 静态阅读。结论：**0 个 P0/P1/P2**；1 个 P3 观察项。

## 1. 结论（verdict）

- P0: 0  P1: 0  P2: 0  P3: 1（一致性/文档 nit，非缺陷）
- A1 本轮 A1（对齐断言）改动**完整、正确、无漏拷**。

## 2. 逐项核查

### 2.1 L01 2 位 tag（`& !3`）安全性 — 通过
- L01 仅两个 packed 解码点：
  - `src/L01_nbe/bump_spine.rs:58` `v_clo_of` → `&*((v.0 & !3) as *const CloCell)`；
    `CloCell`（`:68-72`）只含 `&str` / `Option<&EnvCons>` / `&Bt`，wasm32 对齐 4。
  - `src/L01_nbe/native_clo.rs:50` `v_clo_of` → `&*((v.0 & !3) as *const Clo)`；
    `Clo` 只含 `&dyn Fn`（胖指针，wasm32 对齐 4）。
- 两处均已有 `const _: () = assert!(align_of::<…>() >= 4)`（`bump_spine.rs:78`、
  `native_clo.rs:42`）。2 位 tag 只要求低 2 位为 0 → wasm32 对齐 4 足够。**结论：安全，
  断言取值正确（≥4 而非 ≥8）。**
- 另：`bump_spine.rs:86` 对不参与 ptr|tag 的 `EnvCons` 也加 `>=8` 断言（因含 `V(u64)`），
  无害；`v_lvl`/`v_spine` 为立即数 tag，无需断言。无遗漏 packed 类型。

### 2.2 L02/L03 3 位 tag（`& !7`）与对齐断言 — 通过
- L02 `src/L02_tyck/bump_spine_iter.rs`、L03 `src/L03_holes/bump_spine_iter.rs` 的
  pointer 解码只有 `CloCell`(tag1)/`PiCell`(tag4)（`grep 'as \*const'` 各 2 处）。
- 三个类型断言齐全：
  - L02：`CloCell` `repr(align(8))` + `:136` 断言；`PiCell` `:146`；`EnvCons` `:153`。
  - L03：`CloCell` `repr(align(8))` + `:232` 断言；`PiCell` `:242`；`EnvCons` `:169`。
- L02/L03 **无 XCell**（L06+ 才引入），故 A1 的 XCell 专项改动在此层不适用，非漏拷。
- SAFETY 注：L02 `parser/lex.rs:79` 新增的 `get_unchecked(..ident_len)`（`:80`）说明正确
  （`head`/`tail` 为前缀、`ident_len ≤ input.data.len()`）；L03 `parser/lex.rs:79` 原有
  同款 SAFETY 注，无缺口。

### 2.3 `bench.rs` forget 修复 — 通过
- `src/L01_nbe/bench.rs:888` 在 `rows.is_empty()` 提前返回前补 `std::mem::forget(check)`。
- `check` 全程仅被 `iter_eq_bump(res, &check)` 借用、未被 move；末尾
  `:893 std::mem::forget(check)` 为正常路径。新增的提前返回分支原会递归析构百万层
  `Box` 树爆栈（`--only naive` 等未选中变体时可达），修复正确、无双重 forget 风险。
- `print_table`（`:907` 起）的 `rows.is_empty()` 提前返回不持深树，无需同样处理。

### 2.4 README 测试计数 — 通过
- 静态 `#[test]` 计数：L02 = 10(mod)+13(bump_spine_iter)+2(parser/mod)+1(lex) = **26**，
  与 `src/L02_tyck/readme.md:34` 一致；L03 = 9+16+2+1 = **28**，与
  `src/L03_holes/readme.md:49` 一致。

## 3. P3 观察项（不需修，供 orchestrator 知悉）

- **[P3] 断言一致性 nit**：L01 `EnvCons` 断言 `>=8`（`:79`）、L02/L03 `EnvCons` 断言
  `>=8`，但三者均不参与 ptr|tag 解码，属"额外钉住"。L11/L12 本轮同样采用此写法，
  口径一致，无行为影响。
- **[P3] 文档措辞**：L02 `bump_spine_iter.rs:127-130` SAFETY 注写"`CloCell` 只含引用，
  wasm32 上仅 4 字节对齐"——同为引用的 `PiCell` 因含 `V(u64)` 为 8，表述准确，无问题。

## 4. 跨切片需 orchestrator 处置

- 无。A1 切片本轮未发现需转交的问题。
