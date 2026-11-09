# A4 Round2 — 交叉审计 A5（L11_macro / L12_canonical）

> 只读审计。审计时点约在 A5 第 2 轮进行中（A5 正并发编辑），下列“未做”均按
> **审计快照**陈述，orchestrator 最终以 A5 r2 为准。未改对方任何文件。

## 1. 结论（verdict）

- 交叉发现：**P0: 0  P1: 0（1 项 needs-verify 待裁决）  P2: 2  P3: 1**。
- ROUND2 各项修复的**两版同步性**总体良好：A1/A2/A3/A4/A5(第3项)/A6/A7 均已核对。
- 主要遗留：**A8 宏递归深度上限在 L12 快照中尚未落地**（L11 已落地）；L12
  `vals_eq_ground` / `val_match` 存在两处需要探针裁决的匹配宽松点。

## 2. 修复同步性核对（逐项）

| ROUND2 项 | 位置 | 状态 | 证据 |
|---|---|---|---|
| A1 `repr(align(8))` + 断言 | L11 `bump_spine_iter.rs:303,462,485-488`；L12 `:329,488,511-514` | ✓ 两版均有 | XCell/CloCell `#[repr(align(8))]`；XCell/CloCell/PiCell/EnvCons 断言 |
| A2 η applicability 守卫 | 参考 L11 `unification.rs:17-22,670,676`、L12 `:18,703,710`；快版 L11 `bump_spine_iter.rs:721-727,2434,2449`、L12 `:772,2485,2500` | ✓ 两版同步 | 参考 `v_applicable` = {Flex,Rigid,Decl,Obj}；快版 `vapp_ok` 等价 |
| A3 `intersect_go` 长度失配 | L11 `unification.rs:608-611`、L12 `unification.rs:620-625` | ✓ 已改 `_ => None` | 注释“回落 unify_sp 判失败，不再 unreachable” |
| A4 u64 溢出 parse | L11 `parser/mod.rs:507-522`、L12 `parser/mod.rs:550+` | ✓ 已改 `map_err` 路径 | 推 IError + `Raw::Hole`，不再 unwrap |
| A5 trait `.unwrap()` | 参考 L11 `elaboration.rs:292-293`、L12 `:312-313`；快版 L11 `bump_spine_iter.rs:5366-5367`、L12 `:5443-5444` | ✓ 已改 `.map_err(...)?` | 两版同 Err 口径 |
| A6 `prune_ty` rev | 参考 L11 `unification.rs:115-147`、L12 `:117-149`；快版 L11 `:3368`、L12 `:3427` | ✓ 已 rev | `mask_inner_first.iter().rev()` 对齐 |
| A7 哨兵边界 | L11/L12 | **N/A** | 无 1919810 数值哨兵：全局走 `Val::Decl`（`L11/mod.rs:173`），`lvl2ix(l,x)=l-x-1` **纯局部**（`L11/mod.rs:208-210`、`L12/mod.rs:261-263`），不会出现全局 Rigid |
| A8 宏递归深度 | L11 `parser/mod.rs:134-174`（`MAX_MACRO_EXPANSION_DEPTH=256` + `thread_local! MACRO_DEPTH` + guard） | L11 ✓ / **L12 未见** | `grep MAX_MACRO_EXPANSION_DEPTH src/L12_canonical/parser/mod.rs` 无命中 |

### 2.1 A2 守卫等价性细核（无发现）
- `vapp_ok`（`L11/bump_spine_iter.rs:721-727`）对 tag1（Clo=λ）返回 true，而参考
  `v_applicable` 不含 `Val::Lam`。初看像分叉，但 η 臂前有 `(t tag1 && u tag1)`
  的 Lam/Lam 臂（L11 `:2414`、L12 `:2485` 前），故进入 η 臂时 `vapp_ok` 的另一侧
  必非 λ，tag1 分支在该上下文不可达 → **实际等价**。仅记 P3。
- 其余 tag：0=Rigid/2=链/5=Flex → true（=参考 Rigid/Flex）；3=U/4=Pi/6=LitType →
  false（参考不含）✓；7 仅 Obj/Decl → true（=参考 Obj/Decl）✓。

## 3. 发现列表

### [P2·needs-verify] L12 `vals_eq_ground` 无环检测且 `Match` 分支体未比较
- 位置：`src/L12_canonical/typeclass.rs:190-234`。
- 证据：
  - `vals_eq_ground_impl(a,b,visited: &mut HashMap<u32,u32>)` 全程**从不读写
    `visited`**（`:194-233`），故形参承诺的环检测并不存在；对自引用/循环 `Val`
    递归无终止保证。
  - `Val::Match` 分支（`:227-231`）只比 scrutinee 与分支**数量**，分支模式/体被
    `//TODO:&& c1.iter().zip(c2.iter()).all(|()| )`（`:230`）显式留空 → 两个
    scrutinee 相同、分支数相同但分支体不同的 Match 值会被判**相等**。
- 影响面：`try_answer`（`:236-244`）与 `find_assertion_entry`（`:280-288`）用它做
  assertion 等价判定，宽松等值可能导致选错答案/错误缓存命中。
- 处置：仅报告（needs-verify）。需 A5 加探针判定 Match 值是否真能作为 trait
  assertion 实参出现（类型级卡住 match 的情形）；`visited` 未使用则建议要么接线、
  要么删参数。

### [P2·needs-verify] L12 `val_match` 的 Rigid 臂第二分支绑定自引用
- 位置：`src/L12_canonical/typeclass.rs:136-144`。
- 证据：
  ```rust
  (_, Val::Rigid(x, sp)) | (Val::Rigid(x, sp), _) if sp.is_empty() => {
      if let Some(existing) = subst.get(&x.0) {
          Self::vals_eq_ground(a, existing)      // a = 第一元
      } else {
          subst.insert(x.0, a.clone()); true      // x -> a
      }
  }
  ```
  该 or-pattern 的第二支 `(Val::Rigid(x, sp), _)` 里 `a` **就是 Rigid 自身**，
  于是把 `x` 绑成 `Rigid(x)`（自引用代换），而非绑定另一侧 `b`。
  且 `val_match(goal, pattern)`（调用点 `:263-265`）中 goal 在前：当 **goal 是裸
  Rigid、instance 是复合模式**（如 `Say[Rigid(0)]` vs `Say[List[Rigid(0)]]`）时，
  第二支命中并返回 true → 与 L10 同类的“泛型被假匹配成 List”松配。
  另有 `(Val::Flex(..), _) | (_, Val::Flex(..)) => true`（`:130`）也是通配路径。
- 影响面：`try_resolve` 会因此接受本不该匹配的实例。
- 处置：仅报告（needs-verify）。需探针：L12 下用 `Say`/`List[T]`/`def f[T](x:T)=x.say`
  （与 A4 §C 同源）断言参考/快版是否都假匹配；并核对第二分支是否应删除或改绑 `b`。
  注意：这是 L12 “新求解器”的潜在缺陷，与 A4 的 L10 旧求解器不同源，请勿等同处置。

### [P2] L12 canonical IDDFS 的 `basic_target_limit` 上界 off-by-one / 完备性
- 位置：`src/L12_canonical/canonical.rs:19-25`（`iddfs`），调用点
  `src/L12_canonical/elaboration.rs:368-376`（`depth=5, target_limit=6`）。
- 证据：`let mut basic_target_limit = 1; while basic_target_limit < target_limit
  { ...; basic_target_limit += 2; }` —— 只尝试奇数且 `< target_limit`；传入 6 时
  序列为 1、3、5，**永不尝试 6**；而 `search` 的准入是 `target.len() > target_limit`
  → `:40`，即长度 6 的 target 在任何一轮都 `6 > 5` 失败。若 `target_limit` 语义为
  “允许的最大 target 长度”，则上界应为 `<=`（或参数应为 7）。
- 处置：仅报告（needs-verify 完备性）。若确认语义应为闭区间，属 A5 可最小修的点；
  需先由测试/文档确认 `target_limit` 契约，勿盲改。

### [P3] 注释 `//TODO: this is incorrect`
- 位置：`src/L12_canonical/canonical.rs:17,37`（`avoid_recurse` 参数自注“不正确”）。
  已自曝，属记录项。

## 4. 需 orchestrator 转交 A5 的事项

1. **A8 未同步 L12**：审计快照中 `src/L12_canonical/parser/mod.rs` 无宏递归深度
   守护（L11 已有 `MAX_MACRO_EXPANSION_DEPTH`）。若 A5 正在补，忽略；否则请转交。
2. **L11 旧 `Synth::unify`**：`src/L11_macro/typeclass.rs:370` 仍是 L10 同款无
   occurs-check 的旧求解器，ROUND2 §B.2 要求写探针；审计时 `tests/l11_fast_parity.rs`
   未见假匹配探针（tests 目录未被 A5 修改）。请确认由 A5 r2 补齐。
3. **探针测试未落地（快照）**：`tests/l11_fast_parity.rs`、`tests/l12_fast_parity.rs`
   在审计快照中无 ROUND2 §C 要求的 η/宏/u64/`:5401` 探针（两文件均未被修改）。
   同样以 A5 r2 为准。

## 5. 设计决定讨论（记录）

- L11/L12 全局用 `Val::Decl` 而非 `1919810` 哨兵，摆脱了 L09/L10 的边界下溢家族；
  `lvl2ix` 纯局部是安全的前提，若未来引入“带 spine 的全局 Rigid”需重估。
- `v_applicable` 排除 `Val::Lam` 是有意为之（避免把 η 应用 β 归约成非预期比较），
  与快版 `vapp_ok` 在可达标签上等价；建议把该等价性作为注释补进快版 `vapp_ok`，
  防止后人把 tag1 的 `_ => true` 当作可复用通配。
