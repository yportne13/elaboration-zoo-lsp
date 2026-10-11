# Review 2026-10-11 — 轮次 7:命名空间与双引擎一致性

> 主题:**package/import 解析 + 参考版/孪生引擎语义一致性**。
> 两部分:30 个命名空间探针(`tools/review-1011/r07-namespace/`,30/30)
> + `tests/r7_engine_parity.rs` 的 33 用例双引擎对照矩阵(全一致)。
> **合计 63 个实验。**

## 1. 命名空间实验(30 个)

| 组 | 代表 |
|---|---|
| package 基础 6 | 全路径调用、package 切换、深四级路径、空包、跨包互调 |
| import 8 | 单名/花括号/通配、不带前缀本体(S3)、Type._ 构造子、缺成员 |
| 优先级 4 | D1 prelude 裸名优先实证、限定名越过本地遮蔽、通配后本地 def |
| 错误 5 | 未知命名空间/成员、后缀 fallback 限域(plain 值拒绝) |
| 类型 7 | 包内 enum/struct/impl 方法、全限定组合 |

### 判定的 quirk(全部固化为预期)
- **D1 实证**:用户 `def nat_add` + import,裸调用仍走 prelude(输出 3
  而非用户的 12)。
- **import 别名赢过同文件后置的同名 decl**(`def sq` 后定义、import 在前,
  调用解析到 import 的)——与文档"全局 decl 精确 → import 别名"的叙述
  在定义顺序上相反(P3,值得修或改文档)。
- `import mylib.math`(导入命名空间本体)不支持(D2:末段一律当成员);
  需 `_` 通配。
- **同包成员不自动可见**:包内 def 需限定或 import(语法文档 §2.6 未写)。
- 包内 enum 构造子打印为 `shapes.Color2::red2`(qualified 形态)。
- 用户 `def zero(x: Nat)` 与 prelude 构造子 zero 冲突 → can't unify
  (D1 的另一面)。

## 2. 双引擎一致性矩阵(33 用例)

覆盖:β/递归/ackermann、rfl 证明、宇宙 ok/err、类型错误、undefined、
match(Nat/Boolean/enum/递归 enum)、GADT 索引、Eq 的 J、隐式求解、
typeclass/supertrait/默认方法、TY001 警告、hole、package/import/限定
构造子、宏(声明级/深度限制/stringify)、struct/tuple、终止 ok/err/λ 形。

**结论:33/33 错误判定与 println 结果逐字节一致**(TY001 的双通道排水
也在 R3 修复时成对实现并在此验证)。已知不对称(记录于 r03/r04/r05)
均未进入矩阵。

## 3. 验证
- r07-namespace 30/30(RESULTS.md);
- `cargo test --test r7_engine_parity` 全绿。

## 4. 遗留
- import 优先级与文档矛盾(P3);
- 同包自动可见性缺文档(P4)。
