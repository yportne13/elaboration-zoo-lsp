# Review 2026-10-11 — 轮次 5:类型类与实例解析

> 主题:**trait/impl、实例搜索、supertrait、derive、outParam**。
> 40 个探针(`tools/review-1011/r05-typeclass/`)。**终局:40/40 PASS**
> (2 项按不支持/quirk 记录)。新增 2 项功能修复。

## 0. 习语校准(本轮最大成本)

类型类的正确习语与直觉差别大,首轮 28/43 失败全部源于用了不存在/错误的形式。
权威来源:`examples/typeclass_complex.typort`(可跑)+ 文档 §4/§5:

- **约束多态**: `def f[T][d: Trait[T]](x: T) = d.method x` —— 字典 `d`
  作接收者投影方法;`trait Trait { ... }` 通常**不带**类型参数(Self 是
  第一个隐式参数,`Trait[T]` 中的 T 填 Self);
- **调用形式**: 具体值上 `x.method` / `x.method arg`;`Trait.method(x)`
  静态形式不支持(与 R3 结论一致);字面量 `1 ++ 2` 的自定义中缀运算符
  **可以**工作;
- **字典实参必须是 T**:`d.method 6`(T:=Nat 场景)在函数体内 can't unify,
  必须传 `t`——`d.method` 的结果类型是 T 而非 Nat(发现过程中最迷惑的一课);
- **方法体优先级**:`a.ca_v t + b.cb_v t` 中 `+` 的左操作数是 `a.ca_v t`,
  右边裸 `t` 变成 `t + ...` 的接收者(`T has no object +`);需括号。

## 1. 发现与修复

### F5-1(已修)derive(Show) 单 case 枚举走错投影路径
`#[derive(Show)] enum Snack { bar(n: Nat) }` → "`this`: Snack has no object
`n`"。parser 把 `struct X {f}` 降为单 case enum(case 名 `X.mk`),derive 用
`cases.len() == 1` 判定"是 struct"并生成 `this.field` 投影——但**真 enum**
的构造子字段是位置的,没有字段投影。修复:改判 `case 名以 ".mk" 结尾`
(struct 专属)才走投影路径,否则与多 case 一致走 match 绑定。
`build_enum_case` 本身正确(多 case 一直好)。钉:`r5_typeclass_regression.rs`
(单 case 枚举 bar(3) + struct Pts(1, 2) 双向)。

### F5-2(已修)impl 方法顺序错位污染 supertrait 实例记录
trait 记录字段序 = [自身方法..., 父类方法...](TraitDecl 臂
`all_methods` 序);而 impl 构建记录时按**声明序**应用方法。当 impl 先写
父类方法再写自身方法,槽位互换——**字段投影返回错误的实现**:
`d.sm` 跑了 `bm` 的函数体(输出 1 而非 2),静默错值,无诊断。
修复(双引擎成对):构建记录前按 trait_methods 的名字位置稳定排序,
未列出的方法沉底。钉:`supertrait_record_slot_order`(双引擎,断言 2)。

### F5-3(未修,记录)父类字典不解析
`def useB[T][d: B2[T]](t: T): Nat = d.bm t`——即便 impl S2 for Nat 提供了
父类方法,父类 trait 的字典投影停在 `?m.bm 0`(无错误,卡住 meta)。
与 F5-2 同域(subtrait 约束传播),修复面大,记 P2。

### F5-4(未修,记录)trait 元数比 impl 宽松
`trait TwoP[A, B]`(2 参)配 `impl TwoP[Nat]` 不报错,到调用点才
间接失败。校验缺失,记 P3。

## 2. 记录的 quirk / 限制(探针预期已固化)
- **类型变量上的接收者方法不考虑约束**:`t.dbl_m`(t: T,有 [T: Doubles])
  → "`t`: T has no object `dbl_m`"(F5-1 号外记录,与 F5-3 一起构成
  "约束多态只能走字典投影"的完整限制面);
- prelude 实例字典可静默中性:`s.show x` 打印 `?m.show 9` 而无错(F5-2);
- 泛型条件实例(`impl[T: Half] Quarter for T`)不支持(prelude show.typort
  自述);带约束的 impl(`impl[T][s: Show[T]] Needs for T`)同样不支持;
- 函数类型/元组类型上的实例不支持;
- `==` 糖不存在(用 `nat_eq`);trait 名可 println(ok);
- `T: CA + CB` 双约束语法用分离字典 `[a: CA[T], b: CB[T]]` 表达。

## 3. 验证
- 轮内:40/40(RESULTS.md);
- 回归钉 3 条(`tests/r5_typeclass_regression.rs`)双引擎全绿;
- 全量门禁:见 commit。

## 4. 遗留
- F5-3 父类字典解析(P2,与约束传播同域);
- F5-4 impl 元数校验(P3);
- 文档 §4.1 的 `s.show x` 示例与 F5-2 的中性卡住现象矛盾,值得在文档标注(P3)。
