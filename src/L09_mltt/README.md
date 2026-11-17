# L09：MLTT 切片（`Type N` 分层宇宙 + 和类型 / match）

本层按“每章 = 上一章实现思路 + 本章新特性”重建（2026-11-17）：实现上**直接
承接 L08**——decl 表名字世界（`Tm::Decl` / `Val::Decl` / `DeclEntry` / `Decls`）、
`Rc<Val>`、显式替换 σ（`Subst` / `Val::VSub` / `frcs` / `SpecSolve`）、L07 蓝本
的逐臂 match 编译器、P1–P11 加固、可变全局 / 文件 IO builtin 注册表、层内
`tests.rs`、bump 孪生 `bump_spine_iter`——只叠加 MLTT 切片增量：**`Type N`
分层宇宙**（宇宙检查 + 高宇宙 enum）。旧 L09 的“再定基”实现（`Infer.global`
+ `1919810` 哨兵、恢复式 parser、删除 `tests.rs`/`struct_eq`/孪生模块）已在
本次重建中撤销，链恢复连续。设计说明见本文件；L08 的全量机制见
`../L08_product_type/README.md`。

## 1. 语言特性（相对 L08 的增量）

```text
def t0 : Type 1 = Type 0
def t1 : Type 2 = Type 1 -> Type 0

enum HighLvl[A] {
    case1(a: A)
    case2(a: t1)      // 字段域在 Type 2 上 → enum 本体是 Type 3 上的 Π 链
}

def hl : HighLvl[Nat] = case1 zero
def t3 : Type 2 = HighLvl[Nat]
```

- **`Type N` 分层宇宙**：`Tm::U(u32)` / `Val::U(u32)` 携带层级；语法 `Type N`
  （`Type` 关键字 + 数字 token）。**裸 `U` 只是普通变量名**——宇宙必须写
  `Type N`。pretty 渲染回 `Type N`。
- **宇宙推进规则**：`Type N : Type N+1`；Π 的宇宙 = max(域层级, 余域层级)；
  enum 本体的宇宙由 §2 的扫描决定。
- **继承自 L08 的全部语言面**：enum/GADT、依赖 match、struct/new 脱糖、值级/
  类型级投影与多段投影链、隐式参数与 `f[A, B]` 逗号合写、字符串字面量与
  `string_concat`/`str_eq`/`str_indent2`/可变全局族/文件 IO 族 builtin、
  `println` 语句、同名重定义定向报错（`redefine {名}`）。

## 2. 宇宙检查（`check_universe`）

所有类型注解入口——`def` 的（折叠后）类型、`enum` 类型、`let` 注解、Π 的
域与余域、enum 构造子类型——统一走 `Infer::check_universe`：

1. `infer_expr` + 隐式参数插入，得到注解项的推断类型；
2. 推断类型是 `Val::U(u)` → 直接返回层级 u；
3. 推断类型是未解 `Val::Flex(m, sp)` → 解 meta 的类型为 `U(0)`：
   - `sp` 为空：meta 类型 force 后是 `U(_)` 则 `m := U(0)`（否则定向报错
     `meta type … is not a universe`）；
   - `sp` 非空：`invert`/`prune_ty` 后经带 occurs 的 `rename` 造出 `U(0)` 的
     λ 解；
4. 其余形态 → `expected universe, got …`。

`enum` 声明额外收集 `universe_lvl`：参数域（显式写 `Type N` 的）与每个构造子
字段域逐个 `check_universe` 取 max；enum 本体的类型是 `Type universe_lvl` 上
的 Π 链，`HighLvl[Nat] : Type 2` 由此成立。隐式参数的无标注域（`[A]`）在
声明处钉为 `Raw::U(0)`（与旧 L09 的“类型参数默认 Type 0”口径一致）——否则
第 2+ 参数的域洞会经 `fresh_meta` 变成部分应用 meta，使用点显式供给隐式实参
时 `invert` 对非变量 spine 直接失败。

宇宙检查对洞/可解 meta 的解算沿用旧 L09 的既有口径（解 meta 的类型为
`U(0)`；注释中的 `TODO:x?` 是旧 L09 遗留，未在本轮改变语义）。

## 3. 名字世界 / 精化 / 加固（原样继承 L08）

- 顶层 `def`/`enum`/构造子/struct 脱糖产物全部进 decl 表：`Tm::Decl(名)`、
  `Val::Decl(名, spine)`，递归检查用“先插入指向自身的占位、检查完覆盖”。
  L09 特有的 `Infer.global`、`global_names`、`1919810` 哨兵已全部删除；
  构造子取类型重新走 decl 表（`Decl.case` 限定键 + 裸名别名）。
- 精化载体：σ 显式替换（`Subst` 持久单链 + `Val::VSub` + `frcs` 读点推开
  + `SpecSolve` 穿参）；`Val::Match` 第 4 字段 pending splice；match 编译器
  为 L07 蓝本的逐臂下钻（`Compiler`）。
- 加固：传递 occurs、`MATCH_CMP_BUDGET`、`UnifyKind` 三档、P5 跨 meta 环守卫、
  深值迭代 quote/rename、pretty 定深、`MetaSnapshot` undo-log 等按 L08 原样保留。

## 4. 显示形态（继承 L08）

- 构造子值：`Enum::case(实参…)`（普通 enum）/ `Point.mk(实参…)`（struct 脱糖
  的 `.mk` 去重）；实参空格分隔（旧 L09 的 comma 血统是再定基产物，已随重建
  撤销）。
- 隐式位用 `[...]`；卡住 match 保留 `(unsolved match n)` 简形；`Type N` 原样
  渲染；`AppPruning` 的显示与 L08 相同（只显示内核，掩码感知 pretty 未移植）。

## 5. 双引擎（`bump_spine_iter`）

L08 冠军配方原样移植，宇宙增量为：`Tm::U(u32)`；打包值 tag 3 改为“层级进高
3 位”（`v_u(lvl)` / `v_u_of`）；`eval`/`quote`/`rename`/`unify`/`struct_eq` 的
U 臂按层级比较；`Machine::check_universe` 对应参考版（含 meta 解 `U(0)` 与
空/非空 spine 两分支）；enum 推断同样扫描 `universe_lvl`。`bench_src` 的负载源
改写成 `Type 0` 形式，负载结构不变。

## 6. 测试

- `cargo test --release --lib L09_mltt::`：83 个（L08 `tests.rs` 继承 + 宇宙
  相关调整）。
- `cargo test --release --test l09_fast_parity`：121 个（参考版 ↔ 孪生；
  含新增宇宙用例：分层推进、高宇宙 enum/struct、层级失配双侧同判、
  `Type 0`/`Type 1 → Type 0` 金标准输出）。
- `cargo test --release --test l09_blackbox`：60 个 + 1 个 `#[ignore]` 深度探针
  （L08 黑盒基线 + 宇宙增量用例）。
- 跨层门禁：`gadt_refine_cross_layer_tests`、`prim_identity_cross_layer`、
  `implicit_comma_args`、`audit_crosslayer_probe`、`backport3_pretty_l0910`
  全部通过（L09 参与部分）。
- 基准自检：`l09bench --workload all` 六类负载（church/strchain/match/enum/
  struct/universe/natadd）参考版与孪生互检通过；`realbench --layer L09` 在
  `tools/bench_corpus/common` 上 pass=6。

## 7. 已知限制 / 与旧 L09 的差异

- 旧 L09 的恢复式 parser（解析错误打印后继续）不再保留：本层完全沿用 L08
  的 parser 契约（解析失败 `Err("parse error")`）。
- 旧 L09 的 comma 血统显示、`Infer.global` 全局表、`recursive_N` 显示、
  `twin/debug.rs`、层内 `struct_eq` 双版差异均随“再定基撤销”消失；
  `struct_eq` 现为 L08 参考版 + 孪生版同构两份。
- 宇宙规则的 `check_universe` 对未解 meta 的解算沿用旧 L09 的 U(0) 口径
  （含其 `TODO` 语义），本轮只保证与旧 L09 行为一致并通过既有用例；
  更严格的 universe 推断留作后续章节统一处理。
- 孪生版错误文案与参考版的既有差异（span/正文细节）按 L08 的文档化口径保留；
  parity 判据仍是“Ok 逐字节一致 / Err 判定一致 + span 归一化正文一致”。

## 8. 参考资料

- `../L08_product_type/README.md`：本层核心机的全部出处；
- 旧 L09（再定基版）文档在 git 历史 `pre-rearch-20261117` 标签可查。
