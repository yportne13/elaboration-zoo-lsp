# L08：积类型（product type / Sigma）

在 L07（和类型 + 依赖模式匹配，机制详见 `../L07_sum_type/README.md`）
之上加**积类型**。与 L07 相对 L06 的大改不同，L08 的核心机**不新增任何
Tm/Val 变体**：`struct` 是语法糖——脱糖成**单构造子 enum**
（构造子名 `{Name}.mk`），字段访问复用 L07 的投影机。推理增量是"接收者
只有类型、没有实例值"时按 `.mk` 剥构造子类型链取字段类型（前字段 binder
以接收者卡住投影精确实例化，§2）；合一臂只补了一条——`unify` 的
`(Obj, Obj)` 合同臂（§2，L07 潜伏缺口的修复而非新语义）。

## 1. 语言特性

```text
struct Point[T] {        // 参数：隐式方括号组（`[A]` / `[A : U]`）
    x: T                 // 字段：按行分隔的 `名: 类型`，全显式
    y: T
}

def p = new Point(zero, four)    // 构造：new Name(实参…)
def q = Point.mk [Nat] two four  // 限定构造子 + 显式实例化隐式参数
def sx = p.x                     // 投影（值级——receiver 是构造子值）
def get_x[T](p: Point[T]) = p.x  // 投影（类型级——只有 Val::Sum 可看）
```

- **脱糖**（解析器内联完成，核心机对 struct 一无所知）：
  - `struct Name[params] { f₁: T₁; …; fₙ: Tₙ }`
    ≡ `enum Name[params] { Name.mk(f₁: T₁, …, fₙ: Tₙ) }`
    ——构造子**名**即字符串 `{Name}.mk`，字段 icit 全部 `Expl`；
  - `new Name(e₁, …, eₖ)` ≡ `Name.mk e₁ … eₖ`（`Raw::Var("{Name}.mk")`
    + 显式应用）。实参走 `p_raw` 且 `p_new` 在其链上，所以
    `new Line(new Point(...))` 合法（裸 spine 实参位除外，§7）；
  - 空 `struct Unit { }` → `Unit.mk`（nullary 构造子）。
- **注册名**走 L07 的 enum 双轨（限定键 + 裸名别名）：对 struct，限定
  键 = `Name.Name.mk`（形态怪异但无人引用），**别名 = `Name.mk`**——
  恰好是 `new`（Var 路径）与 `Name.mk`（Obj 限定路径）两条引用路径的
  查找键；不会产生裸 `mk` 的全局别名冲突。
- **依赖字段（Sigma）**：后面的字段类型可引用参数与在前字段——存在
  谓词对的标准形态：

  ```text
  struct Exists[A: U, P: A -> U] {
      witness: A
      proof: (P witness)
  }
  def exists_two: Exists[Nat][x => Eq x two] =
      Exists.mk[Nat][x => Eq x two] two rfl
  ```

## 2. 投影的类型规则（唯一的推理增量）

`p.f` 的接收者类型有两种形态，各走一条剥链（实现在 `elaboration.rs`
的 `Raw::Obj` 臂，孪生版逐句对应）：

| 接收者类型 | 查找顺序 | 出处 |
| --- | --- | --- |
| `Val::SumCase`（构造子**值**） | 参数（索引）槽 → 剥构造子类型链：隐式参数用头部 Sum 的实参实例化，显式字段 binder 用实例 datas 的**真实值** | L07 已有 |
| `Val::Sum`（只有**类型**，如 `def f(p: Point) = p.x`） | 参数槽 → 若**单 case 且 case 名含 `.mk`**：剥 `mk` 的类型链（隐式参数同上；显式字段 binder 以**接收者的卡住投影值**实例化，见下） | L08 新增 |

- 门控 `cases.len() == 1 && case.data.contains(".mk")` 与旧 L08 一致：
  **普通单 case enum 不享受类型级剥链**（`enum Wrap { only(x: Nat) }`
  上 `w.x` 报 `Wrap has no field x`）——只有 struct 脱糖产物有此能力。
- **剥链是精确的**：剥到目标字段之前经过的每个**显式字段** binder，
  以 `eval(Obj(接收者项, 字段名))`（卡住投影中性值）实例化——依赖在
  **前字段**的在后字段（如 `Exists.proof` 的 `P witness`）因此拿到
  `Eq e.witness two` 这样的精确类型，`def use_proof (e : Exists[Nat][x
  => Eq x two]) : Eq e.witness two = e.proof` 这类合法程序可以判过。
  （旧实现以 `U` 占位，同类字段出现在检查位即假拒——评审发现并修正，
  两版同步；回归测试 `test_product_dependent_check`。）
- 精确化让两个卡住投影首次同场合一（`e.witness ≡ e.witness`），暴露
  L07 潜伏缺口：**参考版 `unify` 没有 `Obj`-`Obj` 合同臂**，同构投影
  落到兜底臂误报 can't unify（孪生版扁平 spine 的头比较天然覆盖，
  所以只补参考版）。新臂：字段名相同 ⇒ 比接收者与卡住期实参 spine。
- 失败文案两版一致：`{类型} has no field {字段}`。
- 值机（`project` / eval / force 的卡住 `Val::Obj` 再投影）全部复用
  L07，零改动。

## 3. 语法扩展：左结合投影链

L07 的 `p_atom` 只允许**单个** `.field` 后缀（`l.a.x` 以 leftover `.`
解析失败）。L08 扩为左结合多段链（fold 成嵌套 `Raw::Obj`），每段各按
§2 的规则推进。单段与无段行为逐字不变——继承的 L07 黑盒基线 97 例
原样全绿。`new` 的结果同样直接接后缀链（`new P(a, b).x` ≡
`(new P(a, b)).x`，评审补齐），裸 spine 实参位不接 `new` 的限制不变。

## 4. 显示形态

pretty 的构造子值原本是 `Enum::case(...)`；struct 的 case 名自带
`{类型名}.` 前缀，照常叠 `::` 会打印成 `Point::Point.mk(...)`。L08 在
pretty 加去重（case 名以 `头部名.` 开头则原样打印）→
`Point.mk(Nat::zero Nat::succ(Nat::zero))`。纯显示层，两版共用。

## 5. 顺手修的一个真 bug（参考版 unify，L07 潜伏）

Lam 的 η 递归臂 `unify(l+1, …)` 时 **cxt 不推进**（η binder 的类型在
值层拿不到），而 Pi 臂用 `quote(cxt.lvl, 域值)` 向下传名字表——
`l == cxt.lvl` 的不变式在 η descent 之后即破裂：域值含 `Rigid(l)` 时
`lvl2ix` debug_assert 炸（L08 的 `Exists` 恰好踩中——P 槽两个 Lam 值
η 展开后进入 Pi 域 quote），release 构建静默降级成错误的 de Bruijn
索引。修法：Pi 臂 quote 改用**当前层级 `l`**（cxt 只服务显示名字表，
对不上时 `go_ix` 有 `@i` 兜底）。孪生版结构不同（Pi 臂不 quote 域值），
无此路径。L07 同码潜伏（其测试集恰好无触发用例），可择机回合。

## 6. 性能孪生（`bump_spine_iter`）

L07 的冠军配方（bump arena + 打包 `V` + 迭代内核 + 复合环境 + 双记忆化
+ `Tycker` 稳态复用 + decl 表平铺化）向 product-type 层的移植。
**机制零新增**——struct/new 在解析器就消失，孪生侧的全部 delta：

1. 标识符改名（`L08_product_type`、`L08_DEBUG` / `L08_LOOP`、测试
   文件名 `l08_test_io.txt` / `l08_builtin_demo.txt`）；
2. `infer_expr` 的 `XCell::Sum` 接收者臂镜像 §2 的类型级 `.mk` 剥链
   （`cxt.decl.borrow()` 取 `mk` 类型 → `force_v` / `v_pi_of` 循环，
   隐式实参消费 + 前字段 binder 以接收者卡住投影（`eval` 一个
   `Tm::Obj`）实例化，与参考版逐句对应）；
3. `unify_iter` 的 `(Obj, Obj)` 合同统一臂（§2 评审修复对位：字段名
   同 ⇒ 比接收者与 spine 实参；裸单元 / spine 链两种形态同臂处理，
   原「Obj 头不进同头」的排除降级为防御性保留）；
4. 新增 `struct_src(k)` 负载（见下）。

### 双 oracle

`cargo test --test l08_fast_parity`（68 例）：DEMO 全串（含积类型段）、
tests.rs 全部既有用例源码、积类型七连（基础 / 泛型 / 依赖 Sigma /
投影链与部分应用 / Err 判定 / 剥链精确检查位 / new 直接接投影）、
继承的 Err parity、深负载
church / strchain / global / match / enum / **struct**（快版 `Tycker`
与参考版 `bench_check_nf` 节点数互检）、稳态复用。判据：**Ok 输出
逐字节一致 / Err 判定一致**（错误文案的 Debug-Span 偏移是文档化偏差，
同 L06/L07）。

### 基准

```text
cargo run --release --bin l08bench -- --workload all --max-k 13 --rounds 3
```

`struct_src`（**L08 特色负载**）：固定 4 层嵌套 Box（类型级 `.mk`
剥链 + 左结合投影链 `p.inner.v` + 一个浅嵌套种子值）+ 2^(k+1) 层
**浅值投影 def 链**（`def q{i} : Nat = get_x(new P(q{i-1}, zero))`——
每层一次构造子 β + 类型级投影 + 合一）。末值 = `zero`（nf 节点数 = 2）。
设计注记：**不**用深嵌套值链（`b_i` 含 `b_{i-1}` 直到底）作主负载——
参考版 decl 表 `Rc` 写时复制 + `Val` 深拷贝下，插入第 n 个 def 要整体
克隆深度 i 的值树，复杂度 O(n³)（k=700 即分钟级）；孪生的平铺表无此
问题，但双 oracle 同负载对比就失去意义。**这是参考版表示的成本，不是
语义的**——积类型的深值恰是孪生最该赢的地方，留给读者。

实测（Windows 10，release，rounds=3 取 min；参考版超线性负载只列
k≤11，同 L07 readme 惯例）：

```text
== workload: church ==（check + nf）
k=12  n=8192    fast=0.728ms         basic=9.782ms      (≈13×)
== workload: strchain ==（每层 prim 触发；basic 二次方）
k=11  n=4096    fast=6.513ms*        basic=2706.3ms     (≈416×)
== workload: global ==（可变全局 + 重入 prim）
k=11  n=4096    fast=11.971ms*       basic=498.9ms      (≈42×)
== workload: match ==（L07 特色：自递归依赖 match def 链）
k=13  n=16384   fast_memo=0.066ms*   basic=0.592ms      (≈9×)
== workload: enum ==（L07 特色：GADT + 投影 + 索引等式）
fast=0.092ms          basic=0.808ms      (≈9×)
== workload: struct ==（**L08 特色**：类型级 .mk 剥链 + new 构造链）
k=9   n=1024    fast=1.729ms*        basic=213.9ms      (≈124×)
k=10  n=2048    fast=3.293ms*        basic=830.1ms      (≈252×)
k=11  n=4096    fast=6.837ms*        basic=3202.1ms     (≈470×)
```

### 已知偏差（与参考版）

同 L07：错误消息 span 全零；unify_catch 文案带 pretty 项 +
`(fuel exhausted)` 尾注，span 数字两版不同。

## 7. 已知限制（诚实清单）

- **struct 不能被 Con 模式解构**：case 名含 `.`，`p_pattern` 的头部是
  单 Ident token，`case Point.mk(a, b)` / `case Point(a, b)` 都解析不
  成；只能变量臂整体绑定后用投影。与旧 L08 行为一致。
- **元组式 struct**（`struct S(Nat, Nat)`）不支持——旧 L08 里就注释掉
  的形态；字段必须具名。
- 字段**按行分隔**（无逗号/分号形态，末字段带逗号会解析失败）；
  struct 参数只认一个前导 `[..]` 隐式组；`(x : T)` 显式组不被接受。
- 裸 spine 实参位不接 `new`（`f new Point(...)` 解析失败；括号形式
  `f (new Point(...))` 可以）——`p_new` 在 `p_raw` 链上，不在 `p_arg`。
- `new` 少给实参不是错误：得到部分应用函数；投影它报
  `cannot project field`（receiver 类型是 Pi）。
- 同名"参数 vs 字段"的投影按**参数槽优先**（与值级 `project` 同序）。
- struct 值上的 `match` 只有单臂变量模式有实际意义（单构造子全覆盖，
  无精化可做）。

## 8. 测试

- `cargo test --lib L08_product_type`：**44**（36 个 L07 继承 +
  7 个积类型专项：`test_product_basic / _generic / _dependent /
  _field_err / _vs_plain_enum / _dependent_check（剥链精确化回归）/
  _new_dot_chain（new 直接接投影）`，另 1 个 lexer 回归
  `test_string_empty_and_escape`（空字面量 `""` 与 `\"` / `\\` 转义））；
  64 MB 栈线程。
- `cargo test --test l08_blackbox`：**55**（L07 基线 46 原样通过 +
  9 个 `product_*` 专项：打印形态 / 投影错误文案 / 普通 enum 门控 /
  投影链 / match 变量臂 / 泛型 struct / new 嵌套 / new 直接接投影 /
  部分应用构造子）；另 1 个 `--ignored` 深度探针。
- `cargo test --test l08_blackbox_v2`：**51**（L07 第二卷基线原样通过，
  另 2 个 `--ignored` 探针）。
- `cargo test --test l08_fast_parity`：**68**（§6 双 oracle；含内嵌的
  43 个既有 lib 用例源码——lexer 回归两版共享同一解析器，不在对照内）。

## 9. 相对旧 L08（移植前）改了什么

旧 L08 建在重构前的 L07 基线上（决策树式模式编译 + 改写式精化、无
builtin 注册表 / decl 表 / 可变全局 / 文件 IO / Error Display、无性能
孪生、println 走 `{:?}`）。本次重构 = **现行 L07 全量继承** +
§1–§4 的积类型层，另附：

- §3 投影链扩展（旧不支持 `x.y.z`）；§4 显示去重（旧打印
  `Point::Point.mk(...)`）；
- §5 的 unify 层级修复；
- 类型级剥链精确化：前字段 binder 以接收者卡住投影实例化，修复
  `U` 占位近似在检查位的假拒（§2，评审修复，两版同步）；随之参考版
  `unify` 补 `(Obj, Obj)` 合同臂（L07 潜伏缺臂，孪生版扁平 spine 已
  天然覆盖、现改为显式统一臂）；`new` 结果可直接接投影后缀链（§3），
  裸 spine 实参位的限制不变；
- 类型级与值级投影统一为**参数槽优先**（旧 L08 两处次序不一致：类型级
  字段优先、值级参数优先）。

## 10. 参考资料

- 本仓库 `src/L07_sum_type/README.md`（本层全部核心机的出处）；
- [elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo)
  上游 08 是 Sigma 类型（`Sig` 与 `Pi` 对偶 + `Fst/Snd` 投影）；本层
  的"积"走记录式具名字段 + 脱糖路线，语义面不同（无匿名 pair、投影
  按名、struct 即单 case enum）。
