# prelude 标准库补充轮（2026-10-01）

三个并行子代理对 `src/prelude` 做了一轮"补齐"，共 12 文件 +640 行、纯增量，
随后集成阶段修复了其中一处语义反转（`Vec.append`，见 §3）。本文件记录
清单、验证方法与过程中发现的引擎怪癖。

## 1. 新增清单（按文件）

### core
- `eq.typort`：`cong2`（两参函数同余性）、`cong_ap`（等函数作用于等参数）。
- `op.typort`：`impl[T] Clone for T` 毯子实例（此前 `Clone` 零实例）、
  `Default for Unit`。
- `nat.typort`（纯增量，primop fallback 五件套未动）：`nat_pow`；
  乘法引理链 `mul_zero_right/left`、`mul_succ_right/left`、`mul_comm`、
  `mul_distrib_left`、`mul_assoc`（`mul_comm` 走 `cong2 nat_add`，见 §3.2）。
- `bool.typort`：`impl Not for Boolean`（`!`）；`Equal[Boolean, Boolean]`、
  `Equal[Nat, Boolean]`（`===` / `=/=`）；`Compare[Nat, Boolean]`
  （`< <= > >=`，返回 `Boolean` 所以只能住这里，nat.typort 里 `Boolean`
  还没加载）；`Boolean` 的内在 `&&` / `||`（按接收者方法名分派，
  hdl `Bool` 同款机制；块体经 And/Or 实例分发，故必须排在实例之后）。
- `calc.typort` / `void.typort`：无改动（calc 是 Rust 侧宏基础设施；
  void 已有 `absurd`）。

### data
- `list.typort`（+151）：`foldr` / `foldl` / `elem` / `zip_with` / `count` /
  `take_while` / `drop_while` / `last_option` / `split_at` / `flat_map` /
  `insert` + `sort`（插入排序，`p: T -> T -> Ordering`）/ `concat`（impl 于
  `List[List[T]]`）/ `unzip` / `sum` / 自由函数 `list_replicate`；
  `Option[T].to_list` 与 `Vec[T] len.to_list` 的 impl 也住这里
  （Option/Vec elaborate 早于 List，加载序所迫，`string.typort` 有先例）。
- `option.typort`：`and` / `zip` / `impl[T] Option[Option[T]] { flatten }`。
- `result.typort`：`map_or` / `swap` / `elim`。
- `either.typort`：`bimap` / `left_to_option` / 自由函数
  `option_to_either[A, B](o: Option[B], if_none: A): Either[A, B]`
  （Option 值放右边）——补齐 Option/Result/Either 转换格最后一个方向。
- `vec.typort`：`append` / `snoc` / `reverse` / `map2` / `zip`（后两者用
  GADT 索引细化，内层单分支 match）。
- `order.typort`：`Ordering.reverse`（lt↔gt）/ `then_with`（字典序串联）。
- `nonempty.typort`：`cons` / `append` / `foldl` / 自由函数
  `nonempty_singleton`。
- `decidable.typort` / `string.typort`：无可补（`Dec` 组合需要不存在的
  证明组合子；String 只有 `string_concat` 一个 prim，无长度/charAt）。

### show
- `show.typort`（+215）：`Show` 实例补到 Boolean / Ordering / Unit / Void
  （空 match 合法）/ String（原样）；`List[Nat|Int|Boolean|String]`
  （`[1, 2, 3]` 风格）；`Option[Nat|Int|Boolean|String]`（`some 3` / `none`）；
  `Product[Nat|Boolean, …]`、`Tuple2[Nat|Boolean, …]`（`(1, 2)` 风格）；
  `Either[Nat, Boolean]`（`left 1` / `right true`）、
  `Result[Nat, Boolean]`（`ok 7` / `err false`）。
  泛型条件实例（`impl[T] Show for List[T] where T: Show`）引擎不支持，
  已在模块头注明；需泛型时只能具象化实例。

## 2. 验证方法

prelude 经 `include_str!` 烧进二进制（`PRELUDE_CORE/HDL/SHOW`，
`src/L13_namespace/mod.rs:3868`），`typort check` 只见编译期快照。
因此采用两段式：

1. **草稿探针**：新定义 + 具体值探针写进 `target/prelude_scratch/`
   的 scratch 文件，`check` 对着旧 prelude 展开，零 `error:` 后才落盘
   （check 恒 exit 0，需自己扫输出）。
2. **集成**：重编译后全量 prelude 展开 + 冒烟程序 + 
   `L13_namespace::prelude_stdlib_tests`（5 个用例逐行断言 println 输出，
   含 `Vec.append` 方向回归钉）；`tools/gate_l13.sh` 快速口径过门禁。

加载序约束（op → eq → nat → calc → bool → option → result → order → void
→ decidable → vec → either → list → string → nonempty → hdl → show）贯穿
始终：只允许引用同文件在前或更早文件的名字。

## 3. 过程中发现的引擎怪癖（维护者向）

1. **`Vec.append` 曾语义反转（本轮已修）**：结果索引用 `len + m` 时
   定义性归约只允许对 `that` 递归，得到 `that ++ this`，连带 `snoc`
   （`[1,2].snoc 3 → [3,1,2]`）与 `reverse` 全错。修法：结果索引改
   `m + len`、对 `this` 递归——`m + 0 ≡ m`、`m + succ l ≡ succ (m + l)`
   皆定义性归约，`this ++ that` 语义与 `List.append` 一致。
   归约方向由 `nat_add` 按第二参数递归决定，写 prelude 索引时务必先算方向。
2. **`cong` 作用于字面 lambda 不做 beta 归约**：`cong (x => x + n) e` 的
   结果类型卡在未归约的 meta-Pi 上无法合一。现用 `cong2 nat_add e rfl`
   绕过；值得修引擎。
3. **裸标识符实参后跟 2+ 括号实参会被错误分组**：`add_assoc n (n * a)
   (n * k)` 解析成 `add_assoc (n (n * a) (n * k))`。绕过：let 绑定复杂实参
   或写成 `(n)`。
4. **错误级联掩盖根因**：一个 def 报错后，引用它的 def 报 "not in scope"，
   其所在 impl 整块不注册实例，下游 `.show` 等分发报
   `solve trait failed` —— 排错只看第一条 error。
5. **无终止性检查**：非结构递归（如 `mul_comm k n` 的欧几里得式递减）
   能通过 elaborate；prelude 内人工保证良基，引擎侧是敞口。
6. **括号续行敏感**：括号包裹的实参写到下一行会终结表达式
   （"expected `}`，found `(`"），链式调用须单行或 let 绑定。
7. **裸构造器元变量不定向**：`lnil.show` / `None.and x` 因 T 未约束而
   失败，需 `let` 注解；Nat 字面量不向 Int 强转，须写 `ofNat 2`。
8. **确认可用**（此前未验证）：对空枚举的空 match（`match this {}`）；
   具象实例头（`impl Show for Either[Nat, Boolean]` 等）正常注册与分发。
