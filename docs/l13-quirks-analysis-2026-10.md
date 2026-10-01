# prelude 补充轮发现的引擎怪癖：根因分析（2026-10-01）

四个并行只读分析（探针均在 `target/quirks/`，未改源码）对 prelude 补充轮
暴露的引擎问题定位根因。每节：现象 → 根因（file:line）→ 修复草图（不实施）
→ 影响面与测试。修复须 **reference 与 twin（bump_spine_iter）双引擎成对落地**。

---

## 1. cong 作用于字面 lambda：三方死锁而非归约缺失

### 1.1 复现矩阵（探针在 target/quirks/cong/）

- **失败**：`cong (x => x + 0) rfl`、`cong (x => x + n) rfl`——find 定型为
  `Eq[Nat](?51567.+ {?51569 n} 0, …)`（卡死投影头）。
- **通过**：lambda 体无方法调用（`cong (x => succ x) rfl`）；lambda 先绑定到
  有标注的 def/let；显式隐参 `cong[Nat, Nat, n, n]`；证明是具类型变量
  `cong (x => x + 0) e`（e : Eq m n）。
- **重要修正**：文档绕过 `cong2 nat_add e rfl` 是**形状巧合**——期望侧出现
  `Eq (m+0) (n+0)` 归约形状时 cong2 同样失败（pr 探针）。
- 判别实验：同一 lambda 换证明 `e : Eq m n` 后 find 已归约——**lambda 的
  β 归约从未缺失，缺的是字典元变量落地后方法投影的重新归约**。

### 1.2 根因：三方死锁（任一方动一步即可解）

- **(a) 字典元变量悬空**：`+` 是 trait 方法，lambda 体走 trait_wrap
  （bump_spine_iter/typeclass.rs:401、601-649），字面 lambda 被 check 到
  `?A -> ?B`，字典 goal `Add[?A, ?O]` 的非 out 参 ?A 仍 flex →
  `solve_trait_ref` 推迟（typeclass.rs:312-317），只进 trait_metas 挂账。
- **(b) `XCell::Obj` 永久卡死**：cong 余定义域 `Eq (f ?x) (f ?y)` 求值时，
  β 归约正常发生（force.rs:79-82），但体里 `Obj(Var $$, ".+")` 在 ObjSel 处
  force 基座得未解 meta → 生成卡死 `XCell::Obj`（eval.rs:517-563）；此后
  **force 的 Obj 臂只 force 内层再重建同样的 Obj，从不重新投影**
  （force.rs:764-769）。
- **(c) unifier 无臂**：unify_iter 的参数对解出 `?B := Nat` 后重试 ?D 仍
  flex 再推迟；`Obj(?D,.+) ?a 0` vs `n`——`flex_of` 对 HK_OBJ 返回 None
  （spine.rs:117-131），中性链分派（unify.rs:800-897）与 (Obj,Obj) 合同臂
  （:1321）均不命中 → `return false`。def 级 Nat-defaulting
  （machine.rs:3604-3666）只在 body check 成功后跑，此处 Err 短路轮不到。
- `e : Eq m n` 能过的机理：签名期 `?A` 被 `m : Nat` 钉死 → LIFO 首参对
  `?A := Nat` → ?D 以唯一实例落地 → 余定义域 eval 晚于 e、投影成功。
  rfl 提供不了刚性锚点，死锁成立。

### 1.3 修复草图

- **方案一（推荐）**：把 `XCell::Obj` 从"永久卡死"改成"挂起的选择子"——
  force.rs:764-769 的 Obj 臂：base force 后若已成 Sum/SumCase（字典
  record/构造子）就地重新投影（复用 eval.rs ObjSel 字段查找）+ 链上实参经
  vapp1 回放，继续 force 循环。约 30 行，落在"该归约而没归约"的真正站点；
  效果：字典 meta 一旦被后续求解落地，所有已建卡死链自然归约。
  reference 引擎 unification.rs:1217 同构，需成对修。
- **方案二（否决）**：unify 侧对 `Obj(Flex ?D, m)` 加"唯一实例默认化"——
  `Add` 有 String/Nat 两实例而 T 侧 flex 无法区分，单做无效。
- **方案三（保守备选）**：扩展 machine.rs:3604-3666 的 Nat-defaulting 块为
  "check 失败 + flex 堵住的 trait 目标 → journal 保护下默认化重试"——治标
  （hover/emit 等路径仍见卡死链），只作防堕底第二道。

### 1.4 影响面 / 测试

现有 prelude 全部绕开了该形状（nat.typort 用具名函数/显式隐参），无代码依赖
此失败；真正不等式的负例仍须失败，但失败位置/文案可能移动——lib.rs:1527 的
`can't unify` 语料白名单与 calc_tests 多处 `assert_err_contains` 需复查。
性能：force Obj 臂多一次 O(1) 判定，命中重投影时链回放 O(spine)；"consult
未解 meta 即 taint 不入 memo"纪律天然覆盖。测试：正例钉进
prelude_stdlib_tests（`cong (x => x + n) rfl` refl 解包值断言）+ 负例钉
calc_tests + twin/参考观察表对拍（prelude_full_observation_tables_match_
reference）。

---

## 2. 解析器：实参平级 vs 括号折叠的错分组 + 续行断开

### 2.1 机制背景

2026-09-19 引入的 SPINE_ESCAPE 哨兵：`p_spine`（parser/mod.rs:1212）的每个
实参用完整 Pratt `expr_bp(0)` 解析（mod.rs:1141-1150），其后缀循环
（mod.rs:809-814）把 `(` 当后缀算子，单实参括号组折叠成
`App(lhs, arg, SPINE_ESCAPE)`（mod.rs:864-876）；`p_spine` 结尾的结算
（mod.rs:1216-1243）把顶层带哨兵的 App 拆成平级实参——**但只拆一层**，
随后 `strip_spine_escapes`（mod.rs:1170-1210）把残余哨兵剥成真应用。

### 2.2 Q1 触发条件矩阵（实测）

| 形状 | 结果 |
|---|---|
| `f n (x)` | OK（2026-09-19 修复的形态） |
| `f n (x) (y)` | **错分组** → `f (n (x)) (y)`：`n (x)` 胶连成首实参 |
| `f (a) (b) (c) (d)`（头位 run） | OK（头位折叠链与平级实参同构） |
| `f n (x) y (z)`（每段 run=1） | OK |
| `f (n * a) n (n * k)`（复杂实参在前） | OK（此前记录有误，实测干净） |

精确条件：**实参位**（第 2 槽起）以非括号原子开头的实参，后跟 **run ≥ 2**
的连续单实参括号组时，除末组外的组全部折叠进该原子。根因：mod.rs:1228-1238
结算只拆一层，mod.rs:809-814 贪心折叠任意层。`add_assoc n (n * a) (n * k)`
的精确错误 AST 是 `add_assoc (n (n * a)) (n * k)`（e1.typort 用异型实参探针
判别）。

### 2.3 Q2：续行断开

spine 实参循环把 `EndLine` 当硬终结符（expr_bp 后缀循环只接受
Op/LParen/LSquare/Dot，mod.rs:809-814；`p_arg.many0` 在 EndLine 处直接失败）。
词法层换行是不带缩进信息的独立 token（lex.rs:288-296）。合法换行点都是显式
`kw(EndLine).option()`（`(` 后、`)` 前、逗号后等），唯独实参间没有——文法上
平级实参靠 juxtaposition，设计者无法区分续行与下一条语句，于是禁止。
下游失效形态随上下文：普通体 → 孤儿行 + "expected newline"；match/let →
"expected `}`"；**花括号块 → 静默错义（被吞成下一条语句，只报体类型不匹配）**
——最危险一族。

### 2.4 修复草图

- **Q1（小改，低风险）**：结算从"拆一层"改成递归"拆到不带哨兵为止"
  （`unescape_spine` 逆序收集保序）。语义决策点：修复后实参位括号组永远
  平级，部分应用须写 `f (g a b) c`。
- **Q2（中改，风险集中）**：必须**缩进感知**（EndLine token 携带下一行缩进列，
  `p_spine` 实参循环在"续行更深缩进且以原子起始"时消费换行、失败回溯）。
  **反对无条件跳行**：实测会击穿 `calc` 宏（calc.typort:48,59 的 `$y: raw`
  片段走 `p_raw → p_spine`，步骤行会被折叠成实参，整个 calc 机制报废）。

### 2.5 影响面（实测扫描）

Q1 修复对现存代码**零影响**：src/prelude 0 处依赖（作者已知此 bug，在
core/nat.typort:96-97 有注释并用 let 绕开）、examples 0 处（唯一命中为头位，
不受影响）、tests 0 处。Q2 缩进方案：prelude+examples 行首 `(` 缩进行 108 处
均为同缩进（calc 步骤/宏体），不受判据影响。主要工程风险在词法 token 结构
改动波及宏展开 re-lex 路径（mod.rs:1560-1597）。

测试落点：`tests/known_bug_pins.rs`（LSP 全路径 pin）、parser 内联
`#[test]`（mod.rs:3558 起 AST 形状断言）、仿 `tests/implicit_comma_args.rs`
建 `tests/spine_paren_args.rs`。守护用例必须含 calc 多步骤块、花括号块
同缩进语句、`succ (x) + y`、`f(a, b)`。

### 2.6 相邻发现（顺带实测）

隐式 `[..]` 折叠不打哨兵（`f n [T]` 胶连成 `f (n[T])`，连拆一层兜底都没有）；
返回类型与 `=` 之间不允许换行；def 绑定组不支持 `(n a k: Nat)` 空格多名；
`--` 不是注释。

---

## 3. 错误级联掩盖根因 + 裸构造器元变量不定向

### 3.1 错误级联（两条传播路径，均实测复现）

- **(a) def 级**：decl 循环（lib.rs:1880-1924）`Err` 分支 continue 不 break，
  且失败 decl 不进环境（`infer_after_prefix` elaboration.rs:1063-1066 先
  `cxt.clone()`，失败时 clone 连同局部注册被丢弃）→ 后续引用逐个报
  "not in scope"，根因淹没。
- **(b) impl 块全有全无**：inherent impl（elaboration.rs:1516-1604）逐方法
  `?` 循环，任一方法失败整块 `ImplDecl` 判死，正确方法一起消失；trait impl
  （elaboration.rs:1605-1835）**实例头先注册**（1677-1683
  `impl_trait_for`，错误后不回滚）、方法拼成**单个**合成 Def 一次性注册
  （1822-1832），任一方法失败 → 实例定义不在 decl 表 → 下游 solve_trait
  Phase 1 找得到实例、Phase 2 查不到定义 → 最迷惑的
  "solve trait failed ... last error: name not in scope"（unification.rs:784-829）。

修复草图：**(a)** 复用现成 `fake_bind` 桩机制（cxt.rs:1228），失败 decl 以
"名字 + 声明类型 + 中性自引用体"占位进环境（A1），叠加 failed-names 集合把
二阶 "not in scope" 降噪为"引用了上方失败的声明"（A2）。**(b)** inherent
逐方法 catch 隔离（B1）；trait impl 拆成逐方法 def、失败方法用 trait 签名
桩字段顶上（B2），可选失败时撤销 `impl_trait_for`（kick journal 已有
`TraitInstancesPush` undo 通道，B2'）。

### 3.2 裸构造器元变量（`lnil.show` / `None.and x` 失败）

决定性线索：接收者类型打印为**泛型 Pi** `[T: Type 0] → List[T]` 而非
`List[?T]`——问题发生在进求解器**之前**：`Raw::Var` 直查分支
（elaboration.rs:2380-2384）返回存表原样类型，不跑 `insert`（负责 Impl Pi
逐参 fresh_meta，elaboration.rs:203-260；只在 App 头部等路径调用）→
`head_key` 对 Pi 返回 None → head 桶查不到 → traits 为空 → "has no object"。
对照实测：`lnil[Nat].show`、`Some(4).map(myid).show`（?U 被实例头定向为 Nat）
均 OK——**嵌套 Flex 的实例头定向今天已存在**（Phase 2 unify
`List[Nat] ↔ List[?T]`，unification.rs:794-796）；裸 Flex 非 out 参在
Phase 2 之前被推迟（unification.rs:765-774）。

修复草图：**C1（推荐）** 成员访问驱动（elaboration.rs:2547 之后）对 Pi 头
接收者跑 `insert`（与 App 路径同款），使 `lnil → List[?T]`，现有流水线自然
闭环（`val_cache_key` 对含 Flex 类型返回 None，无缓存污染）；**C3（补充）**
solver 侧对"裸 Flex 非 out 参 + 候选唯一（或全部候选头一致）"先定向再重走
Phase 1——须保住 765-768 注释的防线（`val_match(Flex,_)` 恒真会选错实例）。

### 3.3 测试

`run_with_prelude` 首个 Err 即中止（mod.rs:4348 `?`），只能 pin 第一个错误；
"下游不再级联"用 `assert_ok` + println 值断言表达；class_tests.rs:626 的
`assert!(!output.contains('?'))` 可复用。Q1b 修复后的多错误并存形态需要新
helper 镜像 lib.rs:1887-1905 的 accumulated_errors 排水。

---

## 4. 无终止性检查：可靠性敞口 + LSP 冻结

### 4.1 现状（探针实测）

- `fake_bind` 占位机制（twin machine.rs:822-847）让自引用以**声明类型**
  自证，零终止判定：`def bad(n: Nat): Nat = bad n`、`def p: Eq 1 2 = p`、
  `def f: Void = f` 全部通过。语言不支持互递归（前向引用 not in scope），
  故检查可退化为单 def 自调用分析，无需调用图 SCC。
- 求值惰性（带参 def 只存 Clo），但强制点（println / 零参 def / 类型 whnf）
  触发的循环 = **静默自旋**：迭代 eval（eval.rs:309-321 `W::CallAsm`）每轮
  push/pop 对称，实测 `check` 挂死时内存恒定 ~205MB——不炸栈、不 OOM、
  无输出。unify fuel=100（machine.rs:1417）只管合一重派发，eval/println
  路径无任何上限；RESIDENT_BUMP_LIMIT 等 arena 检查点在单次 eval 内触不到。

### 4.2 风险分级

- **R1 证明不可靠（最高，两行触发）**：`Eq 1 2 = p` 经 eliminator 可
  transport 出任意假等式（实测推出 `Eq 2 1`）；`Vec[Nat] len` 长度索引 GADT
  + 假 Eq 可索引混淆；Void 可居使 `absurd` 可产任意型。HDL 侧凡用证明做
  宽度/索引精化的路径均可能被污染。
- **R2 LSP 冻结（高，必然复现）**：用户文件每次击键重跑 observe_user
  （lib.rs:1478），单线程串行 worker（lib.rs:1800-1825）挂死即饿死全部后续
  分析，无 watchdog（class_tests.rs:774 的 watchdog 仅测试用），恢复 = 重启。
- **R3 CLI 挂死（高）**：check/build/emit/doc 同引擎族；check 恒 exit 0，
  CI 对"假定理通过"与挂死均无感。
- **R4 大数显示爆炸（中）**：quote 把原生 `XCell::Nat(k)` 展开成 k 节点
  succ 链（quote.rs:556-568），`println(nat_mul 100000 100000)` 即 R2 同款
  冻结，10^6 才 0.16s。

### 4.3 终止性检查草图（三档 × 误杀清单）

| 档 | 判据 | 误杀（须 opt-out） | 健全性 |
|---|---|---|---|
| A（最廉） | 每个自调用至少一个实参是"主语为参数的 match 的模式变量" | nat_div/nat_rem（let 计算值递归）、combReach（worklist）、gcd | 不健全（ping-pong 换参可穿透） |
| B（Agda 式同位） | 匹配主语所在参数位的实参须是模式变量 | 上述 + mul_comm/int_add/int_mul（prelude 招牌引理） | 健全 |
| C（单函数 SCT-lite） | 实参变换关系矩阵幂闭包每环严格 ↓ | 仍拒 nat_div/nat_rem/combReach | 健全且宽松 |

挂载点：twin machine.rs:3589-3590（check 与 wrap 之间）、reference
elaboration.rs:1099-1100；已有可仿写的 AST 走查器（binder_occurs
machine.rs:66）。成本：~442 个自递归 def 全量 <10ms（<0.5% of 3.3s prime），
sub-ms/击键。opt-out：短期引擎侧 allowlist（nat_div/nat_rem 反正加载后被
register_nat_builtins 换成 primop），中期落声明级标注语法。

### 4.4 建议落地顺序

1. **先止损**：LSP kick watchdog（仿 class_tests.rs:732-774 线程模式）+
   CLI `--max-infer-secs`——把 R2/R3 从永久冻结降为可诊断错误。
2. Level A 检查 + allowlist（twin 先行）。
3. 声明级 opt-out 语法落地，清空 allowlist；改写 nat.typort 的
   "引擎不做终止检查"注释。
4. 循环证明可靠性专项（guardedness/positivity 口径，独立立项）。
5. 伴生小修：quote 对 `XCell::Nat(k)` 压缩显示封 R4。

---

## 5. 优先级总览

| 问题 | 严重度 | 修复成本 | 建议 |
|---|---|---|---|
| 循环证明 / 无终止检查（§4） | 可靠性敞口 + LSP 冻结 | watchdog 小 / Level A 中 | watchdog 先行，检查跟进 |
| cong+lambda 投影卡死（§1） | 引擎 bug（证明写法受阻） | 小（force.rs ~30 行 + reference 同构） | 独立小 PR |
| 裸构造器元变量（§3.2） | 用户体验 | 小（C1 一处 insert） | 低垂果实 |
| 错误级联（§3.1） | 用户体验（掩盖根因） | 中（双引擎三入口对齐） | A1+B1+B2 起步 |
| 解析器 Q1 错分组（§2.2） | 语言可用性 | 小、现存代码零影响 | 可直接实施 |
| 解析器 Q2 续行（§2.3） | 语言可用性 | 中、须缩进判据 | 随 Q1 一起，先写守护用例 |
