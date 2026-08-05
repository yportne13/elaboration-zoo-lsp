# Module 宏重构分析报告（2026-08-04）

> 状态：分析完成，方案已确认，待实现。
> 前置：class 机制已优化（见 L13-code-review.md 与 class_tests.rs），
> module 宏将重构在优化后的 class 机制上。
> 对照：docs/task2-module-macro-notes.md（上一次重构尝试的教训）。

## 1. 现状机制

### 1.1 数据流

- `ModuleTree { num: Nat, data: Vec[ModuleDef] num }`、`ModuleDef { name, cd, expr_num, expr }`
  存在 **Infer 的全局 mutable_map**（`RwLock<HashMap<SmolStr, Rc<Val>>>`，cxt.rs:154-217）。
- 模块 body 的每个副作用（信号创建、赋值、when 栈）通过 `change_mutable("ModuleTree", ...)` /
  `change_mutable_default` / `create_global` / `get_global` 写/读全局状态。
- `WhenStack`（whenBegin/whenEnd/whenElseBegin/whenOtherwiseBegin）同样在全局 map。
- 信号创建：`newUInt` 等 → `createSignalExpr(name, e)` → 按 Expr 形态决定是否写入树
  （create*/assign 写入；literal/mux/bitsel/subSignal 不写）。
- 赋值：`addSignalAssignment` → `addWhenContext`（按 WhenStack 包 when 节点）→ 写入树。

### 1.2 module 宏展开（现状）

`module M[w: Nat] input a = UInt[w] { body }` 展开为 class：

```typort
class M[w: Nat] impl Module {
    let zz_tree: ModuleTree = let _init = change_mutable_default("ModuleTree", x => x, ModuleTree.mk(0, nil));
        let _ws = create_global("WhenStack", whenStackEmpty);
        let _prev = get_global("ModuleTree");
        let _creat = change_mutable("ModuleTree", x => ModuleTree.mk(0 + 1, ModuleDef.mk(stringify M, defaultClockDomain, 0, nil) :: nil));
        $( let $p: $t[$w] = $t.mk(Some(stringify $p), createPortExpr(...)); )*   // 第一遍：真实信号
        $($body)*
        let module_result = get_global("ModuleTree");
        let _restore = create_global("ModuleTree", _prev);
        module_result;
    $( let $p: $t[$w] = $t.mk(None, subSignal(bn.name, stringify $p)); )*        // 第二遍：句柄字段
    def tree: ModuleTree = this.zz_tree
}
```

- 端口声明**两次**：第一遍真实信号（body 内 `sum := a` 用），第二遍 subSignal 句柄
  （父模块 `u.a := sig` 用）——这是语义需要（两个 Expr 形态不同），不是冗余。
- 子模块例化：Expr 宏特例分支 `let $x = $m.create[...]` → 调用点 `mkInstance(name, m)`。
- 全局状态副作用集中在 **zz_tree 一个字段的 let 链**内。

### 1.3 语法

端口必须在 `{` **之前**声明；`{` 内的 `input a = UInt[8]` 会被 Expr 宏静默当作
**模块内部信号**（`newUIntInput`），句柄字段消失、`u.a` 不可访问——**无任何报错**
（实测踩坑：探针把端口写进 `{}` 后 struct 只剩 zz_tree 字段，报 `has no object a`）。

## 2. 实测实验与结论（module_probe_tests.rs）

| 探针 | 输入形态 | 结果 | 结论 |
|------|---------|------|------|
| X3 | module 宏（正确语法） | expr_num=2（1 次累积） | **check 的重复求值被 _prev/_restore 抹平**，树内容正确 |
| X5 | 手写 class 单副作用字段 | expr_num=3 | **无 restore 时字段副作用被求值 3 次**（check 2 + 调用 1），树是脏的 |
| A4 | 手写 class 双副作用字段 | expr_num=8 | 每字段 4 次（check 3 + 调用 1）——**check 求值 × 字段数** |
| A6 | def body 顶层 prim | expr_num=2 | def-check 求值 1 次 + 调用 1 次 |
| D | `def t = M.create.tree` | num=1 | def-check 不执行 create（create 是 Def 调用） |
| E | 嵌套模块（父 body 里 `Child.create`） | num=1 | 现状嵌套只执行 1 次，层次连接正常 |

### 2.1 核心机制（task2 35x 退化的根因）

- **check 阶段对 let 绑定值求值 ~3 次**：`check` 的 `Raw::Let` 分支
  （elaboration.rs:551）`vt = self.eval(&cxt.decl, &cxt.env, &t_checked)` 在类型检查时
  eval 绑定值 → 绑定值里的 prim 副作用（change_mutable 等）**在 check 时执行**。
- 现状 module 宏把全部副作用集中在 **1 个字段**（zz_tree 的 let 链）+ `_prev/_restore`
  恢复 → 每次 check 求值 push 后 restore，**树内容正确**（X3），但**每次求值都执行整条链**。
- **task2 方案（moduleBegin/moduleEnd 栈式 + 扁平化）**：副作用分散到 N 个独立字段/
  局部 → check 求值 ×N → 全局树被反复推进（prepend 的 ModuleDef 反复累积）→
  后续遍历 O(n) → **35x 性能退化**（实测 572s vs 16s）+ debug 栈溢出。

> **2026-08-05 复核（task/hdl-module-macro-cleanup）**：在当前 L13 编译器下重测，
> "扁平化 → 35x" 已**不复现**。同一模块（小模块 / 9 信号 + 7 赋值 + when /
> 嵌套父子）分别用"单字段 let 链"与"每副作用一个 class 字段"实现，耗时与
> Verilog 输出完全一致（如 medium 模块：1.36–1.50s vs 1.28–1.50s；嵌套：
> 71–86ms vs 74–76ms）。此外实测每个 class 字段绑定值在 def-check 只被求值
> 2 次（不随字段数增长：N 字段 → 2N 次），链内嵌套绑定为 5 次/绑定（单行与
> 多行格式完全相同）。task2 的 35x 更可能是该分支自身的 O(n²) 索引缺陷
> （见 §8 同类根因）而非"多字段"本身。**但**仍不能把副作用平铺为独立 class
> 字段：带参数 class（如 `[w: Nat]`）中**无类型注解的字段**会留下未求解的
> struct 元变量（实测 `class c[w: Nat] impl Module { let f = 5 }` 报
> "can't unify for unsolved meta"）；Expr 宏输出的 body 语句都是无注解 let
> （generic `let $x = $y` 无法标注类型）；脚手架 prim 返回值是宇宙类型
> （`U 0`），不能作为 impl Module 类的字段类型。故模块宏保持单字段结构，
> 只做可读性重构（多行格式化、`let _` 丢弃绑定、字段改名 tree_data）。

### 2.2 约束（方案设计红线）

1. **副作用必须集中在单个字段的 let 链内**（不可扁平化为多个独立字段）。
2. **副作用必须幂等/可恢复**（push/restore 配对），check 的重复求值才能被抹平。
3. 信号/句柄的"双声明"是语义需要（真实 Expr vs subSignal 句柄），不可合并为一个。
4. 子模块 instance 记录必须在 **modulePop 之后**（记录进父树）；顶层（空栈）丢弃。

## 3. 问题清单

| # | 问题 | 严重度 |
|---|------|--------|
| 1 | 4 个宏 arm 重复（cd × Bool 端口顺序组合，转录体完全重复） | 维护性 |
| 2 | 6 个脚手架绑定（_init/_ws/_prev/_creat/module_result/_restore）塞在 zz_tree 超长链 | 可读性 |
| 3 | 子模块例化特例分支（Expr 宏 `$m.create` → 调用点 mkInstance） | 设计（用户诉求：不要特例） |
| 4 | when 逻辑在 when 宏与 Expr 宏重复（S5） | 维护性 |
| 5 | 端口在 `{` 内被静默当内部信号（无报错） | 易错性（实测踩坑） |
| 6 | 全局可变状态副作用（check 求值污染靠 restore 抹平，性能开销保留） | 性能隐患 |
| 7 | ModuleDef.expr 逆序（prepend）存储 | 待验证生成器是否已适配 |

## 4. 优化方案（已确认）

### 4.1 hdl-core.typort：语义化辅助函数

```typort
def modulePush(name: String, cd: ClockDomain): ModuleTree =
    let prev = change_mutable_default("ModuleTree", x => x, ModuleTree.mk(0, nil));
    let ws = create_global("WhenStack", whenStackEmpty);
    let d = change_mutable("ModuleTree", x => ModuleTree.mk(x.num + 1, ModuleDef.mk(name, cd, 0, nil) :: x.data));
    prev
def modulePop(prev: ModuleTree): ModuleTree =
    let cur = get_global("ModuleTree");
    let d = create_global("ModuleTree", prev);
    cur
def mkInstanceIfParent(instName: String, moduleName: String): Unit =
    let parent = get_global("ModuleTree");
    match parent.data { case nil => unit; case cons(_, _) => createSignalExpr("", instance(instName, moduleName)) }
```

- 替代 _init/_ws/_prev/_creat/module_result/_restore 六个脚手架。
- 保持"集中 + 幂等"：push 返回 prev、pop 恢复 prev 并取树；check 求值被抹平。
- mkInstanceIfParent：父模块（pop 后树非空）才记录 instance → 顶层 create 丢弃。

### 4.2 module 宏单 arm（能力已探针验证：可选片段 ✓、宏调宏 ✓）

```typort
macro_rules module {
    ($name: ident $( [$cd: ident] )? $( $args: params )* $( $d: ident $p: ident = $t: ident $( [$w: raw] )? )* {$( $body: Expr )*}) => {
        class $name $( [$cd: ClockDomain] )? $({$args})* impl Module {
            let zz_tree: ModuleTree = let _prev = modulePush(stringify $name, $( $cd )? defaultClockDomain);
                $( let $p: $t $( [$w] )? = $t.mk(Some(stringify $p), createPortExpr(stringify $d, stringify $t, stringify $p, $( $w )? 0)); )*
                $($body)*
                let _res = modulePop(_prev);
                let _zz_inst = mkInstanceIfParent(bn.name, stringify $name);
                _res;
            $( let $p: $t $( [$w] )? = $t.mk(None, subSignal(bn.name, stringify $p)); )*
            def tree: ModuleTree = this.zz_tree
        }
    };
}
```

- `$( [$cd: ident] )?` 可选时钟域、`$( [$w: raw] )?` 可选宽度 → 1 个 arm 替代 4 个。
- Bool 端口统一走 `createPortExpr`（内部加 `str_eq(ty, "Bool")` 分支，w 传 0 无效）。

### 4.3 Expr 宏

- 删除 `let $x = $m.create[...]` 特例分支（instance 记录移入 create 末尾）。
- when arm 转录为 `when!(...)` 调用（去重，宏调宏已验证）。

### 4.4 文档

- 明确"端口必须在 `{` 之前、`{` 内 input/output 是内部信号"。
- 记录"为什么不能扁平化"（§2.2 红线）。

## 5. task2 教训对照

| task2 经验 | 本次处置 |
|-----------|---------|
| 功能方案（栈式 push/pop、create 末尾记录实例、去特例、Local/Field 语义）正确 | 复用（modulePush/modulePop/mkInstanceIfParent） |
| 35x 退化根因：扁平化 → check 求值 ×N → 树反复推进 | **保持集中式 + 幂等恢复**（红线） |
| debug 栈溢出（深层嵌套 let） | 保持单字段链结构，不加深嵌套 |
| "the checker evaluates let-bound prim calls at def-check time" | 实测确认：check 对 let 绑定值求值 ~3 次（elaboration.rs:551） |
| 建议先弄清字段求值时机 | 已完成（§2 实验表） |

## 6. 后续方向（本次不做）

1. **根治 check 求值污染**：让 check 阶段不对 let 绑定值求值（elaboration.rs:551
   惰性化）——编译器核心改动，风险大，单独立项。
2. **纯函数式 AST 重写**：module body 构建 AST（when/switch/赋值全部 AST 化），
   消除全局可变状态——SpinalHDL SpinalTree 风格，大工程。
3. ModuleDef.expr 逆序存储的生成器适配验证。

## 7. 验证计划

- 新增 module_tests.rs：基本模块、参数模块、cd 模块、Bool 端口、嵌套 + 层次连接
  （`u.a :=`）、when/switch、reg、顶层 create 无 instance 残留、`let u = m.create`
  实例自动记录。
- **性能基准**：重构前后对比 examples/hdl 与 08-control-flow 耗时（防 35x 退化复发）。
- 全量 `cargo test --lib L13` 回归（含 legacy module/HDL 用例）。

## 8. 性能根因（实测定位，2026-08-05）

### 8.1 现象
重构版 module 宏把 02-arithmetic 从 2.1s 拖到 149–187s（70x）。二分实验链：
旧 prelude（stash）8s → 新 hdl-core/hdl-signals + 旧 hdl-macros 7.6s → 问题锁定
**新 hdl-macros 的 `_creat` 一行**。

### 8.2 根因：lambda 参数引用 → stuck GADT 索引 → force O(n²)

新宏 `_creat` 写成 `x => ModuleTree.mk(x.num + 1, ModuleDef.mk(...) :: x.data)`
（意图：基于当前树推进）；旧宏是 `x => ModuleTree.mk(0 + 1, ... :: nil)`（常量）。

- `x.num + 1` 与 `x.data` 的求值结果是**引用 lambda 参数的 stuck 值**
  （`::` 是普通 def、`+` 需要方法解析，check 时求值不展开）。
- 树的 data 字段类型是 GADT 索引 `Vec[ModuleDef] (x.num + 1)`——**索引本身 stuck**，
  随每次操作**累积**在树/类型里。
- 之后 body 每个信号/赋值（createSignalExpr → addExprToModuleHelper(x.num, x.data, ...)）
  都 force 整棵树 → force(Sum) 递归 force 每个类型参数 → **每次展开 stuck 链**。
  调用次数 × 单次耗时都递增：change_mutable 6ms→230ms 递增、x.num/x.data 字段访问
  1891 次×35–70ms、force >5ms 共 63901 次（中位 179ms）——典型 O(n²)。

微基准定位：组合（x.num+1 + ::x.data）在 def/class/小 body 下都 <55ms；
**9 信号无赋值 749ms，9 信号 + 7 赋值 163s**——`:=`（走 createSignalExpr
`case _` 分支 + addWhenContext）是主要放大器；常量版全程 2s。

### 8.3 修复与红线
- `_creat` 恢复常量形式（`0 + 1` / `:: nil`）——语义等价（`_init` 已把树重置为
  `mk(0, nil)`，`x.num = 0`、`x.data = nil`），但类型索引是 WHNF Nat，force 廉价。
- 修复后全量 examples/hdl：22.3s（旧宏 ~19s），02-arithmetic 2.4s ✓。
- `_inst = mkInstanceIfParent(...)` 的 `x.data` 引用只在构造尾部执行一次（非循环），
  实测 09-hierarchy 0.9s——可保留。
- **红线（写入 hdl-core 注释）**：module 宏里禁止用 `x.num + 1` / `:: x.data`
  这类"基于 lambda 参数推导"的推进写法；GADT 索引字段的参数引用会 stuck 累积。
