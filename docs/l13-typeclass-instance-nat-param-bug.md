# Bug：trait 实例的 Nat 类型参数未在调用点实例化（typeclass elaboration）

> 2026-08-26，由"表达式 let 物化命名 wire"任务（commit bcad744）实测发现。
> **修复状态（同日晚些，commit 见 git log）**：
> - **复现 A（顶层 + 固定宽度）已修**——根因是 `solve_trait` Phase 2 在 unify 解出
>   实例参数**之前**就 `eval` 了实例引用，方法闭包捕获了未解 meta 的冻结环境；
>   修复 = unify 成功后**重新 eval**（`unification.rs` Phase 2）。回归测试
>   `tests/trait_nat_param_tests.rs`。
> - **复现 B（class 参数化）仍存，但已从静默错误变为显式警告**——HDL004
>   （`hdl-check.typort` 的 `ruleWidthGround` + Rust native `nat_is_ground`）：
>   宽度冻结的信号在生成 Verilog 里退化为 1 位时报告。剩余根治需要 meta 解
>   支持 Tm/延迟求值（消费点上下文才能提供正确 spine），见"修复方向"更新。
> - **复现 C（lvl2ix panic）**：`mod.rs::lvl2ix` 改 checked 运算，panic 消息
>   现在指名"悬空 elaboration 变量泄漏进 quote"并链接本文档（不再是裸的
>   subtract overflow）。
>
> 与 `l13-known-bugs-2026-08.md` Bug 2 同族（悬空/越界元变量 → `lvl2ix` 下溢），
> 但触发面与机制链不同。以下为发现时的原始记录 + 修正后的机制链
> （§机制链中标注了哪些推断后来被调试实据推翻）。

---

## 一句话

trait 实例（`impl[w: Nat] Foo[UInt[w]] for UInt[w] { ... 方法体里把 `w` 当运行期 Nat 用 ... }`）
的 `w` 在实例求解时**不会被调用点的实际宽度实例化**：实例的引用里残留
**实例声明上下文的级别变量 `Rigid(Lvl(0))`**。后果按上下文分三种：

| 上下文 | 后果 | 实测 | 状态 |
|---|---|---|---|
| 顶层 def、固定宽度 goal | 直接报错 `can't unify` | §复现 A | **已修**（re-eval 修复） |
| module class 字段、参数化宽度 goal | **不报错**，运行期 `w` 求值成垃圾 → `width_range` 数出 0/1 → 生成无位宽的 `wire x;` / `reg d;` | §复现 B | 仍存，**HDL004 显式警告** |
| 方法调用语法分发（`x.method(...)` 直呼 trait 方法） | 同上，且在方法体对 `w` 做 `match` 时 `lvl2ix` 减法下溢 panic（known-bugs Bug 2 同族） | §复现 C | panic 消息已可诊断 |

**注意**：这不是"表达式 let"功能的 bug——**既有的 `regNext` 在参数化模块下同样中招**
（生成 1 位 `reg d;`，见 §复现 B），只是此前整个代码库没有任何"impl 方法体里
运行期使用 Nat 类型参数"的先例（所有运行期宽度都走显式值参数，如
`memUInt(64, 8)`、`counter(10)`，或 module 宏转录的端口表达式
`createPortExpr(dir, ty, $w)`），所以从未暴露。

---

## 复现矩阵（全部实测，2026-08-26，master + bcad744）

### 复现 A：顶层 + 固定宽度 → 直接报错

```typort
trait WProbe[T] {
    def wOf: Nat
}
impl[w: Nat] WProbe[UInt[w]] for UInt[w] {
    def wOf: Nat = w          // ← 运行期使用 w
}
def probeW[T][p: WProbe[T]](v: T): Nat = p.wOf(v)

def topFixed: Nat =
    let v: UInt[8] = UInt.mk(None, literal(0));
    probeW(v)
```

`typort check` 报错（原文，节选）：

```
error: solve trait failed: WProbe["Sum(\"UInt\" ..., Rigid(Lvl(0), []), ...)", "Sum(\"UInt\" ..., Nat(8), ...)"]
  last error: can't unify
  expected: WProbe[UInt[w], UInt[w]]     ← w 是 Rigid(Lvl(0))，实例声明上下文的级别变量
      find: WProbe[UInt[w], UInt[8]]     ← 调用点 goal，w 已是具体 Nat
```

`expected` 侧（实例侧）的 `w` 是 **`Rigid(Lvl(0))`** —— prelude 里实例声明处的
binder 级别，**不是**调用点新建的 Flex 元变量，也没有被统一成 8。这是最核心的
一手证据：实例引用没有携带"待实例化"的参数。

### 复现 B1：参数化 module + regNext（既有功能中招）

```typort
module p3[w: Nat] {
    input a = UInt[w]
    output y = UInt[w]
    let d = regNext(a)      // RegNext[UInt[w]] 实例的 mkReg 内部 newUIntRegNamed(name, w)
    y := d
}
```

`typort emit --top p3[8]` 输出（**错误**，d 应为 `reg [7:0] d;`）：

```verilog
  reg d;                    ← 位宽丢失：width_range 数出 0/1，返回 ""
  always @(posedge clk) begin
    d <= a;
  end
```

对照：**非参数化** module（07-registers.typort，`regNext(a)` 且 a: UInt[8]）
输出正确的 `reg [7:0] rd;`——固定宽度下该路径工作（legacy_tests 有断言）。

### 复现 B2：参数化 module + LetNamed（bcad744 新功能）

```typort
module p2[w: Nat] {
    input a = UInt[w]
    output y = UInt[w]
    let z = a + a            // nameWire → LetNamed[UInt[w]] 实例 mkNamed(name, w)
    y := z
}
```

`--top p2[8]` 输出（**错误**，z 应为 `wire [7:0] z;`）：

```verilog
  wire z;                   ← 位宽丢失
  assign z = (a + a);
  assign y = z;
```

同样的代码在**固定宽度** module（`a: UInt[8]`）下输出正确的
`wire [8:0] x; wire [7:0] z; ...`（`+`/`+^`/`-` 全部正确）。

### 复现 C：方法调用语法分发 → lvl2ix panic（与 known-bugs Bug 2 同族）

bcad744 的第一版实现用方法调用语法 `($y).letNamed(stringify $x)` 分发，prelude 形状：

```typort
trait LetNamed { def letNamed(nm: String): Self }
impl[width: Nat] LetNamed for UInt[width] {
    def letNamed(nm: String): UInt[width] =
        match width { case zero => ... case succ(t) => ... }   // ← 强制求值 width
        ...
}
```

参数化 module 下触发：

```
thread 'main' panicked at src\L13_namespace\mod.rs:903:8:
attempt to subtract with overflow        ← lvl2ix(l, x) = l.0 - x.0 - 1，x 引用越界级别
```

与 `l13-known-bugs-2026-08.md` Bug 2（match 分支深处内联 trait 方法 → 元变量悬空
→ `lvl2ix` 下溢）同一崩溃点、同一族根因（实例/约束求解留下的越界元变量引用），
但触发语法不同（这里是接收者方法调用 + impl 体引用自身 Nat 参数）。

### 反证：普通泛型 def 完全正常（bug 锁定在 trait 实例路径）

```typort
def mkNamedPlain[bn: BindingName, w: Nat](v: UInt[w]): UInt[w] =
    let wire = createSignalExpr(bn.name, createWidth(bn.name, w));   // ← 同样运行期用 w
    ...
module iso1[w: Nat] {
    input a = UInt[w]
    output y = UInt[w]
    let z = mkNamedPlain(a + a)
    y := z
}
```

`--top iso1[8]` 输出**正确**：`wire [7:0] z;`。普通函数应用的类型参数由
unify 直接绑定到调用点实参，运行期取值正确。**问题只出在 trait 实例的
求解/实例化路径**（`solve_trait` 及其实例注册/引用构造）。

---

## 机制链（调试实据修订版）

发现当晚加了临时 debug 输出（`solve_trait` Phase 2 / `solve` / `solve_with_pren` /
`width_range` / `count_nat_forced`）逐层观测后，**推翻了初版报告的两个推断**，
修订如下（初版推断以 ~~删除线~~ 标注）：

### 实测部分（debug 输出直接支撑）

1. ~~"insert 没有为实例参数造 fresh meta"~~ **错**：Phase 2 的
   `infer_expr(Raw::Var(实例def))` 返回 `Pi(w: Nat, Impl, ...)`，`insert` 正确造出
   fresh meta（日志：`after insert tm: App(Decl(实例def), AppPruning(Meta(?w)), Impl)`），
   eval 出的 `SumCase.typ` 里 w 是 **Flex**。~~"错误消息里的 w 是 Rigid(Lvl(0))"~~
   **错**：那是 Flex meta 的 pretty 名（以实例参数名 w 命名）。

2. **真正的根因（复现 A）**：Phase 2 的求值顺序——
   ```rust
   let val = self.eval(&cxt.decl, &cxt.env, &tm);   // ← eval 在先
   if let Val::SumCase { typ, .. } = val {
       self.unify_catch(cxt, typ, x, ...)?;          // ← unify（解出 ?w）在后
   }
   ```
   `val`（trait 字典 SumCase，方法闭包）在 **?w 未解时**求值固化——方法闭包捕获的
   环境里 w 是**未解 meta**。unify 虽然随后解了 meta 表里的 ?w（日志确认
   `solve_with_pren renamed OK`），但 `solve_multi_trait` 存进约束 meta 解的正是
   这份**旧 val**（`MetaEntry::Solved(val, ...)`）——运行期 force 得到冻结字典，
   方法体执行时 w 是悬空引用。顶层固定宽度场景下 unify 直接报
   `can't unify expected WProbe[UInt[?w], UInt[?w]] / find WProbe[...]`——
   实为 unify 内部 flex-flex 约束求解对该冻结环境的连锁失败。
   **修复**：unify 成功后重新 eval（闭包捕获已解 meta）。

3. **复现 B（class 参数化）的剩余机制**：unify 解为 `?w := λspine.Var(Ix(1))`
   （"取 spine 第 2 个参数"——因 rhs `Rigid(class_w)` 恰好出现在 spine 中）。
   运行期 force 时 spine 是**冻结的 elaboration 期 Rigid 列表**
   （`Flex(?w, [Rigid(Lvl(1)), Rigid(Lvl(0))])` → force → `Rigid(Lvl(0))`，
   `count_nat_forced` 数出 0 → `width_range` 返回 "" → 1 位信号）。
   **Val 层的 `Rigid` 是绝对级别符号，永不查求值环境**——只有 quote→`Var(Ix)`→
   eval 才能跨上下文解析。固定宽度之所以一直正确：解是常量函数
   `λspine.Nat(8)`，不依赖冻结的 spine。**根治需要 meta 解能表达"消费点
   参数化"**（Tm/延迟形态），当前 `MetaEntry::Solved(Rc<Val>)` 接口不支持。

4. **HDL004 的 Phase-A 误报问题与门控**：class 两阶段的 Phase A（字段值类型
   检查）也会 eval 出一棵一次性树，其中**所有**宽度（含宏转录端口）都是
   class 参数的 Rigid——直接检查会把整个模块报一遍。门控：同一模块存在
   至少一个 ground 宽度（运行期那轮的端口必然 ground）才报告非 ground 信号。

### 推断部分（未逐一验证）

- class 场景 goal 参数（`UInt[Rigid(class_w)]`）在 Phase 1 `val_match` 的
  Rigid-绑定臂与实例模式匹配成功、Phase 2 unify 也成功（无报错），解链条正常
  传导到 `?w := λspine.Var(Ix(1))`——与 2/3 的实测一致。
- `Rigid(Lvl(2))`~`Rigid(Lvl(7))` 等出现在 prelude 加载期 `width_range` 调用中
  的值来自其他 elaboration 上下文（与本 bug 无关的正常 stuck）。

---

## 影响范围

- **现有 prelude**：`regNext` / `regNextWhen`（hdl-signals.typort）、`Mem.readSync`
  等一切"impl 方法体里把宽度参数传给 create* 工厂"的功能，在
  **宽度参数化的 module**（`module m[w: Nat]`）内全部生成错误位宽（静默）。
  固定宽度模块不受影响（现有示例/测试恰好全是固定宽度，因此从未暴露）。
- **bcad744 新功能**：`LetNamed`/`nameWire` 同上——参数化 module 里的表达式
  let 生成无位宽 wire（已在 hdl-types.typort 的注释中标注 KNOWN LIMIT）。
- **用户自定义类型**：任何"带 Nat 类型参数的 trait 实例 + 方法体运行期使用该参数"
  的用户代码都会踩；顶层场景至少有显式报错，class 场景静默产出错误硬件。

## 修复方向

1. ~~"以 Phase 1 subst 实例化实例引用"~~ —— 调试实据显示 Phase 2 的
   insert+unify 管道本身正常，无需替换；真正的修复点见下。
2. **已实施（2026-08-26）**：
   - `solve_trait` Phase 2 unify 成功后**重新 eval** `tm`——方法闭包捕获已解
     实例参数（修复复现 A，全部 ground 宽度场景）；
   - `nat_is_ground` native + hdl-check `ruleWidthGround`（HDL004）——把
     复现 B 的静默 1 位退化变成显式警告（门控避开 Phase A 一次性树的误报）；
   - `lvl2ix` checked 运算 + 指名根因的 panic 消息（复现 C 的可诊断性）。
3. **剩余（复现 B 根治，未做）**：让约束 meta 的解能表达**消费点参数化**——
   例如 `MetaEntry::Solved` 支持 Tm/延迟形态，或 class Phase B 组装字段 Tm 时
   对 `Tm::Meta(约束)` 做 Tm 展开（消费点 eval 时以自己的 env 构造实例应用
   的 spine）。这是 elaborator 架构级改动，影响 quote/eval/meta 全链路，
   需单独立项。

## 相关文件

- `src/L13_namespace/unification.rs` — `solve_trait`（Phase 1/2）、`solve_multi_trait`
- `src/L13_namespace/typeclass.rs` — `val_match`（Rigid 绑定臂）、实例注册
- `src/L13_namespace/elaboration.rs:1441-1447` — 实例 def 合成与注册；
  `:1586-1596` — 实例 def 形态；`:178-230` — `insert`；`:932-966` — Nat defaulting
- `src/L13_namespace/mod.rs:903` — `lvl2ix` 下溢点
- `src/prelude/hdl/hdl-signals.typort:573-631` — `RegNext` trait + `regNext`（受影响的既有功能）
- `src/prelude/hdl/hdl-types.typort` — `LetNamed`/`nameWire`（bcad744，KNOWN LIMIT 注释）
