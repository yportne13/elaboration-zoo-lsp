# Bug：trait 实例的 Nat 类型参数未在调用点实例化（typeclass elaboration）

> 2026-08-26，由"表达式 let 物化命名 wire"任务（commit bcad744）实测发现、
> 已定位现象与边界但**未修复**。与 `l13-known-bugs-2026-08.md` Bug 2 同族
> （悬空/越界元变量 → `lvl2ix` 下溢），但触发面与机制链不同。
> 记录复现矩阵、一手证据（错误消息原文）、机制链（区分实测与推断）与修复方向。

---

## 一句话

trait 实例（`impl[w: Nat] Foo[UInt[w]] for UInt[w] { ... 方法体里把 `w` 当运行期 Nat 用 ... }`）
的 `w` 在实例求解时**不会被调用点的实际宽度实例化**：实例的引用里残留
**实例声明上下文的级别变量 `Rigid(Lvl(0))`**。后果按上下文分三种：

| 上下文 | 后果 | 实测 |
|---|---|---|
| 顶层 def、固定宽度 goal | 直接报错 `can't unify ... Rigid(Lvl(0)) ... Nat(8)` | §复现 A |
| module class 字段、参数化宽度 goal | **不报错**，运行期 `w` 求值成垃圾 → `width_range` 数出 0/1 → 生成无位宽的 `wire x;` / `reg d;` | §复现 B |
| 方法调用语法分发（`x.method(...)` 直呼 trait 方法） | 同上，且在方法体对 `w` 做 `match` 时 `lvl2ix` 减法下溢 panic（known-bugs Bug 2 同族） | §复现 C |

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

## 机制链

### 实测部分（有错误消息/输出直接支撑）

1. **实例注册形态**：`impl[w: Nat] Foo[UInt[w]] for UInt[w]` 被 elaborate 成一个
   合成名 def（`src/L13_namespace/elaboration.rs:1586-1596`，
   `def typ_name[params](方法lambda...): Foo[...]`），同时以**声明时刻的 Val**
   注册进 `trait_solver.class_instances`（`elaboration.rs:1441-1447`）——
   注册的 assertion 参数里 `w` 是**实例声明上下文的 `Rigid(Lvl(0))`**。

2. **Phase 1（实例筛选）**：`solve_trait` 用 `val_match(goal_arg, inst_arg)`
   匹配（`src/L13_namespace/unification.rs:657-704`）。`val_match` 的
   "Rigid 空 spine 绑定任意目标"臂（`typeclass.rs:283-292`）会把实例的
   `Rigid(w)` 当模式变量绑定 goal 值——**这一步的 subst 结果随后被丢弃**
   （Phase 2 不消费 `subst`，只拿 `inst.lvl` 即合成 def 名）。

3. **Phase 2（实例 elaborate + unify）**（`unification.rs:729-752`）：
   `infer_expr(Raw::Var(合成def名))` → `insert` 补隐式参数 → `eval` →
   `if let Val::SumCase { typ, .. }` 时 `unify_catch(typ, goal)`。
   **复现 A 的错误消息证明走到这一步时实例侧的 w 仍是 `Rigid(Lvl(0))`
   而非待解 Flex**——即"为实例参数造 fresh meta 再 unify 回 goal"的预期
   管道没有生效（`expected: WProbe[UInt[w], UInt[w]]` 的 w = Rigid(Lvl(0))，
   `find: WProbe[UInt[w], UInt[8]]` 的 w = Nat(8)，rigid-vs-concrete 直接
   `can't unify`）。

4. **顶层固定宽度场景**（复现 A）：第 3 步 unify 失败被 `?` 记为 last_err，
   所有候选耗尽后报 `solve trait failed`（`unification.rs:754-763`）。
   同时留下 `find unsolved meta with type Nat`——实例参数对应的元变量悬空。

5. **class 参数化场景**（复现 B）：goal 侧是 `UInt[Rigid(class_w)]`——与实例侧
   残留的 `Rigid(Lvl(0))` **形态同类**（都是级别变量），匹配/统一不再当场失败
   （推断：class 两阶段的延迟批量求解 `solve_multi_trait` + Nat defaulting
   兜底把悬空元变量以某种方式消解，见下"推断"）。**求值不报错但级别错位**：
   运行期 `w` 取到错误上下文的值 → `count_nat_forced`（`cxt.rs`，`width_range`
   的底层）对垃圾值数出 0 → `width_range` 返回 `""` → 生成无位宽的
   `wire x;` / `reg d;`。

6. **方法调用路径**（复现 C）：实例引用里的越界级别变量在方法体内被强制求值
   （`match width`）时 quote/求值走到 `lvl2ix`（`src/L13_namespace/mod.rs:903`，
   `l.0 - x.0 - 1`）→ `x > l` → debug 构建减法下溢 panic。与 known-bugs Bug 2
   的崩溃点相同。

### 推断部分（未逐一验证，修复时先证实/证伪）

- **Phase 2 为何没有 fresh meta**：两个候选解释，需要加断言/日志分辨：
  - (a) `insert`（`elaboration.rs:178-230`）对 `infer_expr(Raw::Var(def))`
    的返回没有插入隐式参数——可能 decl 表中该合成 def 的类型已被求值成
    非 `Pi(Impl)` 形态（例如两阶段处理中 whnf 固化），`insert_go` 直接原样返回；
  - (b) `eval` 出的 `SumCase.typ` 来自**声明时刻的闭包**（`typ_name` 的
    `format!("{:?}{:?}", trait_full, trait_param)` 把声明期 Val 烧进了名字/引用），
    应用时不携带调用点的 subst。
- **class 场景为何不报错**：怀疑 `solve_multi_trait`（`unification.rs:579-599`）
  延迟批量求解 + elaboration.rs:932-966 的 Nat defaulting 兜底把悬空元变量
  解成了错误值（而非报错）——这能同时解释"不报错"和"运行期是垃圾"。

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

## 修复方向（未修）

1. **根治（推荐）**：`solve_trait` Phase 2 不应寄望 insert+unify 兜底，应把
   Phase 1 `val_match` 已经算出的 `subst`（goal 值 → 实例参数绑定）用于构造
   实例引用——即实例 def 应用**调用点求出的实际参数**（类似 Lean 的
   `instFOo.{w}` 显式实例化）。同时排查 decl 表中合成 def 的类型形态，
   确保 `insert` 能为 `w` 造出 Flex meta。
2. **防御（低成本，先做）**：
   - `lvl2ix` 改 checked/saturating，把 panic 变成可诊断错误
     （known-bugs Bug 2 修复方向 (b) 同款，一处修两家受益）；
   - hdl-check 给 `createWidth`/`createRegWidth` 等加"宽度为 0"诊断——
     0 宽信号本就非法，能把 class 场景的**静默错宽度**变成显式报错，
     同时兜住本 bug 的可见性。

## 相关文件

- `src/L13_namespace/unification.rs` — `solve_trait`（Phase 1/2）、`solve_multi_trait`
- `src/L13_namespace/typeclass.rs` — `val_match`（Rigid 绑定臂）、实例注册
- `src/L13_namespace/elaboration.rs:1441-1447` — 实例 def 合成与注册；
  `:1586-1596` — 实例 def 形态；`:178-230` — `insert`；`:932-966` — Nat defaulting
- `src/L13_namespace/mod.rs:903` — `lvl2ix` 下溢点
- `src/prelude/hdl/hdl-signals.typort:573-631` — `RegNext` trait + `regNext`（受影响的既有功能）
- `src/prelude/hdl/hdl-types.typort` — `LetNamed`/`nameWire`（bcad744，KNOWN LIMIT 注释）
