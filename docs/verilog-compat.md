# Verilog 语法兼容层（Verilog Syntax Compat）

> 状态：**M1 + M2 已实现**（M1 见 2026-08 提交 `54cb818` / `280af08`；M2 本次
> 在 `task/verilog-compat-m2` 补齐）。
>
> 目标：让常用 Verilog 写法可以直接写在 `.typort` 文件里，与 typort 风格
> HDL 共用同一套 elaboration、Verilog 生成与 LSP 能力。

## 1. 工作原理

- **module 宏的 Verilog 臂**（`src/prelude/hdl/hdl-macros.typort`，`module`
  宏第一条规则）：匹配 ANSI 端口头 + `endmodule` 的模块
  ```verilog
  module top(input clk, input [7:0] a, output reg [7:0] q);
      ...
  endmodule
  ```
  该臂里 `input clk` / `input reset` / `input rst_n` 折叠进模块的隐式
  ClockDomain（`rst_n` → ActiveLow），不生成独立端口。
- **VExpr 语句表**（`src/prelude/hdl/hdl-verilog-compat.typort`）：模块体内
  的每条语句按 `VExpr` 宏的规则转写为与 typort HDL 完全相同的工厂调用
  （`newUInt` / `newUIntReg` / `whenBegin` / …）。`VExpr` 与 typort 的
  `Expr` 表严格分离，两种语法互不污染。
- 表达式层面：解析器（`src/L13_namespace/parser/mod.rs`）把 Verilog 专有
  写法脱糖成等价 typort 表达式（下表「脱糖」列）。

## 2. 映射表

| Verilog 写法 | 转写 / 脱糖 | 状态 |
|---|---|---|
| `module m(input clk, input [hi:lo] p, output reg [hi:lo] q); ... endmodule` | `module` 宏 Verilog 臂；`clk`/`reset`/`rst_n` 折叠进 ClockDomain | M1 |
| `wire [hi:lo] x;` / `wire x;` | `newUInt(hi-lo+1)` | M1 |
| `reg [hi:lo] q;` | `newUIntReg(hi-lo+1)` | M1 |
| `reg [hi:lo] q = <nat>;` | `newUIntRegInitNat(hi-lo+1, <nat>)`；同名 `output reg` 端口不再重复声明，init 进复位分支 | M2 |
| `assign y = e;` | `y := e` | M1 |
| `assign y[i] = e;` / `assign y[hi:lo] = e;` | 位选 / 部分选 LHS | M1 |
| `q <= e;` / `q = e;` | `q := e`（reg 决定时序/组合，组合由上下文决定） | M1 |
| `always @(posedge clk) begin ... end` | 体内语句原样转写 + 时钟名校验（HDV001） | M1 |
| `always @(posedge clk or negedge rst_n) begin ... end` | 复位名折叠进时钟域，体原样 | M1 |
| `always @(*) begin ... end` / `always @* ...` | `combBegin()` / `combEnd()` 上下文；reg 在此被组合驱动（HDV002 提示） | M1 |
| `if (c) ... else ...` / 单语句 / `begin/end` | `whenBegin` / `whenOtherwiseBegin` / `whenEnd` | M1 |
| `case (x) L1: s1; ... default: sd; endcase` | 互斥 when 链（`whenBegin` + `whenElseBegin`）；标签经 `CaseEq` 比较，`default` 恒真 | **M2** |
| `child u1 (.a(x), .y(w));` | `u1 = child.create` + `vconnT`（按子模块端口方向判定 LHS/RHS） | M1 |
| `8'hFF` / `5'd10` / `4'b1010` | `sizedLit(w, v)`；Expr 携带位宽，输出 `8'd255` 这类合法 sized 常量 | M1 / 位宽保真 M2 |
| `a[3]`（RHS） | `a.apply[3]` → `bitsel` | M1 |
| `a[7:4]`（RHS） | `a.slice[7, 4]` → `partsel` | **M2** |
| `{a, b, ...}` | `a ## b ## …`（Cat trait）；可嵌套 | **M2** |
| `&a` / `|a` / `^a` | `a.andR` / `a.orR` / `a.xorR` → `Bool` | **M2** |
| `a == b` / `a != b` | `VEq` trait → `===` / `=/=`（输出 `==` / `!=`） | M1 |
| `!a` / `~a` / `-a` | `not` / `not` / `neg` | M1 |

> 宽度语义：`+`/`-` 保持位宽（溢出截断），`*` 结果加宽，比较恒为 `Bool`，
> `##` 位宽相加 —— 与 typort HDL 完全一致（`docs/hdl-design.md`）。

## 3. 端口头约束（位置分组）

module 宏的 Verilog 臂按**连续段**匹配端口组，无法对可选标记做分支，因此
端口需按以下顺序书写（这也是常见 Verilog 声明顺序）：

1. `input clk`（可选，折叠进时钟域）
2. `input reset` / `input rst_n`（可选，折叠）
3. `[dir] [hi:lo] p` 位宽端口（input/output/inout 皆可）
4. `output reg [hi:lo] q`（时序输出）
5. `output reg qb`（标量时序输出）
6. `[dir] pb` 标量端口

同一个模块**一个时钟域**；折叠端口名必须是 `clk` / `reset` / `rst_n`。

## 4. 本次（M2）补齐的内容

| 项 | 说明 |
|---|---|
| 部分选 `a[hi:lo]` | 解析器把 `[hi:lo]` 脱糖为 `slice[hi, lo]`（读写两侧都支持） |
| 拼接 `{a, b}` | 解析器新增 `{…}` atom → `##` 链；实参位置显式拒绝 `{`，避免吞掉 `impl … { }` / `for … { }` 的块 |
| 归约 `& | ^` | 前缀运算符 → `andR` / `orR` / `xorR` |
| `case/endcase` | 新增 VExpr 臂 + `CaseEq` 类型类（`default` 作为普通标识符的恒真实例） |
| 纯组合模块多余 clk 端口 | 时钟端口仅在真正生成 clocked always 时才发射（`clocked` 非空），不再因 `output reg` 端口而误加 |
| `reg q = <init>` 去重 | 体内 `reg` 与同名 `output reg` 端口不再重复声明（原为非法 Verilog），init 保留进复位分支 |
| sized 字面量位宽 | 新增 `Expr::sizedLiteral(v, w)`，`8'hFF` 输出 `8'd255`；拼接里常量保留位宽（IEEE 1364 禁止拼接内无位宽常量） |

## 5. 已知限制（后续 / M3）

- `parameter` 头、`generate`、`initial`、延迟（`#`）、`$display` 等。
- `always` 体内**手写复位分支**：折叠设计下 `rst_n` 不是用户信号（引用会报
  “name not in scope”）。复位值请用 `reg q = <init>;` 表达（SpinalHDL 语义）。
- 时钟域子模块的实例化：折叠的 `clk` 不是普通端口，父模块暂无法用
  `.clk(...)` 连接；组合子模块的实例化不受影响。
- 头部 `output reg [w] q = <init>`：init 值请写成模块体内的
  `reg [w] q = <init>;`（自动去重并进复位分支）。
- `case` 转写为互斥 `if` 链（配合拼接/归约已验证），非原样 `case` 输出；
  `default` 分支条件带 `1 && …` 前缀（语义等价，仅外观）。
- 多时钟域、`inout` 方向判定等仍以 typort 侧能力为准。

## 6. 验证入口

- 回归测试：`cargo test --lib verilog_compat_tests::`
  （`src/L13_namespace/verilog_compat_tests.rs`）。
- 示例：`examples/hdl/23-verilog-compat.typort`（M1 骨架）、
  `examples/hdl/24-verilog-practice.typort`（M2 实践），
  经 `legacy_tests::test_examples_hdl_dir` 断言。
- 兼容层实现：`src/prelude/hdl/hdl-verilog-compat.typort`
  （VExpr 表）与 `src/prelude/hdl/hdl-macros.typort`（module Verilog 臂）。
