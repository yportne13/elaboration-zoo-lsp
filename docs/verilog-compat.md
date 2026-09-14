# Verilog 语法兼容层（Verilog Syntax Compat）

> 状态：**M1 + M2 + M3 已实现**
> - M1（2026-08 提交 `54cb818` / `280af08`）：module 宏 Verilog 臂 + VExpr 语句表骨架。
> - M2：部分选 / 拼接 / 归约 / case + 代码生成修正。
> - M3：折叠端口成为真实端口；`always` 体内手写复位分支；带时钟域子模块实例化。
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
- **折叠端口 = 真实端口**：`input clk` / `input reset` / `input rst_n` 同时
  ① 经 `compatFoldPort` 折叠进模块的隐式 ClockDomain（`rst_n` → ActiveLow；
  `reset` → ActiveHigh；`clk` 设定时钟名），② 生成真实 Bool 端口，模块体内
  可以直接引用（`if (!rst_n) ...`）。其它标量输入只是普通端口。
- **VExpr 语句表**（`src/prelude/hdl/hdl-verilog-compat.typort`）：模块体内
  的每条语句按 `VExpr` 宏的规则转写为与 typort HDL 完全相同的工厂调用
  （`newUInt` / `newUIntReg` / `whenBegin` / …），elaboration、Verilog 生成、
  LSP 全部复用。
- 表达式层面：解析器（`src/L13_namespace/parser/mod.rs`）把 Verilog 专有
  写法脱糖成等价 typort 表达式（下表「转写 / 脱糖」列）。

> ⚠️ 宏实现注意：Typort 转录器的 `$( ... )*` 重复组**必须引用至少一个元变量**，
> 否则展开 0 次（`macros.rs` `MacroTranscriber::Group`：`loop_num` 取已用元变量
> 数的最大值，无元变量时为 0）。M1 的 `$( let _ = compatSetClk("clk"); )*`
> 因此从未执行——折叠一直是空话。现在模式组用 `$( input $ik: ident )*` 捕获
> 前导标量输入名，转录组引用 `$ik` 才真正迭代。

## 2. 映射表

| Verilog 写法 | 转写 / 脱糖 | 状态 |
|---|---|---|
| `module m(input clk, input [hi:lo] p, output reg [hi:lo] q); ... endmodule` | `module` 宏 Verilog 臂 | M1 |
| `input clk` / `input reset` / `input rst_n` | `compatFoldPort` 折叠进 ClockDomain + 真实 Bool 输入端口 | M1 / 真实端口 M3 |
| `wire [hi:lo] x;` / `wire x;` | `newUInt(hi-lo+1)` | M1 |
| `reg [hi:lo] q;` | `newUIntReg(hi-lo+1)` | M1 |
| `reg [hi:lo] q = <nat>;` | `newUIntRegInitNat`；同名 `output reg` 端口不再重复声明，init 进复位分支 | M2 |
| `assign y = e;` | `y := e` | M1 |
| `assign y[i] = e;` / `assign y[hi:lo] = e;` | 位选 / 部分选 LHS | M1 / M2 |
| `q <= e;` / `q = e;` | `q := e`（reg 决定时序/组合；组合由上下文决定） | M1 |
| `always @(posedge clk) begin ... end` | 体内语句转写 + 时钟名校验（HDV001） | M1 |
| `always @(posedge clk or negedge rst_n) begin ... end` | 复位极性来自折叠（negedge/posedge），复位沿进敏感表 | M1 / M3 |
| `if (!rst_n) q <= 0; else q <= d;`（always 内） | when/otherwise 链；复位沿由折叠极性决定 | **M3** |
| `always @(*) begin ... end` / `always @* ...` | `combBegin()` / `combEnd()`；reg 被组合驱动（HDV002 提示） | M1 |
| `if (c) ... else ...`（单语句 / begin/end） | `whenBegin` / `whenOtherwiseBegin` / `whenEnd` | M1 |
| `case (x) L1: s1; ... default: sd; endcase` | 互斥 when 链（`whenBegin` + `whenElseBegin`）；标签经 `CaseEq`，`default` 恒真 | M2 |
| `child u1 (.a(x), .y(w));` | `u1 = child.create` + `vconnT`（按子端口方向判定 LHS/RHS） | M1 |
| `child u1 (.clk(clk), .rst_n(rst_n), ...)` | 折叠端口是真实端口，方向判定为 input → `.clk(clk)` | **M3** |
| `8'hFF` / `5'd10` / `4'b1010` | `sizedLit(w, v)`；Expr 携带位宽，输出 `8'd255` | M1 / 位宽保真 M2 |
| `a[3]` / `a[7:4]`（RHS） | `a.apply[3]` → `bitsel` / `a.slice[7,4]` → `partsel` | M1 / M2 |
| `{a, b, ...}` | `a ## b ## …`（Cat trait）；可嵌套 | M2 |
| `&a` / `|a` / `^a` | `a.andR` / `a.orR` / `a.xorR` → `Bool` | M2 |
| `a == b` / `a != b` | `VEq` trait → `===` / `=/=`（输出 `==` / `!=`） | M1 |
| `!a` / `~a` / `-a` | `not` / `not` / `neg` | M1 |

> 宽度语义：`+`/`-` 保持位宽（溢出截断），`*` 结果加宽，比较恒为 `Bool`，
> `##` 位宽相加 —— 与 typort HDL 完全一致（`docs/hdl-design.md`）。

## 3. 端口头约束（位置分组）

module 宏的 Verilog 臂按**连续段**匹配端口组：

1. 前导标量 `input NAME`（clk / reset / rst_n 额外折叠；其余为普通 Bool 输入）
2. `[dir] [hi:lo] p` 位宽端口（input/output/inout 皆可）
3. `output reg [hi:lo] q`（时序输出）
4. `output reg qb`（标量时序输出）
5. 其余标量端口 `[dir] pb`

标量输入写在前导段（顺序 1）或尾段（顺序 5）都可以，但**位宽端口必须在标量
输出之前**。同一个模块**一个时钟域**。折叠名固定为 `clk` / `reset` / `rst_n`。

## 4. 各里程碑内容

### M2（表达式与代码生成）

| 项 | 说明 |
|---|---|
| 部分选 `a[hi:lo]` | 解析器把 `[hi:lo]` 脱糖为 `slice[hi, lo]`（读写两侧） |
| 拼接 `{a, b}` | 新增 `{…}` atom → `##` 链；实参位置拒绝 `{`，避免吞掉 `impl … { }` / `for … { }` 的块 |
| 归约 `& | ^` | 前缀运算符 → `andR` / `orR` / `xorR` |
| `case/endcase` | 新增 VExpr 臂 + `CaseEq` 类型类（`default` 为恒真实例） |
| 纯组合模块多余 clk 端口 | 时钟端口仅在真正生成 clocked always 时发射 |
| `reg q = <init>` 去重 | 体内 `reg` 与同名 `output reg` 端口不再重复声明 |
| sized 字面量位宽 | 新增 `Expr::sizedLiteral(v, w)`；拼接里常量保留位宽 |

### M3（复位与时钟层次）

| 项 | 说明 |
|---|---|
| 折叠端口真实化 | `clk`/`reset`/`rst_n` 生成真实 Bool 端口，体内可引用；合成端口按名去重 |
| 手写复位分支 | `if (!rst_n) q <= 0; else q <= d;` 正常转写；复位沿由折叠极性（negedge/posedge）决定 |
| 带时钟子模块实例化 | 折叠端口可连，父模块用 `.clk(clk)` / `.rst_n(rst_n)` 连接 |
| 检查器豁免 | HDL002「declared but never read」跳过 cd 的时钟/复位名（否则每个模块都报） |

## 5. 已知限制（后续 / M4）

- `parameter` 头、`generate`、`initial`、延迟（`#`）、`$display` 等。
- 头部 `output reg [hi:lo] q = <init>` 形式：init 请写成模块体内的
  `reg [hi:lo] q = <init>;`（自动去重并进复位分支）。
- `input reg` / `input wire` 等带类型修饰的输入端口头。
- 实例化的空连接 `.port()`、位置连接（只有命名连接 `.p(sig)`）。
- `case` 转写为互斥 `if` 链（非原样 `case`），`default` 条件带 `1 && …` 前缀
  （语义等价，仅外观）。
- 多时钟域、`inout` 方向判定等以 typort 侧能力为准。

## 6. 验证入口

- 回归测试：`cargo test --lib verilog_compat_tests::`
  （`src/L13_namespace/verilog_compat_tests.rs`，M1+M2+M3 共 25 项）。
- 示例：
  - `examples/hdl/23-verilog-compat.typort`（M1 骨架）
  - `examples/hdl/24-verilog-practice.typort`（M2 表达式/控制流）
  - `examples/hdl/25-verilog-reset.typort`（M3 复位与时钟层次）
  经 `legacy_tests::test_examples_hdl_dir` 断言。
- 实现：`hdl-verilog-compat.typort`（VExpr 表 / CaseEq / 折叠）、
  `hdl-macros.typort`（module Verilog 臂）、`hdl-verilog.typort`（生成器）。
