# Review 2026-10-11 — 轮次 8:HDL→Verilog 语义

> 主题:**emit 管线把 module 树翻译成 Verilog 的语义保真度**。
> 30 个探针(`tools/review-1011/r08-hdl/`),每个一个 module,经
> `typort emit --top <M>` 对生成的 Verilog 文本断言。**终局:30/30 PASS**。
> 驱动新增 `mode: emit -- --top X` 支持(stdout 分支按原始 Verilog 匹配)。

## 1. 实验覆盖

算术 5(+ - * +^ 位宽扩展 & | ^)、移位/切片 4(|<< 常量/变量、slice[3,0]、
位选、## 拼接 {a, b})、比较/mux 3(<、.mux、? : 脱糖)、寄存器 4(reg、
init 0 异步复位、regNext、output reg)、counter/mem 3(willOverflow 的
(~cnt == 0)、同步写 always @(posedge clk)、readAsync 组合读)、
cast 3(asBits、SInt expand 符号扩展 {s[3], s}、常量折叠)、层级/方向 5
(子模块 Half8 u0 ()、input/output 端口方向)、错误面 6(位宽不混合、
未驱动输出、Bool 逻辑、===、FSM、反向驱动)。

## 2. 语义事实(全部经实测确证)
- **裸数字字面量是 Nat,不是 UInt**:`a +^ 1`、`a |<< 2` 都报
  can't unify(expected UInt find Nat)——HDL 域必须用信号或 `literal(n)`;
  与 language-spec 的 UInt 字面量约定一致,但极易踩。
- `+^` 结果位宽 = max+1(`wire [8:0] s`);`*` 结果 = 宽度和。
- 拼接 `##` → `{a, b}`;slice → `a[3:0]`;位选 → `a[0]`。
- `.mux` 与 `? :` 都生成 `(c ? a : b)`(脱糖到同一形态)。
- reg init 0 生成 `always @(posedge clk or posedge reset)`(**posedge**
  reset,不是 negedge)+ if (reset) 块。
- memUInt write → `always @(posedge clk)`;readAsync → 组合 assign。
- `===` 源语法接受,生成 `(a == b)`(Verilog 层无 === 需求)。
- SInt expand → `{s[3], s}` 符号扩展。
- 子模块实例生成 `Half8 u0 ();`(空端口列表——连接机制另查,记遗留)。
- `module  ()` 空名模块在 h23 的输出尾部出现(第二 module 的树打印,
  quirk,不影响语义)。

## 3. 判定的错误面
- **UInt[8] + UInt[4] 不自动扩宽** → unsolved meta 错误(需显式 expand)。
- 未驱动 output:检查通过(生成裸 output 声明)。
- 反向驱动 input(`a := b`):报错。

## 4. 验证与遗留
- 轮内 30/30(RESULTS.md);门禁见 commit。
- 遗留:`mkInstance` 端口连接(本探针只测了声明)(P3);
- `module  ()` 空名打印 quirk(P4);
- "moduleTreeVL" 的 note 在 emit 的 stderr 出现两次(错误路径计数)——
  与错误信息重复有关,记 P4。
