//! `typort quick` — dense language cheat-sheet for engineers who already know
//! Verilog + SpinalHDL + Lean (or an AI assistant that needs to bootstrap
//! quickly). Not a tutorial: every line assumes you know what a dependent
//! type, an implicits-passing function, or a `:=` connection is.
//!
//!   typort quick           # print the whole reference (good for LLM context)
//!   typort quick <topic>   # print one section, e.g. `typort quick hdl`
//!   typort quick --list    # list section keys

use colored::Colorize;

struct Section {
    key: &'static str,
    title: &'static str,
    body: &'static str,
}

macro_rules! section {
    ($key:expr, $title:expr, $body:expr $(,)?) => {
        Section { key: $key, title: $title, body: $body }
    };
}

const SECTIONS: &[Section] = &[
    section!(
        "overview",
        "概览 · Overview（你在 Verilog/SpinalHDL/Lean 里的对应物）",
        r#"TyportHDL = Lean 风格的依赖类型核心 + SpinalHDL 风格的硬件建模。

  语言: 值 · 类型 · 函数 (依赖类型, 无 GADT)
  HDL : module 宏声明电路，生成 Verilog
  证明: Eq/类型即命题，可写定理与正确性证明

  Lean 工程师: 核心就是 MLTT —— def / enum / match / trait(≈typeclass) / Vec[A](n)。
  SpinalHDL 工程师: 硬件侧是 `module { input/output/let/reg ... := }`，
   层次/位选/寄存器/Stream/时钟域都是 SpinalHDL 词汇。
  Verilog 工程师: 你关心的端口、assign、always、例化、拼接都有，见 `hdl` / `hdlsig`。

工具链:
  typort check <file.typort>   # 类型检查（等价于编译）
  typort lsp                   # LSP server (VS Code 扩展)
  typort emit <files> --top 'adder[8]' [--out DIR]   # 落盘 Verilog
  typort build / test          # Typort.toml 工程: 生成 + 仿真 (verilator/icarus/vcs/vivado)
  typort tutorial              # 逐步教学（适合从头学）
  typort quick <topic>         # 本速查表单节
"#
    ),
    section!(
        "def",
        "定义与函数 · def（Lean `def` / Scala 函数）",
        r#"顶层定义:  def 名: 类型 = 表达式
带参函数:  def f(x: Nat): Nat = x + 1
   调用:  f 3  或  f(3)        # 空格应用与括号等价

   def triple(n: Nat): Nat = n * 3
   triple 14                  # => 42

多语句函数体用 let ...; 串联:
   def describe(n: Nat): String =
       let m = n + 1;
       "succ(" + m + ")"
        # 最后一个表达式即返回值

lambda:  x => 表达式
   map_opt(Some 1, x => x + 2)          # Some 3

按模式定义（多分支）:
   def neg(b: Boolean): Boolean =
       match b {
           case true => false
           case false => true
       }
"#
    ),
    section!(
        "types",
        "内置类型 · Types",
        r#"Nat     — 皮亚诺自然数。零 = zero，后继 = succ(n)；整数字面量是语法糖
          `3` ≡ succ(succ(succ(zero)))。字面量可用于 Nat/HDL 宽度等。
Boolean — true / false（归纳类型，运行时真值）
String  — "..."，+ 拼接
Option[A] / Result[A,B] / List[A] / Either[A,B] / Vec[A](n) — prelude 提供
UInt[n] / SInt[n] / Bits[n] / Bool — HDL 数据类（见 `hdl` 节）
注意: 核心 Boolean（枚举 true/false）与 HDL Bool（1-bit 信号）是两种类型，
     用 Into 互转（`impl Into[Bool] for Boolean`）。

类型别名/推导:  top-level `def x = expr` 可省略类型注解。

一切都是表达式，类型检查在 compile-time；运行时只有求值。
"#
    ),
    section!(
        "match",
        "模式匹配 · match（Lean match / Scala pattern match）",
        r#"match 值 { case 构造子模式 => 表达式 }
构造子模式可绑定字段: succ(m) 绑定 m；_ 忽略；leaf(v) 绑定 v。

   def my_pred(n: Nat): Nat =
       match n {
           case zero    => zero
           case succ(m) => m
       }

   enum Tree[T] { leaf(v: T); node(l: Tree[T], r: Tree[T]) }
   def depth[T](t: Tree[T]): Nat =
       match t {
           case leaf(_) => 0
           case node(l, r) =>
               let dl = depth(l);
               let dr = depth(r);
               match nat_compare(dl, dr) {
                   case lt => dr + 1
                   case eq => dl + 1
                   case gt => dl + 1
               }
       }

漏写分支 = 类型错误。枚举构造子裸名在 prelude 自动别名（zero、Some...）。
"#
    ),
    section!(
        "adt",
        "枚举与结构体 · enum & struct（Lean inductive / Scala case class）",
        r#"enum = 求和类型（每个 case 一个构造子）:
   enum Color { red; green; blue }
   构造: Color.red（裸名 red 也自动可用）

   enum Maybe[T] { nothing; just(v: T) }

struct = 积类型（命名的元组，字段方法访问）:
   struct Point {
       x: Nat
       y: Nat
   }
   构造: new Point(1, 2)；访问: p.x / p.y
   struct 可带隐式类型参数: struct Pair[A, B] { first: A; second: B }

枚举构造子可带字段（看起来像 product 变体）:
   enum Tree[T] { leaf(v: T); node(left: Tree[T], right: Tree[T]) }
   leaf(1) / node(leaf(1), leaf(2))
"#
    ),
    section!(
        "poly",
        "多态与隐式参数 · Polymorphism & implicit args",
        r#"方括号 [..] 声明隐式（编译期）参数；调用时自动推导或显式给出:
   def ident[A](x: A): A = x
   ident true      # A := Boolean
   ident[Nat] 7    # 显式填 A = Nat

多个隐式参数块/约束:
   def t[T][s: Pretty[T]](x: T): String = s.pretty x      # 隐式传实例
   def print_it[T](x: T): String where T: Pretty = _pretty_T.pretty x
        # where 子句是 typeclass 约束语法糖（自动注入 `_<trait>_T` 实例名）

依赖类型函数（类型参数可出现在返回类型里）:
   def zeros[n: Nat]: Vec[Nat] n = ...     # 返回类型依赖值参数 n
   zeros[2]                                # 显式填 n
"#
    ),
    section!(
        "tc",
        "类型类 · trait / impl（Lean typeclass / Haskell class）",
        r#"trait 声明接口，impl 提供实例；运算符 `+ * ==` 等经实例派发。
注意 prelude 已定义 Show/Add/Mul/Into/Equal/Compare 等，自定义用新名（如 Pretty）。

   trait Pretty { def pretty: String }
   impl Pretty for Bool {
       def pretty: String = match this { case true => "true"; case false => "false" }
   }
   impl[T] Pretty for Option[T] { def pretty: String = "some|none" }

运算符重载（this 是左操作数）:
   impl Add[Wrap, Wrap] for Wrap {
       def +(that: Wrap): Wrap =
           match this {
               case wrap(a) =>
                   match that {
                       case wrap(b) => wrap(a + b)
                   }
           }
   }
   wrap(40) + wrap(2)          # => wrap 42

类型约束:  `def f[T](x: T): R where T: Pretty`（或隐式 `[p: Pretty[T]]` 后 `p.pretty x`）。
prelude 自带: Add / Mul / Sub / Equal / Compare / Into（Nat→UInt 自动转换）等。
"#
    ),
    section!(
        "dep",
        "依赖类型 · Dependent types（Vec 例子）",
        r#"类型可携带数据; 索引类型在返回类型/模式里被精确追踪。

   enum Vec[A](len: Nat) {
       nil -> Vec[A] 0
       cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (l + 1)
   }

   def zeros[n: Nat]: Vec[Nat] n =
       match n {
           case zero    => nil
           case succ(m) => cons(0, zeros[m])
       }

   def vecmap[T, U, len: Nat](x: Vec[T] len, f: T -> U): Vec[U] len = ...

类型里带长度 → 编译期防越界/防错位。这层类型检查在 elaborate 时完成，
生成 Verilog 时长度信息已被消去（不影响面积/时序）。
"#
    ),
    section!(
        "proof",
        "等式与证明 · Eq & proofs（Lean 风格）",
        r#"Eq a b 是「a = b」的类型; 构造它的项即证明。
  rfl            自反性: 两边可定义归约到同一值即成立（≈ refl）
  trans / symm / cong / subst   组合引理
  calc { ... by ... }           链式推理

   def two_plus_three: Eq (2 + 3) 5 = rfl        # 2+3 归约到 5

   def zero_add_comm(n: Nat): Eq (0 + n) (n + 0) =
       trans (add_zero_left n) (symm (add_zero_right n))

   calc {
       0 + n = n      by add_zero_left n
       n     = n + 0  by symm (add_zero_right n)
   }

prelude 引理: add_zero_left/right, add_comm, add_assoc, cong_succ...
可给 HDL 模块写正确性证明（例: examples/adder_proof.typort;
succ_injective 等自证例子见 examples/theorem_proving.typort）。
"#
    ),
    section!(
        "hdl",
        "HDL 模块与端口 · module（SpinalHDL Component / Verilog module）",
        r#"module 宏声明电路; 端口 = input/output，内部 = let（wire）/ reg（寄存器）。

   module half_adder {
       input  a = Bool
       input  b = Bool
       output sum   = Bool
       output carry = Bool
       sum   := a ^ b
       carry := a && b
   }

数据类: UInt[w]（无符号）/ SInt[w]（有符号）/ Bits[w] / Bool（宽度 = w / 1）。
类型即宽度: UInt[8] = 8 位。

生成 Verilog（在 .typort 文件里）:
   println(moduleTreeVL(half_adder.create.tree))     # 单模块
   println(allModulesVL(buildMultiTree()))           # 多模块树
命令行落盘: typort emit foo.typort --top 'adder[8]' --out out/   # 含 manifest.json

参数化模块（隐式参数 = 编译期参数，SpinalHDL Generic）:
   module myAdder[w: Nat]
       input a = UInt[w]
       input b = UInt[w]
       output sum = UInt[w]
   { sum := a + b }
   例化: let u = myAdder.create[8]        # w := 8

层次化连接（SpinalHDL 风格，u.port 是带类型句柄）:
   module top {
       input a = UInt[8]; input b = UInt[8]; output sum = UInt[8]
       let u = myAdder.create[8]
       u.a := a; u.b := b                 # 输入端口 <- 父信号
       sum := u.sum                       # 输出端口 -> 父信号
   }
"#
    ),
    section!(
        "hdlsig",
        "信号 · 寄存器 · 控制流 · 位操作",
        r#"寄存器（自动加 clk/reset 端口）:
   reg r = UInt[8]              # 普通寄存，自动 clk
   reg r = UInt[8] init 42      # 异步复位初值 42，自动加 reset
   let d = regNext(a)           # 延迟一拍 (SpinalHDL regNext)
   let d = regNextWhen(a, en)   # 条件延迟

驱动:  :=  是连接符（组合或时序均可）。
   r := a + 1

控制流（SpinalHDL when/switch）:
   when sel { out := a } otherwise { out := b }
   when sel === 0 { out := a } elsewhen sel === 1 { out := b } otherwise { out := c }
   switch sel { is 0 { result := a } is 1 { result := b } default { result := c } }

算术（宽度语义精确）:
   +  -      保持位宽, 溢出截断       a +^ b  结果宽 +1（进位）;  -^ 借位
   *         UInt[w1]*UInt[w2] -> UInt[w1+w2]（不丢精度）
   Nat 字面量自动转换: a + 42 / a * 3（via Into）
   a.neg     SInt 取负

比较:  < <= > >=（两侧位宽一致）;  相等/不等是 === / =/=  （结果 Bool）
位运算:  & | ^ ~（按位）;  << >>（编译期 Nat 常量移位）
         a.andR / a.orR / a.xorR  归约 -> Bool

位提取/切片/拼接:
   a[7]           单 bit -> Bool（= a.apply[7]）
   a.slice[7, 4]  范围 -> 宽度 4
   t[0] := x      LHS 位选赋值
   a ## b         拼接, 结果宽 = 左宽 + 右宽（含 Bool）
"#
    ),
    section!(
        "hdlutil",
        "实用构件 · counter / mux / Stream / 时钟域（SpinalHDL lib 移植）",
        r#"组合选择: cond.mux(a, b)（cond ? a : b，SpinalHDL 风格）; C 三目 cond ? a : b 也是语法糖
计数器:   counter(8) → 每周期 +1;  counterInc(8, en) → 使能计数
          cnt.value / cnt.willOverflow（全 1 回绕组合信号）
自动命名: autoUInt(8) / autoUIntInput(8) / autoUIntOutput(8) / autoBool
          / autoUIntReg(8) / autoUIntRegInit(8, 5) — 信号名 = let 绑定名

Stream / Flow / Fragment（SpinalHDL lib 移植, prelude 提供）:
   Stream.mk(valid, ready, payload)
   streamM2sPipe / streamS2mPipe / streamHalfPipe
   streamThrowWhen / streamHaltWhen
   streamFifoConnect / streamFifoCC / streamMux / streamDemux / streamFork
   Fragment（last 信号）;  CcByToggleIO.mk / BufferCC / bufferCCUIntCd

时钟域（多时钟 / 跨时钟）:
   def inCd: ClockDomain = ClockDomain.mk "clkA" "rstA" Async RisingEdge ActiveHigh
   module ccPulse[inCd] { ... }              # 模块级时钟域参数
   pulseCCByToggle / ccByToggle / bufferCCUIntCd / streamFifoCC[8][4]

仿真/波形: Typort.toml [test] 段配置 simulator + trace;
   typort test 编译模型并跑 smoke eval（见 examples/hdl、src/sim/）。
"#
    ),
    section!(
        "tools",
        "工作流 · Workflow",
        r#"一个文件即一个程序; top-level `println(...)` 求值并打印。

检查/跑通:
   typort check examples/hdl_ops.typort          # 0 错即通过
   typort check examples/hdl/09-hierarchy.typort

从 .typort 到 Verilog:
   typort emit examples/hdl/01-basics.typort --top 'basicDecls[8]' --out out/
   # 产物: out/basicDecls.v + out/manifest.json（端口/宽度/方向/时钟域）

工程化（Typort.toml）:
   [project] name / top ;  [test] simulator = "verilator" | "icarus" | ...
   typort build   # emit + filelist(.f) 到 target/
   typort test    # 编译仿真模型 + smoke eval（缺仿真器自动跳过）

编辑器: VS Code 扩展（语法高亮 + LSP）;  hover 看类型 / 跳转定义。

示例库 examples/:
   hdl_ops.typort 位选/切片/布尔/子模块
   alu.typort     UInt 算术 + Into
   hdl/07-registers.typort 寄存器;  hdl/08-control-flow.typort when/switch + for 编译期展开
   hdl/09-hierarchy.typort 层次例化;  hdl/19-stream.typort Stream 全家族
   theorem_proving.typort 证明;  adder_proof.typort 硬件正确性证明
"#
    ),
];

pub struct QuickOptions {
    pub topic: Option<String>,
    pub list: bool,
}

fn print_section(sec: &Section) {
    println!("\n{}", format!("══ {} § {} ══", sec.key, sec.title).bold().cyan());
    println!("{}", sec.body.trim_end());
}

pub fn run(opts: QuickOptions) -> Result<(), Box<dyn std::error::Error + Sync + Send>> {
    if opts.list {
        println!("{}", "typort quick —— 速查主题：".bold());
        for sec in SECTIONS {
            println!("  {:<10} {}", sec.key, sec.title.split('·').next().unwrap_or(""));
        }
        println!("\n用法: typort quick <key>   或   typort quick（全部）");
        return Ok(());
    }

    match opts.topic {
        None => {
            println!(
                "{}",
                "═══ Typort 速查表（为熟悉 Verilog + SpinalHDL + Lean 者准备）═══".bold()
            );
            for sec in SECTIONS {
                print_section(sec);
            }
            println!("\n单节查询: typort quick <key>   ·   全部主题: typort quick --list");
        }
        Some(query) => {
            let q = query.to_ascii_lowercase();
            // Match in priority order: exact key -> key prefix -> title.
            let exact: Vec<&Section> =
                SECTIONS.iter().filter(|s| s.key == q).collect();
            let prefix: Vec<&Section> =
                SECTIONS.iter().filter(|s| s.key.starts_with(&q)).collect();
            let by_title: Vec<&Section> = SECTIONS
                .iter()
                .filter(|s| s.title.to_ascii_lowercase().contains(&q))
                .collect();

            let matches = if !exact.is_empty() {
                exact
            } else if !prefix.is_empty() {
                prefix
            } else if !by_title.is_empty() {
                by_title
            } else {
                Vec::new()
            };

            if matches.is_empty() {
                eprintln!(
                    "{}",
                    format!("没有找到与 `{query}` 匹配的主题。").yellow()
                );
                eprintln!("可用主题: {}", SECTIONS.iter().map(|s| s.key).collect::<Vec<_>>().join("  "));
                eprintln!("或运行 typort quick --list");
            } else {
                for sec in matches {
                    print_section(sec);
                }
            }
        }
    }
    Ok(())
}
