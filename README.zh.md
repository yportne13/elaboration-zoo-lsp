# Elaboration Zoo Lsp

一个拥有 LSP 服务器的依赖类型语言，内置 HDL（硬件描述语言）支持，可生成 Verilog 代码。

## 特性

### 语言核心
- **依赖类型**：全谱依赖类型，支持累积宇宙（`Type 0`, `Type 1`, …）
- **归纳族**：`enum` 支持索引和参数（类似 Agda/GADTs）
- **结构化记录**：`struct` 带命名字段
- **模式匹配**：支持依赖模式匹配和荒谬模式（absurd patterns）
- **隐式参数**：`[param: Type]` 语法配合实例推导
- **类型类 / Trait**：`trait` / `impl`，实例合成，`where` 子句
- **宏系统**：`macro_rules` 支持语法片段匹配（`ident`、`raw`、`params`）
- **可变全局变量**：`create_global` / `change_mutable` / `get_global`

### 定理证明
- 归纳类型 `Eq`，支持 `refl`、`cong`、`trans`、`symm`、`subst`
- 内置引理：`add_zero_right`、`add_comm`、`add_assoc`、`mul_one_right`
- 基于类型类的求解器，支持关联类型和超 trait

### HDL（硬件描述语言）

| 特性 | 示例 | 说明 |
|------|------|------|
| UInt / SInt / Bits | `let a = UInt[8]` | 无符号、有符号、位向量类型 |
| Bool 信号 | `let cond = Bool` | 布尔线网类型 |
| 算术运算 | `sum := a + b` | `+`, `-`, `*`, `+^`（进位） |
| 位运算 | `x := a & b` | `&`, `|`, `^`, `~` |
| 比较器 | `lt := a < b` | `<`, `<=`, `>`, `>=`, `===`, `=/=` |
| 布尔逻辑 | `r := a && b` | `&&`, `||`, `!`, `^` |
| 单比特提取 | `b := a.apply[7]` | 也支持 `a[N]` 方括号语法 |
| 范围切片 | `low := a.slice[3, 0]` | 提取 `(hi-lo+1)` 位 |
| 左值位选 | `t[0] := x` | 赋值到特定位 |
| 多路选择器 | `r := cond.mux(a, b)` | 条件多路复用 |
| 位拼接 | `f := e ## d` | 位拼接 |
| 寄存器 | `reg a = UInt[8]` | 带时钟/复位的时序元件 |
| 子模块 | `mkInstance("u", "Adder")` | 模块例化 |
| Bundle | `#[derive(Bundle)]` | SpinalHDL 风格批量赋值 |

HDL 代码写在 `module` 块中，编译输出 Verilog：

```typort
module adder[w: Nat] {
    input a = UInt[w]
    input b = UInt[w]
    output sum = UInt[w + 1]
    sum := a +^ b
}

println(moduleTreeVL(adder[8]))
```

### LSP 语言服务器
- **跳转到定义** – 导航到声明
- **悬停信息** – 类型和文档展示
- **自动补全** – 字段和方法建议
- **语义令牌** – 语法高亮
- **内联提示** – 推断的类型标注
- **诊断信息** – 内联错误报告
- **代码操作** – 快速修复
- **重命名** – 跨文件符号重命名
- **查找引用** – 查找所有引用

## 快速开始

```bash
# 构建
cargo build --release

# 运行 .typort 文件
cargo run --release --bin typort -- examples/hdl_ops.typort

# 启动 LSP 服务器
cargo run --release --bin typort -- lsp

# 内存基准测试（需要 mem-profile 特性）
cargo run --release --features mem-profile --bin typort -- --stats
```

### VS Code 扩展

仓库中的 `vscode/` 目录包含 VS Code 扩展，提供语法高亮和 LSP 集成支持。

## 示例

| 文件 | 主题 |
|------|------|
| `examples/theorem_proving.typort` | Eq、trans、symm、cong、add_comm、add_assoc |
| `examples/typeclass_complex.typort` | Traits、instances、outParam |
| `examples/alu.typort` | HDL 模块、UInt 算术、Into trait |
| `examples/hdl_ops.typort` | apply、slice、布尔运算、子模块、左值位选 |

## 架构

项目结构为 **elaboration zoo** —— 每个模块（`L01_*` … `L13_*`）增量添加一个语言特性：

| 模块 | 特性 |
|------|------|
| `L01_eval` | 求值（NBE） |
| `L02_tyck` | 类型检查基础 |
| `L03_holes` | 元变量（holes） |
| `L04_implicit` | 隐式参数推导 |
| `L05_pruning` | 剪枝（occurs check） |
| `L06_string` | 字符串字面量 |
| `L07_sum_type` | 和类型（枚举） |
| `L07a_depend_pm` | 依赖模式匹配 |
| `L08_product_type` | 积类型（结构体） |
| `L09_mltt` | MLTT 风格宇宙 |
| `L10_typeclass` | 类型类 / Trait 系统 |
| `L11_macro` | 宏系统 |
| `L12_canonical` | 规范形式（类型类求解） |
| `L13_namespace` | 命名空间 / 包系统、HDL Verilog 代码生成 |

## 基准测试

```bash
# 预加载后的内存统计
cargo run --release --features mem-profile --bin typort -- --stats

# 深度 dhat 堆分析（约 3 分钟）
cargo run --release --features dhat-heap --bin typort -- --stats
```

### 关键指标

| 指标 | 说明 |
|------|------|
| `peak_working_set_mb` | 峰值物理内存（Windows） |
| `meta_entries.unsolved` | 未求解的元变量数量 |
| `timings.total_secs` | 总加载时间 |
| dhat 峰值阶段 | 按调用栈的分配分解 |

## 灵感来源

[elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo) ·
[ShiTT2](https://github.com/KonjacSource/ShiTT2) ·
[PM](https://gist.github.com/Guest0x0/844688233e1ea27b0a2307734271644d) ·
[tabled-typeclass-resolution](https://github.com/purefunctor/tabled-typeclass-resolution) ·
[rust-nbe-for-mltt](https://github.com/brendanzab/rust-nbe-for-mltt) ·
[Canonical-min](https://github.com/chasenorman/Canonical-min) ·
[aya](https://github.com/aya-prover/aya-dev) ·
[lean4](https://github.com/leanprover/lean4) ·
[miniagda](https://github.com/andreasabel/miniagda) ·
[rust-analyzer](https://github.com/rust-lang/rust-analyzer) ·
[tower-lsp](https://github.com/ebkalderon/tower-lsp) ·
[resilient-ll-parsing](https://github.com/matklad/resilient-ll-parsing) ·
[chumsky](https://github.com/zesterer/chumsky)
