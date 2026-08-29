# L02_tyck — 双向类型检查 + 闭包/de Bruijn 求值：参考实现与 `bump_spine_iter` 移植

elaboration-zoo L02（`typecheck-closures-debruijn`，规格见上游仓库同名层的
`Main.hs`）的 Rust
移植：表面语法（无 de Bruijn）→ 双向 elaboration（`check`/`infer` 走廊 +
beta-eta `conv`）→ 核心语法（de Bruijn 索引）→ `nf`/`type` 两种模式输出。
两个实现共用 parser、pretty、错误显示，**输出逐字节一致**（互检测试）：

- [`mod.rs`](mod.rs) — **参考实现**（L03 同款风格：`Box<Tm>` 项、Rc `List`
  环境、递归 eval/quote/conv）。
- [`bump_spine_iter.rs`](bump_spine_iter.rs) — **性能实现**：L01 调研冠军
  配方（`bump_spine_iter`，见 `L01_nbe/readme.md`）移植到带 Π/let 的核心机。
- `parser/` — 词法 + 语法（main.hs 的文法 + `withPos` 源位置包装）。
- `l02bench`（`cargo run --release --bin l02bench`）— 基准（独立 bin，
  `#[path]` 编译，不依赖其余各层）。

## 与 main.hs 的对应

| main.hs | Rust |
|---|---|
| `Raw`（含 `RSrcPos`） | `parser::Raw`（含 `SrcPos`，报错取最内层位置） |
| `eval`/`quote`/`conv`/`nf` | 参考版逐函数对应；性能版见下 |
| `Cxt{env,types,lvl,pos}` | 参考版同记录；性能版全 `Copy`、绑定量进 bump |
| `mainWith`（`--help`/`nf`/`type`） | `main_with(mode, src)` 返回本应打印的文本（测试断言用） |
| `displayError` | `display_error`（megaparsec 风格源码摘录 + caret；路径用 `(stdin)`） |
| `ex0`/`ex1`/`ex2` | `EX0_SRC`/`EX1_SRC`/`EX2_SRC` + 同名函数（ex0 按预期报错） |

## 怎么跑

```text
cargo test --lib L02_tyck                 # 19 个测试：三示例、报错路径、
                                          # 基础/性能互检、深度/稳态/conv 压力
cargo run --release --bin l02bench        # 基准：k=9..15，两负载族 × 三口径
./target/release/l02bench --max-k 21 --only fast,fast_ss   # 大 n 段
```

## 实测结果

机器：Windows x64，release（LTO + codegen-units=1 + mimalloc）。
负载：`church` = church 2^(k+1)（k 次 ×2 翻倍 let 链）的 **check + nf**；
`conv` = 同 church 数之上加 `Eq Nat (add big zero) big = refl Nat big` 的
**check**（beta-eta conv 在 check 内强制两侧完整展开后结构比较）。
口径：预热 1 次 + 5 轮取 min；`basic`/`fast`（每轮新建 Tycker）/`fast_ss`
（Machine + `Bump::reset` 跨轮复用）。

church（min ms / 相对 fast）：

| k | church n | basic | fast | fast_ss | basic/fast |
|---|---|---|---|---|---|
| 9 | 1024 | 0.76 | 0.074 | 0.077 | 10.3× |
| 11 | 4096 | 2.81 | 0.290 | 0.308 | 9.7× |
| 13 | 16384 | 11.5 | 1.11 | 1.33 | 10.4× |
| 15 | 65536 | 44.0 | 4.53 | 4.36 | 9.7× |
| 17 | 262144 | 187 | 19.1 | 19.4 | 9.8× |

conv（min ms / 相对 fast）：

| k | church n | basic | fast | fast_ss | basic/fast |
|---|---|---|---|---|---|
| 9 | 1024 | 2.51 | 0.138 | 0.145 | 18.2× |
| 13 | 16384 | 42.1 | 2.30 | 2.36 | 18.3× |
| 17 | 262144 | 704 | 36.4 | 34.3 | 19.3× |

- 两族负载下两版实现都严格线性（每翻倍 ×2）；`basic`/`fast` 的倍率在
  church ~10×、conv ~19×——conv 负载里 basic 的递归 conv + 深 `Val` 析构
  占比更高，bump/迭代的收益放大。
- **深度无上限**：`fast` 在 church 4194304（k=21）上 313 ms 跑通
  （eval 双栈、quote 任务栈、conv 工作表全迭代）；`basic` 的递归
  eval/quote/conv 受栈限（128 MB 栈 ≈ 26 万层）。
- **稳态复用（`fast_ss`）在 L02 负载上未复现 L01 的大幅收益**（两口径
  速度相当）：L01 的 `_ss` 收益来自 spine/vals 是仅有的两个大缓冲；
  L02 的 elaboration 里 bump 分配（闭包/env/Π 单元）占大头，spine/vals
  复用省的那部分不再显著。接口保留（长驻进程形态仍是对的），但别期待
  L01 式的 17%–3.3×。

### conv 位相等快速路径消融（`L02_NO_BITEQ=1`）

`conv` 的位相等快速路径（同一打包字 ⇒ 同一分配/同一立即数 ⇒ 判等）在
conv 负载上值 **2×**：k=13 关闭后 2.17 → 4.38 ms，k=15 关闭后
9.00 → 17.9 ms。church（nf）负载上中性（该负载几乎没有可剪枝的比较）。
注意：该路径必须只是**优化**而非正确性依赖——结构比较路径要能独立得出
同样的结论（`(3,3)`/`(0,0)` 的显式分支就是为此保留的，见下面的教训）。

## 优化过程中的三个教训

1. **值的共享性是带类型 elaborator 的一级效应**（L01 的纯 NBE 没有暴露）。
   参考版最初把中性应用写成 `VApp(Box<Val>, Box<Val>)`：eval 每次查变量
   都 `clone()` 环境条目，而 let 绑定的 church 数一类中性链会随 β-级联
   在环境里层层传递、反复引用——每次 clone 都是 O(链长) 深拷贝，church
   翻倍负载实测 **O(n²)**（church 4096 的 nf 单步 quote 983 ms）。改成
   `VApp(Rc<Val>, Rc<Val>)`（clone = 引用计数，Haskell 原版 GC 共享的
   对应物；L03 值表示同款）后回到 O(n)：同规模 10.5 ms，**94×**。这就是
   参考版与性能版只差 ~10× 而不是更大的原因——两者都线性后，差距只剩
   表示/分配策略的常数。
2. **不要忽略 unused 警告**：性能版 `Machine::quote` 的 `level` 参数一度
   没有传进 `quote_iter`（硬编码 0），编译器警告了但示例测试全绿——
   直到 `show_val` 在非零 `cxt.lvl` 下引用**含自由变量**的值（报错路径
   里 quote `expected/inferred` 类型）才爆发。位相等快速路径恰好把触发
   条件剪掉了（关掉它做消融时才暴露）。修复即把 level 透传。
3. **快速路径不能是正确性的唯一依托**：`conv` 的 `(3,3)`（U==U）与
   `(0,0)`（变量==变量）最初依赖位相等分支兜底，结构 match 里没有显式
   分支。做位相等消融时 `conv(U, U)` 直接判假。现在显式分支与位相等
   并存：前者保证语义自完备，后者只做加速（消融可测）。

## 性能版移植清单（L01 → L02）

| L01 机制 | L02 移植 |
|---|---|
| bump arena（`Bt`/`Env`/`Bv`） | `Tm`（多出 `Pi`/`Let`/`U`）+ `EnvCons`/`CloCell` 全 bump |
| 打包值 64 位（3 个 tag） | 3 位 tag：Lvl/Clo/Spine/**U（立即数）**/**Pi（单元）** |
| spine 栈（len/base 记账） | 同款；conv 的 eta 也会 push（只增不减，句柄稳定） |
| 流式右链 quote（ChainRun） | 同款逐字移植 |
| eval 双栈 + 右链快速路径 | 同款 + `LetBody`/`PiBody` 续跑任务（let 的类型槽不求值） |
| quote 任务栈 | 同款 + `Pi1`（Π 值先引定义域再引余定义域） |
| Machine 稳态复用 | 同款；`Tycker` owns `Bump`（每轮 `reset`）+ `Machine` |
| ——（L01 无 conv） | conv 改 (level, V, V) 工作表迭代 + 位相等快速路径 |
| ——（L01 无 elaboration） | check/infer 直接在打包值上工作（Cxt 全 Copy） |

## 已知限制

- 两版共用 `parser::parser(..) -> Option<Raw>`：解析失败只有 `parse
  error`，没有 main.hs megaparsec 的带位置报错（token 组合子不追踪
  失败位置；后续层 L13 有完整的诊断设施）。
- `basic` 的递归 eval/quote/conv 深度受线程栈限（church 52 万层需要
  ~256 MB 栈，`L02_STACK_MB` 可调；再深用全迭代的 `fast`）。
- `basic` 的基准口径对 nf 结果 `mem::forget`（深 Box 树的递归析构会爆
  栈；bench 进程一次性，退出即回收——L01 readme「已知限制」同款）。
- 性能版的错误消息路径（`show_val`）会 quote + export 回参考版的
  `Box` 树再走共享的 pretty——只在报错时发生，不在热路径上。
