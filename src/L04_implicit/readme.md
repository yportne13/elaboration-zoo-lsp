# L04_implicit — 隐式参数：参考实现与 `bump_spine_iter` 移植

elaboration zoo 上游 `04-implicit-args` 的 Rust 移植：在 L03（holes + pattern
unification）之上加**隐式参数**（`Icit` 穿线、隐式插入、命名隐式）。

与 L03 同构的双实现：

- `mod.rs`：参考实现（与上游一一对应：`Box<Tm>` 项、`List` Rc 持久环境、
  递归 eval/quote/force/unify/rename）；
- `bump_spine_iter.rs`：极致性能版（L03 冠军配方的移植 + icit/插入机制），
  两版输出**逐字节一致**（互检测试 + `tests/l04_blackbox.rs` 双 oracle）。

## 与上游 Main.hs 的对应

- 语义与 `04-implicit-args` 各模块逐函数对应（已逐字核对 Common /
  Evaluation / Elaboration / Unification / Pretty）；两处历史 `TODO: may be
  wrong` 均与上游同款：`BD` 不带 icit（`vAppBDs` 硬编码 `Expl`）、solve 的
  `lams` 取 meta spine 的 icit（`reverse $ map snd sp`，β 应用不看 icit，
  仅影响解的显示）。
- 错误措辞按上游 Errors.hs：`Name not in scope: x`、
  `Cannot unify expected type…`、`No named implicit argument with name …`、
  `Cannot infer type for lambda with named argument`、`Function icitness
  mismatch: expected %s, got %s.`（implicit/explicit）。

## 与 L03 的语义差别

1. **Icit 穿线**：`Lam`/`App`/`Pi`（表面与核心语法）、spine 实参都带
   icit。β 应用不看 icit；unify 里 **Π 比较要求 icit 相等**、spine 实参
   比较忽略 icit（类型已定，上游 Unification.hs 的注释同款）。
2. **隐式插入**：infer 出的项在显式应用（infer App 的 Expl 分支）与检查
   （check 的 general 回落）前自动补 `?m` 实参（`insert`/`insert_t`）；
   隐式 λ（`\{A} x. …`）本身免插。infer λ 的体推断后在**扩展后**的上下文
   里 insert（上游 `insert cxt'`）。
3. **命名隐式**：`t {x = u}` 实参按 Pi binder 名定位插入（`insert_un-
   til_name`，找不到报 `No named implicit argument`）；`\{x = y}` lambda
   binder 按名匹配隐式 Π（`y` 是体内可见的本地名，`x` 是引用名）。
4. **inserted binder**：检查非 λ 项到隐式 Π 时补的 binder 对源码名字
   **不可见**（`NameOrigin`/`TCons::source`——性能版不入 name_map，等价于
   参考版线性扫描跳过 `Inserted`）。
5. **`{u}` 位置隐式实参**应用到显式 Pi 头 → `Function icitness mismatch`
   （反方向在 check 侧被插 binder 捕获，不产生该错误）。
6. **Pi 合成**：非 Π 头应用挂一对洞（定义域 + 余定义域，合成 binder 名
   `"x"`、不进名字表）并与头类型合一；unify_catch 参数序 `(tty, 合成Π)`
   同上游。

## 怎么跑

```text
cargo test --lib L04_implicit          # 参考版 + 性能版内嵌测试（含互检）
cargo test --test l04_blackbox         # 黑盒双 oracle 套件
cargo run --release --bin l04bench -- --workload implicit
cargo run --release --bin l04bench -- --workload all --max-k 15
```

消融开关（只影响性能，不影响输出）：`L04_NO_CONV_MEMO=1`（unify 判等记忆
化）、`L04_NO_NAME_MAP=1`（名字解析回落线性 walk）。

## 性能版要点（相对 L03 的增量）

1. **icit 的搬运点**（全部机械穿线）：
   - bump 项 `Tm::{Lam, App, Pi}` 与 `CloCell`/`PiCell`/spine 槽 `Entry`
     （quote 的 `f {a}`、solve 的 lams、rename 的 App 重建都从槽位取）；
   - eval 右链下降把 Var 头应用的 icit 压**侧栈**（`ChainWrap` 折叠时成对
     消费；`Vec::new()` 起步，无右链路径零分配）；
   - rename 的账户模型：**只有 `spine_case` 预装载** `done_icits`（按实参
     完成序），Ren 的直接情形与组合器（Lam1/Pi2）不碰它——合并结果压
     `done` 时不带 icit，配对只发生在 `SpineFold` 弹出时（LIFO 对齐）。
2. **name_map 策略**：inserted binder 不入表、不留轨迹、`mark` 不动——
   对源码名的遮蔽语义与参考版一致（源码 binder 才 push trail）。
3. **unify 长度 fail-fast 已移除**（与 L03 的差异！）：`push` 的 len 延展
   启发式（实参是 spine 句柄 ⇒ 链延长）无法区分「实参是本链的 partial
   （ChainWrap 惯例）」与「实参恰好是另一个中性应用」——`B (?m …)` 这类
   **中性头应用到中性实参**的形态（隐式插入大量制造）会让 len 虚增，
   fail-fast 在两链真实应用数相同时误判不等（comp 用例实测回归；L03 的
   负载未触达该形态，属 L03 潜伏缺陷——本层不带走）。真实长度失配由内联
   环兜底（partial-头 对 经工作表派发后必败，结论不变）。
4. **quote/unify 记忆化、复合环境、稳态复用、迭代内核**全部继承 L03，
   icits 不进记忆化键（随 `V` 指向的单元/槽位携带，同一 `V` 同 level 的
   quote 产出唯一）。

## 实测结果（Windows 10，release build，rounds=3 取 min）

```text
== workload: church ==
k=11  n=4096    fast=0.262ms*  basic=2.982ms      (≈11×)
== workload: solve ==
k=11  n=4096    fast_ss=0.546ms / fast=0.525ms*
== workload: implicit ==
k=9   n=1024    fast_ss=8.877ms*
k=10  n=2048    fast_ss=33.151ms*
k=11  n=4096    fast_ss=126.597ms*
```

implicit 负载（n 层 `p_i = id p_{i-1}`，每层一次插入 + 一次求解）呈二次方
增长：每层 fresh meta 捕获的 bds 持久链沿 Defined 槽位逐一走过（
`vAppBDs` 只应用 Bound 槽，但**遍历**整条链）——参考版同款（两边同
复杂度，常数差即真实差距）。根治方向（未做）：平坦 def 区域的 bds 跳段
（Bound 槽都在 binder 链段、Defined 槽都在平坦段，可 O(1) 定位下一 Bound）。

## 已知限制

- check/infer 与 parser 在 let 链上仍是递归（L03 同款），深度负载需要深
  栈（l04bench 默认 128MB 线程；`L04_STACK_MB` 可调）。
- 参考版的深层 Box 项析构会爆栈，bench 里 `mem::forget`（L03 同款处理）。