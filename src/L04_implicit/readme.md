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
3. **unify 长度 fail-fast 已移除，(2,2) 同头臂改为受控内联环**
   （2026-09-02 修订，L02/L03 现已同步跟进）：fail-fast 的两条独立误杀
   机制——① `push` 的 len 延展启发式（实参是 spine 句柄 ⇒ 链延长）无法
   区分「实参是本链的 partial（ChainWrap 惯例）」与「实参恰好是另一个中性
   应用」，`B (?m …)` 这类**中性头应用到中性实参**的形态（隐式插入大量
   制造）让 len 虚增，短侧含未解 meta 时（`B z` vs `B (?m a b)` 可解）误判
   不等（comp 用例实测）；② η 吸收：链 base 的 `a` 是闭包时应用可被收进
   λ 体（`P (h y)` vs `P (\x. h y x)`，L02 黑盒实测）。此外无门控的 `.a`
   下钻对**带求解副作用的 unify** 不健全：「实参恰是另一条中性链」跳过内层
   头分派逐层 pairwise 误比会产出错误解——本层与 L03/L05 统一为**受控内联
   环**：仅在纯 ChainWrap 同头延续处（实参链顶层 `f` 与本层 `f` 同字）下钻，
   否则停钻把子对交回完整分派；派发序与参考版 `unify_sp` 同序（先 tail＝
   最先应用的实参）。church 链零往返保留。黑盒
   `unify_eta_absorption_and_meta_shorter_side` 钉住两类形态。
4. **quote/unify 记忆化、复合环境、稳态复用、迭代内核**全部继承 L03，
   icits 不进记忆化键（随 `V` 指向的单元/槽位携带，同一 `V` 同 level 的
   quote 产出唯一）。
5. **AppBds 跳段**：`BdCons` 入链时维护「向外连续 `bound: false` 槽数」
   （`false_run`）与该 run 的落点（`after_run`）；AppBds 在 binds 耗尽后
   整段 O(1) 跳过——define 槽只递减 `flat_len`、从不产生实参，跳过与逐步
   走**逐字节等价**（implicit 负载整条链全 false：注入评估 O(层深) → O(1)）。
6. **solve 的换代缓冲**（`RenBuf`）：偏置换按 level 存 `val`、`stamp` 记
   生效代数，`reset` 只推进 epoch——`vec![None; γ]` 的 O(γ) 清零与逐次
   分配降为 O(1)（implicit 负载 γ = 层深，二次项之二）。
7. **热路径草稿常驻化**：`icits` 侧栈与 unify 的判等记忆化/实参收集草稿
   （`ConvScratch`）从每次调用的 `Vec::new()` 提升为 `Machine` 字段——
   进核前 clear 保容量，跨调用零分配（`W`/`QJob`/`UItem` 借 bump 生命
   周期，仍按调用新建）。
8. **fresh meta 免 eval 快捷路径**（`eval_fresh`）：bds 全为 define 槽
   （或空）时 AppBds 走空转、结果恒为裸 meta 立即数——直接取 `v_meta`，
   免一次 eval；bds 含 bound 槽时照常求值（产生 pattern spine）。

## 实测结果（Windows 10，release build，rounds=3 取 min）

```text
== workload: church ==
k=11  n=4096    fast=0.262ms*  basic=2.982ms      (≈11×)
== workload: solve ==
k=11  n=4096    fast_ss=0.546ms / fast=0.525ms*
== workload: implicit ==（2026-09-02 复测，受控内联环 + force 缓冲后）
k=9   n=1024    fast_ss=1.413ms*
k=10  n=2048    fast_ss=3.523ms*
k=11  n=4096    fast_ss=6.182ms*
k=12  n=8192    fast_ss=13.481ms*
k=13  n=16384   fast_ss=27.097ms*
k=14  n=32768   fast_ss=55.342ms*
```

implicit 负载（n 层 `p_i = id p_{i-1}`，每层一次插入 + 一次求解）原本
呈二次方（k=13 曾为 1913ms）：每层 fresh meta 捕获的 bds 持久链沿
Defined 槽位逐一走过（`vAppBDs` 只应用 Bound 槽，但**遍历**整条链——
实测插桩 2.68 亿步中 bound 槽为零，纯空转），且 solve 每次 `vec![None;
γ]` 逐槽清零（γ = 层深）。两项均已根治（见下节机制 7/8）：改后近线性
（k=13 → 27.1ms ≈ 71×，k=14 → 55.3ms，改前外推 ~7.6s ≈ 137×），剩余
每层常数大致与 chain 负载同量级。

## 已知限制

- check/infer 与 parser 在 let 链上仍是递归（L03 同款），深度负载需要深
  栈（l04bench 默认 128MB 线程；`L04_STACK_MB` 可调）。实测 ~5 万层
  溢栈（chain/implicit k=15，n=65536）。
- 参考版的深层 Box 项析构会爆栈，bench 里 `mem::forget`（L03 同款处理）。
- **λ 体内的 `let`**（L03 潜伏缺陷的 L04 同款，已修）：define 原本无条件
  追加到全局 `defs`，λ 体内的 define 占位后、外层再 define 会与全局
  位置冲突（debug 断言炸 / release 静默解析错）。修复：`env_ext_defs`
  改 tip 条件分支——define 时 env 在全局末端（模块链/λ 体内）照常入平坦
  区（chain 负载的 O(1) 线性保证不动）；非 tip 环境（λ 体退出后的外层
  define）回落到 binder 链，索引语义不变、仅查链 O(链深)。互检测试
  `define_inside_lambda_matches_basic`（type + nf 双模式）。