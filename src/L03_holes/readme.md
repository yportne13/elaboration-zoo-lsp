# L03_holes — 双向 elaboration + 元变量（holes）与 pattern unification：参考实现与 `bump_spine_iter` 移植

elaboration-zoo L03（`03-holes`，规格见上游同名层的 `Main.hs`）的 Rust
移植：表面语法（无 de Bruijn）→ 双向 elaboration（`check`/`infer` 走廊 +
元变量悬挂与求解）→ 核心语法（de Bruijn 索引）→ `nf`/`type`/`elab` 三种
模式输出。两个实现共用 parser、pretty、错误显示，**输出逐字节一致**
（互检测试）：

- [`mod.rs`](mod.rs) — **参考实现**（上游同款：`Box<Tm>` 项、Rc `List`
  环境、递归 eval/quote/force/unify/rename/solve）。
- [`bump_spine_iter.rs`](bump_spine_iter.rs) — **性能实现**：L01/L02 调研
  冠军配方（`bump_spine_iter`）移植到带元变量的核心机上，eval/quote/
  unify/force/rename 全链路迭代化。
- `parser/` — 词法 + 语法（L02 parser 同款升级：`withPos` 源位置、
  SmolStr 名字、注释、`λ` 重切词；`_` 作 hole 原子兼匿名 binder）。
- `l03bench`（`cargo run --release --bin l03bench`）— 基准（独立 bin，
  `#[path]` 编译，不依赖其余各层）。

L03 相对 L02 新增的语义（元变量机制）：

- `Raw::Hole`（`_`）可出现在任意项位置；elaboration 遇之创建 fresh meta。
  binder 位置的 `_` 只是匿名 binder 名（与 L02 的 `Underscore` 行为一致，
  不产生 meta）。
- 核心语法多出 `Meta m` 与 `InsertedMeta m bds`；值多出 `Flex`（未解
  meta 的中性应用链）。meta 是"函数"：hole 处插入的 meta 抽象掉当前
  作用域的全部 Bound 变量（`InsertedMeta m bds`），因此**解可以引用
  局部变量**（untyped pattern unification 的核心）。
- conv 升级为 **unification**：结构比较带求解副作用；`force` 让值跟上
  metacontext 的演化——模式匹配/引读前必须先 force。
- 解完全展开（不引用 let 定义），通过 `invert`（partial renaming）+
  `rename`（occurs/scope check）+ `lams` 构造。

## 与 Main.hs 的对应

| Main.hs | Rust |
|---|---|
| `Raw`（含 `RSrcPos`） | `parser::Raw`（含 `SrcPos`，报错取最内层位置） |
| `eval`/`quote`/`force`/`unify`/`solve`/`invert`/`rename`/`check`/`infer` | 参考版逐函数对应；性能版见下 |
| `Cxt{env,types,lvl,bds}` | 参考版同记录（+`pos`）；性能版全 `Copy`、绑定量进 bump |
| `freshMeta` / `lookupMeta` / `vMeta` / `vAppBDs` | 参考版方法；性能版 `fresh_meta` + `W::AppBds` 工作项 |
| `mainWith`（`--help`/`elab`/`nf`/`type`） | `main_with(mode, src)` 返回本应打印的文本（测试断言用） |
| `displayMetas` | `Infer::display_metas` / `Machine::display_metas`（`let ?m = ?;` / `let ?m = <nf>;`） |
| `displayError` | `display_error`（megaparsec 风格源码摘录 + caret） |
| 模块注释的 id/id2 示例 | `EX0_SRC` + `ex0()`（elab 模式展示 `?0 := λ x1 x2. x1`） |

## 怎么跑

```text
cargo test --lib L03_holes                 # 26 个测试：三示例、错误路径、
                                           # 基础/性能互检、深度/稳态/求解压力、
                                           # dup 双口径、memo 指针共享、conv_dup/
                                           # chain 互检、shadowing 还原
cargo run --release --bin l03bench         # 基准：k=9..15，七负载族 × 四口径
./target/release/l03bench --max-k 21 --only fast,fast_ss   # 大 n 段
./target/release/l03bench --workload solve --only fast      # L03 特色：求解负载
./target/release/l03bench --workload dup --only fast_memo   # call-by-need 轴
./target/release/l03bench --workload conv_dup --only fast   # 判等记忆化轴
./target/release/l03bench --workload chain --only fast,fast_ss  # 名字解析轴
L03_NO_CONV_MEMO=1 ./target/release/l03bench --workload conv_dup  # memo 消融
L03_NO_NAME_MAP=1 ./target/release/l03bench --workload chain      # 名字 map 消融
```

## 实测结果

机器：Windows x64，release（LTO + codegen-units=1 + mimalloc）。
负载族：`church` = church 2^(k+1)（k 次 ×2 翻倍 let 链）的 **check + nf**；
`conv` = 同 church 数上 `Eq Nat (add big zero) big = refl Nat big` 的
**check**（unify 在 check 内强制两侧完整展开后结构比较，无洞）；
`conv_dup` = `Rel` 型重复谓词（`P x -> P y -> P y`）让 `(add p_k zero, p_k)`
这对比较 3 次——**判等记忆化命中负载**；`chain` = 长 let 链引用最老名字
——**名字解析负载**（详见「名字解析 O(1)」节）；`solve` =
`Eq _ p_k p_k = refl _ _` 的 **check**（L03 特色：期望侧两个 `_` 挂洞，
unify 触发三个求解，其中
`? := p_k` 的大解沿 church 展开的整条 neutral 链 rename）；
`dup`/`dup_deep` = 复制强制族（call-by-need 轴，同 L02）。口径：预热 1 次
+ N 轮取 min；`basic`/`fast`（每轮新建 Tycker）/`fast_ss`（Machine +
metacontext 常住 + `Bump::reset` 跨轮复用）/`fast_memo`（quote 记忆化口径）。

church（min ms / 相对 fast）：

| k | church n | basic | fast | fast_ss | basic/fast |
|---|---|---|---|---|---|
| 9 | 1024 | 0.78 | 0.064 | 0.069 | 12.2× |
| 11 | 4096 | 2.76 | 0.245 | 0.373 | 11.3× |
| 13 | 16384 | 11.4 | 1.04 | 0.98 | 11.0× |
| 15 | 65536 | 51.7 | 3.99 | 3.61 | 13.0× |
| 17 | 262144 | — | ~14 | 18.3 | （深度无上限） |

conv（min ms / 相对 fast）：

| k | church n | basic | fast | basic/fast |
|---|---|---|---|---|
| 9 | 1024 | 2.52 | 0.140 | 18.0× |
| 11 | 4096 | 9.71 | 0.513 | 18.9× |
| 13 | 16384 | 43.2 | 2.15 | 20.1× |
| 15 | 65536 | 203 | 8.29 | 24.5× |

solve（min ms / 相对 fast，L03 特色负载）：

| k | church n | basic | fast | basic/fast |
|---|---|---|---|---|
| 9 | 1024 | 1.71 | 0.202 | 8.5× |
| 11 | 4096 | 6.71 | 0.755 | 8.9× |
| 13 | 16384 | 30.4 | 2.94 | 10.3× |
| 15 | 65536 | 149 | 12.3 | 12.1× |
| 17 | 262144 | — | 51.4 | （深度无上限） |

dup / dup_deep（min ms）：

| 负载（k=15） | basic | fast | fast_memo | memo 收益 |
|---|---|---|---|---|
| dup（强制 ×2） | 116 | 7.77 | 4.03 | 1.93× |
| dup_deep（强制 ×4） | 219 | 15.8 | 4.43 | 3.56× |

- 各负载族两版都严格线性（每翻倍 ×2）；对参考版的倍率 church ~13×、
  conv ~30×、solve ~35×、conv_dup ~21×（提速第二轮后的数字，见下节）。
- **深度无上限**：solve k=17（262144 链 rename）默认栈跑通（51 ms）；
  `basic` 的递归 rename/unify 受栈限（128 MB 栈 ≈ 26 万层，见已知限制）。
- **稳态复用（`fast_ss`）在 L03 未复现 L01 式的大幅收益**——与 L02 的
  结论一致：elaboration 里 bump 分配（闭包/env/Π 单元/meta 解）占大头，
  spine/vals 复用省的那部分不显著；metacontext 常住（每轮清空）的意义
  只在形态上（长驻进程），不期待数字。
- **quote 记忆化（`fast_memo`）在 dup 族 1.9×/3.6×**（L02 同款）：复制
  被塌缩为单次强制。L03 的 meta 不影响 memo 键：quote 期间 metacontext
  冻结（无 solve），同一打包字在同一 level 的 force 结果确定。**现已
  成为生产默认**：`Tycker::run` 的 nf/type 引读走 `quote_memo`（`elab`
  模式的 `display_metas` 仍走普通 quote），`run_no_memo` 为消融对照；
  bench 的 `fast`/`fast_memo` 双口径（`bench_check_nf`/`_memo`）保留作
  该轴的消融。

## 提速第二轮：热路径 scratch 复用 + conv 内联环 + unify 判等记忆化

三项叠加（k=15 min，交替 A/B；消融开关 `L03_NO_CONV_MEMO=1`）：

| 负载 | 改前 | 改后 | 提升 | 归因 |
|---|---|---|---|---|
| conv | 8.8 ms | 6.2 ms | **1.4×** | 内联环（`(2,2)` 沿 `.a` 同步下走，65k 层零工作表往返） |
| conv_dup | 19.9 ms | 13.6 ms | **1.46×** | 内联环 + 判等记忆化（第 2/3 次比较塌缩为查表） |
| solve | 8.0 ms | 4.5 ms | **1.7×** | 判等记忆化：`(p_k, ?x)` 因 `Eq A x x` 型重复出现二次，命中省掉解展开后的整趟重走 |
| church / dup / dup_deep | — | — | 持平 | memo 查表在同二进制消融下零开销 |

配套两处小改：unify/rename 热路径的临时 `Vec`（`(2,2)` 实参收集、
`RJob::SpineFold` 的 `args.clone()`）改为跨迭代复用 scratch。

健壮性论证（相对 L02 纯 conv memo 多出的部分，全文见 `unify_iter`
注释）：meta **写一次**、force 只会 flex→rigid、算法成功对 metacontext
**单调**——故只缓存成功结果（`Store` LIFO 屏障保证整棵子比较成功后才
入表，失败直接 `return false` 无失败缓存）与逐对重比观测等价，且跳过
重比不欠任何求解（M′ 时刻想解的 meta 在 M 时刻同样可见）。solve 分支
的成功也直接入表（无子比较，无需屏障）。互检测试 + 全 k bench 断言
兜底。

移植过程中的一个坑：`std::mem::take` 拿回的 scratch 残留旧数据，而
`collect_args` 是**追加**语义——复用前必须 `clear`，否则 solve 拿到脏
args 直接判失败（首版漏掉后 ex2/solve 全挂，互检测试当场暴露）。

## 名字解析 O(1)（`name_map`）

`Raw::Var` 原本沿 `types` 持久链线性找名——深度 = scope 大小，长 let 链
每层引用老名字时整个 elaboration 是 O(n²)。性能版 Machine 现持
`名字 → (绑定 lvl, 类型值)` 哈希表，`Cxt` 带 `mark`（撤销轨迹基线）：

- **bind/define** 推表 + 轨迹；**binder 递归返回**按父 mark 截断恢复
  （shadowing 还原旧绑定、新名字移除）——兄弟子树不泄漏。正确性由
  `name_map_shadowing_matches_basic`（`apply (\x. x) x` 的第二实参必须
  解析回 def）与全量互检兜底。
- **错误路径**（`?` 早退）跳过恢复，轨迹残留到轮末由每轮 reset 清空——
  L03 无错误恢复，中途不再有 Var 查找。
- **消融** `L03_NO_NAME_MAP=1`：查找回落线性 walk（表的维护照常）。

chain 负载（`p_i = add p_{i-1} p0`，n = 2^(k+1) 条 def）实测：

| k | defs | map OFF（walk） | map ON | 提升 |
|---|---|---|---|---|
| 12 | 8192 | 383 ms | 205 ms | 1.9× |
| 14 | 32768 | 7674 ms | 3430 ms | **2.2×** |

其余六负载同二进制消融持平（church/conv/solve/conv_dup ±2% 噪声内）
——表维护（每 binder 一次 insert + trail push）不在热路径。

### chain 暴露的下一个二次方：eval 环境走链

map 开启后 chain 仍二次方（每 def ~O(i)）：**eval 的 `nth` 沿 EnvCons
持久链取 de Bruijn 槽位**，老名字（`add`/`p0`）的值在链底。这与名字
解析同源不同轴——解析查的是 elaborator 的 types 链（现已 O(1)），`nth`
查的是 eval 时的值环境。根治要换环境表示（分块/平坦 env，见 L01
`env_slice`/`ast_env_arena` 变体的探索），列为本层后续轴。

## 打包值上的元变量机制（性能版）

L02 的打包值有 5 个 tag；L03 增加 **tag 5 = `Meta`（立即数，`m<<3|5`）**，
未解 meta 的"空 spine"形态。带实参的 `Flex(m, args)` 就是普通 spine——
**头槽 `f` 存 Meta 立即数**，实参挂在链上。全部元变量机制落在四个
迭代改造上：

1. **`force` 是循环**：已解 meta 立即数 → 替换为解，继续；已解 flex
   spine → 沿 `f` 指针收集实参、把解按应用序摔上去（解是闭包时 β 经
   `eval_iter`），再继续。未解保持原样。spine 的 `f` 指针语义（为什么
   "沿 `f` 走到底" 就是链头——ChainWrap 惯例的 `f` = 头值、Apply 惯例的
   `f` = 前一个 partial）见下方「spine 语义注记」。
2. **`vAppBDs` 是 work 栈任务**：`InsertedMeta m bds` 求值时先取
   `vMeta m`，再沿 (env, bds) 平行走：`bound` 槽位把环境值**从外层到
   内层**应用上去（递归版尾递归的栈翻转）。应用时值若是闭包 → β（工作
   项继续），否则 `spine.push`。
3. **`invert` 是循环、`rename` 是任务栈**（`RJob::Ren`/`SpineFold`）：
   参考版的 rename 沿 spine 递推（`renameGoSp` 每实参一帧）——church
   展开的 solve 负载下深度 = 链长，递归会爆栈；任务栈沿 `f` 指针收集
   实参（逆应用序）、`SpineFold` 组合器把已重命名实参折回左嵌套 App。
   **partial renaming 表不需要回溯**：lift 单调插入 `ren[cod] = dom`——
   spine 映射管 Γ 变量（< gamma），lift 管 lift 出的 binder（≥ gamma），
   两段不相交，兄弟子树的 lift 键值相同（路径无关），插入顺序与深度
   同步。
4. **unify 工作表带求解副作用**：L02 的 conv 工作表 + 求解分支。`Pair`
   弹出先 force 双方、位相等快速路径 force 前后各查一次；`(2,2)` 同头
   中性逐对压实参比较（含**同号 flex-flex**——同一 meta 的两个独立
   spine，同实参不同句柄，如 cod 位置两次独立求值所得；solve 的 occurs
   check 对同号必败，参考版 `unifySpine` 同款走逐实参比较）；**异头**且
   任一侧头是未解 flex → `solve`（`invert`+`rename`
   +`lams`+空环境 eval，完成前不写表——失败不污染 metacontext）。
   求解只发生在比较成功路径（工作表纯合取，失败早已 return），无回滚
   问题。

### spine 语义注记（L02 的 entry `f`/`a` 惯例）

L02 的扁平 spine 栈一个 entry 是「一次中性应用」，但 `f`/`a` 两个字段
有两种填充惯例，L03 的 meta 机制（头探测、实参收集）必须同时正确：

- **ChainWrap 惯例**（求值器右链快速路径收拢）：`push(头值, partial)`，
  链上所有 entry 的 `f` = 同一头值，`a` = 前一层 partial —— church 展开
  的形状（引用语义的"实参"是嵌套 partial）。
- **Apply 惯例**（`W::Apply` 弹函数值拼实参）：`push(函数值, 实参)`，
  entry 的 `f` = 函数值（中性链上 = 前一个 partial），`a` = 真实参。
- 两种惯例都满足 `value(e_i) = App(f_i, value(e_i.a))`，且 `e_i.a` 恒是
  紧邻前一条目——所以「沿 `f` 走到底」就是链头（Lvl 或 `Meta` 立即数；
  f 指针严格朝更早槽位，必终止），「沿 `f` 收集 `a`」就是引用语义实参
  （逆应用序，两种惯例统一）。**头探测必须走 `f` 链**，不能读顶层
  entry 的 `f`——Apply 惯例链的顶层 `f` 是前一个 partial（本次移植踩中
  的坑，见下）。

### 优化过程中的两个教训（本层特有）

1. **flex 头探测的 `f` 链**：`force`/`flex_of` 最初直接读
   `spine.stack[h].f` 取 meta 号——对 Apply 惯例链取到的是前一个
   partial（一个 spine 句柄），`v_meta_of` 给出错误下标直接越界
   （`len is 5 but the index is 5` 一类）。修复即先 `spine_head` 走底
   再取号——L02 的 ChainRun 只在 ChainWrap 形态的链上跑（`f` 恒同字），
   没暴露过这个区别；L03 的 flex 应用链是 Apply 惯例的常客。
2. **eta 步把 fresh 实参积到 flex 的 spine 上**：unify 的 `(VLam, _)`
   eta 情形把两侧都应用到新变量——若一侧是未解 flex，实参就**追加到
   flex 的 spine**（`?C [N, s, z]`）。多次 eta 之后出现「刚性链 vs 带参
   flex 链」的形态——`(2,2)` 分支必须识别「头是未解 flex」并转求解
   （invert 的 spine 恰好覆盖 rhs 的全部自由变量），不能直接按头字不同
   判失败。最初版在此返回 false，solve 负载的全部 k 都报
   "Cannot unify"（参考版通过——互检测试立刻暴露）。

## 移植清单（L02 → L03）

| L02 机制 | L03 移植 |
|---|---|
| 打包值 64 位（tag 0-4） | + **tag 5 = `Meta` 立即数**（未解 flex 的空 spine 形态） |
| spine 栈（len/base 记账） | 同款；flex 链的头槽 `f` 存 Meta 立即数，`spine_head` 沿 `f` 走底 |
| 流式右链 quote（ChainRun） | 同款 + flex 链头共享单一 `?m` 节点（tag-5 f0 与变量同款特化） |
| eval 双栈 + 右链快速路径 | 同款 + `Meta`/`InsertedMeta` 臂；`vAppBDs` 拆成 `AppBds`/`AppBdsOne` 工作项（外层实参先应用） |
| quote 任务栈 | 同款（Q 入口先 force——已解 meta 展开成解再引） |
| conv 工作表 + 位相等 | → **unify 工作表**：Pair 弹出 force 双方；`(2,2)` **异头**含未解 flex 头时转求解（同号 flex-flex 走逐实参比较——occurs 对同号必败）；求解 = `solve`（全迭代） |
| ——（L02 无 meta） | force 循环：解链展开 + spine 重建（应用可 β，经 eval_iter） |
| ——（L02 无 meta） | invert 循环 + rename 任务栈（`RJob`）；ren 表单调无需回溯 |
| ——（L02 无 meta） | `fresh_meta`（bump 外 `InsertedMeta` + 常住 `Vec<MetaEntry>`，每轮清空） |
| `Machine`/`Tycker` 稳态 | 同款；`display_metas` 引读解值（quote 0） |
| quote 记忆化 `quote_memo` | 同款移植（dup 族 1.9×/3.6×；quote 期间 metacontext 冻结，键稳定） |
| ——（L02 conv memo） | **unify 判等记忆化已移植**（提速第二轮）：只缓存成功 + 单调性论证（见 `unify_iter` 注释与 readme「提速第二轮」节）；solve 分支成功亦入表，`(p_k, ?x)` 型二次重走被命中剪掉 |
| ——（L02 conv 连续链内联环） | **已移植**（提速第二轮）：`(2,2)` 刚性分支沿 `.a` 同步下走 + 连续链长度 fail-fast；conv 的 65k 层比较零工作表往返 |

## 已知限制

- 两版共用 `parser::parser(..) -> Option<Raw>`：解析失败只有 `parse
  error`，没有带位置报错（L02 同款；后续层 L13 有完整的诊断设施）。
- `basic` 的递归 eval/quote/unify/rename/solve 深度受线程栈限（solve
  负载 k ≥ 17 的 rename 需要 >256 MB 栈；`L03_STACK_MB` 可调，再深用
  全迭代的 `fast`）。
- `basic` 的基准口径对 nf 结果 `mem::forget`（深 Box 树的递归析构会爆
  栈；bench 进程一次性，退出即回收——L01/L02 readme「已知限制」同款）。
- 性能版的错误消息路径（`show_val`）会 quote + export 回参考版的
  `Box` 树再走共享的 pretty——只在报错时发生，不在热路径上。
- 解必须是"模式解"（spine 由互不相同的 rigid 变量构成）；非模式情形
  （如 `?m a a` 与 rhs 的合一、scope check 失败）报 Cannot unify——
  与上游一致（L05 才引入完整剪枝）。
- `nf`/`type` 模式对**带 binder 的未解 hole**（`\x. _` 一类）会 panic
  （`vAppBDs` env/bds 错位）——上游 Haskell 同款（`nf [] t` 空环境求值
  越界）；顶层 hole 无碍。`elab` 模式可正常展示。