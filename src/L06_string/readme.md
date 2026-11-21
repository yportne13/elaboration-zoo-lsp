# L06_string — 字符串字面量 + decl 表 + builtin：参考实现与 `bump_spine_iter` 移植

L06 在 L05（typed metas + pruning）之上加 **String 字面量类型**、
**decl 表按名取值**（顶层 `def` 的运行期查找，L13 的 `Decl` 机制前传）、
**builtin 注册表**（prim 于应用时触发；str_eq / str_indent2 / 文件 IO /
可变全局，L13 的 `PrimFunc` 前传）与**顶层 decl 序列**（`def` / `println`，
上游 06 的程序形态）。

与 L03/L04/L05 同构的双实现：

- 参考实现（分文件：`elaboration.rs` / `cxt.rs` / `unification.rs` /
  `syntax.rs` / `pretty.rs`，`mod.rs` 汇总）：`Box<Tm>` 项、`List` Rc 持久
  环境、递归 eval/quote/force/unify/rename/prune、`HashMap` decl 表 +
  `Rc<dyn Fn>` prim；
- `bump_spine_iter.rs`：极致性能版（L05 冠军配方的移植 + string 层机制），
  两版 **Ok 输出逐字节一致**（互检测试 + `tests/l06_blackbox.rs` /
  `tests/l06_blackbox_v2.rs` 双 oracle 套件）。

## 语法要点（与 L05 的表达式形态不同）

- 顶层是 **decl 序列**：`def 名(参数): 返回类型 = 体` 与 `println 体`；
  `def` **无分号终结、无尾表达式行**——parser 要求 decl 流吃完全部
  token，多余 token（含 `;`）使解析整体报错并**带首个残余 token 的内容
  与偏移**（历史版静默截断，曾让 `;` 结尾的测试用例空转）。
- λ 是 `binder组 => 体`（**无反斜杠、无点号**）；隐式 `[x : A]`、命名
  λ binder `[名字 = x]`、命名实参 `[名字 = e]`（L05 的 `{}` 全换成 `[]`）。
- 字符串字面量 `"..."`（支持 `\n` `\t` `\r` `\\` `\"` `\0` 转义，未知
  转义原样保留；空字面量 `""` 合法；注释剥离感知字符串——字面量内的
  `//` / `/* */` 不生效）；`String` 是内置类型名（注册为 `LiteralType`
  值）。
- `let x : A = t; u`（表达式层，体以分号接续；`in` 不是关键字）。

## L06 的语义增量（相对 L05）

1. **LiteralType / LiteralIntro**：`"…"` 的类型是 `LiteralType`（打印
   `String`），值是内容字符串。pretty 打印字面量**原文**（无引号）。
2. **decl 表**：顶层 `def` 登记值/类型（elaboration 时）；`Tm::Decl(名)`
   求值时查表——命中给登记值，miss 保持**卡住的 Decl 头**（带 spine 的
   中性值）。
3. **builtin prim**：`Cxt::new` 注册整组 builtin（值 = 卡住 Decl 头），
   **应用时触发**：每次对 Decl 头的应用把全条累积实参（自然序）交给
   prim，元数不足或实参非字面量则保持卡住（`string_concat x` 部分应用
   即此形态）。文件组失败 panic；`get_global` 缺名保持卡住的 Decl 头
   （不再 panic）；`change_mutable{,_default}` 先取旧值并结束借用再求值
   函数实参（f 的求值可重入任意 prim，历史上持有 `borrow_mut` 求值会
   BorrowError panic）。
4. **可变全局**：`create_global` / `change_mutable{,_default}` /
   `get_global{,_default}` 读写 `mutable_map`（RefCell；参考版随 `Infer`
   每次调用新建，快版随轮清空）。
5. **unify 的 L06 臂**：`(String, String)` 自反；`String` 与**未登记名**
   的卡住 Decl 宽松合一（get_global 族动态余定义域的逃逸舱口；已登记名
   按登记类型把关，U 型 builtin 的卡住值不再冒充 String 型）；同名 Decl
   逐实参（`unify_sp`）；**(Lit, Lit) 恒败**——参考版
   unify 没有字面量臂，连相同字面量也不可合一（快版如实复刻，见下）。
   源码级唯一可达形态是经刚性 spine 的 `F "a" ≡ F "a"`，失败消息会把
   **两个相同的项**并列打印——无字面量臂的已知形态，不是消息构造 bug。
6. **重定义报错**：顶层 `def` 的名字已在 decl 表（builtin / 先前 def）
   中 → `redefine {名}` 定向报错（L13 `fake_bind` 语义前传），不再静默
   覆盖；类型错误先于重定义报出（与 L13 检查顺序一致）。上游演示的
   "同名覆盖"习语随之失效，demo 改独立名（`m2`/`test2`）。
7. **类型注解的 universe 定向报错**：注解形态确定非类型（字面量；名字
   的类型非 `U` 且不是未解 meta）→ `expected universe, got …`（L13
   `check_universe` 的轻量移植；结构预检零副作用，`?N` 编号不受扰动）。
   洞 / 未解 meta 放行——可解性仍交主检查路径。

## 性能版要点（相对 L05 的增量）

1. **值编码的 tag 6/7**：`6=LiteralType` 立即数（同 `U`：tag 本身即值，
   进 `fresh_meta` 的 `binds==0` 常值类型快捷）；`7=XCell` 指针
   （`Lit(&str)` / `Decl(&str)`）。字面量是惰性叶子；带实参的 Decl 头
   是 **tag 2 链**（头是 tag 7 单元）。
2. **builtin 的增量触发**（[`decl_apply`]）：参考版 `v_app` 的 Decl 臂
   ——每次应用都以**全条**累积 spine 触发 prim（中间步骤也触发，与
   `vAppSp` 逐步 `vApp` 语义一致）。所有应用点（eval 的
   Apply/ChainWrap/AppPrunOne、force 的解值应用、unify 的 η 臂、prim 的
   `change_mutable`）经 `Entry::decl` 标志 O(1) 判定后进入该函数——标志
   在 `Spine::push` 时随函数侧传播，不 walks 链（church 热路径零额外
   遍历）。
3. **decl 表 / 可变全局挂机**：`Machine.decls`（`FxHashMap<String, _>`）
   与 `Machine.mutable_map`（`RefCell<FxHashMap<String, V>>`）随轮清空
   并重新注册（`prime_round` = 参考版 `Cxt::new` 的每调用重注册，含
   builtin 类型项求值）；bench 的稳态口径因此与一次性等价。
4. **quote/rename 的 Decl 链**：Decl 头的链走流式右链（共享单一
   `Tm::Decl` 节点）；rename 的 Decl/Lit 头照参考版 `rename_sp` 重建
   App 链；invert 对非变量实参（字面量/Decl）照旧失败。
5. **tag 7 的位相等守卫**：unify 的位相等捷径、同头 lockstep 的实参
   跳过、intersect 回落的实参压栈，凡 tag 7 **不走捷径**——参考版对
   `(Lit, Lit)` 无臂（同字面量也 Err）、同单元 Decl 要走同名逐参分派，
   位相等直接放行会错 Accept（`hello file!!` 类错误判定）。
6. **quote/unify 记忆化、复合环境、稳态复用、迭代内核、`PrCons` 跳段、
   `RenBuf` 哨兵、fresh meta 三级快捷**全部继承 L05。

## 2026-11-18：L07 参考版优化的回填

本章原先是"L05 + string 层"，11 月的多轮优化只落在 L07/L08，参考版因此
落后。本轮把 L07 中**与 L06 语言面无关**的机制按原样移植（判定与 Ok
输出逐字节不变，`l06_blackbox` ×3 = 144 例全绿）：

| 项 | 旧 | 新 | 同机实测（`l06bench --only basic`，k=11，ms） |
|---|---|---|---|
| **载体切换** | builtin / def 都 `define` 进 env 头部 | 只登记 decl 表，引用走 `Tm::Decl` | implicit 386 → **8.5**、strchain 57.0 → **5.6**、global 63.7 → **11.0**；prune（k=9）30 173 → **25.3** |
| **`Rc<Tm>` 闭包体** | `Val::Lam` 每次求值深拷整棵 `Box<Tm>` 体 | 闭包体 `Rc<Tm>` 共享（+ Π 域/余域） | church 2.20 → **1.05**、solve 4.94 → **2.26**（载体切换后口径） |
| **rename 原位 lift** | 每 binder `ren.clone()` 整表（O(bind²)） | 原位插入 + 递归后回滚（P1-1） | prune/solve 的 rename 段（另两项已并入上两行） |
| **prim 元数预检** | 每次应用先收集整条实参 `Vec` 再判元数 | 不足元数零分配保持卡住 | strchain/global 热路径 |
| **pretty 增量渲染** | 逐节点 `format!` 拼接（O(n²) 字节复制） | 单缓冲逐字节写入（输出逐字节不变） | 大 nf 树 |
| **P5 跨 meta 环守卫** | 无，间接环只能等爆栈 | `meta_expanding` 展开栈，环处返回卡住 Flex | `cross_meta_cycle_force_is_bounded` 钉住 |
| **`DeclEntry.arity`** | — | builtin 元数随条目登记（v_app 预检用） | — |

> 交付口径：`l06_blackbox` ×3（42 + 25 + 83）与 `implicit_comma_args`（523）
> 全绿；`cargo test --lib L06_string` 15 例全绿。`workload_node_counts`
> 在本机（Windows 主线程 1 MB 栈）基线即爆栈（church k=11 的 `quote`
> 递归深度 ~4096），与本次改动无关，用 `--skip` 排除；Linux CI 的 8 MB
> 主线程栈不受影响。

**不改的部分（有意）**：

- L07 的 σ 显式替换 / `Subst` / `VSub` / `SpecSolve` / `Sum` / `SumCase` /
  `Obj` / `Match` / `struct_eq` / `MATCH_CMP_BUDGET` 都是**和类型与依赖
  匹配**的机制，L06 没有 `enum`/`match`/构造子值，移植过来没有承载面；
- `VSpan`（Val 名字 span 句柄化）在 L07 的收益来自"`Val` 按值 +
  名字 `String` 随值克隆"；L06 的 `Val` 始终在 `Rc<Val>` 里，克隆是引用
  计数自增，名字深拷只发生在 `Val` **构造**点（每个 λ 求值一次），不是
  `Val` 克隆点——语义上等价的收益面在 L06 不存在，故不移植；
- `unify_fuel` / `UnifyKind` 三档诊断只在依赖匹配的索引槽互相嵌入时
  才有消费者（覆盖判定/可达性），L06 的合一器没有这条路径。

## 已知限制与偏差

- **错误消息内容**：参考版 `{:?}` 直接 Debug 打印引读项/名字 Span，
  文案带源码偏移（`start_offset` 等）；快版项不存偏移（导出 span 全
  零），消息同构但数字不同。**判定（Ok/Err）与 Ok 输出不受影响**——
  互检只比判定，唯一例外是 icit 失配与命名 λ 两类不含 Span 的消息全文
  一致。
- **不可应用值**：参考版 `v_app` 对 Π/U/字面量的应用 panic（"impossible"）；
  快版照 L05 惯例压栈成卡住链。历史上"良类型程序不可达"的论断有一个
  源码级反例：`string_to_global_type` 把 def 的登记值（可以是 λ）当
  "动态类型"返回后，λ 值会以类型身份流入 unify（如 `def f : U -> U =
  x => x` 之后 `get_global "f"` 的类型就是 f 的 λ 值），unify 的 η 臂对
  字面量/U/Π 做 η 应用即触发该 panic（参考版崩溃、快版 Err——判定发散）。
  已修：η 两臂加**可应用性守卫**（只对 Flex/Rigid/Decl 头展开；两版
  同步），λ 与非函数值的比较一致判失败——`can't unify`。`v_app` 的
  panic 分支仍保留（其余路径确实不可达）。
- **`Span` 的 PartialEq 只比 data**（`parser_lib.rs` 自定义实现）：命名
  λ 按名匹配 Π、Decl 头同名可合一——快版按内容比较，一致。
- **顶层程序形态**：无尾表达式；parser 要求 decl 流吃完全部 token，
  `;` / 垃圾 token 一律解析报错（`run` 返回 `Err`，不再 panic/静默截断），
  消息带首个残余 token 的内容与偏移（共用 parser，两版逐字节一致）。
- **preprocess**：行 `//` 与块 `/* */` 注释剥离感知字符串字面量（字面量
  内的注释标记原样保留），注释内容替换为空白——ASCII 下 span 偏移稳定，
  非 ASCII 注释内容会使后续偏移前移（仅影响错误消息里的偏移数字）；
  **未闭合的块注释会静默吞掉余下全部 decl**（无告警，历史行为）。
- **unify/剪枝的掩码方向**：参考版 `prune_ty` 按上游 `pruneTy (revPruning
  pr)` 反转掩码（头 = 最内层 → 外→内配对 Π 层，L05 同款修复），
  `prune_vflex` 的结果折叠按上游 `foldr` 外先序，`intersect_go` 长度
  失配优雅回落逐实参比较（原 `unreachable!()`）；快版 `invert_bump`
  掩码产**内先序**（`prune_ty_bump` 的 `mask_inner_first` 契约）。
- 文件 IO builtin 做真实文件系统副作用；测试里写删固定文件名的用例经
  `FILE_IO_LOCK` 串行（Windows 并行线程的句柄竞争会让删除报 os error 5）。
- **名字表 = 共享表 + 撤销轨迹**（2026-11-10）：`src_names` 改为
  `NameState{map,trail}` + `Cxt.name_mark`，`bind/define` 只做一次 insert +
  一次轨迹 push（O(1) 摊还），lookup 前按 mark 惰性回滚；父子 Cxt 不再因
  `Rc::make_mut` 整表克隆。新增名字读点必须走 `lookup_src`/`has_src`，不要直接
  borrow map；release 依赖深度优先作用域纪律（debug 有 mark 断言）。
  快版 `name_map+trail` 与参考版现在是同一设计口径。

## 怎么跑

```text
cargo test --lib L06_string          # 参考版 + 性能版内嵌测试（含互检）
cargo test --test l06_blackbox       # 黑盒双 oracle 套件
cargo test --test l06_blackbox_v2    # 黑盒第二卷：剪枝路径/跨轮隔离/词法角落
cargo test --test l06_blackbox_v3    # 黑盒第三卷：prim/global 词法与深负载矩阵
cargo run --release --bin l06bench -- --workload church
cargo run --release --bin l06bench -- --workload all --max-k 13
```

消融开关（只影响性能，不影响输出）：`L06_NO_CONV_MEMO=1`（unify 判等
记忆化）、`L06_NO_NAME_MAP=1`（名字解析回落线性 walk）。

## 实测结果（Windows 10，release build，rounds=3 取 min；CLI 默认 rounds=5）

```text
== workload: church ==（check + nf；basic 与 fast 齐跑）
k=11  n=4096    fast=0.278ms         basic=2.701ms      (≈10×)
k=13  n=16384   fast=1.045ms~1.4ms   basic=11.004ms     (≈10×)
== workload: solve ==（check-only）
k=11  n=4096    fast=0.358ms*        basic=5.961ms      (≈17×)
k=13  n=16384   fast=1.475ms*        basic=29.386ms     (≈20×)
== workload: strchain ==（L06 特色：define 链 + decl 表 + 每层 prim 触发）
k=9   n=1024    fast=1.385ms*        basic=89.7ms       (≈65×)
k=11  n=4096    fast=4.695ms*        basic=1386ms       (≈295×)
k=13  n=16384   fast=36.35ms*        basic=31739ms      (≈873×)
== workload: implicit ==（参考版超线性：k=9 已 2.6s、k=10 已 21.5s，
                        高 k 默认不排 basic 行）
k=11  n=4096    fast=6.0ms*
k=13  n=16384   fast=26.9ms*         （k=10 口径 basic/fast ≈ 7600×）
== workload: prune ==（L05 已知超线性：telescope 物化，快版同款行为）
k=9   n=1024    fast_ss=8594ms       （L05 实测 8.7s，一致）
== workload: global ==（L06 特色：可变全局 + 重入 prim；check + nf）
k=11  n=4096    fast=9.8ms*          basic=5338ms       (≈540×)
k=12  n=8192    fast=21.6ms*         basic=35174ms      (≈1630×)
```

church/solve 上快版稳定领先 10~20×；**strchain 是 L06 的主展示负载**。
（2026-09-20：参考版 `Locals` 脊/载荷与 `src_names` 已 Rc 化，并对「无 Bind
槽且闭类型不读 env/decl 表」的 `fresh_meta` 走等价快捷：strchain k=11
1221 → 180 ms、global k=11 4382 → 318 ms、implicit k=9 2350 → 30.7 ms。）
（2026-11-10：`src_names` 升到 `NameState{map,trail}` 后，`define` 的整表 COW
残差也消掉；同批交错 A/B：strchain k=9 **−60%**、global k=9 **−68%**，
church 持平；参考版 strchain/global 曲线进一步接近线性。）

## 负载族（l06bench）

- `church` 2^(k+1)：check + nf（nf 节点数 = 2n + 4，与参考版同式）。
- `implicit`：`id p_{i-1}` 链（L04 配方；meta 类型恒 U 走 tag3 快捷）。
- `prune`：每层洞类型 telescope + `m a a` 非线性 spine（L05 特色）。
- `solve`：`Eq _ p_k p_k = refl`（rename 深负载）。
- `strchain` 2^(k+1)（**L06 特色**）：每层 `string_concat s_{i-1} "x"`——
  define 链 + decl 表增长 + 每层一次 prim 触发；末值 = 长 n 的字面量
  （nf 节点数 = 1）。
- `global` 2^(k+1)（**L06 特色**）：每层
  `change_mutable "k" (s => string_concat s "x")`——mutable_map 读写 +
  函数实参的 β 应用 + 重入 prim 触发；末值 = U（nf 节点数 = 1）。
  参考版超线性（k=12 已 35s），快版近线性（k=12 21.6ms，≈1600×）。

## 2026-11-20/21：L13 的 LSP 引擎侧特性移植 + 性能回退测试

L06 原先没有任何 LSP 相关机制。本轮审计了 L13 为 LSP 交互路径做的一整套
**引擎侧**设施（观察面 / 登记面 / 求值预算 / 失败 decl 通道 / check issue
通道），把可移植子集落到两版（**默认关闭**），并给出同机 A/B 与采集开销数据。
完整审计表、代码坐标与实测见 `docs/l06-lsp-port-2026-11-20.md`。

**可移植（已落地）**

- owned 快照契约 `surface.rs`：`LspSurface`（hover / completion / inlay /
  println_spans / check_issues / failed_decls）+ `hover_entry_at`（最窄 span）
  + `format_check_warning` / `raw_span` 折叠；
- 观察表与 push 点：两版 `observe.rs`（hover：def-site / 使用处 / builtin /
  let binder / 字面量 / 洞；inlay：无注解 let、无返回类型 def、已知期望类型的洞；
  println span；check issue 只读排水）；
- 登记面：`DeclEntry` 增 `span` + `typ_pretty` + `typ_pretty_final`（采集关闭时
  零渲染；使用处 `final` 时直取登记串）；
- 求值预算 `eval_budget.rs`：`scope`/`scope_default`/`tick`/`ElabTimeout` +
  入口 `catch_unwind`，**只在有预算时打点**（见下性能）；
- 失败 decl 记录通道（opt-in `check_with_surface`，不改错误文案）。

**判为不适用（附审计证据）**：常驻 prelude / arena 压实 / twin kick、
`FORCE_MEMO`、`NatChainOverflow`（L06 无原生 Nat / SumCase）、
`push_ctor_hover` / `push_qualified_hover` / completion（无 enum、无成员访问）、
`defer_println` 两阶段（只有一个返回串消费方）。

**入口**

- 参考版：`L06_string::{run_with_surface, check_with_surface, run_with_surface_budget}`；
- 孪生：`Tycker::{set_observe, surface, hover_entry_at, run_input_with_surface,
  check_with_surface, run_input_with_surface_budget}`；
- bench：`l06bench --observe`（`fast_obs` / `basic_obs` 行，与关闭采集同一调用口径）。

**门禁**（`CARGO_PROFILE_TEST_DEBUG=0` 规避本机 MSVC LNK2019；opt-level 不变）

| 套件 | 结果 |
|---|---|
| `l06_blackbox`（`--skip workload_node_counts`） | 51 passed |
| `l06_blackbox_v2` | 34 passed |
| `l06_blackbox_v3` | 94 passed |
| `implicit_comma_args` | 532 passed |
| `--lib L06_string` | 24 passed |
| `tests/l06_lsp_surface.rs`（新增） | 36 passed |

（各套件比移植前多 9 例：新增的 `surface` / `eval_budget` 单元测试随
`#[path]` 包含进每个 L06 测试二进制；既有断言一条未改。）

**性能（同机交错 A/B，k=13，`min`）**

- **采集关闭**：无可见回退。中位差 ≤1%；最坏格 +3~5%（church / strchain /
  global 这类 eval 密集链）来自求值预算的 tick——消融掉 tick 的对照构建回到
  基线 1% 内（church 0.801 vs 0.798 ms、strchain 21.31 vs 21.35 ms）。
- **采集开启**：push 期渲染是 O(类型打印规模) ⇒ 在 4096 层的合成链上是
  **O(n²)**：implicit 3.9→887 ms（224×）、strchain 2.9→944 ms（322×）、
  prune 49→9372 ms（191×）、global 5.9→1018 ms（172×）；k=9→k=11 采集耗时
  增长 15~19×（规模 4×）。真实小文件（DEMO_SRC，45 条 decl）为亚毫秒级。
  要给 LSP 用需按 L13 的 `typ_pretty_final` + 键缓存思路加渲染缓存/惰性渲染。
