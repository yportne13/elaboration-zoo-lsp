# L13：命名空间层（生产版：LSP / HDL 宿主）

本层是全仓最复杂的一层，也是**产品层**：LSP 的 hover / completion /
inlay 观察面、HDL prelude（moduletree codegen）与并行测试基建都压在这
里。相对 L12 的核心机增量：全限定 decl 键的命名空间（package / import
/ `Enum.case` / `Type.mk` / inherent 方法）、**原生 Nat**（`Val::Nat(u64)`
替代一元构造子链）、prim 挂 decl 表（不再有 `Tm::Prim`/`Val::Prim`）、
`SumCase` 按构造子下标、`Call`/`OpCall` 内联节点、class 两阶段、
BindingName 隐参、def replay。

两份实现：参考版（`mod.rs` + 分文件）与性能孪生 `bump_spine_iter.rs`
（L12 冠军配方的移植 + 本层增量，模块头注释逐条记录对位）。共用
parser / pretty / preprocess / trait 求解器 `Synth`，**Ok 输出逐字节
一致**（互检测试 + `tests/l13_fast_parity.rs`）。LSP 侧 `Engine::Twin`
已接线（`docs/lsp-twin-wiring-2026-09.md`）。

---

## 1. 语言特性：命名空间与生产扩展

### 1.1 全限定 decl 键与名字解析

- **decl 表七元组**（`mod.rs:309`）：
  `FxHashMap<SmolStr, (span, Tm, Val, Ty, VTy, Option<PrimFunc>, typ_pretty)>`
  ——比 L12 多 prim 槽与 `typ_pretty` 渲染缓存（§3.4）。`decl.get` 在
  求值热路径上，故用 FxHash（prelude 装载一次 ~4M 次查表）。
- **构造子只登记限定名** `Enum.case`，**不设裸名别名**
  （`elaboration.rs` enum 臂；struct 脱糖出 `Name.mk` 同路）。解析交给
  命名空间机制而不是裸名兜底——这是 L13 与 L10-L12（裸名登记）的根
  本差异，模式编译器的适配点都由此而来（§2）。
- **Var 解析五级链**：局部 binder → decl 精确键 → `import_map` 别名 →
  `namespace_prefix` 前缀 → `.name` 后缀唯一回退（歧义报错并给 import
  修复建议；`elaboration.rs:2323` 优先级注释）。
- **inherent 方法**：impl 的方法注册进 `TypeHead.method` 形态的键，
  `x.m` 经 namespace 条目直查分派；算符方法（`def +`）登记
  `symbol_table`（(方法名, 实参数) → 算符符号），quote 在实参全显式
  且 1-2 个时产显示专用 `Tm::OpCall`（quote → eval 往返恒等）。

### 1.2 package / import（`elaboration.rs:1869-1957`）

- `package a.b`：设 `cxt.namespace_prefix`（后续 def / enum / trait /
  class 名自动加前缀，`prefix_decl_name`；trait/impl **方法名不前缀**
  ——`trait_wrap` 按书写名分派，前缀会同时破坏分派与匹配），并把该
  前缀登记进可见 namespace 集 `namespaces`（后缀回退的范围依据）。
- `import ns.{a, b}` / `import ns._`（通配）：**不写 decl 表**——别名
  是文件局部可见性，进 `Infer.import_map`（(别名 → 全限定键)；挂在
  `Infer` 而非 `Cxt`，per-file 克隆天然从空开始、全局不累积别文件别
  名）。具名 import 同时带点状成员别名（`import mylib.Tree` 附带
  `Tree.mk` / `Tree.leaf`…，保住 `.mk` 简写与限定成员访问）；通配
  import 扫 decl 表前缀键。冲突别名报 ambiguous；单名 `import foo`
  直接拒绝（G4：裸名不可追溯到 provider 文件）。
- **moduletree**：HDL 侧的 `ModuleTree`/`Expr` 是 prelude 类型
  （`hdl-*.typort`），`vconnT` 内建（Verilog 具名端口连接）在 prelude
  装载后注册——它的签名引用 prelude 类型，`Cxt::new` 时登记会留下
  悬垂中性头（`cxt.rs:771` 注释）。

### 1.3 class 两阶段与 BindingName 隐参

`Decl::Class`（struct + Module trait 的 HDL 语法面）分两阶段
（`elaboration.rs:1961` 起）：

- **Phase A**：在本机上下文里先检查每个字段/语句（未注解字段的 fresh
  meta 直解为推断类型；`tm_refs_bn` 判定值是否引用 create 专有的
  `bn` 绑定），产出 `PrecheckedItems`——**struct 先于 create 存在**，
  避免旧路径"struct 槽位是 Hole、later 被 create 的隐参实例化"的
  can't unify for unsolved meta 失败；
- **Phase B**：create / tree 体经 `Raw::Tm` 检查臂复用 Phase A 结果
  （检查过的 Pi 链、方法体 λ），eval 副作用重放 + 空 spine Unsolved
  Flex 直解 / unify 复验，不重复 elaboration。
- **BindingName 隐参**：隐参类型为 `BindingName` 时（HDL 命名纪律：
  工厂生成的 wire/signal 名随 let 绑定名走），`insert_go` 不解 meta，
  而是合成 `BindingName.mk "当前绑定名"` 字面量——绑定名由
  `cxt.binding_name` 携带（`bind` 清空、`define` 保留调用方、
  `with_binding_name` 显式设置，`cxt.rs:928` 注释解释了 HDL 场景）。

### 1.4 原生 Nat / Call·OpCall / def replay

- **`Val::Nat(u64)`**（`mod.rs:724-733`）：definitionally 为
  `succ^n zero` 的值存单个 u64（Lean/Agda 式）。字面量经 `build_nat`
  直构；eval 的 SumCase 装配点折叠（`nat_step_value`：`succ (Nat k)`
  → `Nat (k+1)`）；quote 经 `quote_nat` 展开回 SumCase 链——下游
  （pretty/nf/unify）看到的项形状与一元链时代逐字节一致。算术内建
  `nat_add`…`nat_rem` 把 prelude 的结构递归沉到 u64 运算，同时**逐条
  保留旧定义的可归约性**（`0 + m`、`succ k - 0` 等惰性一步展开见
  `cxt.rs:96-289` 的规则注释；nat.typort 的 rfl 证明因此不碎）。
- **`Call`/`OpCall`**：def 调用内联节点（λ 链体顶端的 Match 包成
  `Call(名, 实参链, Match)`）；求值卡住时保留名字与实参供显示，
  quote 查 `symbol_table` 还原中缀算符形态。
- **def replay**：无参 def 的体含全局副作用（create/change/get_global
  族）时，登记值存 `Val::Decl` 占位**不求值**；eval 的 `Tm::Decl` 臂
  命中 replay 名单（`def_needs_replay`，按名 memo + 环敏感扫描）就
  清空 env 重放体——否则 HDL 语句只在声明期跑一次、进 moduletree 的
  值永远拿不到（`mod.rs:1254-1262`）。

### 1.5 内建与宏

- `Cxt::new` 注册 `String` 类型 + 15 个内建（`cxt.rs:642-753`）：
  string_concat / str_eq / str_indent2 / report_check_issue（HDL
  自检报告，行级去重写 mutable `CheckIssues`）/ string_to_global_type /
  create_global / change_mutable / get_global / get_global_default /
  change_mutable_default / file_read_all_text / file_write_all_text /
  file_append_all_text / file_exists / file_delete。nat 算术 prim 与
  vconnT 仅 prelude 挂载（`register_nat_builtins` /
  `register_vconn_builtin`），`run()` 口径不出现。
- 宏：`macro_rules` 声明级展开 + prelude 导出宏累积（`global_macros`），
  自递归受 `MAX_MACRO_EXPANSION_DEPTH = 256` 守卫
  （`parser/mod.rs:139`）；`preprocess` 注释剥离与 L12 同实现（单遍
  扫描，输出与输入等字节长，保 span 偏移）。

## 2. 匹配编译器：逐臂下钻 + 三字段 `PatternDetail`

（2026-09-18 自决策树矩阵重写：commit `448775c`；根因与代价分析见
`docs/l09l13-match-compiler-analysis-2026-09-17.md`——L13 是决策树
最大的一个：参考版 `compile_aux` 985 行 + 孪生 608 行。）

### 2.1 主干与错误收集

`Compiler::compile`（`pattern_match.rs:425`）逐臂下钻（同 L07/L10-L12
口径，保持用户书写顺序 = 运行时首匹配语义）。**签名保持决策树版的
`Result<Vec<Warning>, Vec<Error>>`**：某个臂的走查/特化/体检查失败只
push 进 `errors`，其余臂照常检查，一次性报全（`accumulated_errors`
进而把每个分支体错误作为独立 LSP 诊断发布，`mod.rs:1220`）。语义相对
决策树的**三处收窄**与 L10-L12 一致：覆盖只做顶层+嵌套位置、遮蔽只
认通配臂、特化失败静默跳过。

**臂前置过滤**（`pattern_match.rs:478-486`，决策树 filter 同口径的本
层保留）：首模式是头部 Sum 的构造子、但索引方程不可解（`Vec[Nat]
zero` 上的 `cons`）——该臂不可能匹配，静默跳过并按"从未走到"记
`Unreachable`，不让它落进 `check_pm_final` 报出假的特化错误。

### 2.2 三字段 `PatternDetail` 与隐式参数命名纪律

L13 的运行时模式形态（`mod.rs:572-585`）是全仓独有的三字段版：

```rust
Any(Span<SmolStr>, Option<Span<SmolStr>>, Icit)  // (变量名, 显式参数名, icit)
Bind(Span<SmolStr>)                              // 裸变量模式
Con(u32, Span<SmolStr>, Vec<PatternDetail>, Option<SmolStr>)
//   (构造子在 Sum cases 表的下标, 分支名, 子模式, 全限定 decl 键)
```

- **`Con.idx` 按下标分派**：`eval_aux` 只比 index（`SumCase` 的
  `case_name` 同步换成 `index: u32`）——名字反查 `cases[index]` 免费，
  比较 O(1)；
- **`Any.var_name` 由 `make_implicit_name` 计数生成**（`_{绑定器名}
  {序号}`，`implicit_counter`，`pattern_match.rs:84`）：同一构造子在
  元组模式里出现多次时，每个出现的隐式绑定器必须拿到**不同名**——
  否则臂上下文里两个 `_l0` 互相遮蔽，`Raw` 回读取错槽（adder_proof
  的 `_l0`/`_l1` 分裂即此族，见 §2.3）；
- **`Any.param_name`**：用户具名隐式子模式（`cons[l=l0](..)`）把参数
  名回写进 detail，`detail_to_raw` 重建特化用 Raw 时产出
  `[pi_param=var]` 具名实参——让 `check_pm` **复用走查已绑定的同一批
  rigid**。若不回写，`check_pm` 会为构造子隐含参数（`cons` 的 `l`
  出现在字段类型 `Vec[A] l` 里）新解一个 meta，臂上下文里的
  `xs : Vec[A] _l0` 与特化出的 `Vec[A] ?m` 各说各话（实测
  `can't unify for unsolved meta`）；
- **`ctor_key`**：走查期从 decl 表取得的全限定键（`6bacd12`），回写
  进特化用 `Raw::Var` 头，让 `check_pm` 的 Var 解析走 O(1) 精确命中
  而不是后缀回退扫描 + 实时渲染。
- **特化用 Raw 从走查产出的 detail 重建**（`detail_to_raw`，
  `pattern_match.rs:503`/`:676`），不是 L10-L12 孪生那样的直接
  `pat.to_raw()`——原因即上两条（隐含参数具名回写 + 全限定键）。用户
  写法、子模式形态仍原样保留在 detail 里（运行时与悬停消费）。

### 2.3 精化载体：`update_cxt` 血统（与 L12 的 σ 路线分叉）

L13 的 `check_pm_final`（`elaboration.rs:365`）返回**精化后的 `Cxt`**
（不是 σ）：`check_pm` → `infer_expr_pm` + `insert` + `unify_pm`，
`unify_pm` 走 `cxt.update_cxt(...)` 把解**直接改写进环境槽**
（`cxt.rs:998`：目标槽 `env.change_n` 替换 + `refresh` 全槽在"更新后
env"下重求值重锚定；`update_from` 记录最早被改的槽位做增量刷新下界；
`update_prune` 时 pruning 槽置 None）。`infer_expr_pm`
（`elaboration.rs:388`）与 `check_pm` 互递归：`Raw::App` 的实参走
`check_pm`（→ `unify_pm`）而不是常规 `check`，模式变量因此获得精化
而非撞常规求解器。第二方程（被匹配项的值 `ori` 对齐模式项值）失败
容忍（`unwrap_or(cxt)`，丢弃第二次方程的解）。

`unify_pm`（`elaboration.rs:475`）的两条关键臂（孪生侧由 `ba90f96`
补齐，对齐参考版）：

- **双裸 Rigid 异名**：查 env 槽是否仍是自引用——已精化的一侧保留
  （早前字段匹配的精化不被覆盖），更新未精化的那侧；
- **已精化不覆盖**：单侧 Rigid 的 env 槽已不是自引用时，把旧精化与
  新值再 `unify_pm`（约束传播：早字段的 `n = succ _l9` 与晚字段的
  `n = succ _l17` 触发 `_l9 = _l17`）——盲覆盖会丢前面字段的约束。

`ba90f96` 的直接动机是 adder_proof 的 `_l0`/`_l1` 分裂：模式里多个
`_l{k}` 指向同一逻辑变量时，缺这两臂的孪生会精化漂移（bench 矩阵
§0.1：`twin_engine_tests` 19 全绿）。

`SumCase`/`SumCase` 臂带 **Sum 头名字判据**（L07 修复 4 同款）：跨
enum 重名构造子（index 同、typ 的 Sum 头异）直接 Err，只比头名、不
unify typ 值（避免索引槽互相引用深递归）。

### 2.4 `patcon_raw`：树专属产物，逐臂不复刻

决策树的叶子在**逐列分解后**才到达（臂模式已被拆成单列片段），原始
用户模式 `succ(x)` 拿去 check 字段类型会越界崩溃——所以树用
`patcon.clone().to_raw()`（由积累的 detail 经 `detail_to_raw` 重建）
构造"当前列深度"的模式（树代码注释明写 NO fallback to raw）。**逐臂
实现天然在顶层整模式上工作**：特化输入是"从走查产出的完整 detail
重建的 Raw"（§2.2）——形式上与树的 `patcon_raw` 同血统，但工作在整
模式深度上，`PatConstructor`/`detail_to_raw 树版`/`FilterResult`/
`ArmEntry`/`MatchContext` 等树内部件随 `compile_aux` 一并删除。

### 2.5 嵌套覆盖两段式 + 可达性探测

- **两段式**（L07 修复 5 的本层移植，`pattern_match.rs:44-67`）：走查
  中嵌套 Con 处只记 `(路径, 字段 Sum)`；**臂特化成功后**才提升为带臂
  上下文快照的完整记账（`NestedCheck { path, field_sum, arm_cxt }`）
  ——L13 的精化载体是 `update_cxt`（解进臂 Cxt 的 env 槽），嵌套位置
  的索引精化在 check_pm 期就已写进臂上下文，延迟探测以臂上下文跑
  即可看到（如 `Vec[Nat] (succ zero)` 尾部上 `nil` 不可达）。荒谬臂
  丢弃记账（其位置不产生覆盖义务）。报缺文案与 L07/L12 统一：
  `match 不完整：模式位置 {path} 缺少构造子 {ctor}`；覆盖贡献判定
  共用 `cover_at`/`PosCover`（`mod.rs:650-680`）。
- **`probe_accessible`**（`pattern_match.rs:96`）：构造子类型经命名
  空间解析（`infer_expr(Raw::Obj(Var(Sum), case))`），Π 链实例化——
  头部隐式实参用 Sum 实参、其余绑定器**绑进探测器 cxt**（不是 L12 的
  scratch 层：L13 `unify_pm` 走 `lvl2ix`，层超出上下文直接 panic），
  返回类型与头部跑索引方程；meta 快照换入换出即回滚。fuel 耗尽的失
  败按可达处理（保守要求覆盖，unsound → incomplete 方向）。
  **无参 Sum 短路**：普通枚举（无参数/索引）恒可达，直接返回 true，
  省掉每构造子一次限定名解析 + hover 渲染。
- **可达性 memo**（`ctor_accessible`，`6bacd12`）：per-match 的
  `Vec<Option<bool>>`，覆盖检查与臂前置过滤共用同一判定（同入口上下
  文里同构造子判定不变）；构造子类型本身走 **decl 表直查**
  `{sum}.{case}` 键（`infer_expr(Raw::Obj(..))` 对该形态的解析结果就
  是 `decl[qual].vty`，实测 1.2µs、非热点），未命中（import 限定 Sum
  等）回退 infer_expr 全链路。

### 2.6 构造子良构性

`check_ctor_wf`（`elaboration.rs:290`，L07 修复 6 的本层移植）：ret
必须是本 enum 的 Sum 且隐式参数位逐一为 telescope 内 bare rigid——
拒绝 phantom 构造子（`c -> Nat`：覆盖完备的 match 在该值上卡死）与
参数位特化（`c -> Foo[Nat]`；显式索引位任由特化，GADT 保留）。构造
子重绑定参数惯用法（`p[A,B](a,b) -> Pack[A][B] a b`）不误伤。

### 2.7 运行时 `eval_aux` 的两个优化

只 force 非构造子头（meta 等）——在已构造子值上重 force 整条深构造
子链是每步 O(n)、`nat_add_helper` 型负载 O(n²)（`pattern_match.rs:602`
注释）；原生 Nat 直接按 `Nat 0 → zero`、`Nat k → succ (Nat (k-1))`
分派（走一 `succ` 的 O(1) 类比，不再建一元链）。

## 3. LSP 观察面

### 3.1 三张 owned 表（阶段 1-4 接线，`docs/lsp-twin-wiring-2026-09.md`）

- **hover_table**（`mod.rs:1191`）：`HoverEntry = (源 span, 定义
  span, 渲染串)`——串在 **push 期**渲染定稿，跨引擎契约：bump 引擎
  （quoted Tm 随轮消亡）也能填同一张表，查询侧只拷出。查询
  `hover_entry_at`（`mod.rs:1316`）取包含光标偏移的**最小 span** 条目
  （tuple 元素条目窄于整 tuple 条目，元素上元素赢）。
- **completion_table**：`(span, 名字)`，trait 方法补全与 struct 字段
  补全路径填充（`elaboration.rs:2568-2603`）；
- **inlay_hint_table**：`(字节偏移, ": <类型>")`，def 未写返回类型 /
  let 未写注解时推；含未解 meta 的类型跳过、超 80 字符截断
  （`push_inlay_hint`，`elaboration.rs:176`）。
- `accumulated_errors`：match 分支体类型错误逐条入表（每条红波浪线
  独立诊断）。观察面 push 都有开关（孪生装载段 `observe=false` 关
  push——prelude 装载不付观察面成本）。

### 3.2 构造子 hover 渲染缓存与 `case_spans` memo（`b3b1700`）

逐臂移植后的勘查发现真正热点不是构造子类型解析（decl 直查 1.2µs、
`infer_expr` 回退 0 次触发），而是**构造子 hover 渲染**：每 match
22µs 的 quote+export+pretty（观察面成本混进 PM 路径）。两刀：

- **decl 键 hover 渲染缓存**（`ctor_hover_memo`，`mod.rs:1268-1275`，
  `push_ctor_hover` 专用）：构造子 hover 值是 decl 条目的**闭合值**，
  渲染串与使用处上下文无关——同键第二次起免 quote/pretty 全管线
  （缓存后实测每 Con 模式 ~0.5µs）。只在渲染**无未解 meta** 时缓存
  （meta 可能首见后才被解，缓存串会把 `?N` 冻进悬浮）；LSP 快照克隆
  此表随 hover_table 一起留空。
- **`case_spans` per-match memo**（孪生 `bump_spine_iter.rs:11270`）：
  一次 match 编译内 decl 表只读，Sum → case span 表按 Sum 名缓存。

悬停语义：模式 token → 构造子（定义 span 指向 enum 声明里的 case
名）；无参构造子给构造子值，参数化构造子给 Π 签名而不是不可读的 λ 串。

### 3.3 force 记忆化与 prelude 缓存 / 池

- **FORCE_MEMO**（`mod.rs:99-147`，`d85a759` 孪生移植同机制）：force
  结果按输入节点地址 memo——正确性三支柱：**keepalive**（条目持输入
  `Rc`，地址不复用）、**taint**（走查途中摸了 meta 解 / 不纯 prim /
  诊断等 memo 抽象不了的状态即不插入；`prim_is_pure` 白名单）、
  **version**（decl 条目 prim-ness 变迁 bump 全局版本号，过期条目按
  miss 处理）。上限 1M 条，epoch 随用户文件变更/prelude 装载重置。
  效果：prelude 装载的 force 调用 636M 次 / 188k 不同节点（~3400×
  冗余）；HDL prelude 11.0s → 1.8s。
- **PreludeSlot / PreludePool**（`mod.rs:3514-3569`）：thread-local
  prelude 状态缓存 + 进程级池（线程退出推池、新线程取池，独占所有权
  跨线程 `Send`——引用计数非原子，安全性由"推池时持最后引用"前提
  承担，`Drop for PreludeSlot` 主动清 `FORCE_MEMO`/`DECLB_CACHE` 两
  个可能钉着池化共享节点的 TLS 缓存来维护该前提）。动机：libtest
  每测试一线程，无池则每个测试重装 ~24 文件 prelude（~1.5s）。
  另有 `PRELUDE_CACHE_NO_HDL`（跳过 hdl 文件的口径）。
- **def-site `typ_pretty`**（decl 表第 7 槽，`cxt.rs:955` 注释）：def
  登记处的类型渲染缓存——raw 项可嵌 pruning 深于任何显示侧名字表的
  `AppPruning(Meta, pr)`，hover 必须显示预计算串而不是无上下文重打
  印。使用处（含 qualified 三连、后缀回退）一律实时渲染（阶段 2 修
  复：登记期缓存串曾把 fresh 名冻结）。

## 4. 性能孪生设计（`bump_spine_iter.rs`，15k 行）

L12 冠军配方（bump arena + 打包值 + 迭代内核 + 记忆化 + 稳态复用）
的移植 + 本层增量（模块头 `bump_spine_iter.rs:1-117` 逐条记录）：

- **原生 Nat**：`XCell::Nat`（打包字 tag 0-7 已满走 bump 单元）；
  曾因 `nat_step_value` 对中性字段不查 tag 就解引用爆
  `STATUS_ACCESS_VIOLATION`，现 `v_tag == 7` 守卫（模块头"已知偏差
  1"的修复记录）；
- **SumCase 按下标**、**prim 挂 decl 表**（`PrimId` 枚举替代闭包，
  执行点 = force/v_app 的 Decl 臂，实参逆 spine 序收集转正序，
  `None` = 卡住）、**Call/OpCall**、**def replay**、**namespace/
  package/import**（五级解析链同参考版）、**class 两阶段**（Phase A
  产 `PrecheckedItems` 经 `export`/`v_to_ref_val`，Phase B 经**指针
  导入表**复用——eval 副作用重放 + 空 spine Flex 直解 / unify 复
  验）、**trait**（`trait_metas` 登记表只扫它、
  `allow_flex_defaulting`、head_index 桶 + GENERIC_SELF_HEAD 通配
  桶、非 out 参数 Flex 推迟）、**BindingName**；
- **unify 增量**：Call/Call 同名 spine 快路径（三重快照回滚）、Decl
  头 prim 视为不透明叶 + 对侧 Flex 先走求解拦截、`unify_pm` 的双裸
  Rigid 异名/已精化不覆盖两臂（`ba90f96`）、solve 的
  non-invertible-spine 常数解 fallback；
- **LSP 接线**：三张观察表 push 期渲染、prelude 装载轮
  （`run_decls_with_prelude`；**无 PreludePool 池化**——每 kick 从
  prime_round 重放）、force 记忆化、**常驻 prelude 检查点**（阶段
  3b：`prime_resident` 一次装载 + `observe_user` 多次复用）+ 阶段 4
  接管单文件诊断（错误 span 保真 + 逐 decl 累积 + `ExportedDecl`
  导出回参考域全局表）：稳态 kick 98ms vs 参考版 359ms（~3.5×），
  常驻态经 arena 压实（`compact` 模块）1835MB → 429MB；
- **不移植**（仍仅参考版）：retry 闭包（canonical/`iddfs`，Err 重试
  路径专属）、`FUNC_PROF`（`TYPORT_PRELUDE_PROF` 门控的函数级排他
  计时探针，`mod.rs:24-97`）、Tm/Val 迭代 Drop（bump 免疫）、
  PreludePool 池化 / defer_println。

## 5. 基准

```text
cargo run --release --bin l13bench
```

`docs/bench-matrix-2026-09-18.md` 全表（`moduletree`/`gadt`/`enum`
k=9，其余 k=11）：

| 负载 | basic (ms) | fast_ss (ms) | fast (ms) |
|---|---|---|---|
| church | 5.853 | 0.969 | 1.145 |
| natadd | 6.953 | 0.972 | 1.179 |
| strchain | 4579.254 | 8.515 | 10.670 |
| struct | 7688.705 | 20.559 | 22.749 |
| gadt | 0.597 | 0.498 | 0.524 |
| enum | 0.754 | 0.650 | 0.647 |
| moduletree | 0.183 | 0.161 | 0.164 |
| prelude-core | 23.081 | 16.171 | 16.443 |
| prelude-hdl | 3184.922 | 1522.939 | 2070.774 |
| examples-hdl | 22.785 | 16.103 | 16.280 |

match 负载（逐臂移植前 09-18 表：basic 0.338 / fast_ss 0.673，孪生
落后 0.5×；`448775c`+`ba90f96`+`b3b1700` 后，矩阵 §0.1 补记）：
**basic 0.245 / fast_ss 0.172 @k=11**——参考版 1.44×（0.352→0.245）、
孪生 3.9×（0.668→0.172），孪生/参考 1.4×（领先）。**PM 路径的
~0.15ms 地板**由语义必需（体检查/特化方程）与 harness（prime_round、
非 match decl elaboration）构成，再往下要动引擎。同窗口跨层对照
（09-20）：L10 孪生 0.052 / L11 0.044 / L12 0.203 / L13 0.172
（L12 偏高是带着其工作区他人 WIP 测的，仅供参考）。

观察面提醒（矩阵 §0.1）：L13 的 bench 口径若开观察面（hover/inlay
渲染），会在 match 上多付每构造子一次 quote+pretty——`b3b1700` 的
hover 缓存已把这条成本 memo 化。

## 6. 已知偏差 / 限制（诚实清单）

1. **诊断三收窄**（相对决策树）：见 §2.1——位置级覆盖检查下的保守
   边界：Bool×Bool 双臂组合缺口（缺 `(true,false)` 组合）仍接受
   （组合维度需真正案例树编译；parity 钉 `(11)` 锁住现状，防日后无
   意收紧）。
2. **单行枚举声明不在语言面**：`enum Nat { zero succ(x: Nat) }`
   （构造子不换行）被共用 parser 的恢复性解析吞掉第二个及之后的构
   造子——两版同错同报（parity 仍逐字节一致），但该形态无构造子可
   用。早期 parity 套件全用单行枚举书写，"全绿"实为两版同错的假阴
   性；现已改用 multiline 声明提供真覆盖（`parity_multiline_enum`
   + 套件头注"语言面注意"）。
3. **快版已知分叉家族**（套件头注登记，缺陷另案跟踪）：GADT 索引宇
   宙判定 × trait 求解交互、struct 接收者实例、单臂构造子匹配、Prim
   求值时机差——在快版分叉或发散，Ok/Err 判定 parity 由结构化用例
   保证。
4. **错误消息内容偏差**：快版错误内嵌 Debug-Val/Tm 的名字 Span 全零
   （参考版携带源码偏移）、meta 编号 `?N` 分配序列不同——套件比对前
   按 `start_offset/end_offset/path_id`/`?N` 归一化；不影响判定与 Ok
   输出。
5. **观察面表形态残余**（阶段 2 登记项）：孪生 Enum 臂构造子体的
   `datas` 复用 `Raw::Var(参数名)` 过 infer，产与 binder 条目同 span
   同串的重复项（查询无影响，全表互检按"无缺失 + 无异质"口径）；tuple
   字段访问 `p._2` 反糖的合成 Var 无源码 span（push 键 t_span=0）；
   使用处 fresh 后缀显示差异（`x` vs `x'`）。
6. **文件 IO 内建无锁、失败即 panic**：`file_*` 五个 prim 对 IO 错
   误直接 `panic!`（`cxt.rs:556-620`），且本层没有 L06-L08 的
   `FILE_IO_LOCK` 串行化——并发测试用固定文件名时会互相踩（测试侧
   靠文件名隔离）。
7. **既有专项分析**（不在本轮范围）：GADT/struct 精化弱点
   `docs/pattern-match-refinement-analysis.md`；trait 实例 Nat 参数
   bug `docs/l13-typeclass-instance-nat-param-bug.md`（`nat_is_ground`
   内建即其检测口）；并行测试 UAF 与池化约束
   `docs/l13-parallel-test-uaf-2026-09.md`。
8. **更新链性能**：`update_cxt` 的 `refresh` 全槽重求值是 update_cxt
   路线的固有成本（L07 §6 淘汰的旧架构在本层仍是精化载体）；嵌套
   match 深负载下的精化传播比 σ 路线（L07/L12）重。属路线级取舍，
   未在本层重做（未核实是否有量化对比）。

## 7. 测试

- **lib 测试**（`cargo test --lib L13_namespace`，`#[cfg(test)]` 模块
  共 341 个 `#[test]`，当前工作区口径）：`legacy_tests` 129、
  `mod.rs` 内 77（含 `test_namespace` / `test_enum_case_namespace` /
  `test_inlay_hint_table`）、`module_tests` 39、`class_tests` 32、
  `verilog_compat_tests` 24、`calc_tests` 19、`debug_test` 15、
  `struct_refine_probe` 4、`module_probe_tests` 2。
- **双 oracle**：`cargo test --test l13_fast_parity`（12 个 `#[test]`
  含多源循环；参考版 `run` ↔ 孪生 `run_fast`，Ok 逐字节 / Err 判定 +
  归一化正文一致）：multiline 枚举真覆盖（构造子子模式 + 递归 +
  非穷尽文案）、单行枚举行为钉（两版同错防分叉）、卡住 Call 实参序
  （quote CallAsm 逆序回归）、trait flex goal 实例选择（meta 头链
  `?m x` 推迟）、稳态复用、解析护栏（超大整数 / 宏自递归）、泛型
  trait 假匹配拒绝、enum 隐式域钉 U(0) 四源、**评审修复轮 2026-09-19
  14 子场景**（嵌套覆盖缺口/正向/GADT 两段式、构造子 WF、臂序、
  位置级保守边界、SPINE_ESCAPE 相邻括号消歧六写法）。
  例数口径：docs 历史记录 372→389 递增（`docs/l13-twin-bench` /
  `docs/lsp-twin-wiring`），主会话口径 412——未核实。
- **LSP 侧套件**（`tests/`）：`namespace_tests` / `hover_tests` /
  `completion_tests` / `cross_file_tests` 等 11 套守卫（两模式全绿，
  `docs/lsp-twin-wiring-2026-09.md` 验收口径）；孪生侧
  `observation_tests` / `twin_engine_tests`（`bump_spine_iter.rs` 内
  模块，观察面全表互检 + 引擎回归）。
- 256MB 大栈线程跑参考/孪生入口（`Error` 携带非 Send 的 retry 闭包，
  线程边界只传归一化文案）。

## 8. 参考资料

- [elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo)
  13（本层骨架的上游）；本仓 `src/L07_sum_type`（显式替换精化的另一
  条路线，其 README 亦指认本层的 GADT 精化弱点分析）、
  `src/L12_canonical`（σ 路线代表 + 孪生前一层）
- `docs/l09l13-match-compiler-analysis-2026-09-17.md`（逐臂移植的根
  因/适配点/代价）
- `docs/lsp-twin-wiring-2026-09.md`（观察面接线四阶段与验收口径）、
  `docs/l13-twin-bench-2026-09.md`（孪生基线）、
  `docs/bench-matrix-2026-09-18.md`（基准矩阵与 §0.1 补记）
- `docs/pattern-match-refinement-analysis.md`（本层 GADT 精化弱点）、
  `docs/l13-typeclass-instance-nat-param-bug.md`、
  `docs/l13-parallel-test-uaf-2026-09.md`、`docs/test-catalog.md`
