# 维度 4：语言表面、声明/元变量机器与工程面

> 对比对象：L07 = `F:\projects\hermes\elaboration-zoo-lsp`（层目录 `src/L07_sum_type/`）；
> dpm = `F:\projects\Rust\dpm-nbe-rs`（核心 crate 根 `src/`，LSP 为独立 crate `lsp/`）。
> 文中 `文件:行号` 以各自仓库根为基准；简写 `L07/` = `src/L07_sum_type/`，`dpm/` = `dpm-nbe-rs/src/`，`dpmL/` = `dpm-nbe-rs/lsp/`。
> 标注：【事实】= 读过代码 / 数过行或测试；【推断】= 由代码推出的语义后果；【存疑】= 证据不足。
> 本维度不覆盖值表示与 quote/conv（见 03），也不展开合一算法的结构细节（见 01/02），只在"元变量是否存在"这一点上与它们交接。

## 一句话结论

两侧的语言表面差距不是渐变而是量级差：L07 是"声明层 + 隐式参数 + GADT 索引 + 元变量/洞 + 投影"的完整小语言，dpm 是"单表达式 + let 收束 + U/Nat/Id/Π + λ 上三种模式"的极简演算；而真正决定二者工程形状的是**元变量机器的有无**——L07 为此付出 `unification.rs` 1117 行实现（其中 ≥674 行纯为 meta 服务，dpm 全无对应物），dpm 的整个合一器只有 105 行、9 个情形、3 种结果。连带地，诊断（`Error(String)` 无位置 vs `Error{msg,pos}` + caret 渲染）与验收口径（自家孪生逐字节 parity vs Haskell 原版 golden + 13 条偏离台账）也完全不同，因此"测试数量/实现行数"只能同维度内比较，不能跨侧当质量指标。

## 代码地图

| 概念 | L07 位置 | dpm 位置 | 是否等价 |
|---|---|---|---|
| 表面语法 AST | `Raw` 12 变体（L07/parser/syntax.rs:51-68） | `Raw` 14 变体含 `SrcPos`（dpm/syntax.rs:84-112） | 形状同类，语义范围差一个数量级 |
| 顶层声明 | `Decl::{Def,Println,Enum}`（L07/parser/syntax.rs:70-84） | **无**（程序 = 单个 `Raw`，dpm/parse.rs:306-333） | **不等价** |
| 核心项 | `Tm` 16 变体（L07/mod.rs:65-94，含 `Meta`/`AppPruning`/`Decl`/`Sum`/`SumCase`/`Match`/`Obj`/`Prim`） | `Tm` 13 变体（dpm/syntax.rs:156-170） | **不等价** |
| 值 | `Val` 14 变体（L07/mod.rs:184-220） | `Val` 10 + `Ne` 4（dpm/syntax.rs:294-310, 348-358） | 骨架同源（见 03）；变体数不可直接比 |
| 模式 | `Pattern::{Any,Bind,Con}`（L07/mod.rs:99-103），构造子树 + 隐式子模式 | `Pn::{Var,Refl,Abs}`（dpm/syntax.rs:76-80） | **不等价**（dpm 无构造子模式） |
| 元变量 | `MetaVar`/`MetaEntry{Solved,Unsolved}`（L07/mod.rs:45-52）+ meta 表（:456-477） | **无** | **不等价** |
| 洞 | `Raw::Hole`（L07/parser/syntax.rs:59）→ `fresh_meta`（L07/elaboration.rs:120） | 无洞；`_` 只作 binder 名（dpm/parse.rs:523-532） | **不等价** |
| 合一器 | `Infer::unify` 23 臂（L07/unification.rs:825-1115）+ invert/prune/rename/solve/intersect | `unify`/`unify1` 9 情形（dpm/elab.rs:36-113） | **不等价**（10× 规模） |
| 模式特化状态 | `SpecSolve{solvable, acc}`（L07/unification.rs:42-45） | 合一直接返回 `Sub`（dpm/elab.rs:26-33, 42-65） | 思想等价、载体不同 |
| 顶层环境表 | `Decls`（`Rc<HashMap<SmolStr, Rc<DeclEntry>>>` + 版本号，L07/cxt.rs:18-36, 235-271） | `Ctx{names,types,env,lvl}`（dpm/context.rs:11-18），无全局表 | **不等价** |
| 错误类型 | `Error(String)`（L07/mod.rs:445-455），**无位置** | `Error{msg,pos}`（dpm/context.rs:21-25）+ `render`（:50-96） | **不等价** |
| 解析器 | 组合子 540 行（L07/parser/mod.rs）+ `preprocess`（L07/mod.rs:1713-1764） | 手写递归下降 547 行（dpm/parse.rs） | 同族，错误面差异大 |
| 测试入口 | 库内 `run(input,path_id)`（L07/mod.rs:1514-1531），不启进程 | `CARGO_BIN_EXE_dpm-nbe` 驱动真实二进制（dpm/tests/golden.rs:69） | **口径不同** |
| LSP | 本层**未接入**项目 LSP（`src/lib.rs:52` 仅 `pub mod`） | 独立 crate，25 集成测试（dpmL/tests/lsp.rs） | **不等价** |
| 依赖 | crate 16 项（Cargo.toml:137-163），层内直接用 smol_str + bumpalo | 核心 0；LSP 仅 serde_json（dpm/lsp/Cargo.toml:17-23） | **不等价** |

## 逐点对照

### D1 语言表面：变体数接近，语义范围差一个数量级

【事实】L07 的表面语言（README §2，L07/README.md:117-165）包含：`enum`（方括号隐式类型参数 + 圆括号显式索引 + 每构造子 `-> ret` 的 GADT 返回类型）、`def`（隐式/显式参数表）、`println`、`match`（嵌套模式、隐式子模式）、`.field` 投影、点号限定构造子 `Vec.cons`、洞 `_`、隐式实参 `f[A]` 与命名隐式实参 `f[x = e]`、字符串字面量、15 个 builtin（L07/cxt.rs:133-199：字符串族 / 可变全局族 / 文件 IO 族 / report_check_issue）；`U` 是唯一宇宙（无累积性）。

dpm 的表面语言（README.md:86-104 表）只有：`U`、`(x:A)->B`/`A->B`、`λ p1 … pn . t`（或 `\ p1 … pn . t`）、`let x:A=t;u`、应用、`Id A x y`/`refl`、`Nat/zero/suc/plus`、注释；语法糖仅 `succ` 同义（NOTES 偏离 12）与标识符可含 `'`（偏离 12，为读回 freshen 名）。

【差异实质】不是"少实现几条语法"，而是**缺了"用户可声明类型"这一层**：dpm 的 `Val`/`Tm` 里没有任何用户定义的型构造子/构造子，唯一的索引类型是内建 `Id`，`Nat` 也是内建。L07 靠 `Sum`/`SumCase`/`Decl` 三个变体（L07/mod.rs:67-93）撑起整个声明层。反过来，dpm 的 `Val` 变体数并不少（10+4），是因为它把 `Ne` 单列成层——变体数不能当能力指标。

【后果】dpm 无法表达 `Vec[A](len)` 这类索引族，也无法声明递归数据类型，所有依赖模式匹配的例子只能落在 `Id` 上（NOTES.md:23-31 的 `H` 例）。这**不是实现缺口**：dpm 是 `KonjacSource/dpm-nbe` 的逐行移植，原版目标就是"refl 精化索引"这一件事（NOTES.md:3-7 "faithful: the module split, the data types, the algorithm and the user-visible messages all follow the original"），`NOTES.md:281-313` 的 "Inherited limitations" 明列"no case trees / plus,suc,Id 必须全应用 / refl 不可推断 / `(!)` 不能作首模式"。应记为**范围刻意最小化**，而非"未实现"（全部源码中没有任何 TODO 承诺补上）【事实+推断】。

### D2 声明层与递归：decl 表 + 自引用占位 vs 完全没有顶层

【事实】L07 的 `Cxt.decl: Rc<Decls>`（L07/cxt.rs:235-271）是全局名字表，`def`/`enum`/`构造子` 都注册进去；项里的引用是 `Tm::Decl(name)`（L07/mod.rs:67-68），求值查表取缓存的 WHNF。递归的实现是**两阶段占位**：先 `decl_insert` 一个指向自身的 `Val::Decl(name, [])`，检查体，再用真实 WHNF 覆盖同一条目（L07/elaboration.rs:216-238；enum 同构于 :321-337，构造子注册 :338-377）。表的写时复制语义（`Rc::make_mut`，L07/cxt.rs:258-271）保证"占位只对本定义的检查可见"。

dpm 没有任何全局环境：`Ctx` 只有 `names/types/env/lvl`（dpm/context.rs:11-18），`typecheck_named` 每次从 `Ctx::empty` 起（dpm/lib.rs:56-60）；`Raw`/`Tm` 无 `Decl` 变体；`program()` 只返回一个 `Raw`（dpm/parse.rs:306-333）。因此 **dpm 不能定义递归函数**：递归性只存在于内建 `plus` 的原语归约里（dpm/eval.rs:178-189）。

【后果】(1) dpm 无法写归纳证明（`add_zero_right` 之类），只能在具体数值上做实例级证明；L07 的 `test_eq_add_comm`/`test_eq_add_assoc`（L07/tests.rs 测试名列表）正是靠递归 def + match 完成的。(2) L07 因此背上了"decl 表 COW + 占位可见性 + 递归值只求值一次"的一整套纪律；dpm 完全不需要，但也失去了表达力。(3) dpm 的 `let` 是唯一命名机制，遮蔽合法（dpm/lib.rs:275-278 `lets_shadow_correctly`）。

### D3 重定义 vs 遮蔽：一条定向报错的有无

【事实】L07 在 `def`/`enum` 注册前检查名字是否已在 decl 表（builtin / 先前 def / enum），命中即 `redefine {name}`（L07/elaboration.rs:213-215 与 :318-320），且**先类型检查后重定义检查**（注释 :210-212）；构造子裸名跨 enum 重名不报错，按最后注册解析，同时注册限定名 `Enum.case`（L07/elaboration.rs:372-376 两条 `decl_insert`）。

dpm 无此概念：`let` 可无限遮蔽（dpm/lib.rs:274-278），也没有可被"重定义"的全局名。

【后果】L07 的 `redefine` 是给 IDE 用的语义护栏（同名覆盖会让后续引用静默指向新定义）；dpm 的遮蔽是 λ 演算原生语义，不存在歧义。二者风险面不同：L07 要防"静默覆盖"，dpm 要防"作用域搞错"（已由 `Ctx::lookup` 的 de Bruijn 序覆盖，dpm/context.rs:120-127）。

### D4 元变量入口：洞 + 自动隐式插入 + λ 推断 vs 零元变量

【事实】L07 有三处产生 meta：`Raw::Hole` 在 check 模式（L07/elaboration.rs:120）与 infer 模式（:674-679，产 `?m : ?n` 一对）、隐式 Π 的自动插入（:92-100：非 λ 项 against `Val::Pi(_, Impl, ..)` 直接包一层 `Tm::Lam(_, Impl, ..)`）、λ 推断时域用 fresh meta（:555-567）。meta 的类型按当前上下文封口成 `?m <pruning>`（`Tm::AppPruning`，L07/mod.rs:513-518）。

dpm 完全没有：`Raw` 无 hole 变体，λ 不可推断（dpm/elab.rs:330 报 "Can't infer type for lambda expression"），`refl` 不可推断（:351），所以每个 λ/证明都必须**先给出完整类型**，所有参数必须显式写。`_` 只是 binder 名（dpm/parse.rs:523-532），可作 Pi/let 的占位名但不可省略。

【推断】后果有三：
1. **可写程序集合**：L07 能写 `def pr1 = f => x => f x`（L07/mod.rs:1558，DEMO 源），dpm 必须写 `let pr1 : ... = λ f x . f x`。
2. **合一器的义务**：L07 的合一必须能"解出未知"，dpm 的只需"解方程/判矛盾"——这是 D5 的根因。
3. **错误面**：L07 因为能推断，多出 "icit mismatch"（L07/elaboration.rs:594）、"no named implicit arg"（:64）、"cannot project field"（:551）这类只在推断路径上存在的错误；dpm 的错误集合小得多（D9）。

### D5 元变量机器：≥674 行纯 meta 代码，dpm 为 0

【事实·规模】L07 `unification.rs` 实现部分 1117 行（`#[cfg(test)]` 起于 :1118）：

| 函数 | 行范围 | 行数 | dpm 对应物 |
|---|---|---|---|
| `invert_go`/`invert`（spine → PartialRenaming） | :104-157 | 54 | 无（无 spine 反演概念） |
| `prune_ty_go`/`prune_ty` | :158-203 | 46 | 无 |
| `prune_meta` | :204-228 | 25 | 无 |
| `prune_vflex_go`/`prune_vflex` | :229-303 | 75 | 无 |
| `rename_sp`/`rename`/`rename_deep`/`rename_arm` | :304-652 | 349 | 无（dpm 的解直接是 `Sub`，无需回写项） |
| `solve`/`solve_with_pren` | :653-689 | 37 | ≈ `insert_sub`（11 行，dpm/subst.rs:45-49） |
| `flex_flex` | :717-759 | 43 | 无 |
| `intersect_go`/`intersect` | :761-805 | 45 | 无 |
| `unify` 本体 | :825-1115 | 291 | `unify`+`unify1`+`as_var` = 105 行（dpm/elab.rs:36-124） |

纯 meta 机制（前 8 行）= **674 行**，占该文件 60%，dpm 侧**没有任何对应实现**；再加 mod.rs 的 meta 表/快照/fresh/pruning（L07/mod.rs:456-561 的 106 行 + `v_meta` :1030-1036 + `v_app_pruning` :1078-1101），L07 为"能解未知"付出的代码 ≈ 811 行。

【事实·臂数】L07 `unify` 有 23 个 match 臂（:867-1113），其中 4 个直接处理 `Val::Flex`（同 meta :933、异 meta :936、Flex/非 Flex :963、反向 :964），2 个处理"可解 rigid"（:901/:915）；另有 L07 特有臂：`Val::Decl`（:930）、`Sum`（:983）、`SumCase`（:1003）、`Val::Match` 两条（:1034/:1089）、`Prim`（:978/:981）、宽松 String（:970/:973）。dpm `unify1` 只有 9 个情形（var-var / var 左 / var 右 / Refl-Refl / Zero-Zero / Succ-Succ 单射 / Zero-Succ 矛盾 / conv 兜底 / Idk 兜底，dpm/elab.rs:70-113）。

【事实·支撑设施】L07 还有：meta 覆写撤销日志 + 两水位快照（`meta_undo`/`MetaSnapshot`，L07/mod.rs:456-463, 483-487, 533-550，专为"可达性探测逐构造子回滚"服务）；共享 fuel 池 `UNIFY_FUEL=4096`（:479）与 `burn`（:395-402）；`Cxt.pruning`（L07/cxt.rs:240）与 `Tm::AppPruning`。dpm 侧全无：它的合一失败**没有副作用可回滚**（`unify1` 是纯函数返回 `UnifyRes`，dpm/elab.rs:70-113），也不需要 fuel（防护是 `MAX_DEPTH=512`，dpm/parse.rs:63）。

【推断】这是两侧最大规模差，且是**结构性**的：dpm 的合一在"值世界"里一次性算出 `Sub` 交给 `subst_ctx`（dpm/context.rs:174-186），因为被解的永远是一个 `Ne::Var`，解值不必变成项；L07 的 meta 解必须**存回 meta 表**并能在任意上下文被 force 出来，所以解要 quote 成 `Tm`——而把"值层解"转成"目标层级的项"正是 `rename`（349 行）的职责。**没有 meta，就没有 invert/prune/rename 这一整条链。**

> 顺带修正任务描述的一个措辞：dpm 的方程并不是"closed 值"的方程——它同样是**开值**（含 `Ne::Var(l, [])` 刚性变量）的方程。真正的区别是 **metavariable-free**：不需要"猜"，只需"解"，因此能直接产出替换，不需要解的表与回写、不需要回滚。

### D6 SpecSolve：L07 的第二条解路径，dpm 只有一条

【事实】L07 的 `unify` 带 `spec: Option<&mut SpecSolve>`（L07/unification.rs:825-833），`SpecSolve{solvable: &[Lvl], acc: Rc<Subst>}`（:42-45）：
- `spec` 非空（模式走查 / 覆盖探测）时，**bare 可解 rigid** 与任意非 Flex 值相遇即解入 `acc`（:901-914 与 :915-928 两条对称臂），环守卫 `val_mentions_lvl` 失败则 Err；
- `spec` 为空（分支体检查等常规转换）时这两条臂不成立，落到后续臂——否则 `Eq x y` 会被"证成" `Eq y y`（注释 :895-900）；
- 递归入口把方程两侧置于当前 `acc` 之下再解释（:860-865，注释称之为 dpm-nbe "剩余方程置于解之下"的惰性等价物）。

dpm 做同一件事但**不需要许可**：`unify_s` 把剩余方程逐个 `subst_val` 到新解之下（dpm/elab.rs:54-60），`unify1` 无条件解任何 `as_var`（:82-93）并把上下文层级 `g.pred()`（:84-92）。原因是 dpm 的合一**只在模式编译点被调用**（`check_pm` 的两个模式分支，dpm/elab.rs:221/247），不存在"同一条合一器还要服务常规转换"的情形。

【推断】(1) L07 用一个合一器服务两种模式，代价是 2 个 spec 臂 + 入口包裹 + `spec.as_deref_mut()` 穿透 4 个函数（`unify`/`unify_sp`/`intersect`/`loose_string`），收益是删掉了旧版 `unify`/`unify_pm` 双轨（L07/README.md:288）。(2) dpm 的"解即缩小上下文"（`g.pred()`）与 L07 的"解即替换、层级不动"（README §1.2 纪律二；`Cxt::subst_cxt` 明确"lvl/locals/pruning 不动"，L07/cxt.rs:329-333）是两种不同不变量：dpm 靠上下文收缩保证"已解变量不再出现在后续类型里"，L07 靠 σ 包裹保证"槽位布局 = 运行时布局"。

### D7 合一的第三种结果：dpm 有 Idk，L07 没有

【事实】dpm 的合一结果是三值 `UnifyRes::{Succ{lvl,sub}, Abs, Idk}`（dpm/elab.rs:24-33），`Idk` 对应 Agda 的 "I am not sure if there should be a pattern refl"（:31 注释），用于"方程既不可解也不矛盾"的场合（`unify1` :107 只判可转换，否则 :111 Idk），并在 `check_pm` 里变成一条**独立用户错误**（:235-239、:267-271，文案 `NOT_SURE` 在 :130-131）；`Abs` 则允许 `(!)` 荒谬模式（:241-266）。

L07 的 `unify` 只有二分结果 `Result<(), UnifyError>`（L07/mod.rs:425-426）；模式编译把失败一律解释为"分支不可达"（L07/pattern_match.rs:390 起 `构造子 {ctor} 与被匹配类型不相容（分支不可达）`），覆盖探测把"解得出"当可达（:276-356）。对"疑似可解但解不出"的情形，L07 用 **fuel 尾注**近似：特化方程失败文案带 `(fuel exhausted)`（L07/pattern_match.rs:386），README §7.2（L07/README.md:309-319）明说"极深嵌套模式负载下可能把合法分支误判为不可达（假 absurd）"。

【推断】这是**语义精度**差异而非实现细节：dpm（承袭 Agda 口径）不会把"不知道"误判成"矛盾"，L07 会（有界降级，靠加大 `UNIFY_FUEL` 缓解）。反向地，L07 的二分在"确实矛盾"时更简洁，且它的"不知道"窗口有确定性诊断标记（`(fuel exhausted)`），dpm 的 Idk 则是纯语义判定。

### D8 声明表 / meta 解与 σ 的可见性边界

【事实】L07 的 σ 只对**被包裹过的值**生效，代码路径可验证：`force` 只有在遇到 `Val::VSub` 时才推 σ（L07/mod.rs:605 → `frcs`）；`frcs` 对 `Val::Decl` 只包裹 spine 然后交回 `force`（:727）；而 `force` 的 `Val::Decl` 臂直接取 decl 表里缓存的 WHNF 并 `v_app_sp`（:629-641），**全程不接触 σ**；`Val::Flex` 的已解展开同样只是 `v_app_sp(t_solved, sp)`（:591-599），不带 σ。

【推断】于是 README §1.3 末段（L07/README.md:92-95）声称的边界是代码级事实：**decl 表条目与 meta 解值不在 σ 的扫描/包裹范围内**；若某个 def 的缓存值里含稍后被模式特化的槽位，精化在该读点不可见。

【后果】这是 L07 独有的问题域——**只有存在全局定义或元变量解时才会出现**。dpm 两者都没有（无 decl 表、无 meta 解），因此根本不需要"可见性边界"这条纪律；反过来说，L07 的这条边界是它为"decl 表 + meta"付的额外概念债（README 明确要求孪生移植对齐同一取舍，L07/README.md:94-95），若未来 L07 要与 dpm 语义完全对齐，这是最先暴露分歧的点。

### D9 诊断：`Error(String)` 无位置 vs `Error{msg,pos}` + caret 渲染

【事实】L07 的错误类型就是 `pub struct Error(String)`（L07/mod.rs:445-455），**不含任何 span/位置**，`run` 返回 `Result<String, Error>`（:1514）。虽然 `Raw`/`Tm` 到处带 `Span<String>`（L07/parser/syntax.rs:1, 51-68），但约 24 处 `Error(...)` 构造点（L07/elaboration.rs 与 pattern_match.rs）全部丢弃 span，只留文案；解析层更粗：`parser()` 把所有失败折叠成 `"parse error"`（L07/parser/mod.rs:125, 128），只有"残余 token"一种情况带字节偏移（`leftover token ... @ start_offset,end_offset` 形态，:119-123）。

dpm 的错误是 `Error{msg, pos: Pos{file,line,col}}`（dpm/context.rs:21-25），`Pos` 由 `Raw::SrcPos` 在每个 atom/raw 层附加（dpm/parse.rs:335-345, 471-520）；`Error::render` 输出 `file:line:col` + 源码行 + caret（dpm/context.rs:50-70），并带两道防灌屏截断：行窗口 `MAX_ECHO=160`（:30）与名字截断 `MAX_NAME_ECHO=64`（:35, :38-46）。解析器报**最远失败位置**（`best`，dpm/parse.rs:92-95, 306-333）。

【推断】后果：
1. **定位粒度**：L07 只能定位到"哪次 `run` 失败"级，文案里印的是 pretty 后的项；dpm 能定位到字符列并画 caret（README.md:47-63 直接展示）。对 IDE 体验是数量级差异。
2. **可恢复性**：L07 侧项目确有 `src/parser_lib_resilient.rs`（`or_far` 最远失败合并，:24-45），但 L07 的 `parser` **没有用它做错误恢复**——只复用组合子框架，仍整体折叠为 `Err`（L07/parser/mod.rs:104-130）。dpm 的 LSP 则显式采用两层策略：诊断只来自真解析器/真展平器，hover/补全用独立的宽松镜像语法（dpmL/README.md:113-117; dpmL/src/analysis.rs:1037-1061）。
3. **文案风格**：L07 中英混排（`can't unify A == B`、`缺少构造子`、`分支不可达`），dpm 全英文且**逐字节对齐 Haskell 原版**（golden.rs:76-93 直接抄 `Elab.hs` 常量）。这决定了两侧"可被逐字节钉住"的测试面不同。

### D10 解析器与预处理：组合子 + 注释剥离 vs 手写递归下降 + 深度预算

【事实】L07：`preprocess` 先按词法规则把注释替换为空白（字符串内不生效，行/块注释都支持、块不嵌套，L07/mod.rs:1707-1764），再 `lex::lex` 切 token（L07/parser/lex.rs 306 行），最后组合子 `p_decl` 解析（L07/parser/mod.rs:104-130）；`EndLine` 是显式 token，`match` 臂与 enum case 分隔都放宽为 `EndLine+`（:419-433, :484-496）。

dpm：无独立 lex 层，手写递归下降直接在 `Vec<char>` 上走，`skip_ws` 处理空格与两类注释（dpm/parse.rs:1-18 的语法注释），对每个候选完全回溯（NOTES 偏离 11），`MAX_DEPTH=512` 是**共享预算**，覆盖 raw/atom 递归、应用实参数、binder 组数、λ 模式数（dpm/parse.rs:55-63, 338, 371, 401, 410, 463, 473），超限报 "expression nesting is too deep"（:312-319）。

【推断】(1) 防爆栈策略不同：dpm 在**解析器内部**设预算（解析器跑在调用者栈上），L07 把防爆栈外包给大栈线程（L07/tests.rs:15-23 用 64 MB；tests/l07_fast_parity.rs:28-47 用 256 MB）。(2) 错误粒度：dpm 有最远失败位置，L07 折叠（D9）。(3) 语法糖代价：dpm 为可读回把 `succ` 变保留字（NOTES 偏离 12 明说是有意取舍）；L07 的读写不对称留在别处（打印 `Vec::cons`、读入 `Vec.cons`，L07/pretty.rs:180-205 vs L07/elaboration.rs:459-472）。

### D11 运行契约与程序形态：println 串 vs 单表达式 + 退出码

【事实】L07 的程序是**声明序列**，`run` 顺序 elaborate 每个 decl，只把 `DeclTm::Println` 的结果拼进返回值（L07/mod.rs:1517-1529）；类型错误/覆盖错误在遇到时立即 `Err`，已输出的 `println` 内容随 `Err` 一起丢弃（`run` 直接 `?`，:1523）。

dpm 的程序是**单个表达式**，CLI 两个模式：`nf` 打印「normal form，换行，两空格 + `:`，换行，type」、`type` 只打印类型（dpm/lib.rs:82-99）；退出码契约明确：成功 0、解析/展平错误 1（stderr + caret）、stdin 读失败或线程起不来 2、worker panic 101、`--help`/无参/未知参数 → 用法到 stdout 且 0（dpm/main.rs:21-33, 45, 57, 79, 84；NOTES 偏离 9）。

【推断】这决定了"同一件事怎么观察"：L07 的可观测面是"N 行 println 输出"，dpm 的可观测面是"一个 nf + 一个 type + 退出码"。二者都不提供"只检查不输出"的模式（L07 的 `bench_check` 例外，L07/mod.rs:1619-1629），因此**跨侧做 golden 对比必须先把输出形态对齐**，否则第一行就会不等。

### D12 测试与验收口径：孪生 parity vs 外部原版 golden

【事实·L07】(1) 库内 48 个 `#[test]`（实测计数 48，`src/L07_sum_type/tests.rs`），全部经 `run()` 驱动，跑在 64 MB 栈线程（tests.rs:15-23）；(2) 黑盒三套实测 `#[test]` 数：`tests/l07_blackbox.rs` 49、`l07_blackbox_v2.rs` 53、`l07_blackbox_v3.rs` 47（v3 另经 `#[path]` 引入 `mod.rs`，:1001-1010，故 lib 测试在其中再跑一遍），唯一入口 `L07_sum_type::run`（l07_blackbox.rs:5-6），**不启进程**（三套 `Command::new` 计数 0）；(3) `tests/l07_fast_parity.rs` 23 个测试，把 `run` 与孪生 `run_fast` 对撞：**Ok 输出逐字节相等、Err 只要求判定一致**（:49-65 `assert_parity`），覆盖 DEMO 全串、tests.rs 全部用例源码、错误例、深负载、稳态复用。即 L07 的 oracle 是**自己第二份实现**。(4) 工程根另有 60+ 个 LSP/引擎测试文件，但测的是 L13 生产引擎；grep 全部 `src/**/*.rs`，`L07_sum_type` 只出现在 `src/lib.rs:52` 的 `pub mod`、`src/bin/l07*.rs` 与 L07 自身目录。

【事实·dpm】(1) 113 个库内 `#[test]`（实测：lib 41 / eval 18 / parse 17 / elab 13 / pretty 10 / syntax 6 / context 4 / subst 4 = 113，与 README.md:9 一致）；(2) `tests/golden.rs` 7 个测试 / 116 条表格检查（OK 表 :100、ERR 表 :422 带 `(line,col)`、PARSE_ERR 表 :531），经 `CARGO_BIN_EXE_dpm-nbe` **驱动真实二进制**（:69），断言 stdout/stderr/退出码与 caret 列逐字节；(3) 期望值来源被明确写死为 **Haskell 原版**而非 Rust 实现（golden.rs:3-14），端口自身行为用 `_DEVIATION` 命名约定标记（:31-63）——这与 NOTES 的 13 条偏离清单一一对应；(4) LSP 独立 crate 25 个集成测试（实测 25，与 dpmL/README.md:126 一致）；(5) `reviews/robustness/` 有 fuzz 语料与发现（`findings/*.txt|bin` 千级）、PowerShell harness 与结果 JSON（`harness/*.ps1`、`results_*.json`）。

【推断·可比性】三句话：(a) L07 的验收是**内部一致性**（两份独立实现互证 + 错误文案被黑盒钉住），dpm 的验收是**外部符合性**（与原版逐字节对照 + 每条偏离有测试）；(b) 因此"dpm 测试少"是假象——7 个 golden 测试塞了 116 条检查，且每条跨进程验证；(c) 反过来 L07 的测试数里有相当比例是重复覆盖（v3 与 fast_parity 通过 `#[path]` 把 lib 测试又跑一遍），拿测试数比强度会失真。

### D13 依赖、体量与性能口径

【事实·依赖】L07 所在 crate `[dependencies]` 16 项（lsp-types / lsp-server / walkdir / serde / serde_json / toml / ropey / bumpalo / log / colored / crossbeam-channel / dashmap / smol_str / codespan-reporting / clap / rustc-hash，外加 mimalloc，Cargo.toml:137-163）——但 L07 层**实际直接用**的只有 `smol_str`（`SmolStr`，L07/mod.rs:33）与孪生的 `bumpalo`，其余服务项目 LSP 面。dpm 核心 crate 依赖为空（dpm/Cargo.toml:23-24），LSP crate 仅 `serde_json`（dpm/lsp/Cargo.toml:17-23），注释明确"保持库与 CLI 的 zero-dependency identity"。

【事实·实现行数】（`#[cfg(test)]` 之前的行数，排除测试/文档/LSP）：

| 组件 | L07 参考版 | L07 孪生 `bump_spine_iter/` | dpm |
|---|---|---|---|
| 核心类型/语法 | syntax.rs 24 | syntax.rs 248 | syntax.rs 408 |
| 解析 | parser/ 540+306+94 = 940 | （复用参考版 parser，entry.rs:355） | parse.rs 547 |
| 检查/展平 | elaboration.rs 725 | machine.rs 1833 | elab.rs 381 |
| 合一/特化 | unification.rs 1117 + pattern_match.rs 658 | unify.rs 885 + compiler.rs 590 | （含在 elab.rs）105 |
| 求值/force/quote | mod.rs 1588（含 meta 表、force、eval、quote） | eval 465 + force 720 + quote 465 | eval.rs 507 |
| 其它 | cxt 329 + struct_eq 351 + pretty 279 | 其余 10 文件 2967（含 rename 846 / struct_eq 411 / subst 323 / entry 336 / prim 302） | subst 56 + pretty 155 + context 187 + lib 105 + main 87 |
| **合计** | **≈6011** | **≈7925** | **≈2433**（+ LSP 1872） |

【推断】核心实现 6011 / 2433 ≈ **2.5×**；把 L07 的"性能孪生"算进工程总投入则 ≈ 5.7×；单看合一器 1117 / 105 ≈ **10.6×**。差异主项就是 D5 的 meta 机制 + D1 的 Sum/GADT 层。

【事实·性能口径】L07 有专用 bench bin `src/bin/l07bench.rs`（workload：church/strchain/global/match/enum/natadd，clap 参数，mimalloc），README §10 给出 release 下 min-of-rounds 实测与 15×/27×/18×/3×/5× 的孪生加速比（L07/README.md:417-496），另有深值栈安全轮的 A/B 方法学（独立 worktree、交错 10 轮取 min，:498-506）。dpm 没有 `benches/` 目录（实测不存在），性能只以**复杂度回归测试**出现：`generated_transitivity_proofs_scale_polynomially` 断言 n=1..30 全跑完 < 10s（dpm/lib.rs:344-358，实现 :153-163），NOTES 偏离 4 记录"分层替换把 2^n 变二次"的实测（trans60: 16 ms，NOTES.md:116-141）。即：L07 测"多快"，dpm 钉"不退化"。

### D14 IDE 面：L07 未接入 LSP，dpm 有完整 LSP

【事实】L07 层只导出 `run`/`run_fast`/`bench_check`/`DEMO_SRC` 等（L07/mod.rs:1514, 1619；bump_spine_iter/entry.rs:347）；项目的语言服务器服务的是 typort 语言、引擎是 L13（`src/lib.rs` 里 60+ 处 `L13_namespace::` 调用，如 :100-104, :1311），L07 只在 `src/lib.rs:52` 被 `pub mod` 导出供测试/bench 使用。README §6 的"深值栈安全轮（2026-09-18，LSP 接入前置）"说明接入尚未完成（L07/README.md:301）。

dpm：`lsp/` 是独立 crate，功能表列出 diagnostics / hover / completion / definition / documentSymbol / tokens / evaluate / pull-diagnostics（dpmL/README.md:17-27）；诊断代码 `analysis::diagnostics` 直接复用 `parse_named`/`typecheck_named` 并把 `Error` 映射成 LSP range + `data.rendered` 的 caret 图（dpmL/src/analysis.rs:1037-1088），超过 200 KiB 拒绝检查并降级为 warning（:1034-1051）。

【推断】这是工程面上最实质的不对称：**dpm 的库 API 就是为 IDE 服务的**（`typecheck_named(src, file)`、`run_named`、bounded parser、`Error::render`、panic 捕获成 `internal-error`，dpmL/README.md:136-143），L07 的 API 是"测试/bench 友好"的（无文件参数、无位置、整串 `run`、靠调用方开大栈）。若目标是把 L07 做成可比 dpm 的产品级实现，缺口不在算法而在 D9/D14（错误携带位置 + 有界/可恢复解析 + 库 API 分层）。

## 可观测的语义差异

按各自语法书写；L07 侧走 `run(src, 0)`，dpm 侧走 `dpm-nbe nf`。标【推断】者由代码推出、未实际运行。

| # | 程序 | L07 | dpm | 依据 |
|---|---|---|---|---|
| 1 | 推断 λ 类型 | `def pr1 = f => x => f x` **接受**（域用 fresh meta） | `\ f . \ x . f x` **拒绝**：`Can't infer type for lambda expression` | L07/elaboration.rs:555-567；dpm/elab.rs:330 |
| 2 | 洞 | `def ck(x: Nat): Nat = _` 后 `println "ok"` **接受**（可打印 `?0`） | 无洞语法；`_` 仅 binder 名 | L07/mod.rs:155；dpm/parse.rs:523-532 |
| 3 | 无标注隐式实参 | `enum Eq[A](x:A, y:A) { refl[a:A] -> Eq[A] a a }` + `def ok: Eq zero zero = refl` **接受** | 不适用（无用户 enum）；`refl` 必须能推出完整 `Id` | L07/elaboration.rs:92-100；dpm/elab.rs:160-176 |
| 4 | 递归定义 + 归纳证明 | `def add(x,y) = match x {...}` + `add_comm`/`add_assoc` **接受** | 无法定义递归函数，只能在 `plus` 原语上做实例证明 | L07/elaboration.rs:216-238；dpm/eval.rs:178-189 |
| 5 | Nat 上模式匹配 | `match n { case zero => .. case succ(k) => .. }` **接受** | **语法上不可能**（`Pn` 无构造子模式），`λ zero . t` 把 zero 当变量名 | L07/parser/syntax.rs:16-19；dpm/syntax.rs:76-80 |
| 6 | 重定义 | 两个 `def Nat` → `redefine Nat` **报错** | `let x:Nat=zero; let x:Nat=suc x; ...` **接受**（遮蔽） | L07/elaboration.rs:213-215；dpm/lib.rs:274-278 |
| 7 | 未解 meta 落盘 | 分支体写 `_` 后 `println "final"` **通过**（不检查未解 meta） | 不适用（无 meta，写不出占位证明） | L07/tests.rs:695-736；全层无 "unsolved meta" 文案 |
| 8 | 声明表被特化后的可见性 | def 的缓存值若引用稍后特化的槽位，**精化在 decl 读点不可见**（σ 不扫 decl 条目） | 不适用（无 decl 表） | L07/mod.rs:605, 629-641, 727；README §1.3 |
| 9 | 同一类型错误的定位 | `can't unify Nat == Bool`（无位置、无源码行） | `<stdin>:1:17:` + 源码行 + caret + 消息 | L07/mod.rs:1317-1333；dpm/context.rs:50-70 |
| 10 | "不知道"方程 | 无第三结果；失败 = 分支不可达，fuel 耗尽时附 ` (fuel exhausted)` | `I am not sure if there should be a pattern 'refl' for equation between plus m zero and succ zero.` | L07/pattern_match.rs:386-391；dpm/elab.rs:130-131, 235-239 |
| 11 | 打印产物可读回 | 打印 `Nat::succ(..)`/`Vec::cons(..)`，读入用 `Vec.cons` → **输出不是合法输入** | 打印 `succ (succ zero)`，解析器接受 `succ` → **可读回**（除 `⊥`） | L07/pretty.rs:180-205 vs L07/elaboration.rs:459-472；dpm/NOTES.md:253-265 |
| 12 | 卡住的 match 打印 | `match m { ... } j` 形态（pending 实参在分支外层应用） | 卡住的模式 λ 直接打印成 λ 本身（保留源模式名），部分应用按「饱和」规则补满 | L07/tests.rs:646-670；dpm/NOTES.md:106-114, 288-290 |

## 机制有无矩阵

### 5.1 类型系统能力面（逐项"哪侧有"）

| 能力 | L07 | dpm | dpm 缺的性质 |
|---|---|---|---|
| 和类型 / 枚举声明（多构造子） | 有 `enum`（L07/parser/mod.rs:477-504） | 无 | 刻意最小化（原版只有内建 Nat） |
| GADT 风格构造子返回类型 `-> ret` | 有（L07/elaboration.rs:284-299） | 无 | 刻意最小化（唯一索引类型是 `Id`） |
| 隐式方括号参数 + 自动插入 | 有（L07/parser/mod.rs:321-337；插入 L07/elaboration.rs:92-100） | 无 | 刻意最小化（全显式） |
| 命名隐式实参 `[x = e]` | 有（L07/parser/mod.rs:266-270, 300-302） | 无 | 刻意最小化 |
| 索引族（构造子索引等式） | 有（`Sum` 参数逐槽合一，L07/unification.rs:983-995） | 仅 `Id` 的索引（无用户索引族） | 刻意最小化 |
| 元变量 / 合一求解 | 有（L07/mod.rs:456-477, unification.rs） | 无 | 刻意最小化（故 λ/refl 不可推断） |
| 洞 `_` | 有（L07/parser/syntax.rs:59） | 无 | 刻意最小化（`_` 只剩 binder 名） |
| 投影 `.field` | 有（L07/elaboration.rs:459-553） | 无 | 刻意最小化 |
| 限定构造子 | 有（`Enum.case`，L07/elaboration.rs:372-376） | 无（无构造子） | 随构造子一并缺失 |
| 递归定义 / 顶层声明 | 有（decl 表 + 占位，L07/elaboration.rs:216-238） | 无 | 刻意最小化（程序 = 单表达式） |
| Π 类型 / 依赖函数 | 有 | 有（dpm/syntax.rs:92, 160） | — 等价 |
| 宇宙 `U` | 有（单一 `U`，无累积） | 有（单一 `U`） | — 等价 |
| 自然数 | 用户定义 enum（L07/mod.rs:1541-1544 的 DEMO） | 内建 `Nat/zero/suc/plus`（dpm/syntax.rs:101-107） | 等价能力，不同实现层 |
| 等式类型 | 用户定义 enum `Eq`（测试源）/ `Id` 风格 | 内建 `Id` + `refl`（dpm/syntax.rs:96-99） | 等价能力 |
| 构造子模式匹配 | 有（`Pattern::Con`） | 无（`Pn` 只有 Var/Refl/Abs） | **语义范围差异**（非"未实现"） |
| 荒谬模式 `(!)` | 无（用"分支不可达"报错代替） | 有（dpm/syntax.rs:108-109, elab.rs:241-266） | L07 无此语法，但可达性判定等价 |
| η 展开 | 有（L07/unification.rs:947-962） | 无（NOTES "Inherited limitations"） | 刻意最小化 |
| 无 K 的安全保护 | 无（README §7.3 明说教学取舍） | 无（NOTES:12 "with-K implementation"） | — 两侧一致 |

> 结论（对应问题 a）：dpm 缺的每一项都能在原版 `NOTES.md:281-313` 的 "Inherited limitations" 或语言表（README.md:86-104）里找到范围依据，**没有一项带"未实现/TODO"标记**；L07 多的每一项都能追到"元变量 + 声明层"这两个根。故应表述为"范围差异"，而不是"实现进度差异"。

### 5.2 机制清单

| 机制 | L07 | dpm | 备注 |
|---|---|---|---|
| 用户定义数据类型（enum / 构造子） | 有 | 无 | dpm 只有内建 Nat/Id |
| GADT 返回类型（`-> ret`） | 有 | 无 | L07/elaboration.rs:284-299 |
| 索引族 + 索引等式 | 有（`Sum` 参数逐槽合一） | 仅 `Id` 的索引 | L07/unification.rs:983-995 |
| 隐式参数 / 自动插入 | 有（`Icit::Impl` + pruning） | 无（全显式） | L07/elaboration.rs:92-100 |
| 命名隐式实参 `[x = e]` | 有 | 无 | L07/parser/mod.rs:266-270 |
| 洞 / 元变量 / 解的表 | 有 | 无 | L07/mod.rs:45-52, 456-477 |
| meta 快照回滚（undo-log） | 有 | 无 | L07/mod.rs:483-550 |
| invert / prune / rename / solve / intersect | 有（674 行） | 无 | L07/unification.rs:104-805 |
| flex-flex 双向尝试 | 有 | 无 | L07/unification.rs:717-759 |
| 合一的第三种结果（Idk） | 无 | 有 | dpm/elab.rs:31, 111 |
| 可解 rigid（`SpecSolve`） | 有 | 无（无条件解 var） | L07/unification.rs:42-45 |
| 合一深度燃料 | 有（4096 + 尾注） | 无 | L07/mod.rs:479 |
| 顶层声明表 / 递归 def | 有 | 无 | L07/cxt.rs:235-271 |
| 重定义检查 | 有 | 无（遮蔽） | L07/elaboration.rs:213 |
| 投影 `.field` | 有 | 无 | L07/elaboration.rs:459-553 |
| 限定构造子 | 有（`Enum.case` / 打印 `::`） | 无 | L07/elaboration.rs:372-376 |
| 字符串字面量 / builtin / 全局 / 文件 IO | 有（15 个 builtin） | 无 | L07/cxt.rs:133-199 |
| σ 的可见性边界（decl/meta 解不扫） | 有这条边界（需纪律） | 不存在该问题 | L07/README.md:92-95；D8 |
| 带位置的错误 + caret 渲染 | 无 | 有 | L07/mod.rs:445 vs dpm/context.rs:50-96 |
| 解析深度预算 | 无（靠大栈） | 有（512 共享预算） | dpm/parse.rs:63 |
| 可恢复解析 | 框架在（resilient），L07 未用 | LSP 层宽松镜像语法 | L07/parser/mod.rs:104-130；dpmL/README.md:113-117 |
| 真实 LSP | 无（本层未接入） | 有（独立 crate，25 测试） | src/lib.rs:52；dpmL/tests/lsp.rs |
| 黑盒驱动真实二进制 | 无 | 有（golden + 退出码） | tests/l07_blackbox.rs:5-6；dpm/tests/golden.rs:69 |
| 双实现 parity oracle | 有（run vs run_fast） | 无（原版不便进 CI） | tests/l07_fast_parity.rs:49-65 |
| 性能 bench | 有（l07bench，7 workload） | 无（只有复杂度断言） | src/bin/l07bench.rs:1-26 |
| 模糊测试资产 | 无 | 有（reviews/robustness/fuzz） | dpm/reviews/robustness/ |

## 存疑与待核实

1. 【存疑】L07 的测试计数口径：README §8（L07/README.md:353-401）声称 48 库测 + 49/53/95 黑盒 + 70 parity；我实测 `#[test]` 为 48 / 49 / 53 / 47 / 23。v3 的 95 可由 `47 + 48`（`#[path]` 引入 lib 测试）解释，但 parity 的 70 与 `23 + 48 = 71` 差 1；若把 `mod.rs` 里另外 6 个 `#[test]`（mod.rs 3 + unification 1 + entry 1 + lex 1）也算，v3 应为 101。可能 README 只数 tests.rs 的 48，但我未能确定。**引用测试数时建议直接用实测 `#[test]` 计数。**

2. 【存疑】L07 是否真的完全未接入 LSP：依据是"grep 全部 `src/**/*.rs`，`L07_sum_type` 只出现在 `src/lib.rs:52` 与 `src/bin/l07*.rs`"。若存在按 feature 或运行时字符串选择层的路径（例如配置项里写 "L07"），按类型名 grep 可能漏掉；我没有通读 `src/config.rs`/`src/ls.rs`。

3. 【推断未验证】dpm 的"上下文收缩"（`unify1` 返回 `g.pred()`，dpm/elab.rs:84-92）与 L07 的"层级不动 + σ 包裹"（L07/cxt.rs:329-333）在**多方程顺序**下是否对每个用例给出相同精化：dpm 用 `subst_sub` 组合（dpm/eval.rs:30-57），L07 在 unify 入口按当时 `acc` 重新包裹（L07/unification.rs:860-865）。二者"后解覆盖先解"的语义我读了注释但未构造反例。

4. 【推断未验证】"L07 不报告未解 meta"的结论依据是：全层 grep 无 "unsolved" 错误文案，且 `test_hole_in_branch`（L07/tests.rs:695-736）在分支体留 `_` 仍断言成功。但 `run()` 的输出只来自 `println`（L07/mod.rs:1514-1531），所以"洞被静默接受"也可能被上层另行检查——L07 层内确实没有任何这种检查。

5. 【存疑】dpm `main.rs` 的 panic 兜底（捕获后 `ExitCode::from(101)`，dpm/main.rs:71-80）与 LSP 的 `internal-error` 诊断是否覆盖全部 panic 点：`Raw::Bot` 的 `panic!("infer: impossible (Bot)"`（dpm/elab.rs:372）我未构造触发输入（NOTES 未列该点）。

6. 【存疑】两侧"深值"边界不可直接对比：L07 记录 `struct_eq`/occurs/rename 已迭代化但 `quote/pretty` 仍递归（L07/README.md:330-340），dpm 全靠 `MAX_DEPTH` + 64 MiB 栈（NOTES.md:210-231）。哪一侧在 10^5 层值上先失败，我没有实测（需运行两侧二进制）。

7. 【存疑】L07 的 `redefine` 只查 def/enum 名，不查构造子裸名（跨 enum 重名按最后注册），这与 README §2（L07/README.md:145-148）一致；但"裸名最后注册"与限定名 `Enum.case` 同时存在于同一张表（L07/elaboration.rs:372-376），是否存在"裸名被后注册覆盖后，先前构造子的**类型**仍被缓存在某个值里"的用例，我未追（属 02 维度的合一细节）。

## 给 Lead 的三条要点

1. **元变量是两侧规模差的唯一主因，也是最不可移植的部分**：L07 `unification.rs` 1117 行里 ≥674 行（invert/prune/rename/solve/intersect/flex_flex）纯粹为"解未知"服务，dpm 对应物是 105 行一阶合一器（10.6×）。汇报"L07 比 dpm 复杂多少"时这是最硬的数字；同时要说明不是 L07 写得啰嗦——dpm 能这么小，是因为它的语言里**根本没有可解未知**（λ 不可推断、refl 不可推断、全显式参数）。

2. **能力矩阵必须按"刻意最小化 vs 未实现"分层叙述，否则会误导结论**：dpm 缺 enum/GADT/隐式/洞/投影/递归定义，是原版 `KonjacSource/dpm-nbe` 的范围选择（NOTES.md:3-7 "faithful" + :281-313 "Inherited limitations"，无任何 TODO 承诺补上），不能当实现质量差距；真正可比的是"依赖模式匹配精化"同一件事的机制（dpm 的 `unify`+`Sub` vs L07 的 `SpecSolve`+`Subst`+`VSub`）。L07 多出来的 meta 机器与它多出来的语言表面（隐式参数/洞/推断）是同一枚硬币的两面。

3. **工程面上真正的不对称是诊断与 API，而非算法**：L07 的 `Error(String)` 无位置（L07/mod.rs:445）、解析错误折叠为 `"parse error"`（L07/parser/mod.rs:125-128）、本层未接入 LSP（仅 `src/lib.rs:52` 导出）；dpm 的 `Error{msg,pos}`+`render` 带行/列/caret、被 golden 逐字节钉住、并被 LSP 直接复用（dpm/context.rs:50-96；dpmL/src/analysis.rs:1037-1088）。若结论要包含"L07 能否承担 dpm 的工程位"，这两条（错误携带位置、有界/可恢复解析）最需要点名，且它们**独立于模式匹配算法**。

---

*核实方式：本文所有行号为 2026-10-30 在本地仓库实测（`Get-ChildItem` 计行数、`Select-String` 定位符号、分段 `read` 精读），未运行任何测试或二进制；标【推断】者未实测。未引用 `docs/l07-dpm-refactor-design.md` 的任何断言。*
