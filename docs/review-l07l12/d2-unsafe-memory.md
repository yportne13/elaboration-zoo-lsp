# D2 unsafe 与内存安全(孪生版 packed-word 与 bump arena) — L07–L12 只读评审

## 1. 结论(verdict)

- **P0: 0  P1: 1  P2: 2  P3: 2  needs-verify: 1**
- 覆盖范围与方法:
  - `grep -n "unsafe"` 枚举六个模块全部 unsafe 块(共 109 处 `unsafe {`:`bump_spine_iter.rs` 六层 103 处 + `parser/lex.rs` 六层 6 处),逐类审计:packed-word tag 解引用(3×6)、`string_concat` 手工拼接(1×6)、lexer `get_unchecked`(1×2 块 ×6)、`'static`↔`'a` 缓冲洗白 transmute(L07 10 处 / L08 10 / L09 16 / L10 14 / L11 16 / L12 19,含 L11/L12 特有 `DECLB_CACHE` 与 L12 特有 `MetaSnap`)。
  - 精读 L07 蓝本 `bump_spine_iter.rs` 全文(7672 行),建立不变式清单(tag 编码/轮界纪律/缓冲借用纪律),再对 L08–L12 做机械 diff(与 L07 差异行 L08=1116、L09=6983、L10=8763、L11=8597、L12=8656)并对全部 `V(` 构造点、`v_clo_of/v_pi_of/v_xcell_of` 消费点、各层 `clear_round`/Tycker 入口做定点核对。
  - lexer 侧下钻 `parser_lib.rs` 的 `Pattern for F: FnMut(char)->bool` 实现(pmatch/is 的边界来源)验证 `get_unchecked` 论证。
  - git 只读(log)核对 `7cfbb8e`(宽松臂 tag 检查 P0 修复回灌)、`dbe79cf`(L10/L11/L12 燃料池)是否覆盖到全部六层。
  - 未运行 cargo(按 BRIEF 硬约束),全部结论为静态推理。

## 2. 发现列表

### [P1][needs-verify] vapp1 的 Clo 臂尾调 eval_iter 会 clear 调用方尚有 pending 项的共享 work 缓冲——"嵌套调用点进入时缓冲必为空"不变式存在反例(影响面:全部六层)

- 位置:
  - `src/L07_sum_type/bump_spine_iter.rs:1175-1180`(vapp1 Clo 臂)、`:2049-2051`(eval_iter 入口 `work.clear()`/`vals.clear()`)、`:2212-2222`(W::ChainWrap 无守卫 vapp1)、`:2285-2297`(W::AppPrunOne)、`:1208-1213`(VSub 臂)、`:4895-4899`(被违反的字段级不变式声明)
  - 同构分叉:`src/L08_product_type/bump_spine_iter.rs:1175`、`src/L09_mltt/bump_spine_iter.rs:939`、`src/L10_typeclass/bump_spine_iter.rs:895`、`src/L11_macro/bump_spine_iter.rs:924`、`src/L12_canonical/bump_spine_iter.rs:964`
- 证据:
  ```rust
  // L07:1175  vapp1 的 Clo 臂——把调用方传进来的 work 原样交给 eval_iter:
  if v_tag(f) == 1 {
      let c = v_clo_of(f);
      let env = env_ext(bump, c.env, a);
      eval_iter(bump, spine, work, vals, icits, ..., env, c.body)   // 入口即 work.clear()
  ```
  而 L07:4896 字段注释声明的不变式是:"eval/quote/unify 共用一个 workbuf 是安全的:work 是「排空即返回」的暂存栈,**嵌套调用点(eval_iter → solve → eval_iter)进入时它必已为空**"。该声明对 `unify_iter → solve → eval_iter` 成立,但对 **eval_iter 自己经 vapp1 的重入**不成立:
  - `W::Apply`/`W::AppPrunOne` 只对 `v_tag==1`(裸闭包)内联 β,非 clo 一律进 vapp1;`W::ChainWrap` 的链头完全无守卫直进 vapp1。
  - vapp1 的 `XCell::VSub` 臂(L07:1208)`force` 后**递归再入 vapp1**:若 force 产出闭包(被解槽的值是 λ,或 frcs 对闭包 env 逐槽包裹后返回的新 `CloCell`),第二次 vapp1 命中 Clo 臂 → `eval_iter(work.clear())`——此刻外层 eval_iter 的驱动循环里可能还有 pending 项,被整体清掉。
- 机制/影响(反例构造):VSub 头只在显式替换精化上下文出现——match 臂入口 `subst_cxt` 把上下文**全部** env 槽包成 `VSub(·, σ)`(L07:5404-5452;σ 非空即包裹,`case true` 这类无 GADT 方案的 Con 臂也会因头部精化使 σ 非空)。于是精化臂内任何"被包裹的函数槽被应用、且该应用不是当前 eval 的最右 spine 尾"的编译期求值都命中:
  1. eval 驱动:`Tm::Let` 臂压 `LetBody` 后继续在同一 eval 内求值定义项(L07:2092-2095);定义项 `(g zero)`、g 为臂外 `let g = λ…` 的槽(已被 subst_cxt 包裹)→ 下钻 `Var(g)` 得 VSub 头(非 clo)→ `vals.push` + `ChainWrap(1)` → ChainWrap 弹出时 `vapp1(VSub)` → force → clo → vapp1(clo) → `eval_iter(work.clear())` 抹掉 `LetBody` → 外层循环 work 空、提前退出,`vals.pop()` 返回内层结果——**let 体静默丢失**。
  2. 可达的编译期入口:精化臂内 `check(Raw::Let)` 对定义项整值求值(L07:5646 `vt = self.eval(..., t_tm)`,cxt 即带 VSub 槽的 `cxt_arm`)、`t_tm` 本身是嵌套 let(内层 let 的定义项应用 g)时即命中;quote 的 Match 分支体重求值(L07:2542)与 unify 的 `MatchBranch`(L07:3181)以被包裹 env 整体重求值分支体,同理。
  3. 后果:编译期求值结果错误 → define 槽/类型求值/分支体比较拿到错值 → 错误的 meta 解或错误的 unify 判定,属**静默错误结果**一类;因触发需要"精化 + 嵌套 let/复合头 + 函数槽被应用"三者叠加,现有 parity/内部测试未覆盖(全绿)。
  - 该问题不是内存不安全(clear 合法,丢的是逻辑层数据),故按 P1 报;若能演示"应拒绝的程序被静默接受"可升 P0。
- 处置建议:vapp1 的 Clo 臂改为与 `W::Apply` 一致的内联尾推(`work.push(W::Tm(c.body, env_ext(...)))` 返回哨兵)或在 eval_iter 入口 clear 前加 `debug_assert!(work.is_empty())` 并以回归用例钉住;六层同修。

### [P2] `Rc<SubstV>` 嵌入 bump 分配的 `XCell::VSub`——bump reset 不跑 Drop,σ 链跨轮泄漏,长期存活的 Tycker 无界增长(影响面:全部六层)

- 位置:`src/L07_sum_type/bump_spine_iter.rs:307-313`(`XCell::VSub { val: V, sub: Rc<SubstV> }`)、`:487-496`(`wrap_sub` 每次 `sub.clone()` 后 `bump.alloc`)及各层同名(frcs_env / subst_cxt 的逐槽包裹是高产点,L07:5421-5429、1818-1841)。
- 证据:bumpalo 从不运行析构函数;`XCell::VSub` 里的 `Rc<SubstV>` 强引用随 bump reset 一起被"遗忘",计数永不归零,`SubstV`/`SubEntryV` 链(及其 `val: V` 引用的概念存活)只在进程结束释放。每个包裹点(模式编译的每个读点、每个臂的每槽 subst_cxt)泄漏一个强引用;多轮复用的 `Tycker`(LSP 会话常驻,L07:7453-7463)跨轮只增不减。参考版 `Val::VSub(Box<Val>, Rc<Sub>)` 挂在正常 drop 的 Infer/值树上,无此问题——**快版独有**。
- 机制/影响:非 UB,纯资源泄漏;单轮量小(σ 链节点),但逐键触发的 LSP 轮次 × 精化臂内包裹次数 → 无界。显式替换移植(design doc §9.4 定稿的持久化单链)把共享语义搬进 packed-word 时新增的唯一堆共享载体就是它。
- 处置建议:把 `SubstV` 链也 arena 化(对齐 Spine/EnvCons 的 `'a` 引用表示,回滚改指针赋值),或在轮界显式释放;至少在文档标注该泄漏上界。

### [P2] L07 孪生版 10 处缓冲洗白 transmute 无任何 SAFETY 注释,且借出点不 clear,与 L08–L12 的防御口径分叉(影响面:L07)

- 位置:`src/L07_sum_type/bump_spine_iter.rs:5183, 5221, 5223, 5225, 5268, 5270, 5272, 5274, 5332, 5334`;对照 L08(`bump_spine_iter.rs:5337-5339, 5378-5392` 等)每处均有 `// SAFETY:'static 仅是存放口径…借出期 = 本次调用,槽内容下次借出前必 clear` 且**借出点显式 clear**(`work.clear()/tasks.clear()/done.clear()/stack.clear()`,L08:5390-5392)。
- 证据:L07 全文件 SAFETY 计数 4(三个 tag 解引用 + string_concat),unsafe 块 14——10 处 transmute 的不变式只写在字段声明注释(4895-4899,即 P1 条目里被找出反例的那条);L08 SAFETY=14/blocks=14、L09 14/20、L10 13/18、L11 16/20、L12 16/23。L07 借出点不 clear(eval 依赖 eval_iter 入口清、quote 依赖 quote_iter 入口清 tasks/done),`quote_memo` 是唯一借出点即清的(L07:5275)。
- 机制/影响:不变式真实存在且当前成立(kernel 入口清 + 元素无 Drop glue:`W`/`QJob` 全 Copy 字段,`UItem::MatchBranch` 的 `Rc<declb>` 与 `QuoteMemo` 的 drop 只触堆分配,跨轮 drop 安全),故不报 bug;但注释缺口让 P1 那类"共享缓冲纪律"回归无守门,L07 与 L08+ 的结构分叉(eval/quote/unify 共用一个 `workbuf` vs 三独立缓冲)正是高危信号位。
- 处置建议:L07 对齐 L08 口径(每处 SAFETY + 借出点 clear + 分缓冲),顺带消除 P1 的触发面。

### [P3] L09–L12 的 lexer `get_unchecked` 无 SAFETY 注释(L07/L08 有,论证本身成立)

- 位置:`src/L09_mltt/parser/lex.rs:197-200, 229-232`;`src/L10_typeclass/parser/lex.rs:197, 229`;`src/L11_macro/parser/lex.rs:197, 229`;`src/L12_canonical/parser/lex.rs:197, 229`(共 8 块);对照 `src/L07_sum_type/parser/lex.rs:162-168`、`src/L08_product_type/parser/lex.rs:170-176`(有注释)。
- 证据/论证核对:边界论证为真——`parser_lib.rs:43-55` 的闭包 `Pattern::strip_prefix_of` 按 `chars()` 累加 `c.len_utf8()` 后 `haystack.get(matched..)`,切点恒为 char 边界且 ≤ len;`ident`/`macro_ident` 的 `head.len()+tail(_len)` 均由同一 `input.data` 的逐 char 消费叠加而来,UTF-8 多字节、多行、截断输入(未闭合即 None)都不会越界。仅注释缺失。
- 处置建议:回灌 L07 的 SAFETY 注释文本即可。

### [P3] `lit_of` / `xcell_head_name` 等辅助函数是签名级生命周期洗白(任意 `'a` 由调用点自选),健全性完全依赖调用纪律

- 位置:`src/L07_sum_type/bump_spine_iter.rs:865-873`(`lit_of<'a>`)、`:784-795`(`xcell_head_name<'a>`);各层同构(如 `src/L11_macro/bump_spine_iter.rs:860-866`)。
- 证据:`fn lit_of<'a>(v: V) -> Option<&'a str>` 的 `'a` 与入参无 link,调用点可合法地选 `'static` 而编译器不拦;L07:859-863 的文档声明("所有 V 的 XCell 都指向当前轮 bump 或 'static 钉串,跨轮 reset 前一切句柄已消亡")是全局不变式,无法静态保证。审计了全部调用点(prim_reduce/宽松臂/struct_eq),当前均绑定当轮 `'a`,无违规。
- 机制/影响:无现实违反;记录在案是因为这类"内部正确"的洗白函数与 transmute 共享同一弱点——新增调用点时无类型系统防线。与 P2(缓冲注释)同属"防线停在纪律层"。
- 处置建议:保持文档;若日后重构,让 `lit_of` 返回与 bump 参数挂钩的生命周期(把 `&'a Bump` 穿入)可把这层洗白消掉。

## 3. needs-verify 清单(验证方法)

1. **P1 条目的端到端可达性与可观测后果**(唯一需要动态验证的项)。静态论证已给出完整调用链,未运行验证(禁 cargo)。验证方法:任取一层(建议 L07),在 `eval_iter` 入口 `work.clear()` 前临时加 `debug_assert!(work.is_empty(), "workbuf 复用不变式被违反")`,构造回归源:
   ```text
   enum Nat { zero
     succ(x: Nat) }
   enum Bool { true
     false }
   def test(b: Bool): Nat =
     let g = (n: Nat) => succ n in
     match b { case true => let x = (let y = g zero in succ y) in x }
   println (test true)
   ```
   (arm 入口 subst_cxt 使 g 槽带 VSub;外层 let 的定义项是嵌套 let,`check(Raw::Let)` 的 `vt = eval(cxt_arm.env, t_tm)` 整值求值触发 ChainWrap→vapp1(VSub)→vapp1(clo)→eval_iter 清掉 pending 的 `LetBody`。)若断言触发或输出与参考版不一致即坐实;然后六层各加 parity 用例钉住。

## 4. 设计决定讨论(不属 bug,只记录)

1. **L07 单一共享 `workbuf` vs L08+ 的 `eval_work`/`quote_work`/`unify_work`/`unify_stack` 分缓冲**(L08:5005-5013)。L08+ 口径更防御(借出点 clear + 每处 SAFETY);L07 的共享在"kernel 排空即返回"纪律下成立,但其纪律恰好是 P1 反例所在。建议借 L07 下次改动时向 L08+ 对齐,而非保持两套口径。
2. **L11/L12 的 `DECLB_CACHE`(TLS 指针键缓存)**(L11:2551-2599、L12:2577-2626)。审计结论:成立。键 = 源 `Rc<Decls>` 地址,条目钉住源表克隆使地址在缓存存活期不可复用(无 ABA);stub 与源的同步靠 pin 迫使后续 `Rc::make_mut` 走克隆(COW);`clear_round` 显式清缓存(L11:4235、L12:4285),Tycker 三入口 `bump.reset()` → `clear_round()` 1:1 配对,panic/错误早退路径在下一轮入口清,无跨轮读。'static 存放口径与各缓冲一致,条目无 Drop 粘胶(Rc drop 只触堆)。注意其正确性完全依赖"clear_round 与 reset 同界"这条文档纪律——若未来新增 Tycker 入口忘记配对即成 use-after-free,建议在 Tycker 入口集中封装 reset+clear。
3. **L12 `MetaSnap<'static>`**(L12:864-893、4042-4048、4469-4475)。`metas` 每轮 `clear()`(L12:4288 清单项),快照只在同轮错误路径被 `meta_unsolved` 洗回 `'a` 读;COW(`Rc::make_mut` 被快照 pin 住强制克隆)保证快照内容不被改写。纪律成立。drop 链(Rc<MetaSnap>→Rc<Decls>→FxHashMap<SmolStr,…>)不触 bump 内存,reset 后 clear 安全。
4. **`v_u` 编码分叉**:L07/L08 `v_u() = V(3)`(常量),L09–L12 `v_u(lvl) = V((lvl<<3)|3)` 携带宇宙层级(L09:180-182)。tag 3 是立即数、无解引用路径,分叉无内存安全影响,仅提示读代码时勿混淆。
5. **L11 vapp1 把 VSub 臂提到 Clo 臂之前**(L11:902-912),L07/L08 在 tag-7 分支内、L09/L10 在 tag-7 分支内但先列 Obj——三写法等价,均为"先 force 再分发",且依赖同一不变式"force 顶层不产出 VSub"(结构上成立:force 的 VSub 臂替换 v 后重派发,frcs 各臂都不返回 VSub;quote 的 VSub 臂注释里"fuel 耗尽时原样返回"实为不可达的防御分支)。
6. **递归终止依赖标注**(任务书第 4 点):unsafe 块本身(tag 解引用、transmute、拼接)均不依赖递归终止;但 VSub 消费链(vapp1 VSub 臂、frcs)的终止依赖"σ 无环"(浅 occurs 守卫 + L07/L08/L10/L11 的 fuel 有界降级)。L09/L12 孪生**无燃料池**(L09 XCell::VSub 注释自认"本层无燃料池"),环防护只剩 occurs 浅扫——深环下 L09/L12 的行为差异(发散 vs 有界降级)属 D3 发散维度,此处仅记录 unsafe 视角无影响。
7. **跨轮悬垂与 arena 别名总评**(任务书第 1/4 点审计结论,无发现):六层轮界纪律统一为 Tycker 入口 `bump.reset()` → `clear_round()`,被洗白载体的元素类型全部无 Drop 粘胶或 drop 只触堆分配(W/QJob/RenBuf/Entry/QuoteMemo/UItem 的 Rc 项),未发现跨轮读路径;arena 对象只经 `&` 共享,唯一 `&mut` 写是 `string_concat` 的 `alloc_layout` 新分配,无双重 `&mut`;`Spine` 句柄(tag 2)索引仅当轮有效且载体(metas/defs/mutable_map/name_map/spine)逐轮清空,陈旧句柄无回流路径。`7cfbb8e` 的"宽松臂 tag 检查(P0)"已覆盖六层(各层 unify 宽松臂均先 `v_tag(hd)` 再 `v_xcell_of(hd)`,如 L09:1192-1194 注释在案)。

---
verdict:P0:0 P1:1 P2:2 P3:2 needs-verify:1
