# D3 稳健性/全函数性（panic·溢出·燃料·发散） — L07–L12 只读评审

## 1. 结论（verdict）

- **P0: 0  P1: 4  P2: 5  P3: 2  needs-verify: 4**

### 范围校准（影响定级，必读）

- 任务背景假设"LSP 场景，panic 杀死语言服务器会话"。机械核实结果：**L07–L12 六层均未接入 LSP 主路径**。`src/lib.rs:27-32` 仅 `pub mod` 声明；`run_lsp_server`/`Backend::main_loop`/`process_file`/`tutorial` 全部走 L13（`Engine::lsp_default` 的 Twin/Reference 都是 L13 引擎）；六层只被 `src/bin/l0Xbench.rs`（固定 workload、自建大栈线程）与 `tests/l0X_*` 驱动。因此本报告把"通过各层公开入口 `run()`/`run_fast` 的合法源码可达 panic"按 BRIEF P1（可达 panic）定级；若这些层未来像 L13 一样接入 LSP（`catch_unwind` 只包 `main_loop` 整体、panic 后服务器退出，见 `src/lib.rs:3654-3670`），其中多条将升级为 P0。诚实声明：定级依据是当前接线，不是假想接线。
- 六层 `UNIFY_FUEL` 恒为 4096（`mod.rs`/`bump_spine_iter.rs` 各 14 处定义，逐一核对一致）。

### 覆盖范围与方法

- `grep -rnE "unwrap\(\)|expect\(|panic!|unreachable!|todo!|unimplemented!"` 六层共 904 命中，逐类过筛：`panic!/unreachable!/todo!` 全量 130+ 处逐条看上下文；`unwrap` 抽样 mod.rs/unification.rs/pattern_match.rs/elaboration.rs/cxt.rs/pretty.rs（parser 组合子与 `#[cfg(test)]` 内的命中不计）。
- 已知线索复核：L09 pretty.rs:52 **已修复**（`go_ix` 越界退化 `@ix` 不 panic，`src/L09_mltt/pretty.rs:43-54`）；L09 pattern_match.rs:581 的 todo **在块注释里**（:604-610）；L12 elaboration.rs:576→现 :674、L11:528→现 :606 的 `todo!()` 为 parser 形状守卫下的死臂；四份 `//TODO:todo!()`（L09 unification.rs:746、L10:743、L11:788、L12:841）是**注释**，非代码。
- 燃料：对比六层 mod.rs/unification.rs/pattern_match.rs/bump_spine_iter.rs 的池定义、燃烧点、充值点（grep -c 与定点读）；dbe79cd 在本仓库工作树**不存在**（`git cat-file -t dbe79cd` → not a valid object），按现状直接核对：L10/L11/L12 孪生版 `PM_FUEL` 线程局部池齐全（`bump_spine_iter.rs` L10:936-947 / L11:962-973 / L12:1009-1020），燃烧点（Meta 解、Match 重选、frcs/spine 链 lookup 命中）与各自参考版对齐——该项 P1 已落地，无"一份修了其他份没修"。
- 下标/截断：`as u32/u16/u8` 全量过筛（无 u16/u8；`as u32` 仅 lexer 偏移 `input.len() as u32`，>4GB 不可行）；`as u64<<3` packed-word 编码往返无损；孪生 `globals[(*i - GLOBAL_BASE)]` 等索引有 `>= GLOBAL_BASE` 守卫（L10 twin 1554/1666）。
- 递归/发散：核对 eval/quote/force/frcs/walk_con/pretty/unify 的递归与燃料兜底、`unify_catch` 诊断路径的 fuel 覆盖；读 `tests/large_did_open_no_hang.rs` 全文。
- 未运行 cargo；git 仅只读。

## 2. 发现列表

### [P1] 合法源码可 panic：卡住 match 被应用（影响面：L09/L10/L11/L12；L07/L08 已修）

- 位置：`src/L09_mltt/mod.rs:614`、`src/L10_typeclass/mod.rs:710`、`src/L11_macro/mod.rs:764`、`src/L12_canonical/mod.rs:896`（孪生同款：`L09/bump_spine_iter.rs:955-958`、`L10:908-911`、`L11:931-934`、`L12:978-981`）
- 证据：四层 `v_app` 的兜底臂 `x => panic!("impossible apply\n ...")`；值层有 `Val::Match` 变体但 **v_app 无 Match 臂**。对照 L07/L08 已实现值层实参吸收：`src/L07_sum_type/mod.rs:999-1002`、`src/L08_product_type/mod.rs:1001-1005`（`Val::Match(.., mut pending) => pending.push((u,i))`）。L12 额外有 `Val::Call` + Match `origin` 路径（`src/L12_canonical/mod.rs:998-1006`）——但只覆盖宏生成的 `Tm::Call`，普通 `Tm::App` 仍直落 panic（`mod.rs:961`）。
- 机制/影响：`f : A -> B` 类型的**卡住 match**（scrutinee 是变量，臂体是 λ）通过类型检查后，`eval(Tm::App)` → `v_app(Val::Match, arg)` → panic。L09 头注 `src/L09_mltt/mod.rs:3-11` 明确承认"合法源码……可触发"（已知限制、双版同崩、parity 锁定）；**同样的限制在 L10/L11/L12 头注中无任何记载**，属于未文档化的同款可达 panic。
- 处置建议：至少把 L09 的已知限制文案复制到 L10/L11/L12 头注；若要根治，按 L07 的 pending 机制或 L12 的 origin 机制补 `Val::Match` 臂（参考版+孪生同步）。

### [P1] typeclass 求解器 `panic!("Too much effort :(")`：循环实例/深实例链可触发（影响面：L10/L11/L12）

- 位置：`src/L10_typeclass/typeclass.rs:218-224`（effort>1000 → panic）、`:268`（`panic!("Cannot resume with empty subgoals.")`）；`src/L11_macro/typeclass.rs:205`、`src/L12_canonical/typeclass.rs:315` 同款。孪生版复用同一模块（`L10/bump_spine_iter.rs:85`、`L11:78`、`L12:101` 均 `use super::typeclass::…`），故双版同崩。
- 证据：`synth` 的主循环以 `effort` 计数封顶 1000 次迭代后 **panic** 而非返回 `None`/Err。终止性只靠 `assertion_table` 对**完全相同 goal** 的记忆化；实例依赖经一阶匹配代入后 goal 若**同尺寸复现**（实例体引用本实例自身：`new_subgoal` 用 `insert` 覆盖表项、已积累 answers 丢失，`typeclass.rs:293-299`），或 >1000 个互异 goal 的深链（如千层嵌套 `List[List[…]]` 的类型类求解，几 KB 源码即可），都会烧穿 effort。
- 机制/影响：用户可写出的合法（语义错误但语法合法）实例声明 → 整个进程 abort，无诊断输出。
- 处置建议：把 effort 封顶改为返回 `None`（调用点 `trait_wrap` 已按 `is_some()` 过滤，天然降级为 "no instance"），三份同步改。

### [P1] 文件 IO 内建 panic：`file_read_all_text` 等对 IO 失败直接 abort（影响面：L07/L08）

- 位置：`src/L07_sum_type/mod.rs:880-889`（read）、`:891-899`（write）、`:901-919`（append）、`:945-953`（delete）；孪生 `src/L07_sum_type/bump_spine_iter.rs:1079-1142`；L08 同款（`mod.rs:891-960`、`bump_spine_iter.rs:1079-1142`）。
- 证据：`std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("file_read_all_text: failed to read …"))` 等五处。这些内建**可从源码调用**：`src/L07_sum_type/tests.rs:1325` `def r : String = file_read_all_text "l07_test_io.txt"`，blackbox 套件亦用（`tests/l07_blackbox_v2.rs:379-381`）。
- 机制/影响：路径不存在/无权限/是目录 → panic。测试只覆盖成功路径；任何 IO 失败即进程死亡。L09 起已删文件内建（L09 bin 头注"builtin 只剩 string_concat"），仅 L07/L08 受影响。
- 处置建议：失败改为返回约定错误值或 Err（参考版+孪生同步），与 `file_exists` 的布尔风格对齐。

### [P1] `eval_aux` 的 "by now only can match a sum type"：参考版/孪生版行为分裂，孪生侧 panic（影响面：L09 双版、L10/L11/L12 孪生）

- 位置：L09 参考版 `src/L09_mltt/pattern_match.rs:595`（**活** panic）+ 孪生 `src/L09_mltt/bump_spine_iter.rs:1330`（同崩，层内一致）；**L10/L11/L12 参考版已改优雅降级**（`src/L10_typeclass/pattern_match.rs:608-612`、`L11:611`、`L12:605`：panic 被注释，`_ => (empty_span("$unknown$"), vec![], vec![])`），但**孪生版仍是活 panic**：`src/L10_typeclass/bump_spine_iter.rs:1408`、`L11:1453`、`L12:1492`。
- 证据：L10 孪生 panic 臂上方的注释自证可达性——"参考 panic：typ 不是 Sum（**中性 global 下的重求值可达**）"，而其声称的"参考 panic"在参考版里早已不存在（注释过期）；L10 参考版 ：609 的同款 panic 已注释。
- 机制/影响：match 的 SumCase typ 槽 force 后非 Sum 时（重求值/GADT 角落），参考版把该 match 当"无分支可匹配"继续，孪生版 panic——同一输入双引擎一 Ok 一 crash：既是可达 panic 又是 parity 裂缝（Err/Ok 判定不一致方向）。
- 处置建议：L10/L11/L12 孪生按参考版改优雅降级并删除过期注释；L09 双版一起决定（降级或保留但补文档）。

### [P2] L09 的 `unify` 入口缺燃料护栏（双版一致地缺失，其余五层都有）

- 位置：参考版 `src/L09_mltt/unification.rs:535-545`（`unify` 入口无 `burn/check fuel`）对比 L07 `src/L07_sum_type/unification.rs:610-623`、L08 `:612-623`、L10 `:600-603`、L11 `:637-640`、L12 `:654-657`；孪生版 `src/L09_mltt/bump_spine_iter.rs:2543` 明文"**无燃料（参考版无 fuel）**"。
- 证据：L10 注释自证历史："unify/force 的共享递归 fuel 池容量（L08 护栏前向传播：**L09 重写时丢失**…）"（`src/L10_typeclass/mod.rs:411-413`）。L09 的 `unify_fuel` 池存在（`mod.rs:412-428`）但只护 force 侧；unify 的结构递归（Pi/Lam/η/Sum/SumCase/Match 臂）无任何步数上限。
- 机制/影响：L07 加入口护栏的原因是"索引槽互相嵌入的构造子值比较会无限递归"（`L07/unification.rs:611`）；L09 同样有索引和类型（`Vec` 风格 GADT 在 l09bench enum workload 中）。若该构造在 L09 可复现，结果是无限递归→栈溢出 abort（比 fuel 耗尽的优雅 Err 更糟）。见 needs-verify #1。
- 处置建议：按 L07 形状给 L09 `unify` 入口补 `burn`（参考版）+ `unify_iter` 补步数上限（孪生），两侧同步。

### [P2] L10/L11/L12 参考版 `check_pm`/`check_pm_final` 缺"模式编译入口充值"，孪生版有——跨引擎燃烧剖面分裂

- 位置：孪生有充值：`src/L10_typeclass/bump_spine_iter.rs:6107`、`:6127`（注释"模式编译入口充值精化燃料池"），L11 `:5456`、`:5479`，L12 `:5568`、`:5592`；参考版无：`src/L10_typeclass/elaboration.rs:84-112`、`src/L11_macro/elaboration.rs:85-…`、`src/L12_canonical/elaboration.rs:87-105`（grep 三文件 `refuel|meta_refuel` 仅 L12:327 的顶层 unify 入口一处）。
- 证据：L07/L08 在模式编译入口 `infer.meta_refuel()`（`src/L07_sum_type/pattern_match.rs:87`，注释"编译期间的所有合一共享一个 fuel 池（深层递归防护）"）；L09 也在两个 `check_pm*` 入口充值（`src/L09_mltt/elaboration.rs:84`、`:117`）。L10–L12 参考版把该纪律**只落在孪生侧**，参考版的 `unify_pm` 探测（可达性判定）烧的是上一个 `unify_catch`/`nf` 以来剩余的共享池，中途无充值点。
- 机制/影响：深模式程序里参考版可能在编译中期耗尽池 → force 降级/`unify` 判失败 → 可达构造子被误判不可达（假 "unmatched" 警告或假 absurd），而孪生版同输入正常——Ok 路径 parity 测不出（绿色用例两侧都过），极端输入下 Err/警告文本分裂。这正是 L07 `test_deep_pattern_fuel_budget_regression`（`src/L07_sum_type/tests.rs:1484-1533`）钉死过的一类问题。
- 处置建议：把孪生 `check_pm*` 入口的 `refuel()` 回移到三个参考版（一行级改动、无行为分歧风险）。

### [P2] `lvl2ix` L11/L12 无护栏：`Ix(l.0 - x.0 - 1)` 可下溢（debug panic / release 回绕）

- 位置：`src/L11_macro/mod.rs:418-420`、`src/L12_canonical/mod.rs:483-485`。对照：L07/L08 有护栏（`src/L07_sum_type/mod.rs:377-383`：`x.0 >= l.0` 时 `debug_assert!(false)` + release 退化 `Ix(0)`）；L09/L10 因 1919810 全局哨兵改写边界并注释口径（`src/L09_mltt/mod.rs:363-367`）。
- 证据：L07 护栏是显式替换重构期加入（commit `c18fef5`，"语义上不可达……debug 断言捕捉，release 保守降级"）；L11/L12 在 `2129975`/`58073dd` 移植显式替换时 `lvl2ix` **未随行**，仍是 elaboration-zoo 上游裸减法。
- 机制/影响：一旦越界 rigid 到达 quote（σ 链/η 臂层级的角落，L08 评审就修过一处 `quote(cxt.lvl)`→`quote(l)` 的实例，L09 注释回移记录在 `src/L09_mltt/unification.rs` η 臂），debug 构建在减法处 panic，release 回绕成 `Ix(~4e9)`：打印垃圾 `@4294967295`，若该项再被 eval 则落入 `panic!("var … not found")`（`src/L11_macro/mod.rs:797-800`）。是否真有可达路径见 needs-verify #2；至少与 L07–L10 的"防御性护栏齐备"不一致。
- 处置建议：把 L07 的护栏形状复制到 L11/L12（release 降级 + debug_assert）。

### [P2] 值层字段投影 `find(...).unwrap()` / `panic!("impossible {typ:?}")`（L09–L12），对照 L07 的全函数 `project()`

- 位置：`src/L09_mltt/mod.rs:671-684`（SumCase typ force 非 Sum → panic；字段 `find(..).unwrap()` 两处）、`src/L10_typeclass/mod.rs:758-762`、`src/L11_macro/mod.rs:807-822`、`src/L12_canonical/mod.rs:940-950`。对照 `src/L07_sum_type/mod.rs:1284-1306`：`project()` 返回 `Option<Val>`，查不到字段/typ 非 Sum 一律 `None` → 卡成中性 `Val::Obj`。
- 机制/影响：接收者值层形态与类型层承诺不符时（GADT 索引槽、σ 推开的角落）L07 优雅卡住，L09–L12 panic。类型正确程序下 `find` 理应命中，故可达性存疑（needs-verify #4），但防御姿态明显落后于 L07 的重写。
- 处置建议：按 L07 `project()` 形状把四层投影改全函数（查不到 → 中性 Obj）。

### [P2] 参考版全链递归无深度上限；`tests/large_did_open_no_hang.rs` 只护传输层死锁，不护深度/发散

- 位置：参考版 eval/quote/force/frcs/closure_apply 互递归（如 `src/L07_sum_type/mod.rs:1129-1208` quote、`:995+` v_app）、模式编译 `walk_con` 递归、`pretty_tm` 递归；全六层 grep 无 `MAX_DEPTH/depth_limit`（仅宏展开有 `MAX_MACRO_EXPANSION_DEPTH=256` 的 RAII 守卫，`src/L12_canonical/parser/mod.rs:142-176`、L11 同款——这是唯一有深度上限的环节，做得对）。
- 证据：`src/L07_sum_type/tests.rs:1484-1533` 为 depth=400 的模式匹配**专门开 512MB 栈线程**并注释"走查递归深度 × walk_con 帧较大"——即主线程默认栈（Windows ~1MB）下几百层嵌套即可栈溢出（abort，`catch_unwind` 也拦不住）。各 bin 亦自建大栈（`src/bin/l09bench.rs:99`）。孪生版 eval/unify/quote 已显式栈化（`L09/bump_spine_iter.rs:1899 quote_iter`、`:2546 unify_iter`），但 `export`/pretty 链仍按值深度递归。
- `tests/large_did_open_no_hang.rs` 覆盖的是 didOpen **>1MiB 帧的传输管道死锁**（回归 4 方死锁，走 L13 后端），**不覆盖**：深嵌套源码（深 λ/app/match/模式）、求值/quote 栈深、fuel 耗尽路径、任何 L07–L12 引擎行为。
- 机制/影响：若有朝一日按 L13 的方式接 LSP，深嵌套文件 = 会话死亡且无诊断。当前仅 bench/tests 受影响，故 P2。
- 处置建议：至少在 README/各层头注记下"输入深度有栈上限，宿主需大栈线程"；根治需给参考版 eval/quote 加深度计数（超限转 Err "expression too nested"）。

### [P3] 死代码 todo 标记与守卫死臂，宜改 Err 或删

- 位置：`//TODO:todo!()` 注释 ×4（`L09/unification.rs:746`、`L10:743`、`L11:788`、`L12:841`）；块注释内 todo（`L09/pattern_match.rs:604-610`）；`_ => todo!()` 死臂（`src/L11_macro/elaboration.rs:606`、`src/L12_canonical/elaboration.rs:674`——parser 侧 `p_impl` body 只产 `Decl::Def`（`src/L11_macro/parser/mod.rs:1626-1655` `brace(p_def.many0_sep …)`），臂不可达）。
- 机制/影响：当前不可达；但它是"静默契约"——parser 若日后放宽（如 impl 体允许嵌套 enum）即变 panic。改 `Err(...)` 成本为零。
- 处置建议：改 `Err` 或加 debug_assert 注记；`//TODO:todo!()` 字样建议改为可 grep 的说明文字。

### [P3] 解析总失败的处理跨层不一致：L07/L08 优雅 Err，L09–L12 unwrap/panic（现状均不可达）

- 位置：L07 `src/L07_sum_type/mod.rs:1330` 与 L08 `:1338` 用 `.map_err(Error)?`；L09 `:889`、L10 `:986`、L11 `:1037`、L12 `:1204` 用 `.unwrap()`；孪生对应 `panic!("parse failed")`（`L09/bump_spine_iter.rs:7189` 等，注释"参考版 run 对 parse 失败 unwrap panic——同款"）。
- 证据：`parser()` 返回 `None` 的唯一路径是 `lex()` 失败，而六层 lexer 末尾 `err_token = pmatch(|c| !c.is_ascii_whitespace())` 兜底任意非空白字符（如 `src/L09_mltt/parser/lex.rs:296-320`），`many0` 恒成功 → `lex` 实际不返回 `None`；声明级错误在 `parser()` 内被 `recover_with(skip_until_decl)` 收进 `err_collect` 返回 `Some`（`src/L09_mltt/parser/mod.rs:174-200`）。
- 机制/影响：死防御代码，无用户可达路径；但两套口径并存容易在"lexer 将来引入可失败 token"时无声分叉。
- 处置建议：统一成 L07 的 `map_err(Error)?` 形状（六份各一行）。

## 3. needs-verify 清单（验证方法）

1. **L09 unify 无燃料护栏的真实发散性**：把 L07 触发"索引槽互相嵌入无限递归"的构造（GADT 索引等式 + 嵌套 match 精化，参考 `docs/l07-dpm-refactor-design.md` §4 槽位纪律的复现样例）移植为 L09 测试（`tests.rs` 加 case，512MB 栈线程跑 `run`）。若复现无限递归 → P2 升 P1。静态旁证：L10 注释承认"L09 重写时丢失"该护栏。
2. **L11/L12 `lvl2ix` 下溢可达路径**：构造 η/σ 角落让 quote 以小于 rigid 层级的 `l` 调用（历史实例：L08 的 η 臂 `quote(cxt.lvl)` 错位，见 `src/L09_mltt/unification.rs` η 臂注释）。方法：debug 构建跑 l11/l12 全套件 + 针对 `Lam` 值合一/`subst_cxt` 后臂体的定向测试；若命中 `debug_assert`/减法 panic → 升 P1。
3. **L10–L12 参考版缺 `check_pm` 充值的可观测后果**：把 L07 的 `test_deep_pattern_fuel_budget_regression`（d=400 逐层 cons + GADT 索引）移植为 l10/l11/l12 参考版测试，观察是否出现假 "unmatched" 警告或 Err；同输入跑孪生对比。若复现 → P2 升 P1（同输入双引擎判定分裂）。
4. **L09–L12 值层投影 `.unwrap()` 的可达性**：尝试构造"接收者类型含字段、值层 Sum/SumCase 参数链查不到该字段"的程序（GADT 构造子部分提供字段的 enum + 投影 + 卡住 scrutinee）。若可达 → 并入 P2 投影条目升 P1。

## 4. 设计决定讨论（不属 bug，只记录）

- **L09 "卡住 match 不可应用" 已知限制**（`src/L09_mltt/mod.rs:3-11`）：文档化、双版同崩、parity 锁定，属于"接受的时代缺口"。本报告仍列 P1 是从稳健性维度出发（可达 panic 本身），并非翻案其"非缺陷"定性；真正的问题是 L10/L11/L12 的**同款限制未文档化**（发现 #1 的另一半）。
- **燃料燃烧剖面逐层不同是有意的**：L07/L08 在 Meta 解/Match/Decl/frcs 多点燃烧（`L07/mod.rs:511-619`），L09–L12 收敛为"lookup 命中 + Match 重选"三点点（各自 mod.rs 与孪生对齐）；`UNIFY_FUEL=4096` 与"外层入口充值、内部共享"的口径六层一致。逐层燃烧剖面差异被 parity 套件锁在各自层内，不跨层比较，视为演进而非缺陷。
- **L12 的双燃料（`unify(.., fuel)` 参数 + `burn_fuel` 池）**：`mod.rs:565-568` 注明"参数只护 Decl 展开重试臂，本池补齐"——口径有文档，非"修一份漏一份"。
- **L10 `to_typ` 的 Sum 参数 `flat_map` 静默剔除**（`src/L10_typeclass/typeclass.rs:63-85`）：注释明示"刻意语义（本轮评审论证，勿修）"，从全函数性角度看它恰恰是把 panic 换成 None 的正确方向，与 D3 无冲突。
- **`effort>1000` panic 源自 elaboration-zoo 上游**（"Viciously terminate on cycles"）：上游以 panic 充当断言，本仓库在 LSP 化语境下沿用该形状才成为问题——修复建议（返回 None）不改变对外成功语义，只把"崩"变"no instance"。
