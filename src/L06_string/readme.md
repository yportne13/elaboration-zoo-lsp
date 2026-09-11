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

church/solve 上快版稳定领先 10~20×；**strchain 是 L06 的主展示负载**——
参考版每次 define 克隆 `src_names`（O(n)/次 → O(n²) 全局）+ prim 触发链
的求值开销，快版 name_map+trail 与稳态复用把曲线拉回近线性，n=16384 时
领先 **≈870×**。implicit/prune 的参考版超线性与 L05 readme 的「已知限制」
同款（src_names 克隆 + telescope 物化），快版保持近线性（implicit
n=16384 仅 27ms）。

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
