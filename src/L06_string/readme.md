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
  两版 **Ok 输出逐字节一致**（互检测试 + `tests/l06_blackbox.rs` 双
  oracle）。

## 语法要点（与 L05 的表达式形态不同）

- 顶层是 **decl 序列**：`def 名(参数): 返回类型 = 体` 与 `println 体`；
  `def` **无分号终结、无尾表达式行**——parser 只取 decl 前缀，任何多余
  token 都会截断后续 decl。
- λ 是 `binder组 => 体`（**无反斜杠、无点号**）；隐式 `[x : A]`、命名
  λ binder `[名字 = x]`、命名实参 `[名字 = e]`（L05 的 `{}` 全换成 `[]`）。
- 字符串字面量 `"..."`（支持 `\\`、`\n` 转义）；`String` 是内置类型名
  （注册为 `LiteralType` 值）。
- `let x : A = t in u`（表达式层，与 L05 同名不同关键字形态）。

## L06 的语义增量（相对 L05）

1. **LiteralType / LiteralIntro**：`"…"` 的类型是 `LiteralType`（打印
   `String`），值是内容字符串。pretty 打印字面量**原文**（无引号）。
2. **decl 表**：顶层 `def` 登记值/类型（elaboration 时）；`Tm::Decl(名)`
   求值时查表——命中给登记值，miss 保持**卡住的 Decl 头**（带 spine 的
   中性值）。
3. **builtin prim**：`Cxt::new` 注册整组 builtin（值 = 卡住 Decl 头），
   **应用时触发**：每次对 Decl 头的应用把全条累积实参（自然序）交给
   prim，元数不足或实参非字面量则保持卡住（`string_concat x` 部分应用
   即此形态）。文件组失败 panic、`get_global` 缺名 panic（参考版同款）。
4. **可变全局**：`create_global` / `change_mutable{,_default}` /
   `get_global{,_default}` 读写 `mutable_map`（RefCell；参考版随 `Infer`
   每次调用新建，快版随轮清空）。
5. **unify 的 L06 臂**：`(String, String)` 自反；`String` 与卡住 Decl
   互通；同名 Decl 逐实参（`unify_sp`）；**(Lit, Lit) 恒败**——参考版
   unify 没有字面量臂，连相同字面量也不可合一（快版如实复刻，见下）。

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
  快版照 L05 惯例压栈成卡住链（良类型程序不可达；两版都会在后续比较中
  失败，只是失败形态不同）。
- **`Span` 的 PartialEq 只比 data**（`parser_lib.rs` 自定义实现）：命名
  λ 按名匹配 Π、Decl 头同名可合一——快版按内容比较，一致。
- **顶层程序形态**：无尾表达式；`println` 后再出现无法解析的 token 会被
  静默截断（parser 只取 decl 前缀——参考版行为，两版一致）。
- 文件 IO builtin 做真实文件系统副作用；测试里写删固定文件名的用例经
  `FILE_IO_LOCK` 串行（Windows 并行线程的句柄竞争会让删除报 os error 5）。

## 怎么跑

```text
cargo test --lib L06_string          # 参考版 + 性能版内嵌测试（含互检）
cargo test --test l06_blackbox       # 黑盒双 oracle 套件
cargo run --release --bin l06bench -- --workload church
cargo run --release --bin l06bench -- --workload all --max-k 13
```

消融开关（只影响性能，不影响输出）：`L06_NO_CONV_MEMO=1`（unify 判等
记忆化）、`L06_NO_NAME_MAP=1`（名字解析回落线性 walk）。

## 实测结果（Windows 10，release build，rounds=3 取 min）

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
