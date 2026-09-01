# L05_pruning — meta 探测（pruning）：参考实现与 `bump_spine_iter` 移植

elaboration zoo 上游 `05-pruning` 的 Rust 移植：在 L04（implicit args）之上加
**typed metas + meta 探测**（把 meta 从它的一部分 spine 实参里剪出来，让本不可解
的方程变得可解）。

与 L03/L04 同构的双实现：

- `mod.rs`：参考实现（与上游一一对应：`Box<Tm>` 项、`List` Rc 持久环境、
  递归 eval/quote/force/unify/rename/prune）；
- `bump_spine_iter.rs`：极致性能版（L04 冠军配方的移植 + pruning 机制），
  两版输出**逐字节一致**（互检测试 + `tests/l05_blackbox.rs` 双 oracle）。

## 与上游 Main.hs 的对应

- 语义与 `05-pruning` 各模块逐函数对应（已逐字核对 Cxt / Evaluation /
  Unification / Elaboration / Pretty / Errors / Main）；错误措辞按上游
  Errors.hs；`displayMetas` 采上游 05 的**带类型**形态（`let ?m : A = v;`）
  ——meta 类型要保留正是 pruning 的前提。
- 两处旧移植遗留的 TODO（`//TODO:revPruning`、`//TODO:need rev()?`）均已
  核对上游后修正：
  - `pruneTy` 收 **`RevPruning`**：外→内走掩码、配对 Π 层（旧移植内→外，
    掩码与 Π 层错位）；
  - `pruneVFlex` 的结果折叠对齐上游 `foldr`：**最外层实参先应用**（旧移植
    `iter().fold` 从内层起，应用序倒置）。

## 与 L04 的语义差别

1. **typed metas**：`MetaEntry` 携带类型（已解也保留）；fresh meta 的类型是
   `eval [] (close_ty locals (quote lvl a))`——把当前局部 telescope 闭成迭代
   Π（Bind→显式 Π、Define→let）。
2. **`AppPruning` 掩码**：洞不再抽象成一串 `BD`，而是 `Pruning =
   [Maybe Icit]`——绑定槽 `Just i`（按该 icit 应用实参）、define 槽
   `Nothing`（跳过）。显示时（上游 `goPr`）只打印绑定槽的实参名，匿名 binder
   `_` 打印 `@位序`。
3. **unify 升级**：同头 flex-flex 由 L04 的逐实参 `unify_sp` 改为
   **`intersect`**（两 spine 都是变量序列时取交、剪差异槽造新 meta）；异头
   flex-flex 走 `flexFlex`（较长 spine 一侧优先反演）。
4. **rename 的 flex 分支 = pruneVFlex**：spine 是 renaming 且含越界变量时剪
   掉越界槽、造新 meta；含非变量实参即不再可能是 renaming。
5. **非线性 spine**：`invert` 允许重复变量（记 `nlvars`），产出把重复变量全部
   出现剪为 `Nothing` 的掩码；`solveWithPRen` 先 `pruneTy` 验证剪枝可行性再解。
6. **λ 包裹取自类型**：`lams` 沿 meta 类型的 Π 层剥（名字随 Π，`"_"` 改名
   `x{l}`），不再是 L04 的 spine-icit 版。

## 怎么跑

```text
cargo test --lib L05_pruning          # 参考版 + 性能版内嵌测试（含互检）
cargo test --test l05_blackbox        # 黑盒双 oracle 套件
cargo run --release --bin l05bench -- --workload prune
cargo run --release --bin l05bench -- --workload all --max-k 13
```

消融开关（只影响性能，不影响输出）：`L05_NO_CONV_MEMO=1`（unify 判等记忆化）、
`L05_NO_NAME_MAP=1`（名字解析回落线性 walk）。

## 性能版要点（相对 L04 的增量）

1. **`PrCons` 掩码链**：把 L04 的 `BdCons`（`bound: bool`）泛化为
   `slot: Option<Icit>`——应用实参时 icit 取自掩码（L04 的 `AppBdsOne`
   硬编码 Expl 在此变成带 icit 的 `AppPrunOne`）。none-run 跳段、
   `eval_fresh` 快捷路径原样继承（`None` ⇔ L04 的 define 槽）。
2. **typed-meta 闭类型的三级快捷**（`fresh_meta`）：`binds == 0` 时
   telescope 只剩 define 的 Let 层（只往 env 塞值、不添 Π 层），故常值类型
   （`U` / 裸未解 meta，tag 3/5）闭类型恒等、直接取；`quote` 产物无自由变量
   时可跳过 Let 链求值（顶层 define 链的逐层重 eval 免掉）；否则与参考版同形
   构造。
3. **同头刚性逐实参环的修正**：L04 的内联环在实参本身是**异头 flex 链**时会
   错误地"下钻"进实参链逐层比较（把 `?6 a b` 与 `?0 a a` 的内层 `b`、`a`
   当成要比较的对，误判 `(0,0)` 不等）。L05 的插入/剪枝大量制造该形态，故
   把每层只比较「函数部分入栈递归 + 最外层实参入栈」，实参整体交给 flex-flex
   / intersect——与参考版 `unify_sp` 的「先 tail 后 head」严格同序。
4. **`RenBuf` 加非线性哨兵** `NONE_MARK`：`invert` 把重复变量整级标为该哨兵，
   `get` 视其缺项（rename 的 scope check 自然失败、掩码记 `None`），无需第三
   集合；换代缓冲不互踩（`prune_ty` 的嵌套 rename 自带 RenBuf）。
5. **quote/unify 记忆化、复合环境、稳态复用、迭代内核**全部继承 L04；
   `AppPruning` 是项层的洞形态（值层无此构造），quote/unify 主体不增分支，
   pruning 只活在 `fresh_meta` / `solve` / `rename` 的 flex 分支 / `intersect`。

## 实测结果（Windows 10，release build，rounds=3 取 min）

```text
== workload: church ==（basic 与 fast 齐跑）
k=11  n=4096    fast=0.269ms*         basic=3.339ms      (≈12×)
k=12  n=8192    fast=0.524ms          basic=6.581ms*→... (≈13×)
k=13  n=16384   fast=1.060ms          basic=15.948ms     (≈15×)
== workload: solve ==
k=11  n=4096    fast_ss=0.342ms*      basic=8.145ms      (≈24×)
k=12  n=8192    fast=0.680ms*         basic=17.869ms     (≈26×)
== workload: implicit ==（L04 同款链，验证 typed-meta 不劣化线性）
k=9   n=1024    fast_ss=1.387ms*
k=11  n=4096    fast_ss=7.570ms*
k=13  n=16384   fast_ss=29.880ms*
== workload: prune ==（L05 特色：每层非线性求解 + 闭型 telescope）
k=9   n=1024    fast=8739ms / basic=80076ms   (≈9×，见「已知限制」)
```

implicit 负载（顶层 `id p_{i-1}`，插入 meta 类型恒 `U`）走 `binds==0`+tag3/5
快路径保持近线性（每层 ×2 递增，与 L04 同量级）。church/solve 上快版稳定领先
参考版 12~26×。

## 已知限制

- **prune 负载的 telescope 物化代价**（L05 相对 L04 新增的固有开销）：typed
  meta 的闭类型 `eval [] (close_ty locals q)` 沿增长的 define 链构造，绑定层
  下的每次 `fresh_meta` 是 O(上下文深)——`prune_src` 每层在 `\a b.`（2 binder）
  下插入数个 meta、且链上有大量 define，`close_tm`+eval 使快版与参考版都超
  线性（快版 n=1024 约 8.7s，参考版 80s）。这是上游 05 用惰性/持久结构隐藏、
  本层显式物化后暴露的成本；`binds==0`（顶层）的插入仍走快路径 O(1)。
- check/infer 与 parser 在 let 链上仍是递归（L03/L04 同款），参考版的深层
  rename/prune 在深负载需大栈（l05bench 默认 128MB 线程，`L05_STACK_MB` 可调；
  互检/黑盒里深负载用 `with_big_stack` 线程跑参考版）。
- 参考版深层 Box 项析构会爆栈，bench 里 `mem::forget`（L03/L04 同款处理）。
- `intersect` 的长度失配分支（上游 `impossible`）在本层落地为「共同前缀照常
  比较 + 必败哨兵」，双实现一致，不炸栈、结论同为失败。
