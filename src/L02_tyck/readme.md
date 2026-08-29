# L02_tyck — 双向类型检查 + 闭包/de Bruijn 求值：参考实现与 `bump_spine_iter` 移植

elaboration-zoo L02（`typecheck-closures-debruijn`，规格见上游仓库同名层的
`Main.hs`）的 Rust
移植：表面语法（无 de Bruijn）→ 双向 elaboration（`check`/`infer` 走廊 +
beta-eta `conv`）→ 核心语法（de Bruijn 索引）→ `nf`/`type` 两种模式输出。
两个实现共用 parser、pretty、错误显示，**输出逐字节一致**（互检测试）：

- [`mod.rs`](mod.rs) — **参考实现**（L03 同款风格：`Box<Tm>` 项、Rc `List`
  环境、递归 eval/quote/conv）。
- [`bump_spine_iter.rs`](bump_spine_iter.rs) — **性能实现**：L01 调研冠军
  配方（`bump_spine_iter`，见 `L01_nbe/readme.md`）移植到带 Π/let 的核心机。
- `parser/` — 词法 + 语法（main.hs 的文法 + `withPos` 源位置包装）。
- `l02bench`（`cargo run --release --bin l02bench`）— 基准（独立 bin，
  `#[path]` 编译，不依赖其余各层）。

## 与 main.hs 的对应

| main.hs | Rust |
|---|---|
| `Raw`（含 `RSrcPos`） | `parser::Raw`（含 `SrcPos`，报错取最内层位置） |
| `eval`/`quote`/`conv`/`nf` | 参考版逐函数对应；性能版见下 |
| `Cxt{env,types,lvl,pos}` | 参考版同记录；性能版全 `Copy`、绑定量进 bump |
| `mainWith`（`--help`/`nf`/`type`） | `main_with(mode, src)` 返回本应打印的文本（测试断言用） |
| `displayError` | `display_error`（megaparsec 风格源码摘录 + caret；路径用 `(stdin)`） |
| `ex0`/`ex1`/`ex2` | `EX0_SRC`/`EX1_SRC`/`EX2_SRC` + 同名函数（ex0 按预期报错） |

## 怎么跑

工具链：nightly（`parser_lib` 的 `Pattern` 泛型约束；仓库根
`rust-toolchain.toml` 已固化，rustup 自动切换）。

```text
cargo test --lib L02_tyck                 # 24 个测试：三示例、报错路径、
                                          # 基础/性能互检、深度/稳态/conv 压力、
                                          # dup/conv_dup 负载、memo 指针共享
cargo run --release --bin l02bench        # 基准：k=9..15，五负载族 × 四口径
./target/release/l02bench --max-k 21 --only fast,fast_ss   # 大 n 段
./target/release/l02bench --workload dup --only fast,fast_memo   # call-by-need 轴
```

**测量方法论**：默认全量跑（不加 `--only`）在同一进程内按
`fast_ss → fast → fast_memo → basic` 顺序逐口径计时，内存足迹大——`fast_ss`
跨轮持有的大 bump 池（数 MB 至数十 MB）在足迹压力下页被淘汰，大 k 段
conv/conv_dup 的 min 被高估（实测 conv_dup k=15 全量 21 ms vs `--only
fast_ss` 隔离 12 ms；`fast` 因每轮新建 Tycker，受影响小）。**口径间的
数字对比请用 `--only` 隔离跑**；全量跑只作相对排序参考。

## 实测结果

机器：Windows x64，release（LTO + codegen-units=1 + mimalloc）。
负载族：`church` = church 2^(k+1)（k 次 ×2 翻倍 let 链）的 **check + nf**；
`conv` = 同 church 数之上加 `Eq Nat (add big zero) big = refl Nat big` 的
**check**（beta-eta conv 在 check 内强制两侧完整展开后结构比较）；
`conv_dup`/`dup`/`dup_deep` = 复制/重复强制族（call-by-need 轴，见下文
第三、四轮小节）。口径：预热 1 次 + N 轮取 min；`basic`/`fast`（每轮新建
Tycker）/`fast_ss`（Machine + `Bump::reset` 跨轮复用）/`fast_memo`
（quote 记忆化口径）。

church（min ms / 相对 fast）：

| k | church n | basic | fast | fast_ss | basic/fast |
|---|---|---|---|---|---|
| 9 | 1024 | 0.79 | 0.061 | 0.065 | 12.9× |
| 11 | 4096 | 2.70 | 0.21 | 0.22 | 12.9× |
| 13 | 16384 | 10.8 | 0.85 | 0.95 | 12.7× |
| 15 | 65536 | 44.4 | 3.3 | 3.5 | 13.5× |
| 17 | 262144 | 181 | 14.2 | 14.2 | 12.8× |

conv（min ms / 相对 fast）：

| k | church n | basic | fast | fast_ss | basic/fast |
|---|---|---|---|---|---|
| 9 | 1024 | 2.52 | 0.10 | 0.12 | 25× |
| 13 | 16384 | 40.1 | 1.5 | 1.5 | 27× |
| 17 | 262144 | 668 | 26.6 | 25.1 | 25× |

- 两族负载下两版实现都严格线性（每翻倍 ×2）；`basic`/`fast` 的倍率在
  church ~13×、conv ~25×——conv 负载里 basic 的递归 conv + 深 `Val` 析构
  占比更高，bump/迭代的收益放大。
- **深度无上限**：`fast` 在 church 4194304（k=21）上 ~247 ms 跑通
  （eval 双栈、quote 任务栈、conv 工作表全迭代）；`basic` 的递归
  eval/quote/conv 受栈限（128 MB 栈 ≈ 26 万层）。
- **稳态复用（`fast_ss`）在 L02 负载上未复现 L01 的大幅收益**（两口径
  速度相当）：L01 的 `_ss` 收益来自 spine/vals 是仅有的两个大缓冲；
  L02 的 elaboration 里 bump 分配（闭包/env/Π 单元）占大头，spine/vals
  复用省的那部分不再显著。接口保留（长驻进程形态仍是对的），但别期待
  L01 式的 17%–3.3×。

### conv 位相等快速路径消融（`L02_NO_BITEQ=1`）

`conv` 的位相等快速路径（同一打包字 ⇒ 同一分配/同一立即数 ⇒ 判等）在
conv 负载上值 **~2×**：k=13 关闭后 1.5 → 3.5 ms，k=15 关闭后
6.7 → 14.2 ms。church（nf）负载上中性（该负载几乎没有可剪枝的比较）。
该开关同时关闭链内环（下节）里的位相等剪枝——**这条路径必须只是优化
而非正确性依赖**：结构比较路径要能独立得出同样的结论（`(3,3)`/`(0,0)`
的显式分支 + 链内环无条件入栈的消融形态就是为此保留的，见下面的教训）。

## 后续提速（2026-08-29）：β 岔路直送 + conv 链内环

分相位探针（临时计时打点）定位出两负载的热点后，各落一刀：

1. **eval β 岔路 `ApplyKnown`**（church 全链路 1.24–1.48×，conv ~1.3×）。
   右链快速路径在头变量解析出**闭包**时退回通用三推
   （`ChainWrap/Apply/Tm(a)/Tm(f)`），其中 `Tm(f)` 要把已经 `nth` 到手的
   闭包值压回 work 栈、经 `Tm(Var)` 臂**重查一遍环境**再进 vals——church
   展开的每次 β 都走这条路。改为 `W::ApplyKnown`（函数值随 work 项携带，
   弹实参直接 β），同时 `heads == 0` 时不再压 `ChainWrap(0)`（church 展开
   的岔路全部发生在链首，收拢数为 0，原来每层一推一弹是纯浪费）。
2. **conv 连续链内联环**（conv 再 ~1.1–1.2×）。`(2,2)` 中性比较原来是每
   条 spine 条目 2 次 worksheet 入栈 + 2 次弹压；church 数展开后的链
   `s (s (… z))` 沿条目 `.a` 连续，改为内联环直接前进：f 位相等不入栈、
   双方 `.a` 仍为 spine 就地推进，只有真正待比较的子对才入工作表；入口处
   两侧都是连续链时先比 `len`（f 分量永不可能是闭包——β 岔路即时归约、
   eta push 处已排除——条目数即归一化后的应用个数），长度不等等价于必不
   等，fail-fast 省掉整趟游走。位相等剪枝受 `L02_NO_BITEQ` 统辖（消融
   仍可关掉全部捷径）。

探针给出的画像（k=17）：church 总时 ~93% 在 quote 相（其中又以 quote 强制
闭包触发的 eval 展开为主：β = 3n、spine push = n、nth 链步数 ≈ 11n、
bump 分配 ~250B/输出节点）；conv 总时 ~99.5% 在 conv（两侧各 3n β + 每元素
worksheet 往返）。

同轮**实测否决**的轴（保留结论，免得重试）：

- **左折叠应用树下钻**：把 `((clo N) s) ARG` 一类左嵌套应用树沿函数侧
  下钻、实参入缓冲、一次生成折叠弹压序列（省掉逐层 `Tm(f)` 重入）——
  church 15.2–16.3 ms（vs 现状 14.1–15.0），**略负**：实参缓冲 Vec 的
  维护 + 分支形态劣化超过了省下的重入。
- **`ApplyKnown2`/`ChainWrapVal`**（实参/base 也是 Var 时连值一起带上）：
  两负载中性偏负——多出的 work 变体让分发变宽，抵消了省下的弹压。
- **`nth` 小下标展开**（idx 0..3 unroll）：church 17.0 ms，**变慢**；
  只留 0/1 也无收益。编译器对短循环的处理已够好，多余分支反成负担。
- **spine 预分配 2^18**（免 6 次倍增拷贝）：中性——顺序 memcpy 比想象的
  便宜，不值得常备 6 MB。
- **`-C target-cpu=native`**：church 略快、conv 略慢，均在噪声内，且牺牲
  二进制可移植性，不采纳。
- **β(clo, arg) 结果记忆化**（call-by-need 对偶的 eval 侧）：纸面推演 +
  实测标定后否决——church/conv 展开里**昂贵的** β（`(C2, Z)` 一类整链
  展开）的键从不重复（每次的 Z 是新链），可复用的只有 `(vt_j, N)` 一类
  便宜的闭包创建 β；每次 β 换一次哈希查找（~8–10ns）对标 β 连带成本
  （~14ns），净收益太薄。L01 的 quote 侧 memo（1.8–3.6×）不迁移的原因
  同此：那边 memo 挂在少量 Q 任务上，这边挂在海量 β 上。**[后文修正]**
  quote 侧的「不迁移」被第三轮的 dup 负载推翻——「键从不重复」只是
  当时两个负载的属性，不是机制的属性；β 侧的否决（键真不重复）经住了
  复验，见「优化过程中的教训」第 4 条。

## 名字表示换 SmolStr（2026-08-29）

`Name = Span<String>` → `Span<SmolStr>`（parser 与参考版一起换；性能版
热路径名字是 bump `&str` 指针，不受影响）。交错 A/B（String/SmolStr 各
两轮，k=9..17 双负载族）+ parse 分相位探针 + 名字构造/clone 微基准：

- **fast/fast_ss 不动**：性能版 eval/quote/conv 全程零字符串操作——名字
  表示轴对性能版无肉（这条结论对以后所有名字类优化同样适用）。
- **参考版 conv 快 ~3–6%（church ~3–4%）**：参考版 `eval` 每次求值
  `Tm::Lam` 都 clone 名字（church 展开下 O(n) 次），SmolStr clone 1ns
  vs String clone 7ns（≤23 B 内联存储免堆分配）。
- **parse 慢 15–29%**（2 万行标识符密集源 29.4 → 34.2 ms；church/conv
  小源 +25–30%）：`SmolStr::new` 构造 13–18 ns vs `String::from` 5 ns
  ——mimalloc 小分配太便宜，smol_str 0.3 的内联路径（23 B 零填充拷贝 +
  `Option<Repr>` 中转）反而更贵，换 `new_inline`（13 ns）也修不掉。
- **取舍**：parse 在 l02bench 计时外，且在整体负载里占比小（后续扩展新
  功能后更是小头），参考版 eval 的收益是纯赚，**采纳**。未实测的备选：
  `Rc<str>`（clone ≈ 引用计数、构造同 `String::from`）理论上「clone
  便宜且构造不贵」两全，若 parse 成本将来要紧可以再比。

## 后续提速（2026-08-29）：dup 复制强制负载 + quote 记忆化（call-by-need 轴）

- **新负载族 `--workload dup|dup_deep`**：`dup = D p_k`（`D = \x f. f x x`），
  nf = `λf. f C C`——λ-binder 把同一闭包值复制进两个实参槽，quote 对它
  **强制 2 次**；`dup_deep = D1 (D0 p_k)`，nf =
  `λf. f (λf'. f' C C) (λf'. f' C C)`，C 强制 **4 次**。L01
  `dup_pair`/`dup_deep` 的 L02 对应物，nf 节点数 4n+12 / 8n+28
  （`tm_size` 逐出现计数，DAG 共享不改断言）。定位（承接 L01 readme）：
  NbE 的 CBV 只急切到 WHNF、丢弃实参几乎免费，**真正的重复在
  readback**——这两族负载专门造出「同一句柄被多次 quote」的场景。
- **quote 记忆化口径 `quote_memo`**（L01 `bump_spine_memo` 的移植）：
  `Q` 先查 memo（键 = 值打包字 × quote level；闭包/spine 句柄单轮内全局
  唯一、spine 栈只增不改，缓存可靠），未命中则以 `MemoStore` 屏障压到
  任务栈最深处（LIFO 保证该值的整棵子任务先跑完，弹出时回填），命中
  直接共享子树（结果从树变 DAG）。表随每次 quote 调用新建——
  `Bump::reset` 后无跨轮悬垂键；Lvl/U 的 `Q` 是 O(1) 不走表。
- **实测**（k=15，n=65536）：dup 1.9×（fast 7.42→3.91ms）、dup_deep 3.4×
  （14.47→4.24ms），对 basic 22×/41×；**复制被完全塌缩为单次强制**
  （memo 后两负载同价，收益随复制层数指数增长）；church 线性负载零回归
  （fast_memo ≈ fast：`Q` 次数只有 O(λ 层)，链节点走 ChainRun 不过 memo）。

## 后续提速（2026-08-29）：conv 判等记忆化 + conv_dup 重复子对负载

- **conv 工作表记忆化**：同一 `(t.0, u.0)` 子对只结构比较一次。与 quote
  侧的键设计差异：**判等结果与 level 无关**（eta/Π 的 fresh 变量两侧对称
  插入、恒异于自由变量，比较树在任意 level 同构），键无需带 level；
  「已判等」靠工作表 LIFO 屏障 `WItem::Store`（机制同 quote 的
  `MemoStore`：纯合取下屏障弹出时其上方子比较全部完成——任何失败早已
  return false——弹出即入表）。表随本次 conv 调用新建，无跨轮悬垂。
- **新负载 `--workload conv_dup`**：`Rel = \A x y. (P : A -> U) -> P x ->
  P y -> P y` 的三个 cod 槽位让同一昂贵子对 `(p_k, add p_k zero)` 在一次
  check 里比较 3 次（建模依赖类型里「同一索引在类型多处重现」的常态；
  现有 conv 负载无命中场景——`P y` 两侧是同一句柄，被位相等剪掉）。
  无 memo：3 × O(n) 闭包展开 + 链游走；memo：1 次游走 + 2 次哈希命中
  （连同其下挂的展开整段跳过）。check-only，与 conv 同走 bench_check。
- **实测**（7 轮 min）：conv_dup 1.4-1.6×（k=13：5.12→3.27ms、k=12：
  2.38→1.71ms）；conv/church 零税（k=12 conv 0.833 vs 消融 0.807ms，
  噪声内）。`L02_NO_CONV_MEMO=1` 消融开关（NO_BITEQ 同款风格）。
- 负载构造的两个坑：初版 `Rel : U -> U -> U` 的 b 槽要求 `U` 但实参
  `x : A`，签名本身类型即错（改 Eq 同构的 `(A : U) -> A -> A -> U`）；
  λ binder 数须对齐展开后的箭头数（`Rel A x x` = `(P : A -> U) -> P x ->
  P x -> P x` 需 5 个 binder，多一个则 body 顶到非 Pi 值上报
  "Can't infer lambda"）。

## call-by-need 与 WHNF（概念注记）

常被问：call-by-need 是不是要专门做 WHNF？对教科书惰性图归约（Haskell
式）成立：call-by-need = **按需强制到 WHNF** + **thunk 原地更新共享**。
拆到本模块的 NbE 架构上，两个成分各有对应物——一个结构内建，一个是
第三/四轮补的：

- **WHNF 粒度 = 结构内建**。eval 遇 `Lam` 只做 O(1) `CloCell` 创建（体不
  运行），β 只是挂 env 继续创建闭包——「未强制的 thunk」就是闭包本身；
  真正做功的强制只发生在 quote/conv，quote 的每个 `EvalQ` 只剥一层
  binder，即一次 WHNF 步。这就是 L01 readme「NbE 的 CBV 只急切到
  WHNF」的含义——不需要再造一台「返回 WHNF 并更新 thunk」的求值机。
- **共享（同一值至多强制一次）= memo 表**。惰性机改写堆里的 thunk 格子
  （原地更新）；这里值是不可变 64 位打包字、env 节点跨闭包共享不可改写，
  以 (句柄, level) 表实现同等的「第二次 O(1)」——quote memo 管 readback
  强制（键含 level），conv memo 管 conv 内的强制（键 = 句柄对）。
- **demand-avoidance（未用实参不求值）= 免费**：核心无构造器/模式匹配，
  CBV 白求一个被丢弃的实参也只是 O(1) 闭包创建（L01 readme「丢弃参数
  几乎免费」），惰性的这第三半买不到东西。

两个容易误判的点：

1. **quote memo 键带 level 不是「漏掉的共享机会」**：同一值在不同 level
   强制时 fresh 变量不同，产出树索引平移本就不是同一棵树——惰性机的
   原地更新在此无对应物可省，属固有成本而非实现缺陷。
2. **eval 顺序是 CBV**：未类型化/不终止的输入上行为与惰性不同（惰性能
   返回处我们会发散）。类型检查只跑良构子项（强规范化保终止），实际
   无影响；做部分求值或非终止项推理时才需重估。

这句话何时才构成行动项：给惰性语言写运行时（必须造 WHNF 机）；核心
引入构造器/模式匹配后（L07+）重估强制粒度与求值策略的成本结构。

## 优化过程中的四个教训

1. **值的共享性是带类型 elaborator 的一级效应**（L01 的纯 NBE 没有暴露）。
   参考版最初把中性应用写成 `VApp(Box<Val>, Box<Val>)`：eval 每次查变量
   都 `clone()` 环境条目，而 let 绑定的 church 数一类中性链会随 β-级联
   在环境里层层传递、反复引用——每次 clone 都是 O(链长) 深拷贝，church
   翻倍负载实测 **O(n²)**（church 4096 的 nf 单步 quote 983 ms）。改成
   `VApp(Rc<Val>, Rc<Val>)`（clone = 引用计数，Haskell 原版 GC 共享的
   对应物；L03 值表示同款）后回到 O(n)：同规模 10.5 ms，**94×**。这就是
   参考版与性能版只差 ~10× 而不是更大的原因——两者都线性后，差距只剩
   表示/分配策略的常数。
2. **不要忽略 unused 警告**：性能版 `Machine::quote` 的 `level` 参数一度
   没有传进 `quote_iter`（硬编码 0），编译器警告了但示例测试全绿——
   直到 `show_val` 在非零 `cxt.lvl` 下引用**含自由变量**的值（报错路径
   里 quote `expected/inferred` 类型）才爆发。位相等快速路径恰好把触发
   条件剪掉了（关掉它做消融时才暴露）。修复即把 level 透传。
3. **快速路径不能是正确性的唯一依托**：`conv` 的 `(3,3)`（U==U）与
   `(0,0)`（变量==变量）最初依赖位相等分支兜底，结构 match 里没有显式
   分支。做位相等消融时 `conv(U, U)` 直接判假。现在显式分支与位相等
   并存：前者保证语义自完备，后者只做加速（消融可测）。
4. **否定一个轴前先确认负载覆盖了它的触发条件**：第二轮暂缓 quote 侧
   memo 的理由是「键从不重复」——那是当时两个负载（church/conv）的
   属性，不是机制的属性。补一个造命中场景的负载（dup 族）后 1.9×/3.4×
   立即兑现。反过来，β(clo,arg) eval 侧记忆化的否决经住了复验：NbE 的
   CBV 只强制到 WHNF，昂贵的整链展开 β 键在任意负载下都不重复（见上节
   call-by-need 注记）。

## 性能版移植清单（L01 → L02）

| L01 机制 | L02 移植 |
|---|---|
| bump arena（`Bt`/`Env`/`Bv`） | `Tm`（多出 `Pi`/`Let`/`U`）+ `EnvCons`/`CloCell` 全 bump |
| 打包值 64 位（3 个 tag） | 3 位 tag：Lvl/Clo/Spine/**U（立即数）**/**Pi（单元）** |
| spine 栈（len/base 记账） | 同款；conv 的 eta 也会 push（只增不减，句柄稳定） |
| 流式右链 quote（ChainRun） | 同款逐字移植 |
| eval 双栈 + 右链快速路径 | 同款 + `LetBody`/`PiBody` 续跑任务（let 的类型槽不求值） |
| quote 任务栈 | 同款 + `Pi1`（Π 值先引定义域再引余定义域） |
| Machine 稳态复用 | 同款；`Tycker` owns `Bump`（每轮 `reset`）+ `Machine` |
| ——（L01 无 conv） | conv 改 (level, V, V) 工作表迭代 + 位相等快速路径 |
| ——（L01 无 elaboration） | check/infer 直接在打包值上工作（Cxt 全 Copy） |
| ——（L02 后续提速） | eval β 岔路 `ApplyKnown` 直送（免 `Tm(f)` 重查环境）+ `ChainWrap(0)` 消除 |
| ——（L02 后续提速） | conv 连续链内联环（沿 `.a` 前进免 worksheet 往返）+ 入口长度 fail-fast |
| ——（L02 名字表示） | `Name = Span<SmolStr>`（≤23 B 内联，clone 免堆分配；性能版热路径是 bump `&str`，零字符串操作） |
| ——（L01 `bump_spine_memo`） | quote 记忆化 `quote_memo`：`MemoStore` LIFO 屏障 + (句柄, level) 表，重复 quote 共享子树（DAG） |
| ——（L01 无 conv） | conv 判等记忆化：`WItem::Store` LIFO 屏障 + (t.0, u.0) 成功集（判等结果与 level 无关，键无需 level） |

## 已知限制

- 两版共用 `parser::parser(..) -> Option<Raw>`：解析失败只有 `parse
  error`，没有 main.hs megaparsec 的带位置报错（token 组合子不追踪
  失败位置；后续层 L13 有完整的诊断设施）。
- `basic` 的递归 eval/quote/conv 深度受线程栈限（church 52 万层需要
  ~256 MB 栈，`L02_STACK_MB` 可调；再深用全迭代的 `fast`）。
- `basic` 的基准口径对 nf 结果 `mem::forget`（深 Box 树的递归析构会爆
  栈；bench 进程一次性，退出即回收——L01 readme「已知限制」同款）。
- 性能版的错误消息路径（`show_val`）会 quote + export 回参考版的
  `Box` 树再走共享的 pretty——只在报错时发生，不在热路径上。
