# D5 · 性能技术矩阵（技术 → 实测增益 → 复杂度/unsafe 代价 → 取舍）

> 角色：twin-techniques。只读静态分析，**不运行 cargo/bench**（bench 归 perf-experimenter，协议见 FRAMEWORK §2）。
> 口径：工作树 HEAD `8443586e`（2026-11-08）。标注：`[历史实测]`＝仓库既有实验数字（注明日期/出处；
> 跨窗口不可比）、`[码]`＝源码核对、`[文档]`＝文档断言、`[推断]`＝我的判断。
> 本文件回答 FRAMEWORK 的 **Q2（逐轴优劣）在性能技术上的一面**，并为 EXP-4 设计可执行消融方案（§7）。
> 读法：§2 是总矩阵，§3 是对易误读项的展开，§4 是单引擎可迁移性判决，§5 是双引擎产品判断，
> §6 是保留/重写/砍排序，§7 是 EXP-4。

## 0. 一页纸结论

| 决策 | 技术（按优先级） |
|---|---|
| **保留** | ① bump arena + 打包值 + 扁平 spine + 迭代内核（含右链快速路径）；② 有界记忆化（quote/conv/force）但必须带 fuel/taint/内存口径；③ `Tycker` 稳态复用 + 常驻 prelude（LSP 生命周期唯一正确解法）；④ 观察面 push 期渲染 + `observe` 闸；⑤ `name_map`+trail、复合环境 |
| **重写** | ① 记忆化基础设施（指针键/强持有 → 内容寻址 + 分代/Weak + 预算）；② prelude/resident/compact 三件事收成一个"快照层"；③ decl 表（`String` 键 + COW 整表 clone → `SmolStr` + 平铺快照）；④ 深值 Drop/quote/export/pretty 统一走显式栈 API；⑤ fuel 从"静默降级"改为"可诊断耗尽"；⑥ bench 口径补齐 `bench_check_nf`（L11/L12） |
| **砍** | ① Sum 臂 eval 记忆化（负结果）；② L12 `canonical`/`iddfs` 重试搜索（成功路径不经）；③ L01 已否决变体（`bytes_flat_value`/`native_clo`/`compiled`/条目瘦身等）与 17 个 `.bak`；④ L07–L12 的孪生从"产品候选"清单移除（只留 oracle/教学）；⑤ 无消费方的 eager nf+pretty（已删，禁止回归） |

**最意外的历史实测**（按意外程度）：
1. **最大的两个性能台阶都不是"优化算法"，而是删死工作和换共享方式**：L10 删 eager nf+pretty
   church k=13 **199.4→6.78 ms（29.4×）**；L11/L12 decl/name 表 COW 后 macro k=11 **114.6→4.00 ms（28.6×）**
   `[历史实测 2026-09-12，docs/opt-name-table-cow-2026-09-12.md §1/§2]`。
2. **Sum 臂 eval 记忆化：完整实现、正确性全绿，但性能全线回归 +5…+33%，已整体撤销**
   `[历史实测 2026-08-14，docs/l13-perf-review-4.md §9]`——"40% 重复求值"的量化依据是调用次数，不是成本。
3. **迭代内核不是普适赢家**：非右链形状上递归版 `bump_spine` 反超迭代版 **1.42×**（parigot_add n=10）
   `[历史实测 2026-10-06，docs/perf-l01-optimization-2026-10-06.md §0.1]`；而 12 行"尾任务寄存器化"
   （控制流事实）却测得 **−5.7…−7.4%**，条目宽度 40→24B 则测不出 `[历史实测 2026-10-06，perf-l02 §4.2/4.3]`。
4. **"稳态复用"本身只有 2–8%，但 bench 口径把它放大成幻觉**：`fast_ss` 排除了建表成本，
   `fast_ss` vs `fast` 同批交错仅 +1.6…+8.3% `[历史实测 2026-10-06，docs/perf-l02/00-baseline.md §4.4]`；
   它的真实价值在 LSP（常驻 prelude、kick 98 vs 359 ms、3.5×），不在 bench。
5. **双引擎问题已经从"要不要"变成"怎么收口"**：LSP 默认引擎已是孪生（`src/lib.rs:255-260`），
   语料 29/30 文件由孪生接管、总成本 1.64×/1.78× 领先参考版 `[文档 lsp-twin-wiring 经 l13-perf-replace §1.5]`。

## 1. 方法与口径（先于数字）

- **证据分级**：本文件不产生新数字。`[历史实测]` 分为三个窗口：08-06/08-14（L13 早期 perf 轮）、
  09-12/09-17/09-18/09-20（L07–L13 矩阵与专项）、10-06/10-07（L01/L02 严格 A/B）。窗口之间**不可直接比较**。
- **四个口径陷阱**（继承 D5 前一轮 L11 分析 + CROSS §3.1）：① `basic` 对 L11/L12 是全流程 `run`
  （参考版缺 `bench_check_nf`），对 L09/L10 是 check+nf；② `fast_ss` 解析在计时外、且含 `Tycker` 复用，
  与 `fast` 一次性不可混读；③ `fast_memo`/`fast` 是孪生内部口径，不等于参考版同机制；
  ④ 大值负载倍率随参考版地板变化（strchain L07 23× vs L09 867×），只读绝对时间或同层倍率。
- **测量噪声**：L01/L02 两轮已证本机 governor 有"档位成块"效应，min-of-min 的 p95 假阳可达 14–19%；
  可信判定必须是**同批交错 + 配对统计 + 每侧 ≥21 reps + 同批 null 地板**（L02 用此法把 ~6% 效应判出，
  C1 的 +0.4% 判为曲线噪声）`[历史实测 2026-10-06，perf-l02 §0.2/§4.1/§6]`。EXP-4 必须复用这套协议。

## 2. 技术总矩阵

### 2.1 表示与求值内核（孪生独占，L01 有系统实测）

| 技术 | 实现层/锚点 | 解决什么瓶颈 | `[历史实测]` 增益（日期/出处） | 复杂度/unsafe/维护 | 失败·回退/限制 | 可迁单引擎？ | 判定 |
|---|---|---|---|---|---|---|---|
| bump arena | L01 `bump_spine` 起；L02–L13 孪生（L13 `entry.rs:849 Tycker`）；分配器 mimalloc（`src/bin/l11bench.rs:29-30` 等） | 分配/释放局部性；树形 Rc 的每节点 malloc | 抬速账本里 arena 是底盘：`bump_tree` 0.197 ms → 打包+扁平 spine 0.160（−19%）`[历史实测 L01 readme:156-163，经 D1 §2]`；mimalloc 对 Windows 默认堆 4×（同源） | 中；`unsafe` 集中在打包/生命周期；无 Drop、跨轮泄漏须 reset/compact | wasm 2 GiB 硬顶：常驻 twin 单文件 ~1.2 GB vs 参考 0.33 GB → wasm 默认参考版（`l13-perf-replace §1.2`）；arena 换代会留下地址键缓存悬垂（a2-r1/a3-r1 已修类） | ✅（单引擎即选孪生内核） | **保留（基底）** |
| 打包 tag 值 `V` | L01 `bump_spine.rs:34-68`；L13 孪生 `syntax.rs`（`V`/`XCell`/`v_*`） | 24B→8B 值、O(1) tag 判定、免 enum 分支 | 打包 8B：−19%（同上账本）；`W` 枚举 40→24B 则**无可测收益**（store-forwarding 吸收）`[历史实测 2026-10-06，perf-l02 §4.2]` | 高；依赖对齐/高位 tag，`unsafe` 解码 | **真实 UB 案例**：wasm32 `&str` 仅 4 对齐导致低 3 位非 0（a5-r1 #1 已修，补 `#[repr(align(8))]` + const 断言）；tag 位宽 2-bit 已无余量（L01 判死） | ✅ | **保留，但补安全断言** |
| 扁平 spine + 右链快速路径 | L01 `bump_spine`；L13 孪生 `spine.rs:40` | 右链形状的 push/pop 与 O(1) 头判定 | 流式 quote −46%、eval 右链 fast path −43%（账本，同上） | 中高；不变量多（连续性引理） | — | ✅ | **保留** |
| 显式工作栈迭代内核（eval/quote/unify/rename） | L01 `bump_spine_iter`；L13 孪生 `eval.rs`/`quote.rs`/`unify.rs`/`rename.rs` | 深值栈溢出；可控 fuel/预算 | 迭代化 −21%（账本）；但非右链形状递归反超 **1.14–1.42×**（parigot/exponential）`[历史实测 2026-10-06，perf-l01 §0.1]` | 高；任务枚举/状态机重复 4 份；语义必须逐字等价 | 递归 fast path 未做（"值得做但窄"，同形状 memo 337× 更优）；`export`/析构不在计时窗（未测轴） | ✅ | **保留 + 重写为双模（递归快路径）** |
| 尾任务寄存器化（C2，12 行） | 模板：L02 `/tmp/l02-exp/exp9-c2.patch`；适用于 L03–L13 的 `eval`（3 处/层） | 免一次 40B store+load + 一轮 dispatch | **−5.70…−7.42%**（church/conv，k=13/15，四格判定成立）`[历史实测 2026-10-06，perf-l02 §4.3]` | 极低；纯控制流等价 | **未入 master**（补丁在 `/tmp` + `docs/perf-l02/raw/exp9-c2.patch`）；需逐层 A/B | ✅（最高性价比下沉项） | **重写/立即下沉** |
| `W` 缩小 / `#[inline]` / `ChainRun` 外提 | L02 | 缓存/分发 | C1 40→24B 未判定；`#[inline]` 预期 0–2%；`ChainRun` 0.00% `[历史实测 10-06]` | — | 均判"不要做" | — | **砍（不重试）** |

### 2.2 记忆化与稳态复用

| 技术 | 实现层/锚点 | 解决什么瓶颈 | `[历史实测]` 增益 | 复杂度/风险 | 失败·回退记录 | 可迁单引擎？ | 判定 |
|---|---|---|---|---|---|---|---|
| quote 记忆化（值×level） | L01/L02 `Machine.quote_memo`；L03+ 孪生默认；L13 `machine.rs:1366` | 共享子图重复 quote | dup 复制负载 1.25×（本机）/ readme 1.9×；线性负载中性 `[历史实测 10-06；docs/perf-l02/00-baseline §4.3]` | 中；`&'a Tm` 生命周期擦除（`unsafe` 引用回写）、跨轮清理 | 引用悬垂规则靠"入口 clear + bump.reset 不读"维持（a1-r3 审计） | ✅ | **保留** |
| conv/unify 判等记忆化（BITEQ + 工作表 memo） | L03+ 孪生 `unify.rs`；开关 `L0x_NO_CONV_MEMO` | 同层合一重复 | BITEQ 关掉 conv **+102…+121%**（2.02–2.22×）；conv memo 对 `conv_dup` **+47.6…+49.4%**、对 `conv` ≈0、church 反而 +1.8…+4.6% `[历史实测 10-06，perf-l02 §3]` | 中；memo 键/失效/快照三层耦合 | 归因不可单条：`NO_BITEQ` 同时关 4 个决策点、`NO_CONV_MEMO` 关"查表+插入+扩容" | ✅ | **保留（按负载调，不要默认全开）** |
| FORCE_MEMO（L13） | 参考 `mod.rs:163/194`（cap 1<<20，keepalive/taint/epoch）；孪生 `force.rs:297` | force 的巨量冗余 | prelude 装载 force **636M 次 / 188k 不同节点（~3400× 冗余）**，HDL prelude **11.0 s→1.8 s** `[文档 L13 README §3.3 / L13.md:149]` | 高；地址键 + 强持结果 + epoch 失效 | 1<<20 强持是长跑内存共同被告；`fuel0>0` 正确性洞已补（wip 评审轮）；孪生同代不回收免 keepalive（`bump_spine_iter.rs:77-78`） | ✅ | **保留，重写内存口径** |
| FRCS_MEMO（仅 wip 补丁） | `docs/wip/README.md` §四/§五 | σ/frcs 重建的重复（L13 σ 迁移语境） | 1<<20 口径把长链图钉到 **8 GB**；改 1<<18+溢出存活清扫：同速 9.2–9.8 s、CLI 峰值 430 MB；Weak/Weak 14.4 s；1<<14+溢出即清 **103 s**（抖动）`[历史实测 2026-09-16]` | 高；正确性守卫（fuel=0、σ-ABA、taint） | **未入 master**；长跑仍 13 GB 且增长（记录未修）；随 σ 迁移回退一起归档 | ⚠️ 仅当保留 σ 才需要 | **砍（随 σ 迁移）** |
| Sum 臂 eval 记忆化 | `eval(Tm::Sum, env)` 点级缓存 | 40% 同 (tm,env) 重复求值 | **净损失**：01-basics +22%、02-arithmetic +33%、hdl_ops +21%、adder_proof +30%、10-bundle +12%、11-bundle-deep +5%；正确性全绿（22 例逐字节一致）`[历史实测 2026-08-14，l13-perf-review-4 §9]` | 高（Mutex、DECL_VERSION、安全门控） | 已完整实现→验证→**撤销**；原因：一次性求值占 60%，守卫+锁+哈希成本 > 重复节省；命中窗口被 class Phase-B 表写切碎 | ❌ | **砍（负结果，勿重试）** |
| `Tycker` 稳态复用 | L13 孪生 `entry.rs:849`；bench `fast_ss` 口径 | 跨轮建表/建缓冲成本；LSP 常驻 | 同批交错仅 **+1.6…+8.3%**（church/dup_deep）`[历史实测 10-06，perf-l02/00-baseline §4.4]`；LSP 价值：kick **98 vs 359 ms（3.5×）**、语料总成本 1.64×/1.78× `[文档]` | 中；`!Sync` bump → TLS 常驻、`'static` transmute 纪律 | 常驻内存 429 MB 稳态/730 MB 峰值 vs 参考 ~200 MB（2.2×）；prime 失败需整段重建（~3.3 s 量级）；wasm 不可用 | ✅（LSP/CLI 常驻面） | **保留（产品必需，bench 收益小）** |
| σ 跨轮回收（`VSUB_REGS`/`vsub_reclaim`） | L07–L12 孪生 `subst.rs` | arena 跨轮泄漏 | 无独立数字（只做对拍）`[码]` | 中；出口归还 + 悬垂 Rc 不读的纪律 | 轮尾/出错出口都要 reclaim（`entry.rs:297-303`） | ✅ | **保留** |

### 2.3 工程/生命周期/语言耦合技术

| 技术 | 实现层/锚点 | 解决什么瓶颈 | `[历史实测]` 增益 | 复杂度/风险 | 失败/限制 | 可迁单引擎？ | 判定 |
|---|---|---|---|---|---|---|---|
| `name_map` + trail 撤销（O(1) 名字解析） | L03 孪生 `bump_spine_iter.rs:29/1475/1478`；`L0x_NO_NAME_MAP` 消融 | 长 let/binder 链名字解析 O(n²) | **仓库内无可引用的量化数字**（开关在、历史未测）`[码]` | 中；trail 与 mark 配对、遮蔽恢复 | 参考版仍线性 walk；L07+ 参考实现同族 | ✅ | **保留 + EXP-4 首测** |
| 复合环境（定义域平坦 defs + 绑定域持久链） | L03 起孪生；D1 A3 | 环境按位 nth O(D) | D1 判"决定性（O(n²)→线性）"，无单点数字 `[文档 D1 §1/A3]` | 中高；两套索引不变量 | L09/L10 参考版残余 D^1.93 未根治（loading 需换表示） | ✅ | **保留** |
| decl 表 COW（参考）/ 平铺就地写（孪生） | 参考 `cxt.rs:308/331 Rc<Decl>`；孪生 `&mut Cxt + Rc::make_mut`（`opt-name-table-cow §2`）；L13 decl 七元组 `mod.rs:432` | 每次 Cxt 构造整表克隆 O(D) | 参考 `53e8adb`：struct 2952→846 ms、macro 2696→842 ms（3.2–3.5×）；孪生：L11 macro 114.6→4.00 ms（28.6×）、universe 178.8→65.4 ms（2.7×）、prelude-hdl 2480→2366 ms（1.05×）`[历史实测 2026-09-12/17]` | 中；COW 语义 vs `&mut` 独占快照 | **残留 O(n²)**：插入仍"先 clone 再 make_mut"，缩放 3.5–4.0×/翻倍（末次 5.5×）；键 `String`（L12+ 才 `SmolStr`）→ 每条目一次 malloc（`perf-l08l13-followup §3.4`） | ✅ | **重写（平铺+快照）** |
| `Rc<dyn Fn>` → `PrimId` 枚举 | 参考 L11 `mod.rs:64`；孪生 `syntax.rs:17`、`eval.rs:235-319` | bump 不能携闭包；dyn 间接调用/胖指针；不可分析 | 无隔离数字（与表示层收益混合）`[未核实]` | 低；5 个内建要逐句移植（语义漂移风险） | 卡住 Prim 的 unify 臂、`string_to_global_type` 查表语义要逐一对齐（parity 闸门覆盖） | ✅ | **保留（单引擎采纳枚举）** |
| `Val::Nat(u64)` + `quote_nat` | L13 参考 `mod.rs:280/905/1080/115`；孪生 `XCell::Nat`；`NAT_CHAIN_LIMIT` 护栏 | Nat 一元链的定义相等与 eval 成本 | 无隔离数字；属语言语义而非纯性能 `[未核实]` | 高；与定义相等/quote 展开/prim 惰性归约耦合 | 孪生不会把 `succ(原生 Nat)` 折成 `Nat(k+1)`（语义分歧，`docs/l13-quirks-handoff-2026-10-02.md:206`）；trait 印象参数交互有已知 bug | ⚠️ 语言层单选，教学核心不宜 | **保留（生产层），需孪生对齐** |
| `Call`/`OpCall` 内联节点 | L12 `mod.rs:97-98`；L13 `mod.rs:533/655`、孪生头 `bump_spine_iter.rs:28-33` | def 体内联后的调用身份；quote 还原中缀显示 | 无隔离数字；L12 `canonical/iddfs` 是**负结果样本**（FINAL:520）`[文档]` | 高；与 canonical/replay/观察面耦合 | `unify` Call 快速路径的**无-Flex 预检**另计 −39%（`l13-perf-review §2.2`），那是"别克隆 meta"而非 Call 本身 | ⚠️ 生产层保留，教学层不要 | **保留（渲染/重放）；砍 canonical 搜索** |
| prelude 池化（参考 `PreludeSlot/PRELUDE_CACHE`） | L13 `mod.rs:1250-1257` 注释、`debug_test.rs:354`；孪生**无池**（`bump_spine_iter.rs:75`） | 进程内重复装载/编译 prelude | `PRELUDE_CACHE` 缓存预编译 prelude：debug 126 s→3.9 s `[文档 L13-code-review:57]`；Backend prelude 无缓存 每次启动 ~1.6 s（`l13-perf-review §3.1`，第三轮已实现） | 中；TLS 析构/池化状态清空纪律（PreludeSlot Drop 约束） | 孪生每 kick 从 `prime_round` 重放，靠常驻检查点而非池 | ✅（产品） | **保留（参考）/ 重写为统一快照层** |
| 常驻检查点 `prime_resident`/`observe_user` + `compact` 压实 | L13 孪生 `entry.rs:898/1134`、`compact.rs:589-600`；开关 `TYPORT_TWIN_NO_COMPACT` | LSP 每次编辑重建 prelude；arena 增长 | 压实：**每 kick 908 MB→181 MB**、常驻态 1835→429 MB；**代价 `compact_resident` 0.1→150–190 ms/kick**（A2.4 分解主体即压实）；kick 98 vs 359 ms `[文档 L13 README §4 / wip A-perf:197-198/252-272]` | 高；换 arena 后**所有地址键 TLS 缓存必须失效**（a2-r1/a3-r1 修复类；`resident_compaction_*` 测试仍 26.8 s 失败） | wasm 内存上限；`prime` 失败重建 ~3.3 s；不压实则 9× 内存；调大 `TYPORT_TWIN_BUMP_BUDGET_MB` 不改善墙钟（2.85 vs 2.86 s） | ✅（LSP 产品层） | **保留，重写为"快照层"（压实改阈值触发）** |
| push 期渲染 + `observe` 闸（owned 观察表） | L13 参考 `mod.rs:1413-1439/1542`；孪生 `machine.rs:523 observe: bool`/`1057`、`observe.rs:36/85/111`、prelude 期 `entry.rs:910 observe=false`；27 个 push 点 | bump 生命周期跨事件（hover/completion/inlay 必须在当轮转 owned String） | 观察面成本：prelude-core **39–41%**、prelude-hdl **19.0%**、wide_enum k=6/9 **54–59%**、k=11 15–21%（`L13BENCH_NOBSERVE=1`，wip 二进制）`[文档 round-23b §3 经 wip A-perf §A2.5]`；prelude LSP 表渲染 ~600 ms（core 1242 vs 637 ms）`[历史实测 2026-09-16，wip §一]` | 中；owned 快照契约、渲染与核心解耦 | master 孪生已有 prelude 闸（`entry.rs:910`）与用户面开关 `TYPORT_TWIN_NO_USER_OBSERVE`（`entry.rs:1152-1153`；LSP 用户面实测噪声内：20-misc 2807 vs 2827 ms）；**master 参考版无 prelude 总闸**（渲染后清空=死工作；wip 补丁 21.1 s→9.3 s，未全量落地） | ✅ | **保留（契约）；重写为按需渲染** |
| 迭代 Drop（`Tm`/`Val`） | L13 参考 `mod.rs:559/924` | 深值递归析构栈溢出 | 无性能数字；是健壮性技术 `[码]` | 中；析构状态机、每类型一份 | 孪生 bump 免疫（无 Drop）；参考版其他层仍递归 Drop（P11 未回灌） | ✅（参考/单引擎若有 Rc 树） | **保留（安全）** |
| fuel 降级（`UNIFY_FUEL` 4096 / `PM_FUEL` / L13 内层 100） | 各层 `mod.rs`；孪生 `force.rs:166`；CROSS §2.1 | 失控搜索/深链的有界化 | 无性能收益数字；是**正确性护栏** `[码]` | 中；三族语义不同、耗尽行为不一致 | **PM_FUEL 耗尽静默降级为裸 rigid**（`twin/unify.rs:413`）；L13 12k meta 解链仍爆栈（wip §二） | ✅ | **重写（预算耗尽=可诊断错误）** |

## 3. 易误读项展开

### 3.1 表示层：先问"这份工作是否必须做"，再问"用什么表示做"
L01 的单变量抬速账本（`bump_tree` 0.197 → 0.160 → 0.086 → 0.068 → 0.039 → 0.030 ms，
`[历史实测]` L01 readme:156-163 经 D1 §2）说明：打包/扁平 spine（−19%）、流式 quote（−46%）、
迭代化（−21%）、右链快路径（−43%）、稳态复用（−17%）——**量级逐级递减，最大的一档来自"把递归
quote 换成流式"而非"更快的数据结构"**。同一逻辑在带类型侧重演：删 eager nf+pretty（29.4×）、
decl 表 COW（28.6×）都大于任何指令级优化。⇒ 单引擎设计应先消除**无消费方工作**（渲染、克隆、
重复探测），再谈表示。

### 3.2 记忆化：三种成本必须同时记账（查表、失效、内存）
- **查表成本**有阈值：conv memo 对 `conv` 负载 ≈0（+0.2/−0.1%），对 `conv_dup` 才 +48%；BITEQ
  则对 `conv` 就是 2.02–2.22× `[历史实测 10-06]`。⇒ memo 必须按负载/形状选择，不能"全开"。
- **失效成本**：FORCE_MEMO 用 epoch/taint；FRCS_MEMO 需 σ-ABA 守卫 + fuel 守卫；Sum eval memo
  被 class Phase-B 的频繁 decl 表写切碎命中窗口（直接导致负结果）。
- **内存成本**：强持结果=钉住整张重建图。FRCS_MEMO 1<<20→8 GB / 1<<18→430 MB，
  FORCE_MEMO 1<<20 双强持是长跑另一被告 `[历史实测 09-16，wip §四/§五]`。⇒ 单引擎的 memo
  接口应内建"容量+分代+Weak+按输入存活清扫"，而不是每个 memo 各自发明。

### 3.3 迭代内核：保留，但要承认它不是普适最优
- 深值安全（避免栈溢出）+ 可显式 fuel 是**正确性收益**，这部分无条件保留。
- 性能上非右链形状递归更快（1.14–1.42×）`[历史实测 10-06]`。单引擎可做"递归快路径 + 迭代兜底"，
  但两套语义必须逐字等价（D1 A4 同判断）——先由 EXP-3/EXP-4 定制混合形状负载确认收益，再动手。
- C2（尾任务寄存器化）12 行、−6%、跨 L03–L13 全链同构，是**当前最值得立刻下沉的单点**；
  注意它未入 master，D6 应确认补丁可重放。

### 3.4 prelude/resident/compact/push 渲染：四件事一个生命周期
LSP 的真实成本结构是"prelude 装载一次 + 每 kick 复用 + 观察表跨 bump 转 owned + arena 增长后压实"：
- 常驻把 kick 从 359→98 ms，但内存 2.2×（429/730 MB vs 200 MB），wasm 因此必须回参考版；
- 压实把每 kick 908→181 MB，但代价是 `compact_resident` 从 0.1 ms 涨到 **150–190 ms/kick**，
  且换 arena 使所有**地址键缓存**失效（TLS 缓存/指针键 memo 必须同点清）；
- push 期渲染在 prelude 期是纯死工作（渲染后清空），参考版 master 缺总闸、wip 补丁 21.1→9.3 s；
- 观察面成本在 wide_enum 上可占 54–59%，说明"渲染"必须可关、可懒、可只对用户文件开。
⇒ 单引擎应把四件事收进一个显式 `PreludeSnapshot` 生命周期对象（装载→常驻→压实→观察闸），
而不是散在 `lib.rs`/`entry.rs`/`compact.rs`/`observe.rs` 四处靠注释维持纪律。

### 3.5 语言耦合技术（Nat/Call/OpCall/PrimId）不能只按性能评估
- `Val::Nat`/`Call`/`OpCall` 改变定义相等或节点身份，属**语言语义选型**：放进单引擎=承认"定义相等
  依赖表示"；放进教学核心会让"最简语义"失真。D5 的建议是：**生产引擎保留，教学/参考实现不要**，
  并把孪生与参考的 Nat 折叠差异（quirk:206）作为 parity 必修项，而不是性能项。
- `PrimId` 相反：它是纯表示选择（闭包→枚举），语义可逐句等价，且让 prim 可匹配/可分析，**应进单引擎**。

## 4. 可迁移性判决（目标：一个引擎）

| 技术 | 进单引擎？ | 以谁为基底 | 前置条件/改造 |
|---|---|---|---|
| arena+打包+spine+迭代内核 | ✅ 核心必选 | 孪生 | 补递归 fast path（可选）、对齐/生命周期断言、arena 换代清缓存纪律 |
| C2 尾任务寄存器化 | ✅ 立即 | 孪生（补丁） | worktree 重放 12 行补丁 → 逐层 A/B → 门禁 |
| quote/conv/FORCE 记忆化 | ✅ 统一接口 | 取三方经验 | 容量+分代+Weak+taint/fuel 守卫 + 按输入存活清扫；默认档随负载 |
| FRCS_MEMO / Sum eval memo | ❌ | — | 前者随 σ 迁移砍，后者负结果 |
| `Tycker` 稳态 + 常驻 prelude | ✅ 产品面 | 孪生 | 与 PreludeSnapshot 生命周期合并；wasm 降级策略 |
| prelude 池化/compact/push 渲染 | ✅ 产品面 | 参考池化 + 孪生常驻/压实 | 统一快照层；observe 闸默认对 prelude 关 |
| `name_map`+trail / 复合环境 | ✅ | 孪生 | 参考版也可受益（线性 walk 同源瓶颈） |
| decl 表 | ✅ | 双向 | `SmolStr` 键 + 平铺写 + 显式快照（替代 COW 整表 clone 的 O(n²) 残差） |
| `PrimId` | ✅ | 孪生 | 五个 builtin 逐句移植 + parity 钉 |
| `Val::Nat` / `Call` / `OpCall` | ✅ 仅生产 | 生产引擎 | 语义层决定；孪生 Nat 折叠对齐；不放入教学核心 |
| fuel 降级 | ✅ | 参考的"三档"思路 + 孪生有界池 | 耗尽→可诊断错误；补 `MATCH_CMP_BUDGET` 家族（L09–L13 缺） |
| 迭代 Drop / 深 quote/pretty | ✅ | L13 参考 + L07 `quote_deep` | 统一显式栈遍历 API，覆盖 Drop/quote/pretty/export |
| L01 已否决变体 | ❌ | — | readme 负结果清单，不再重试 |

## 5. 双引擎是否值得进产品？

**结论：产品只应有一个引擎（孪生内核），参考版降级为"测试 oracle + 受限回退"，不再作为并列交付面。**
证据（均为 `[文档/码]`，非本轮实测）：

| 事实 | 数据 | 锚点 |
|---|---|---|
| LSP 默认引擎已是孪生 | `Engine::lsp_default()`，仅 `TYPORT_LSP_ENGINE=reference` 才回参考 | `src/lib.rs:255-260/298/323` |
| 语料接管率 | examples 30 个中 29 个由孪生拥有，仅 `18-utils` 因 `untrusted-error` 回落 | `l13-perf-replace §1.3/§1.5` |
| 真实负载领先 | 每 kick 11,281 vs 18,461 ms（0.57×）；HDL 主力 2.7–4.1×；总比 1.64×/1.78× | 同上 §1.5 |
| 代价 1：内存 | 常驻 twin 429 MB 稳态 / 730 MB 峰值 vs 参考 200 MB（2.2×）；wasm 大证明 1.2 GB vs 0.33 GB → wasm 默认参考 | 同上 §1.2/§1.4 |
| 代价 2：跨文件 | 有 import/package 的文件仍回落参考（`twin_can_own`），twin 不导出 `cxt.namespace` | `src/lib.rs:1398-1402` |
| 代价 3：观察面降级 | 字段投影 `def_span` 退化为使用处 token（F12/rename 精度缺口） | `lsp-twin-wiring:1505-1510` |
| 代价 4：双引擎维护 | 孪生 62.7k 行（≈七层 49%）、parity 归一化盲区、17 个 `.bak`、文档腐化 | CROSS §1.1/§4 |

**判断（Q4 相关）**：
1. **L13 的"双引擎"保留但非对称**：参考版只做 oracle/教学/wasm/跨文件回退；孪生做交付。
   继续投 A2/A3（依赖文件喂常驻 twin、导出 namespace）把 cross-file 也收进孪生。
2. **L07–L12 的孪生不进产品**：外部消费者只有层内 parity/bench（CROSS §1.2 已 grep 证实），
   它们的价值是"第二实现 oracle + 技术孵化器"（本轮 D5 的大量数字来自它们）。
3. **不要再新增第三引擎**；新层的性能研究应在"单引擎 + 可消融开关"上做，而不是复制第二实现。
4. **双引擎维护成本可压缩**：先抽 `pretty/syntax`（D3/CROSS 已建议），再谈 parser；core 不合并。

## 6. 保留 / 重写 / 砍（排序与判据）

**保留（P0→P2）**
1. **表示内核**（arena+打包+扁平 spine+迭代内核+右链快路径）：唯一被系统实测证明的赢家组合（L01 账本）。
2. **有界记忆化三件套**（quote/conv/force）但统一接口、默认按负载：历史实测 1.25–2.2× / 3400× 冗余。
3. **`Tycker` 稳态 + 常驻 prelude + observe 闸**：LSP 产品的唯一可行生命周期（kick 98 vs 359 ms）。
4. `name_map`+trail / 复合环境 / `PrimId`：低成本、可验证、可进单引擎。
5. 迭代 Drop / 深值安全：正确性，不是性能。

**重写（P0→P2）**
1. **记忆化基础设施**：现在 4 套 memo 各自发明键/失效/容量（FORCE_MEMO/FRCS_MEMO/quote/conv），
   且两次因内存口径翻车（8 GB、13 GB）。改成统一 `Memo<K,V>`：内容/指针键 + 分代 + Weak + 预算 +
   fuel/taint 守卫；默认容量按"活跃值集"而非固定格数。
2. **prelude 快照层**：池化（参考）/常驻（孪生）/压实（孪生）/observe 闸四件事合并，边界一个对象。
3. **decl 表**：键 `SmolStr` + 平铺写 + 显式快照；消掉参考版 COW 残留 O(n²)（3.5–4.0×/翻倍）。
4. **深值遍历统一 API**：Drop/quote/pretty/export 四份递归各自防爆栈不是长久解。
5. **fuel 语义**：耗尽=可诊断错误（三档），补 `MATCH_CMP_BUDGET`；这比继续调大 4096 更重要。
6. **bench 口径**：L11/L12 补 `bench_check_nf`，否则跨层参考版数字长期不可比（a7-r1 §3.2/§4）。

**砍（P0→P2）**
1. **Sum 臂 eval 记忆化**：完整实现后 +5…+33% 回归，撤销（p0 负结果）。
2. **L12 canonical/`iddfs` 重试搜索**：成功路径不经，负结果样本；保留 `Call` 渲染价值即可。
3. **L01 已否决变体**（`bytes_flat_value` 2547×、`native_clo`/`compiled`/条目瘦身/内联槽等）：
   readme 已判死，不再进任何"最优"候选。
4. **17 个 `.bak`（12,464 行）与 L07–L12 孪生的"产品候选"身份**：前者删，后者降级为 research artifact。
5. **micro-opts 负结果**：Obj 帧 Sum 快跳（1.485 vs 1.461 s 噪声内）、`W` 缩小、`#[inline]` 提示、
   `ChainRun` 外提——列入"不要做什么"。

## 7. EXP-4 消融实验设计（交 perf-experimenter 执行；本报告只设计）

### 7.1 协议（复用 L01/L02 已证方法，避免 09-20 前的噪声结论）
1. **构建一次**：`CARGO_TARGET_DIR=C:\ezl-target cargo build --release --bins`；同一二进制跑 A/B
   （环境开关在两臂间切换，**每臂独立进程**——开关是 `LazyLock` 只读一次，见 `perf-l02 §3`）。
2. **配对交错**：每实验三段 `nullA / A-B 交错 / nullB`，每侧 ≥21 reps（或 bench `--rounds` 内轮），
   pair 内顺序奇偶交替；判定用同批 null 配对地板（p95），`|ratio−1| ≤ 地板` 判"未判定"。
3. **记录**：`experiments/raw/exp4-<子号>-<负载>-<k>.json`（原始 rep、二进制 sha256、CPU 频率/温度提示、
   owner/时间）；文件锁 `experiments/.lock`（FRAMEWORK §2.5）。
4. **门禁**：任何 patch 类实验先过 `cargo test --lib <层>` + 对应 `lXX_fast_parity`；主树工作区零改动，
   patch 走 `git worktree`（FRAMEWORK §2.6）。

### 7.2 开关现状审计（先纠正 FRAMEWORK 的清单）
| 开关 | 是否真消融 | 语义/锚点 | EXP-4 处置 |
|---|---|---|---|
| `L02_NO_BITEQ` | ✅ | 关"位相等+链内联环"（4 个决策点之和） | E4.3 |
| `L02_NO_CONV_MEMO` / `L03…L06_NO_CONV_MEMO` | ✅ | 关 conv 判等 memo（查表+插入+扩容之和） | E4.1 |
| `L03…L06_NO_NAME_MAP` | ✅ | 回落线性名字 walk（`L03 bump_spine_iter.rs:34`） | E4.2（首测） |
| `TYPORT_TWIN_NO_COMPACT` | ✅ | 关 L13 孪生压实（`compact.rs:589-591`） | E4.4 |
| `TYPORT_TWIN_NO_USER_OBSERVE` | ✅ | 关用户文件观察面渲染（`entry.rs:1152-1153`；prelude 期已由 `entry.rs:910` 置 `observe=false`） | E4.5 |
| `TYPORT_LSP_ENGINE` | ✅（引擎级） | 选参考/孪生（`src/lib.rs:298/323`） | E4.7 的端到端对照 |
| `L07_LOOP` / `L08_LOOP` | ❌ **调试打印** | `LOOP_DEBUG`（`L07/mod.rs:23-25`），非性能机制 | **从 EXP-4 移除**（误列）；可改名为 `*_DBG` |
| `L11_LOOPCAP` | ❌ **错误渲染探针** | `eprintln!("TRACE no_object …")`（`L11 twin machine.rs:1376`） | 移除；同上 |
| `L13BENCH_NOBSERVE` / `L13BENCH_NO_LSPTABLES` | ⚠️ 仅 wip 二进制 | 不在 master bin（grep 0 命中）；wip 实测 19–59% | E4.5 需 worktree 重放补丁 |
| quote memo / FORCE_MEMO / FRCS_MEMO | ❌ master 无开关 | quote memo 恒开；FORCE_MEMO 恒开；FRCS 只在 wip | E4.6/E4.8 需 10–20 行 worktree 开关 |
| decl 表 COW/平铺 | ❌ 无开关 | — | E4.9 需 worktree A/B（克隆 vs `make_mut`） |

### 7.3 实验清单
| ID | 实验 | 变量/控制 | 负载·k | 指标 | 假设/预期（历史依据） | 优先级 |
|---|---|---|---|---|---|---|
| E4.1 | conv memo 消融 | `L0x_NO_CONV_MEMO∈{0,1}` × 层 L02–L06 | 各层 `conv` + `conv_dup`/`dup`，k=11/13 | 每 rep 时间、null 地板 | L02：conv ≈0、conv_dup +48%；L03–L06 是否同构未测 | P0 |
| E4.2 | 名字表消融 | `L0x_NO_NAME_MAP∈{0,1}` × L03–L06 | 深 binder/let 链（`universe`/`strchain` 或 `church`），k=11/13 | 时间 scaling 每翻倍因子 | 假设 O(D²)→线性；**仓库无历史数字**，首次量化 | P0 |
| E4.3 | BITEQ 分解 | `L02_NO_BITEQ`（4 决策点之和） | `conv`/`conv_dup`，k=13 | 时间 + 分配计数（`l02l05mem`） | 2.02–2.22×（conv）复现；勿拆成单条归因 | P1 |
| E4.4 | L13 压实 | `TYPORT_TWIN_NO_COMPACT∈{0,1}` | `l13bench prelude-core/hdl`、LSP kick 序列（`typort` 或 `l13bench --only fast`） | 时间、峰值 RSS、每 kick 增长 | 省内存 908→181 MB/kick，代价 **+150–190 ms/kick**（A2.4）；找触发阈值（live 字节/增长比）以摊销 | P0 |
| E4.5 | 观察面渲染成本 | master `TYPORT_TWIN_NO_USER_OBSERVE`（`entry.rs:1152`）+ wip `L13BENCH_NOBSERVE` | prelude-core/hdl、wide_enum k=6/9/11、examples 用户文件 | 时间、观察表条目数 | prelude 已由 `observe=false` 闸掉；用户面 19–59%（wip round-23b，需 HEAD 复测）；判断"按需渲染"是否优于"全量 push" | P1 |
| E4.6 | quote memo 边际 | L02 `fast` vs `fast_memo`（口径同二进制） | dup/dup_deep/church，k=11/13 | 时间、节点数互检 | 复制负载 1.25–1.9×、线性中性；本机复测 | P1 |
| E4.7 | 稳态复用真实收益 | `fast` vs `fast_ss`（同批交错） × L09–L13 | 各层主负载，k=11 | 时间、常驻内存 | 仅 2–8%（church/dup_deep 已知）；验证是否被建表税放大 | P1 |
| E4.8 | FORCE_MEMO 能力曲线 | worktree 加开关：`{on, off, cap=1<<18}` | L13 prelude-hdl / adder_proof | 时间、峰值 RSS、命中率 | on：11.0→1.8 s（HDL）；off 复现瓶颈；cap 选址 | P2 |
| E4.9 | decl 表写策略 | worktree：参考 COW vs 平铺 `&mut`（L11/L13） | `universe`/`macro`/prelude-hdl，k=11 | 时间 scaling、内存 | 期望消 O(n²)（残留 3.5–4.0×/翻倍） | P2 |
| E4.10 | C2 寄存器化 | worktree 重放 `exp9-c2.patch` × L02–L13 | church/conv（L02）、各层主负载 | 时间（同批交错） | −5.7…−7.4%（L02，10-06）；L13 真实负载端到端是否仍成立 | **P0（唯一已判定待下沉）** |
| E4.11 | fuel 耗尽行为 | worktree 设 fuel=0/极小 | 深值/深链样例 | 判定（Ok/Err/崩溃）+ 时间 | 验证"耗尽=假不可达/静默降级"的面；为语义重写立据 | P2 |

### 7.4 与判决的映射
- E4.1–E4.3 决定 conv/BITEQ 的"默认开/按负载开"；E4.4–E4.5 决定 prelude 快照层与 observe 闸；
  E4.7/E4.6 决定 `Tycker`/quote memo 的展示口径；E4.8/E4.9 支撑记忆化与 decl 表重写；E4.10 是
  唯一"已判定、只差落地"的收益项，建议 Lead 直接排期；E4.11 服务 D2 的正确性口径。
- 若 E4.1 在 L03–L06 复现 L02 的 +48%，则"conv memo 默认开"成立；若否，则 memo 应做成**按负载/
  形状自适应**而非默认，避免 church 类负载的 +1.8…4.6% 税。

## 8. 局限与缺口（诚实清单）

1. **本文件零新测量**：所有数字来自 08/09/10 月历史轮次；09-20 后 L07/L08 加固、3b907be9 拆分、
   1719292d 寄存器化均可能改变基线，EXP-3/E4.10 需重测。
2. **部分技术在仓库内没有隔离数字**：`name_map`、复合环境、`PrimId`、`Val::Nat`、`Call`/`OpCall`、
   迭代 Drop——只能给机制作用与锚点，不能给增益；已标 `[未核实]`，由 EXP-4/EXP-5 补。
3. **测量环境**：本机 governor 档位噪声使 <3% 的效应不可判；EXP-4 必须带 null 地板，否则会重演
   "跨批比较得出假收益"。
4. **σ 迁移负结果**（22.4→637 ms、12k meta 解链、13 GB、4 个 parity 失败）与本矩阵交叠：
   FRCS_MEMO/深 quote 两行应读作"该路线的成本记录"，不是"这些技术本身无效"。

## 9. 给 Lead 的一句话结论

**性能赢家是"删死工作 + 单一有界记忆化 + 孪生内核 + 常驻 prelude"，不是继续堆第二引擎；先落地 C2（−6%）与 EXP-4 的 4 个 P0 消融，再谈架构合并。**
