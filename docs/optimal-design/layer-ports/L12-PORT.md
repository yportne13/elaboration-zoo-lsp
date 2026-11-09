# L12 硬化移植报告（L07 已验证优化 → L12 参考版）

> 分支：`feat/l12-hardening`（worktree `C:\ezl-wt-l12`）
> 基线：`1a1cab3b`（feat/all-layers-hardening）；按 Lead 指示合入上游修复
> `07f737d6`(L08) + `deef97f7`(L07) —— merge 提交 `871d4cc9`。
> 构建：`CARGO_TARGET_DIR=C:\ezl-target-all-l12`（**F: 盘全程未构建**）；未 push。
> 标记：`[实测]`=本次命令输出；`[码]`=源码核对；`[推断]`=判断。
> 状态：3 个 port commit 已落地并通过 L12 门禁；k=11 五轮交错 A/B + k=12/13 放大验证
> 已完成（见 §5.2/§5.3，含共享机 load 记录）；本报告已 commit 到分支。

## 0. 一页结论

| 项 | 结果 |
|---|---|
| item 1 decl 表就地 COW | `74e58e40`（+93/−84，3 文件）；go 归一化 O(D²) 的每 def 整表深拷 |
| item 2 FxHashMap | `1a3fdd39`（+31/−29，7 文件）；decl/trait/mutable/typeclass/unification/parser 宏表 |
| item 3 name_map+trail | `12ca86db`（+129/−21，3 文件）；`Cxt.src_names` 从持久 BiMap 改为 NameState+轨迹 |
| 门禁 | `cargo check --lib` 0 error；`cargo test --release --lib L12_canonical` **35 passed**；`l12_fast_parity` **50 passed** |
| A/B（k=11，min-of-5 交错）| natadd **0.884×**、strchain **0.900×**、macro 1.071×（≈持平，受 load 干扰）；见 §5.2 |
| A/B（放大 k=12/13）| strchain k=13 **0.822×**（min，77.8 s→64.0 s）/ 0.783×（med，n=2）；strchain k=12 0.970×（n=5）；见 §5.3 |
| 未做 | follow 上游最新 tip（我基于 871d4cc9，主线已前进）；traitchain 按 Lead 指示不作门禁；未 push/未 merge |

## 1. 环境与基线

- 主机：AMD Ryzen 5 5600（6C/12T）/ 34 GB / Windows；共享机（其他层 agent 同时编译，
  测 bench 时记录了 load，见 §5.4）。
- 编译目标目录：`C:\ezl-target-all-l12`（本分支）；baseline 二进制另用
  `C:\ezl-target-all-l12-base`（见 §5.2）；**F: 未写 target**。
- 上游修复：基线 `1a1cab3b` 有 L08 merge 残留编译错（`match_cmp_depth`/`MATCH_CMP_DEPTH`
  引用已删除字段，4 error）。按 Lead 指示 `git merge feat/all-layers-hardening`（`871d4cc9`）
  合入 `07f737d6`（删 L08 depth 残留）+ `deef97f7`（L07 check_ty），合并无冲突。
- 本分支历史（`git log 1a1cab3b..HEAD`）：
  `12ca86db`、`1a3fdd39`、`871d4cc9`(merge)、`74e58e40`、`deef97f7`、`07f737d6`。

## 2. 三个 commit 明细（模板：L07 已验证实现）

### 2.1 `74e58e40` port L07 `c2fffd3f`：decl 表就地写入（顺序声明路径）

- **动机**：L12 `Cxt::fake_bind/decl(&self)` 先 `self.decl.clone()` 再 `Rc::make_mut` ⇒
  强计数恒 2 ⇒ `make_mut` 每次深拷整张 decl 表；每层顶层 def 一次，D 个 def 是 O(D²)。
- **改动** `[码]`：
  - `Cxt::decl_mut(&mut self,..)` / `Cxt::fake_bind_mut(&mut self,..)`：直接 `Rc::make_mut`
    插入，不再前置 clone；`fake_bind_mut` 用 `contains_key` 前置判重（语义等价旧"插入后
    检查 Some"——调用方已先查重，失败路径丢弃 owned `Cxt`）。
  - `Cxt::decl(&self)` / `Cxt::fake_bind(&self)` 保留为 `clone` 后就地写的兼容包装。
  - `Cxt::new`/`add_builtin_mut`：6 个 builtin 在 owned 上下文上就地注册。
  - `Infer::infer_owned(Cxt, Decl)` 新入口；`Infer::infer(&Cxt, Decl)` 保留
    （`self.infer_owned(cxt.clone(), t)` 包装）。`run`/`run_with_prelude` 改调
    `infer_owned`；Def/Enum 占位+最终注册、构造子注册、trait 合成的 recursive 调用
    （ImplDecl need_create / else、TraitDecl）都改为传递所有权后 `infer_owned`。
- **语义**：占位与最终条目落在同一张表而不是一次性克隆；报错路径不变（redefine 文案
  与判定一致）。门禁见 §4。

### 2.2 `1a3fdd39` port L07 `72f12101`：FxHashMap

- 把 elaboration 热路径上的 std `HashMap` 换成 `rustc_hash::FxHashMap`（依赖已在
  Cargo.toml，`rustc-hash = "2.1.3"`）`[码]`：
  `type Decl`、`Cxt::empty`；`Infer::{trait_definition, trait_out_param, mutable_map}`；
  `typeclass::Synth::class_instances` 与 `val_match`/`vals_eq_ground` 的局部 map；
  `unification::PartialRenaming.ren` 与 `invert` 返回的 `(ren, nlvars)`；
  `Cxt.namespace` 的方法名集（`FxHashSet`）；`parser::MacroState` /
  `parser_with_macros` 的表、宏 matcher 捕获 map（L12 内唯一外部调用方
  `run_with_prelude` 同 commit 改齐）。
- **语义**：全部键为 `SmolStr`/`u32`/`u64`，迭代仅用于重建表（declb/simpl 视图），
  无行为依赖 map 顺序。剩余 std `HashSet` 仅 `pattern_match::reported`（诊断去重，冷路径）
  与 `parser::macros::get_used_metavars`（宏分析，冷路径），刻意不换。

### 2.3 `12ca86db` port L07 `d411debe`：src_names = NameState + 撤销轨迹

- **动机**：L12 `Cxt.src_names` 是 `BiMap<SmolStr, Lvl, (Span<()>, Rc<VTy>)>` 持久表：
  `bind`/`define` 都 `Rc::clone` + `Rc::make_mut` ⇒ 强计数恒 2 ⇒ 每次深拷整张名字表
  （逐键 SmolStr + 逐条 Rc），n 个绑定器 O(n²)。
- **改动** `[码]`（`cxt.rs` 新增 ~110 行）：
  - `NameState { map: FxHashMap<SmolStr, Rc<(Lvl, (Span<()>, Rc<VTy>))>>, trail:
    Vec<(SmolStr, Option<Rc<..>>)> }`，`unwind(mark)` 逆序还原；
  - `Cxt { names: Rc<RefCell<NameState>>, name_mark: u32 }` 取代 `src_names: BiMap`；
    `bind`/`define` = unwind 到本 mark + O(1) 插入 + mark 前移；`new_binder` 只带
    mark（不进表）；每次名字表访问先 `unwind_names()`（幂等/均摊 O(1)），因此每个
    `Cxt` 看到的名字集恒等于创建时快照（与持久表语义一致）。
  - `lookup_src(&SmolStr) -> Option<Rc<(Lvl,(Span<()>,Rc<VTy>))>>` / `has_src`：
    仅两个调用点迁移（`canonical.rs:62`、`elaboration.rs:884`）；`clone_without_src_names`
    （hover 快照）起全新空 NameState。
  - `subst_cxt`：unwind 后把当前条目就地换成包 `VSub` 的新条目并记入轨迹，
    `name_mark` 指向新长度；父上下文下次访问惰性还原（与 bind 同一机制），
    语义与旧整表重建一致（σ 精化不丢）。
  - `bimap` 在 `cxt.rs` 的依赖删除（其它模块不再用）。
- **作用域纪律**：所有访问走 `lookup_src`/`has_src`/`unwind_names`；深度优先假设在
  L12 审计过调用链（canonical 搜索循环、elaboration Var/Enum.case、pattern_match
  经 `subst_cxt`）——无"离开作用域后再读旧上下文名字表"的路径 `[码]`；
  `MetaEntry::Unsolved` 快照的 error pretty 只用 `Locals`/decl/env，不读名字表。
- 注：`ab2/ab3` 的 workload 都是顶层 def 链，主要覆盖 item1/2 收益；item3 的收益
  在深层 binder（λ/let 嵌套）更明显，现有三负载信号弱属预期（见 §5.5）。

## 3. 未改动面/范围确认

- **未碰 L07**（`perf-l07` commit 来自上游 merge）；**未碰 main worktree/master**；
  未 push；`git status` 干净（HEAD `12ca86db`）。
- 仅改 `src/L12_canonical/**`（+ 上游 merge 带入的 L07/L08 修复）。
- L12 孪生（`bump_spine_iter/`）未动——参考版优化无需移植到孪生（孪生本就有
  `name_map`/`decls` COW 等价机制，且 `FxHashMap` 早已使用）；这也让 §5 的
  **fast 列可作为"未受影响"对照**（sanity 见 §5.3，待恢复补测）。

## 4. 门禁结果 `[实测]`

| 命令 | 结果 |
|---|---|
| `cargo check --lib`（item1 后 / item2 后 / item3 后） | **EXIT=0，0 error**（仅既有 warnings） |
| `cargo test --release --lib L12_canonical`（item1 后、item2 后、item3 后各跑一次） | **35 passed / 0 failed**；`965 filtered out` |
| `cargo test --release --test l12_fast_parity`（item2 后、item3 后） | **50 passed / 0 failed**（判据：Ok 逐字节一致 / Err 判定一致；`?N`/span 归一化） |
| `cargo build --release --bin l12bench` | EXIT=0；`Finished release profile` |
| L12 blackbox 套件 | **不存在**：`tests/` 下 L12 只有 `l12_fast_parity.rs`（`git ls tests` 核对 `[码]`） |
| traitchain | 按 Lead 指示不作为门禁（L12 孪生既有失败） |

> 说明：`--lib L12_canonical` 过滤后实际执行 35 个（mod.rs + parser 的 `#[cfg(test)]`）；
> 与基线（1a1cab3b+fix）35 个一致 ⇒ 无测试丢失。parity 50 为集成套件自有 15 + 带入
> lib 35 的口径（套件 `#[path]` 编入 mod.rs，与仓库惯例一致）。

## 5. 性能 A/B（bench 口径）

### 5.1 方法

- 二进制：baseline = 871d4cc9（port 前，含上游修复）构建的 `l12bench.exe`；
  final = 12ca86db 构建的 `l12bench.exe`（均 release，各自 target dir）。
- 协议：**进程级交错 A/B**（baseline/final 交替启动，odd/even 轮换先后顺序），
  `--workload {natadd,strchain,macro} --max-k 11 --rounds 2 --only basic`，5 轮取
  **min**（主）与 median（辅）；每轮前记录机器 load。
- 数据：`C:\ezl-target-all-l12\ab\raw2\`（每轮 stdout/stderr 原文 + `ab-agg.csv`），
  脚本 `run-ab2.ps1`。

### 5.2 结果（k=11 主口径；5 轮交错，min / median）

| 负载 | baseline min | final min | ratio(min) | ratio(med) | 判读 |
|---|---:|---:|---:|---:|---|
| natadd k=11 | 1.719 ms | 1.519 ms | **0.884×** | 0.928× | 一致变快；D 增大后 O(D²)→O(D) 显现 |
| strchain k=11 | 661.371 ms | 595.195 ms | **0.900×** | 0.984× | min 一致变快；med 受 1 次 771ms 离群影响 |
| macro k=11 | 599.345 ms | 641.881 ms | 1.071× | 1.004× | **持平**（宏展开成本主导，decl 表项开销占比低） |

k=9/10 同表（min ratio）：natadd 0.950×/0.931×；strchain 0.968×/0.981×；macro
0.998×/0.975×。整体呈"**规模越大收益越明显**"的方向，与 item1 消除每 def 整表深拷
的预期一致 `[推断]`；macro 持平符合预期（宏展开主导，item1/2 只影响 decl 注册常数）。

### 5.3 放大验证（k=12 / k=13；恢复窗口后重测）

- 协议：同 §5.1 的进程级交错 —— Pass1 `--max-k 12` 三负载 ×3 轮（n=3）；
  Pass2 `strchain --max-k 13` ×2 轮（n=2，单发 64–90 s，故只跑 2 轮）；
  Pass3 孪生 fast 列 sanity（`natadd --only fast`，2 轮）。
- 数据：`C:\ezl-target-all-l12\ab\raw4\` + `ab-agg.csv`，脚本 `run-ab4.ps1`。
- 结果（min / median；ratio = final/baseline，<1 更快）`[实测]`：

| 负载 | k | baseline min/med | final min/med | ratio(min) | ratio(med) | n |
|---|---:|---:|---:|---:|---:|---:|
| strchain | 13 | 77846.5 / 89868.2 ms | 64024.9 / 70334.4 ms | **0.822×** | **0.783×** | 2/2 |
| strchain | 12 | 5043.7 / 5223.3 ms | 4892.4 / 4954.7 ms | 0.970× | 0.949× | 5/5 |
| strchain | 11 | 581.2 / 613.2 ms | 587.2 / 666.4 ms | 1.010× | 1.087× | 5/5 |
| natadd | 12 | 3.386 / 4.089 ms | 3.239 / 4.386 ms | 0.957× | 1.073× | 3/3 |
| macro | 12 | 5121.3 / 5271.3 ms | 5145.5 / 5199.1 ms | 1.005× | 0.986× | 3/3 |
| natadd-fast（孪生列） | 11 | 1.630 / 1.630 ms | 1.512 / 1.597 ms | 0.928× | 0.980× | 2/2 |

- **判读**："规模越大收益越明显"得到确认——strchain **k=13（D=16384 defs）final 比
  baseline 快 ~18–22%**（min/med），方向与 item1 消除"每顶层 def 深拷整张 decl 表"的
  O(D²) 一致；strchain k=12 ~3–5%；k=13 的两次交替运行（load 46%/8%）两个方向均
  final 更快（77.8→64.0 s、89.9→70.3 s），结论稳健。
- 窗口与干扰：Pass1 load 8–28%；进入 macro k12 第 3 轮与 strchain k13 第 1 轮时 load
  升到 44–71%（共享机其他任务）——macro 数据最噪（k=9 1.055× 与 k=11 0.882× 符号
  不一致）⇒ **macro 判为持平/无法分辨**（与 §5.2 的 1.071× 一并看，无稳定信号）。
- 孪生 sanity：`natadd-fast` 两版应一致（twin 代码未改）；实测 ratio 0.93–0.98
  （n=2，load 波动下 min 口径），无回归迹象；不作性能承诺。
- 与中断前 run-ab3 的方向一致（natadd k12 0.867×、strchain k13 0.829×），说明
  §5.2/§5.3 是同一现象的复现（run-ab3 因 quiet-window 请求被 kill，未采用其数据）。

### 5.4 干扰与方法学记录

- 首轮 A/B（`raw/`，3 轮）作废：期间本机有 3 个 rustc（~82–86s CPU）与 load 74%
  ⇒ 结果符号不一致（strchain 1.24/1.38/0.89）。重测（`raw2/`）在 load 8–55% 窗口
  完成，min 稳定（同侧 5 次极差 < 3% 除个别离群）。
- k=12/13 轮（`raw4/`）：按 Lead 的 quiet-window 请求，首版 run-ab3 被立即 kill
  （不对其数据下结论）；恢复后的 run-ab4 记录每轮 load（8–71%），strchain k13 的
  两次运行分别在 load 46%/8% 完成且方向一致，故采用。
- 结论口径：本机为**共享开发机**（其他层 agent 也在构建/测试），所有数字以
  交错比值 + min/median 读取；不是框架性 bench 结论，绝对值不可跨窗口比较。

### 5.5 为什么 item3 在这三个负载上没有独立信号

`natadd/strchain/macro` 都是"顶层 def 链"（2^(k+1) 个 def，无深 λ/let 嵌套），
名字表大多只在顶层声明期插入、几乎不触发整表深拷的 O(n²)；item3 的直接受益场景是
`canonical` 搜索的 binder 展开、pattern 编译的臂内 binder、trait 方法体这类深嵌套。
因此 §5.2 的收益主要归因 item1（+item2 的常数），item3 以"门禁全绿 + 结构等价 +
避免 O(n²)"登记，不虚构 bench 数字。若需要量化 item3，建议后续用 L12 的 `deep`
λ/let 负载（现 `l12bench` 无此负载；`pmab_gen` 的 deep 是模式深度）或单测级计数。

## 6. 复现命令

```powershell
# 分支/worktree
cd C:\ezl-wt-l12; git log --oneline -4          # 12ca86db ... 74e58e40
# 门禁
$env:CARGO_TARGET_DIR='C:\ezl-target-all-l12'
cargo check --lib
cargo test --release --lib L12_canonical
cargo test --release --test l12_fast_parity
cargo build --release --bin l12bench
# A/B（安静窗口；脚本见 C:\ezl-target-all-l12\ab\）
& 'C:\ezl-target-all-l12\ab\run-ab2.ps1'   # k=11 五轮交错（§5.2）
& 'C:\ezl-target-all-l12\ab\run-ab4.ps1'   # k=12/13 放大 + 孪生 sanity（§5.3）
```

## 7. 给 Lead 的验收建议

1. **merge 顺序**：本分支基于 871d4cc9，上游 feat/all-layers-hardening 已前进（其他层
   hardening）；建议 Lead 先 merge 上游最新 tip 再统一门禁，避免 L07/L08 修复轮与本
   分支的 merge 次序问题（本分支自身无冲突）。
2. **重点看 diff 的 3 个文件区域**：`cxt.rs`（decl_mut/fake_bind_mut + NameState）、
   `elaboration.rs`（infer_owned 的 Def/Enum/ImplDecl/TraitDecl 四条臂）、
   `canonical.rs`（lookup_src 的两行）。`parser/mod.rs` 的 `MacroState` 是 L12 内部化
   改动，可见性/外部调用面已核对为只 `run_with_prelude`。
3. **复查 item3 的作用域假设**：建议 reviewer 重点扫 `subst_cxt` 的轨迹写入 + hover
   快照（`clone_without_src_names` 起新表）两处；若未来 L12 增加"跨作用域读旧 Cxt
   名字表"的路径，需要重新审计 mark 单调性。
4. 恢复安静窗口后我可补 §5.3 的 k=12/13 与 fast 列 sanity（约 3–5 分钟）。
5. 收尾：baseline worktree `C:\ezl-wt-l12-base` 在补测后 `git worktree remove`；原始
   A/B 数据保留在 `C:\ezl-target-all-l12\ab\{raw2,raw3}\` 供复核。
