# 2026-09-12 性能优化：L10 参考版 eager nf+pretty 移除 + L09-L13 孪生名字/声明表 COW

> 起因：2026-09-12 对 L02-L13 全章做 basic（参考版）vs fast（`bump_spine_iter`
> 孪生）普测（口径：各章 bench 默认负载，`--only` 隔离进程、取 min），发现
> 两个大倍率异常点与一条共性的 O(D²) 曲线。逐 decl 探针 + 代码定位后各落
> 一刀，全套测试绿（lib 682 + parity 31/32/37/36/393）。本文记录根因、改动、
> 安全性论证与实测。

## 1. 优化一：L10 参考版移除逐 def 的 eager nf + pretty

**根因**（`src/L10_typeclass/elaboration.rs` Def 臂）：`Decl::Def` 臂对每个
def 无条件 `self.nf(...)` + `pretty_tm(...)` 计算类型/函数体的显示串填入
`DeclTm::Def { typ_pretty, body_pretty }`——而这两个字段**自引入起无任何消
费方**（`run` 只取 `DeclTm::Println`，grep 全仓只有构造处）。函数体完整规范
化在大值负载上每 decl 一次 O(值大小)（nf 的代入展开 + 深链 pretty 拼接），
church 翻倍负载实测每翻倍 ×4.2（O(n²)）。

探针（逐 decl infer vs 最终 quote，k=13）：

```
decls=16 infer_total=279ms   quote=9.6ms   d[last]=205ms
```

平方项全部在逐 decl 的 infer 里（nf+pretty），最终 quote 只有 9.6ms——
与 L09 参考版（同 church 源，无 eager pretty，k=13 18.8ms 线性）互为对照。
L11（`elaboration.rs:341`，body 侧置 `String::new()`）与 L13
（`elaboration.rs:975` 整段注释）此前已各自处理过同一段代码，L10 是漏网
的最后一个。

**改动**：删除两字段与计算（`DeclTm::Def` 缩为 name/typ/body 三字段）。

**实测**（l10bench church，rounds 5，min）：

| k | before | after | 加速 |
|---|---|---|---|
| 11 | 11.3 ms | 1.66 ms | 6.8× |
| 13 | 199.4 ms | 6.78 ms | **29.4×** |

增长因子 ×4.2/翻倍 → ×2.0/翻倍（恢复线性）。修后 L10 参考版 church 比
L09 参考版（18.8ms）还快 2.8×——`Rc<Val>` 表示的红利此前一直被 pretty
开销掩盖。对孪生倍率 162× → **5.1×**。

## 2. 优化二：孪生 define/fake_bind 路径的名字/声明表 COW（L09-L13）

**根因**（逐 decl 探针，L09 universe k=11）：参考版与孪生**都**呈每 decl
O(D)（首 100 decl 平均 22µs → 末 100 decl 1581µs），4101 个平凡 def 合计
3.67s。代码定位：

- 孪生 `define_name`/`fake_bind`（L09/L10）：`(*cxt.names).clone()` 每 def
  深克隆整张名字表（by_name + by_lvl 两个 FxHashMap）——这是 L09 移植时
  丢掉 L08 `name_map + name_trail` O(1) 机制的回归（L08 孪生 struct
  4096 decl 仍是平的 1µs/decl）。
- 孪生 `fake_bind`/`decl_reg`（L11/L12/L13）：decls 表每 def **两次**
  `cxt.decls.clone()` + `Rc::make_mut`（先克隆再写，make_mut 恒见计数 2）。
- 参考版 `Cxt::define` 的 `src_names.clone()`（BiMap，L08 起）——参考版的
  对应平方项，本文**不动**（参考版定位是可读规格实现；孪生侧收益已足够）。

**改动**（孪生侧，L09-L13 五章同构）：`fake_bind`/`define_name`（L09/L10
的 names 表）/`fake_bind`/`decl_reg`（L11-L13 的 decls 表）改收
`&mut Cxt`，`Rc::make_mut(&mut cxt.names / &mut cxt.decls)` 就地写，返回
`clone_cxt(cxt)`（浅克隆）。调用点（infer_decl 的 Def/Enum 臂、
prime_round、elab_all/run_decls/step_round_decl）按值/&mut 传递；fake 视图
用完后 `drop(fake)` 再 define，避免多出的 Rc 引用触发 make_mut 回退。

**安全性论证**：

- `Rc::make_mut` 在强计数 1（cxt 独占快照，顺序 decl 路径恒成立）时原地
  写；计数 >1（match 臂捕获的快照、refresh 克隆、包装器浅克隆等观察者
  存在）时自动深拷贝——**与旧"克隆整表再插"行为逐字一致**，隔离语义由
  Rc 计数保证，无需逐调用点论证。
- fake_bind 就地插入的占位条目（`by_lvl[GLOBAL_BASE+idx]` /
  decls 存根）残留在父视图中：by_lvl 只点查不迭代、按名解析随后被 define
  的真名覆盖，旧实现中父视图本就在下一轮被丢弃——无观察路径。
- L13 的 class Phase B 等借用 `&Cxt` 的调用点走
  `infer_after_prefix`（&Cxt 包装器：`clone_cxt` 后转 `&mut` 内部版）——
  对父视图只读的语义与旧实现一致；`infer_decl` 顺序路径直通 `_mut` 版。
  `prime_resident` 的 `Cxt<'static>` transmute 处经 &mut 不可缩（不变型），
  用浅克隆出本地副本（该路径仅在 LSP 装 prelude 时跑一次）。

**实测**（同机同状态，改动用 `git stash` 式还原后复测）：

| 负载 | before | after | 加速 | 增长因子 |
|---|---|---|---|---|
| L11 macro fast k=11 | 114.6 ms | 4.00 ms | **28.6×** | ×3.7 → ×2.0（平方→线性） |
| L09 match fast k=11 | （平方形态） | 0.70 ms | — | → ×1.1/翻倍（线性） |
| L09/L10 universe fast k=11 | 178.8 ms | 65.4 ms | 2.7× | ×4.0 → ×3.9（仍平方，见残留） |
| L13 prelude-hdl fast | 2480 ms | 2366 ms | 1.05× | D=943 时表克隆占比小 |
| L11/L12 natadd、L10 church fast | — | 无回归 | 1.0× | |

## 3. 残留已知项（记录，未动）

1. **`bind_name` 每 binder 仍整表克隆**（O(D)）——universe 负载的剩余平方
   项（`Type 1 -> Type 0` 每 def 一个 Π binder）。bind_name 的插入对父视图
   不总安全（同名遮蔽/未绑名误成功风险），无法机械套 make_mut；彻底解法是
   恢复 L03-L08 的 `name_map + name_trail` 持久结构（需 meta 快照语义的
   专项设计与验证，见 L03 readme「名字解析 O(1)」）。
2. **`update_cxt`/refresh 的 names 克隆**（match 精化路径，O(D)/次）——
   match-heavy + 大 decl 数源才触发，现有负载面未覆盖。
3. **L12 traitchain 孪生 parity 失败**（bench 自检 k=9 即
   `fast check+nf 未通过`，既有问题非本轮引入）——修复前该负载无对照。
4. 参考版 `Cxt::define` 的 `src_names` 克隆（L08 起 `HashMap<String,…>`、
   L09+ 升级 BiMap 双表）——O(D²) 与孪生改前同源，L08 struct（参考版
   750×）与 L06 strchain（参考版 eager String 拼接，285×）的平方项同属
   参考版侧；参考版定位为可读规格实现，仅记录。
5. L13 文档旧数字订正见 §4。

## 4. 顺带订正

`docs/l13-twin-bench-2026-09.md` §8.2 的 core 1.67× / hdl 1.83× 与当前代
码不符（2026-09-12 复测：core 1.00×、hdl 1.34-1.37×，`fast_ss` ≈ `fast`，
排除稳态口径解释）——该文数据为 2026-09-09 快照，此后代码有多次变更。

## 5. 复现命令

```bash
cargo test --lib                                   # 682 通过
cargo test --test l09_fast_parity                  # 31（l10: 32 / l11: 37 / l12: 36 / l13: 393）
cargo run --release --bin l10bench -- --workload church --rounds 5 --only basic
cargo run --release --bin l11bench -- --workload macro  --max-k 11 --rounds 3 --only fast
cargo run --release --bin l09bench -- --workload universe --max-k 11 --rounds 3 --only fast
cargo run --release --bin l13bench -- --workload prelude-hdl --rounds 3 --only fast
```

## 6. 优化后全章汇总（2026-09-12 复测，同机同状态）

主口径（L02-L10/L13 = church，L11/L12 = natadd；隔离进程，min）：

| 章 | 负载 | k | basic | fast | basic/fast |
|---|---|---|---|---|---|
| L02 | church | 15 | 44.2 ms | 3.25 ms | 13.6× |
| L03 | church | 15 | 51.1 ms | 3.89 ms | 13.1× |
| L04 | church | 15 | 54.2 ms | 4.06 ms | 13.3× |
| L05 | church | 15 | 55.1 ms | 3.89 ms | 14.2× |
| L06 | church | 13 | 10.5 ms | 1.08 ms | 9.8× |
| L07 | church | 13 | 18.9 ms | 1.64 ms | 11.6× |
| L08 | church | 13 | 19.0 ms | 1.34 ms | 14.1× |
| L09 | church | 13 | 18.7 ms | 1.44 ms | 13.0× |
| L10 | church | 13 | 8.11 ms | 1.24 ms | **6.6×**（修复前虚高 162×） |
| L11 | natadd | 13 | 7.34 ms | 3.73 ms | 2.0× |
| L12 | natadd | 13 | 7.32 ms | 3.71 ms | 2.0× |
| L13 | church | 13 | 23.3 ms | 16.8 ms | 1.4× |

特色负载（max-k 11，rounds 3）：

| 章 | 负载 | k | basic | fast | basic/fast | 修复前 fast |
|---|---|---|---|---|---|---|
| L06 | strchain | 11 | 1234 ms | 5.58 ms | 221× | 4.64 ms（未改动） |
| L07 | match | 11 | 0.43 ms | 0.039 ms | 11.1× | 0.041 ms（未改动） |
| L08 | struct | 11 | 2992 ms | 4.25 ms | 704× | 4.22 ms（未改动） |
| L09 | universe | 11 | 3285 ms | 68.1 ms | **48.3×** | 178.8 ms → 2.6× |
| L11 | macro | 11 | 2737 ms | 4.30 ms | **637×** | 117.3 ms → 27× |
| L13 | prelude-core（134 decls） | — | 25.1 ms | 24.9 ms | 1.0× | 持平 |
| L13 | prelude-hdl（943 decls） | — | 3105 ms | 2385 ms | 1.3× | 2480 → +5% |
| L13 | moduletree | 9 | 0.194 ms | 0.170 ms | 1.1× | 持平 |

L10/L12 traitchain 不列入：前者两版都病态（basic 24s / fast 13s），
后者孪生 parity 失败（既有问题，见 §3）。

读表要点：L02-L09 的 10-14× 是纯求值机的真实加速比；L10 的 6.6× 才是
孪生对"无浪费参考版"的真实 church 倍率（162× 里 96% 是 eager pretty
的浪费）；L09 universe 的 48× 与 L11 macro 的 637× 是 COW 消掉 O(D²)
后的结果，且 L11 macro basic 这次在 k=11 跑完了（此前未完成）；L13 的
1.0-1.4× 维持 elaborator 主导负载的预期形态。
