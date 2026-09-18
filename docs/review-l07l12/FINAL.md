# L07–L12 多维并行评审 · 总报告(FINAL)

> 2026-09-15。6 个维度 agent 并行只读评审,规范见 [BRIEF.md](BRIEF.md)。
> 评审期间基线:6 个 parity 套件 + l07/l08 blackbox v1–v3 全部绿(exit 0)。
> 本轮为纯评审,未改任何源码。

## 1. 各维度 verdict

| 维度 | 报告 | P0 | P1 | P2 | P3 | needs-verify |
|---|---|---|---|---|---|---|
| D1 显式替换语义(蓝本一致性) | [d1-subst-semantics.md](d1-subst-semantics.md) | 0 | 0 | 1 | 4 | 4 |
| D2 unsafe/内存安全 | [d2-unsafe-memory.md](d2-unsafe-memory.md) | 0 | 1 | 2 | 2 | 1 |
| D3 稳健性/全函数性 | [d3-robustness.md](d3-robustness.md) | 0 | 4 | 5 | 2 | 4 |
| D4 parity 与跨层分叉 | [d4-parity-drift.md](d4-parity-drift.md) | 0 | 0 | 2 | 3 | 2 |
| D5 性能/分配/确定性 | [d5-performance.md](d5-performance.md) | 0 | 0 | 4 | 11 | 4 |
| D6 测试质量/文档准确性 | [d6-tests-docs.md](d6-tests-docs.md) | 0 | 0 | 5 | 2 | 3 |
| **合计(去重前)** | | **0** | **5** | **19** | **24** | **18** |

范围校准(D3):L07–L12 均未接入 LSP 主路径(lib.rs 仅裸 `mod` 声明,LSP/tutorial/CLI
全走 L13),只被 l0Xbench 与 tests 驱动——故用户源码可达 panic 定 P1 而非 P0;
若日后某层接入 LSP,多条发现会升 P0。

## 2. 总体结论

**显式替换机制层本身是干净的**:D1、D4 独立对照均确认 L07 蓝本的 13 个机制点
(Subst 单链、右偏 extend、O(|σ|) compose、条件包裹、frcs 槽位纪律、燃料剖面、
SpecSolve 穿参、subst_cxt、force_arg 等)在五层移植中**无缺失、无变形**;旧机制
pm_defs/pm_solvable/pm_mark 已删净。当前 parity 全绿与"未发现真实 parity 裂缝"
相互印证。

问题集中在四处**接缝与防护**,而非机制:

1. **孪生版深层共享缓冲纪律**(D2):vapp1 Clo 臂尾调 eval_iter 清空调用方
   尚有 pending 项的共享 workbuf(P1);Rc<SubstV> 嵌入 bump 后跨轮泄漏(P2)。
2. **各层特性与机制的接缝**:L09 unify 无燃料护栏、L12 canonical 读点未 force
   + HashMap 序泄漏、L10/L11 漏移一个上游修复、typeclass 求解器 panic 臂。
3. **测试防护未跟上重构**(D6):L09–L12 无 blackbox 套件、L11/L12 parity 剔除
   GADT/依赖索引族且无跟踪案、设计文档 §9.5 钉死测试未复刻。
4. **文档滞后**(D6/D1):L09 README 与现状相反、L10/L11 README 燃料 bullet
   未随 dbe79cf 更新、L11/L12 孪生模块头仍描述已删除的 update_cxt/refresh。

## 3. P1 汇总(5 项,详见各报告)

| # | 发现 | 层 | 报告 |
|---|---|---|---|
| 1 | 孪生 `vapp1` Clo 臂尾调 `eval_iter` 会 clear 调用方尚有 pending 项的共享 workbuf,精化槽内嵌套 let 的编译期求值可静默丢项错值(附回归构造,标 needs-verify) | 六层孪生 | D2 |
| 2 | 卡住 match 被应用 → `panic!("impossible apply")`;L09 头注已文档化,L10/L11/L12 同款可达**未文档化**;L07/L08 已用 pending 机制修复 | L09–L12 | D3 |
| 3 | typeclass 求解器 `panic!("Too much effort :(")`:循环实例或 >1000 互异 goal 链可触发,effort 封顶后 panic 而非返回 None | L10/L11/L12 | D3 |
| 4 | 文件 IO 内建(`file_read_all_text` 等 5 个)对 IO 失败直接 panic,源码可调用 | L07/L08 | D3 |
| 5 | `eval_aux`"只能 match sum type"panic:L10/L11/L12 **参考版已改优雅降级但孪生版仍 panic**(可达 panic + parity 分裂双料);L09 双版一致 panic | L09–L12 | D3 |

## 4. P2 按主题归并(19 项去重后)

**正确性/parity 裂缝类**
- `v_applicable`(ref)不含 `Lam` vs 孪生 `vapp_ok` `_ => true`:σ 中有 λ 解且读点
  带非空 spine 时 ref 卡住、twin β-归约——潜在 parity 裂缝;孪生注释自称"与参考
  版同判"失实(六层)。〔D4〕
- L10/L11 参考版漏移 bbcf214 的 quote VSub 防御修复(仍是修复前
  `debug_assert!(false)`+降级 `U(0)` 形状);L07/L08/L09/L12 及其孪生均已修。〔D4〕
- L12 `canonical.rs:62-94` canonical 求解读点按形态匹配 src_names 类型/env 槽
  未 force,移植后值被 `subst_cxt` 包成 VSub → Pi 剥链失败,quickfix 候选漏报。〔D1〕
- L12 `canonical.rs:67` 用 `cxt.decl.iter()`(std HashMap 随机序)枚举合成候选取
  首个成功者 → quickfix 跨进程不可复现。与上条同一读点区,建议一并修。〔D5〕

**燃料/护栏缺口类**
- L09 unify 入口无燃料护栏(L10 注释自证"L09 重写时丢失")。〔D3〕
- L10–L12 参考版 `check_pm` 缺孪生版有的模式入口充值,燃烧剖面跨引擎分裂。〔D3/D1〕
- L11/L12 `lvl2ix` 裸减法无护栏(L07–L10 都有)。〔D3〕
- L09–L12 值层投影 `find().unwrap()` vs L07 全函数 `project()`。〔D3〕

**内存/资源类**
- `Rc<SubstV>` 嵌入 bump 的 `XCell::VSub`,bump reset 不跑 Drop → σ 链跨轮泄漏
  (六层孪生;参考版无此问题)。〔D2〕
- L07 十处缓冲 transmute 无 SAFETY 注释且借出点不 clear,与 L08+ 分口径分叉。〔D2〕
- 参考版递归无深度上限(depth400 需 512MB 栈,L07 测试自证);
  `large_did_open_no_hang.rs` 只护传输死锁不护深度。〔D3〕

**测试防护类**
- L09–L12 无 blackbox 契约套件;L09/L10/L11 的 mod.rs 内测(2/9/12 个)**零断言**
  (println 冒烟)——parity 只锁两版互证,对外行为无跨重构 oracle。〔D6〕
- L11/L12 parity 系统性剔除 GADT/依赖索引族,文件头称"另案跟踪"但全仓无跟踪案
  ——σ 传播最敏感路径在这两层覆盖为零。〔D6〕
- design doc §9.5"必须复刻"的钉死测试(slot-applied、d=400 燃料边界)仅 L07 有;
  L07 parity Err oracle 只判 Ok/Err 同型不比正文,弱于其余层。〔D6/D4〕
- 六层 bench 的 match 负载全是双臂浅 Nat match(σ 长度恒 ≤2),重构核心性能主张
  (σ 读写剖面)在仓库内不可验证。〔D5〕

**性能类**
- L09/L10 参考版卡住 match 的 quote/rename/unify 路径每分支整 `Infer::clone()`
  (L07/L08 已改 simpl_decl,移植缺口);L07/L08 force 卡住 Match 臂每次深拷贝
  scrutinee。〔D5〕

## 5. needs-verify(18 项)

各报告 §3 均附验证方法,共性主题:L09 叶子 unwrap 触达性、L10–L12 叶子 Err 后
reachable 标记缺臂、决策树空 pats 覆盖假阳性、λ 解构造程序比对 ref/twin(验证
D4 的 v_applicable 分叉)、debug 构建跑 d=400 语料验证 force 顶层 VSub 可达性、
孪生 `mentions_level` 链头嵌链形态。建议先跑 D2/D4 给出的两个回归构造——
它们是唯二可能升 P0/P1 的未决项。

## 6. 设计决定记录(不属 bug)

- 可解集三层口径:L07/L08 白名单、L09 混合(界守卫+unify 内白名单)、L10–L12
  无白名单——有文档/测试依据。〔D1/D4〕
- `Infer.global` 在 L09–L12 实为**全局定义表**而非精化通道,BRIEF"应已删除"
  表述过宽;`unify_pm` 名字沿用但机制已换。〔D1〕
- 孪生燃料实现位置差异(参数 vs thread_local)、L09 Match 重选位置等已归类合法
  分歧,详见 D4 对照表。〔D4〕
- probe_* 回归系列仅 L11/L12(+L13)有,按适用性大体合理。〔D6〕

## 7. 建议处置顺序(供决策,本轮未实施)

1. **先验证两个 needs-verify 回归构造**(D2 workbuf、D4 λ 解)——唯二可能升级项;
2. P1-2/3/5(panic 臂改优雅降级,其中 P1-5 同时修 parity 分裂);
3. D4 两项 P2(λ 判定分叉、bbcf214 漏移)——parity 裂缝预防性修复;
4. L12 canonical 读点(D1+D5 两项合并处理:补 force + 有序枚举);
5. 燃料/护栏补齐(L09 unify、L10–L12 check_pm、lvl2ix、值层投影);
6. 测试防护(D6):L09–L12 blackbox、L11/L12 GADT 覆盖跟踪案、钉死测试复刻;
7. 文档批量订正(D6 §4 清单)+ bench 负载补 σ 深链场景。

---

## 8. 修复轮（已完成，见 [FIXES.md](FIXES.md)）

2026-09 按上述顺序执行：39 文件、+1091/−373；六层 parity/blackbox 与各层
lib 测试全绿；L07 parity 的 Err oracle 已升级到与其余五层同级（升级后 64
例全绿）。新登记两项**既有**分歧（L09–L12 在 §9.5 两个哨兵程序上非终止，
`git stash` 基线对照确认非本轮引入）。未做项清单见 FIXES.md §4。

