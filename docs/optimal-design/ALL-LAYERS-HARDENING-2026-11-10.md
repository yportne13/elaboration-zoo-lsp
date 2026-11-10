# 全层硬化/优化落地（2026-11-10，分支 `feat/all-layers-hardening`）

> 前置：master 已合并远程 review + L07/L08 hardening 并 push（`1a1cab3b`）。
> 本分支从 master 拉出，按"把已验证的 L07 优化与 hardening 推广到后续章节"执行。
> 所有改动都已提交在本分支；CI 只在 push master 时触发，本分支 push 不触发。

## 0. 本轮范围

| 层 | 改动 | 备注 |
|---|---|---|
| L07 | `deef97f7` `check_ty` 按值 move Pi Raw；`87924b00` 无注解 let 直接推导 binder 类型；`2d4eb32c` `Tm::Lam/Pi` body 改 `Rc<Tm>`（消 eval 深拷） | 深 let n=1000 **168→2.4ms**；深 λ n=1000 **~223→3.0ms**（均近线性） |
| L08 | Locals `Box→Rc`、FxHashMap、decl 表就地 COW、`src_names` NameState+trail；`2a1f378f` `check_ty` move + 无注解 let；`6175987e` `Tm::Lam/Pi` Rc；`cdd19e73` U1/U2 | 4 项累计 strchain 13.2×/global 7.8×/struct 7.8×；deep let 179ms→1.8ms、deep λ 343ms→**2.6ms**（~81×）；church −38%、natadd −13%、match −12.7%、enum −10.8% |
| L09/L10 | FxHashMap（global/PartialRenaming/Trait/Synth 等）+ 穷尽 match 跳过覆盖探测（U2） | L09 match −7~−9%；L10 match k11 −8.9% |
| L11 | FxHashMap、decl COW、name_map+trail | macro 14.9×、struct 16.2×；`hover_table` 观察表加 `collect_observations` 门控 |
| L12 | decl COW、FxHashMap、name_map+trail | strchain k13 −17.8%（0.822×）、natadd k11 −11.6%（0.884×） |
| L13 | `55f2d42e`：`lsp_collect` 观察面总闸（prelude/bench 期死渲染）、U2、12 张 lookup-only 表 FxHash | prelude-core −22.7%、prelude-hdl −7.0%、match k11 −28.1%、enum −52.5%、church k11 −10.7% |
| L01–L06 | `dce5c61c`（L05 src_names `Rc<FxHashMap>` COW + unify FxHash）、`df2fde54`（L06 6 处 Fx）、`dd10d59b`/`0cd81a42`（L03/L04 invert/PartialRenaming Fx）、**`a4520491`/`dfd7ca92`（L05/L06 src_names → NameState+trail）** | L05 chain **−50.8%→−25%（trail 后再测）**、implicit −33%/−27%；**L06 strchain −60%、global −68%**；L03/L04/L06 其余中性；L01/L02 审计无适用项 |

## 1. 各层门禁（本分支集成后统一复跑，全部 EXIT=0）

| 套件 | 结果 |
|---|---|
| `cargo check --all-targets` | 0 error |
| L07 lib | **70 passed** |
| L08 lib | **60 passed**；blackbox 57+1 / v2 51+2；parity **95** |
| L09 lib / parity | **10 / 39** |
| L10 lib / parity | **25 / 46** |
| L11 lib / parity | **33 / 52** |
| L12 lib / parity | **35 / 50** |
| L13 lib / parity / twin / hdl042 | **614 / 629 / 28 / 2** |
| L03 lib / blackbox | 28；136 / 81 |
| L04 lib / blackbox | 30；75 / 73 |
| L05 lib / blackbox | 23；41 / 54 / 62 |
| L06 lib / blackbox | 13；41 / 23 / 81（需 `RUST_MIN_STACK=67108864`，基线同样溢出；已加 CI `test-full` env）；**L05/L06 NameState 后 lib/blackbox 仍全绿** |
| L07 lib/blackbox/parity | 70；48+1 / 51+2 / 116+1；parity **97** |

> 加跑 L08 debug lib（60 passed）验证 NameState 的 `mark <= trail.len()` debug_assert；
> L08 item4 深 let 探针 n=1000 −22.3%；L11/L12 的 twin 列在 A/B 中作为不变对照。

## 2. 关键结果（各层报告原数字）

- **L08**：基线 `deef97f7` → final：strchain 127.1→9.6ms（13.2×）、global
  141.4→18.0ms（7.8×）、struct 138.6→17.7ms（7.8×）；item4 name_map/trail
  对标准负载中性（0.96–1.05），深 let n=500/1000 −24.9%/−22.3%。
- **L09/L10**：L09 match 编译 −7~−9%（k9/k10/k11 三档一致）；L10 match k11
  −8.9%；twin 列不变（1.000±2%）；L10 traitchain 方向相反判噪声。
- **L11**：macro 1134.5→76.2ms（14.9×）、struct 1111.1→68.6ms（16.2×）、
  natadd 1.92→1.71ms（1.13×）。`hover_table` 是 write-only；不门控会让
  clone Cxt 钉住 decl Rc，COW 收益从 ~15× 退化到 ~2×。
- **L12**：natadd k11 0.884×、strchain k11 0.900×、strchain k13 0.822×
  （77.8s→64.0s）；macro 持平；twin fast 列 0.93–0.98 无回归迹象。

## 3. L07 深作用域 O(n²)：进展与剩余

deep 探针 check-only 仍 4.1–4.6×/翻倍；计数排除名字表（unwind O(n)）与
`Cxt::define`（n=1000 约 2ms）。已定位并处理：

1. **`check_ty` 的 Pi Raw clone**：`deef97f7` 按值解构 `Raw::Pi`，去掉每层
   `*a.clone()`/`*b.clone()`。
2. **无注解 let 的 `fresh_meta`/`close_ty`**：`87924b00` 直接 `infer_expr` 推导
   binder 类型，不再为每个 hole 造闭合 meta；深 let n=250/500/1000 =
   0.42/0.85/2.44ms（原 ~10.3/40.6/168.5ms），**该 O(n²) 已消**。
3. **深 λ 的 `eval(Tm::Lam/Pi)` body 深拷**：`2d4eb32c` 把 `Tm::Lam` body 与
   `Tm::Pi` 域/余域改为 `Rc<Tm>`，eval 的 Closure 直接共享；深 λ
   n=250/500/1000 = **0.80/1.54/3.03ms**（原 ~12/54/223ms，近线性）。
   仍剩：显式 hole/其它 `fresh_meta` 仍走 `close_ty`（非深 λ/let 主链）；
   `eval(Tm::Var)` 的 `env.iter().nth` 是潜在 O(depth)/变量。
4. **错误修法（已回滚，不落本分支）**：fresh_meta 若 quote 类型无自由局部变量
   就跳过 close_ty → L07 lib **26 failed**，说明 close_ty 的 telescope 语义不能
   跳过；剩余项需要 lazy/open meta 类型或共享上下文 telescope 的设计。

## 4. 风险与已知限制

1. `name_map+trail`（L08/L11/L12）依赖**深度优先作用域纪律**：访问前按 mark
   惰性回滚；debug_assert 兜底，release 无断言；新增访问点需复核。
2. `RefCell` 重入 panic 面；L08/L11/L12 的 bind 点已审计。
3. L08/L11/L12 decl 表 COW 的"占位与最终值同表"细节与旧 `&Cxt` 包装保留。
4. A/B 受共享机 load 影响（L08 首轮 +9% 经 5 分钟后重测消失；L12 首轮因
   rustc 并发作废）；各 PORT/AUDIT 文档均已记录作废数据与窗口 load。
5. 本轮未做 L07 的 19-bin/Error 载体、L13 的剩余性能项、L01–L06。

## 5. 提交/文档

- 分支：`feat/all-layers-hardening`（从 `1a1cab3b` 起；已 push 远程，不触发 CI）。
- 逐层报告：`docs/optimal-design/layer-ports/{L08-PORT,L09L10-AUDIT,L11-PORT,L12-PORT}.md`。
- 原始 A/B/门禁日志：`C:\ezl-target-all-l08\`、`C:\ezl-target-all-l11\`、
  `C:\ezl-target-all-l12\`、`C:\ezl-target-all-l09l10\`（scratch，不入 git）。

## 6. 下一波建议

1. **L07 fresh_meta O(n²)**：单独立项；先 profile（close_ty vs eval closure），
   再设计 open meta type / 共享 telescope。
2. **L01–L06**：审计 Locals/FxHash/名字表是否还有可借项（L06 有 strchain/global）。
3. L13：核对 `src_names`/decl 表是否还有未覆盖热点（已有 FORCE_MEMO/prelude 池）。
4. 合并前在 master 上再跑一次完整 `cargo test --release` + `gate_l13`/P0 gate。
