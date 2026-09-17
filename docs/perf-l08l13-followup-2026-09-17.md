# L08–L13 同族性能问题排查与修复（2026-09-17）

> 承接 [perf-l07-2026-09-17.md](perf-l07-2026-09-17.md)：那份查的是 L07，本文把
> **同一类问题**（"热路径上的全量/深拷贝表"）在后续章节逐层核对，能测的先测、
> 实测为冷的就登记为不做。上一提交（`370fb3f`）已完成 L07/L08。

## 0. 结论

| 层 | 同类点 | 判定 |
|---|---|---|
| L08 | `Decls = HashMap<_, DeclEntry>` 写时复制深拷贝 | **已修**（与 L07 同批，`Rc<DeclEntry>`） |
| L09 | `avoid_recursive = self.clone()`（3 处） | **实测冷，不做**（见 §2） |
| L10 | 同 L09（3 处） | **实测全负载 0 命中，不做** |
| L11 | `Cxt.decl` **按值持有** `HashMap<String,5 元组>`，每次 `Cxt` 构造整表克隆 | **已修：3.2–3.5×** |
| L12 | 同 L11（键为 `SmolStr`） | **已修：3.4–6.4×** |
| L13 | `decl: Rc<Decl>` + `simpl_decl` 带缓存 | **早已达标，无需改** |
| L11/L12 | 中性 decl 表在分支循环内重建（`d5` P3-11） | 已提到循环外；**实测无差别**，作一致性清理保留 |

排查口径：一个"同类点"要同时满足 ①是一个随源码规模增长的表；②在每定义/每
绑定/每分支这类高频事件上被**全量或深拷贝**；③能被现有负载触发。三条只满足前
两条的，实测为冷就明确登记为"不做"，避免把静态论证当收益。

## 1. 逐层是怎么找的

1. `grep make_mut`：找写时复制的表（L07/L08 命中，L13 命中但已是 `Rc` 元组）。
2. `grep "self.clone()"` + `avoid_recursive`：找"整对象深克隆"的读路径（L09/L10 命中 3+3 处）。
3. 逐层读 `cxt.rs` 的字段与所有 `Cxt { .. }` 构造点：**按值持有的表**会在每个
   构造点克隆（L11/L12 的 `decl` 命中 8 处；L13 是 `Rc` 所以只有引用计数）。
4. `grep "simpl_decl|declb = "`：核对"中性表"是否在循环内重建（L11/L12 命中，
   其余层已提升或带缓存）。

## 2. L09/L10：`Infer::clone()` —— 静态论证成立，实测为冷

`d5-performance.md` P2-2 记 L09/L10 在 quote/rename/Match-vs-Match 三处
`let mut avoid_recursive = self.clone()`（克隆整个 `Infer`：`meta: Vec<MetaEntry>`
深值 + `global: HashMap<Lvl, VTy>`），并称"quote 在 println/nf 路径……上都热，
基准即触发"。**实测否掉了这个判断**：

| 层 | 负载 | 命中次数/单次 run | 规模 |
|---|---|---|---|
| L09 | enum | **12** | `\|meta\|=55, \|global\|=10` |
| L09 | church / strchain / match / struct / universe / natadd | **0** | — |
| L10 | church / strchain / match / enum / struct / universe / traitchain | **0** | （traitchain 单 run 23 s，仍 0 命中）|

12 次 × O(55) 条目的克隆，相对该负载 13.2 ms 的耗时量级在 1% 以内。**不做**：
把 `meta` 改成 `Rc<Vec<_>>` 会牵动 5 个写入点与 `Infer` 的表示，换不到可测收益。

（`d5` 同时把这条列为 P2，与本文的 L11/L12 是同一轮评审的发现——差别在于
L11/L12 那两条有 3–6× 的实测收益，这一条没有。）

## 3. L11/L12：`Cxt.decl` 按值持有 —— 本轮最大的单项收益

### 3.1 问题

`L11_macro/cxt.rs`：`pub decl: HashMap<String, (Span<()>, Rc<Tm>, Rc<Val>, Rc<Ty>, Rc<VTy>)>`
（L12 同款，键为 `SmolStr`）。因为它是**按值字段**，cxt.rs 里 8 处
`decl: self.decl.clone()` 与 2 处 `let mut decl = self.decl.clone(); decl.insert(..)`
都会**克隆整张表**——`bind` / `define` / `new_binder` / `subst_cxt` / `fake_bind` /
`decl` 每次调用一次。值虽然是 `Rc`，但键是 `String`（L11），每次条目拷贝都是一次
堆分配。

探针实测（L11 `struct` 负载，k=11，单次 run）：

```
[decl-clone] calls=70000 entries=103641185     # 7 万次整表克隆、1.04 亿次条目拷贝
```

对照该负载修复前的 2.95 s 总耗时，这几乎就是全部（键 `String` 每次克隆一次
malloc，1.04 亿次 ≈ 秒级）。

### 3.2 修法

对齐 L13 的形态：`pub decl: Rc<Decl>`（L11/L12 的 `Rc` 是 `Arc` 别名）。
- 所有 `decl: self.decl.clone()` **不用改**（变成引用计数递增，O(1)）。
- 两处插入改 `Rc::make_mut(&mut decl).insert(..)`，写时复制语义不变
  （"占位只对本定义的检查可见"仍然成立）。
- 所有读点传 `&cxt.decl`（`&Rc<Decl>`）靠 deref 强转继续工作，零改动。
- L12 `unification.rs:171` 的 `empty_cxt.decl = decl.clone()` 补 `Rc::new(..)`
  （该处仍是全表克隆，与修前同价，见 §3.4）。

### 3.3 收益（同窗口交错，min；A = 修复前二进制，B = 修复后）

| 层 | 负载 | k=9 | k=10 | k=11 |
|---|---|---|---|---|
| L11 | struct | 118.1 → **43.5** (0.37×) | 469.9 → **152.7** (0.33×) | 2952.3 → **846.1** (0.29×) |
| L11 | macro | 109.0 → **43.3** (0.40×) | 441.0 → **163.5** (0.37×) | 2695.7 → **842.5** (0.31×) |
| L12 | struct | 108.1 → **38.0** (0.35×) | 423.6 → **138.4** (0.33×) | 3396.7 → **530.2** (0.16×) |
| L12 | macro | 100.3 → **40.6** (0.41×) | 405.9 → **146.2** (0.36×) | 2731.2 → **801.3** (0.29×) |

（单位 ms，`--only basic`，即参考版。L11/L12 的孪生版不受影响——它们本来就是
平铺表。）

### 3.4 残留（仍未做）

插入路径的 `Rc::make_mut` 在表被共享时仍要克隆一次整表 ⇒ 仍然是 O(n²)（修复后
缩放 3.5–4.0×/翻倍，L11 最后一次 5.5×）。要彻底消掉得改成**平铺插入**
（`Rc<RefCell<..>>`，孪生版口径，其注释已论证顶层插入单调因而语义等价）。本轮
没做：这是**语义表示**的变更（参考版从此不再是"写时复制"的语义 oracle），
超出"同类性能修复"的范围。若要继续收，这是 L11/L12 的下一刀。

另外 L11 的键是 `String`（L12/L13 都是 `SmolStr`）：即便保留写时复制，把键换成
`SmolStr` 也能消掉残留里每一次条目克隆的堆分配。同样未做（会牵动 `Decl` 的键
类型与若干构造点）。

## 4. L11/L12：中性 decl 表在分支循环内重建（`d5` P3-11）—— 已改，实测无差别

`quote` 的 Match 臂与 `rename` 的 Match 臂各自在**分支闭包内**重建中性 decl 表
（`decl.iter().map(..).collect()`），共 4 处（L11/L12 各 2）。L07/L08 与 L13 早已
提到循环外（L13 还带缓存）。已按同款提升到循环外。

**实测无差别**：L11 `struct` 118.7/471.7/3021.0 → 122.6/488.4/2984.5（0.99–1.04×），
`macro` 111.1/430.6/2610.7 → 108.7/421.0/2597.2（0.98–0.99×）。原因很清楚：命中
该路径的负载（`match`）decl 数只有十位量级，decl 数大的负载又不命中该路径。
按"一致性清理"保留（与 L07/L08/L13 同形，且消掉 #分支 × |decls| 的冗余）。

## 5. 验证

| 项目 | 结果 |
|---|---|
| `cargo test`（全仓） | 69 个测试目标全绿、0 失败（改动后重跑） |
| `--lib L11_macro` / `--lib L12_canonical` | 22 / 23 通过 |
| `l11_fast_parity` / `l12_fast_parity` | 37 / 36 通过 |
| `l11bench` / `l12bench` 正确性断言 | 全部通过 |

## 6. 复现

```bash
# 修复前的 L11/L12 二进制（2026-09-16 构建）
ls target/post_refactor_bins/l11bench.exe target/post_refactor_bins/l12bench.exe

# 交错 A/B（min）
python target/agg_bench.py target/post_refactor_bins/l11bench.exe \
       target/release/l11bench.exe 2 --max-k 11 --rounds 3 --workload struct --only basic

# L09/L10 的"冷路径"证据：探针已随本文撤除，复现需按 §2 重加 3 处
# `eprintln!("[avoid_recursive] |meta|={} |global|={}", ..)` 后跑
#   L09: --workload enum   --only basic      （预期 12 次）
#   L10: --workload traitchain --max-k 9 --only basic （预期 0 次）
```
