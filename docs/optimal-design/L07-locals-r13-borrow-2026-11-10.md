# L13 是否解决了 L07 的 `src_names`/深作用域问题，能否借鉴（2026-11-10）

> 对象：L13 **参考版**（`src/L13_namespace`，不含 `bump_spine_iter`）与 L13 孪生。
> 结论基于代码核对 + 双向 A/B：L13 ref 深 λ 探针、L07 Locals-Rc 原型、此前两条路线数据。

## 0. 结论

1. **L13 参考版没有解决 `src_names` 深拷贝**：它和 L07 一样是
   `src_names: Rc<BiMap<...>>` + `Rc::make_mut`（`cxt.rs:1207-1210` / `:1274-1277`），
   `bind/define` 在 `&self` 下强计数 2 ⇒ 整表深拷。实测 L13 ref 深 λ 探针仍呈二次方（见 §2）。
   **这一项不能从 L13 参考版借鉴。**
2. **L13 参考版确实解决了 `Locals` Box 链深拷贝**：L13 `syntax.rs:10-13` 用
   `Rc<Locals>`（`Bind(Rc<Locals>, …)` / `Define(Rc<Locals>, …)`），L07 用的是
   `Box<Locals>`（`syntax.rs:10-14`）。把这一刀（约 25 行）单独搬到 L07，深作用域实测
   **−48%~−57%**，几乎等于此前"所有权/`&mut Cxt` 路线 A"的 −55%~−58%，但 diff 只有 A 的
   1/10，且不改 `check`/`Cxt` 公共路径。**这是最值得借鉴的一刀。**
3. L13 **孪生**（不是参考版）才有 `name_map + name_trail` + arena `LCons`；这正是 L07
   `name_map+trail` 路线 B 的原型。L13 孪生深 λ 明显更快（总时间 20/23/34ms vs ref
   59/66/96ms，含同一 core prelude），但那是孪生的表示红利，不是参考版可抄的代码。
4. 建议：**先落 L13 的 `Locals: Rc` 这一刀**（小、测试全绿、深作用域收益接近 A）；若之后还追求
   消除剩余 `src_names` 表拷贝，再考虑路线 B 或 A（A 需要 pattern_match 收尾 0.5–1.5 人日）。

## 1. 代码对照

| 机制 | L13 参考版 | L07 现状 | 可否借鉴 |
|---|---|---|---|
| `src_names` 名字表 | `Rc<BiMap>` + `Rc::make_mut`（`cxt.rs:1207-1210`, `:1274-1277`）——同样每次 bind 深拷 | `Rc<FxHashMap>` + `Rc::make_mut`（`cxt.rs:297-334`） | **不能**：L13 ref 也没解 |
| `Locals` 链 | `Bind(Rc<Locals>)` / `Define(Rc<Locals>)`（`syntax.rs:10-13`） | `Bind(Box<Locals>)` / `Define(Box<Locals>)`（`syntax.rs:10-14`） | **可**：约 25 行，实测 −48~−57% |
| 名字解析 | 参考版仍靠 `src_names` 表；孪生用 `name_map+name_trail` | 参考版 `src_names`；孪生已有 name_map+trail | 孪生方案不能直接用于 ref（需 mutable Infer/Cxt 作用域纪律） |
| 免 names 上下文 | `Cxt::clone_without_src_names()`（`cxt.rs:1180`） | 无 | 可作小补充：不需要源码名的内部上下文可跳过 map 拷贝 |
| 深 λ 的剩余平方项 | 参考版仍有 `src_names` 拷贝（见 §2） | `Locals` Box + `src_names` 表 | 先抄 `Locals: Rc`；剩余再单独评估 |

## 2. L13 参考版深 λ 探针（`Nat -> … -> Nat`，core prelude）

`l13bench --file n{250,500,1000}.typort --with-prelude core`，min-of-5：

| n | L13 ref basic（含 core prelude） | 空 prelude 基线 53.4ms → 粗扣后用户段 | L13 twin fast（含同一 prelude） |
|---:|---:|---:|---:|
| 250 | 58.920 | ≈5.5 | 20.219 |
| 500 | 66.086 | ≈12.7 | 22.694 |
| 1000 | 95.568 | ≈42.2 | 34.232 |

- ref 用户段 5.5→12.7→42.2：每翻倍 2.3× / 3.3×，**仍在向二次方走**（`src_names` 整表拷贝）。
- twin 20→23→34：含 prelude 固定成本后已接近线性（`name_map+trail` + `LCons`）。
- 结论：**L13 ref 自己也没解决 src_names 拷表**；它的深路径常数比 L07 小，主要因为 `Locals` 是 Rc。

## 3. 把 L13 的 `Locals: Rc` 单独借到 L07（原型实测）

worktree `C:\ezl-src-locals`，改动仅 `syntax.rs`（`Box`→`Rc`，`close_ty` 解引用）+ `cxt.rs`
3 处构造（`Box::new`→`Rc::new`），真实源码 diff **约 25 行**（另有临时 deepbench/Cargo 项不计）。
测试全绿：lib 70；blackbox 48+1 / 51+2 / 116+1；parity 97；`l07bench` 节点断言通过。

| 深探针 | n | 基线 | L07 + `Locals: Rc` | Δ |
|---|---:|---:|---:|---:|
| 嵌套 λ | 250 | 32.747 | **16.381** | **−50.0%** |
| 嵌套 λ | 500 | 154.177 | **74.333** | **−51.8%** |
| 嵌套 λ | 1000 | 626.471 | **326.228** | **−47.9%** |
| 嵌套 let | 250 | 25.963 | **11.774** | **−54.7%** |
| 嵌套 let | 500 | 112.794 | **48.932** | **−56.6%** |
| 嵌套 let | 1000 | 465.373 | **203.605** | **−56.2%** |

对比此前两条路线（同探针）：A 所有权路线 −55%~−58%（diff +306/−67，覆盖 60–91%）；
B name_map+trail 路线 −6%~−13%（diff +132/−34）。**`Locals: Rc` 用 25 行拿到接近 A 的收益。**

现有 `l07bench` 六负载：与基线 ±5% 散点内，church k13/k12 约 +6~10%、global/strchain 基本 0
（单轮 5 次 min，未做完整多轮交错；无一致回归）。

## 4. 建议

1. **落地 `Locals: Rc`**（L13 参考版已验证表示，L07 小改，测试全绿）；这是"L13 已经解决、L07 可直接借鉴"的那一项。
2. `src_names` 表拷贝：**不要从 L13 ref 借鉴**（它同样没解决）。若以后还要再压深作用域，二选一：
   - 路线 B（name_map+trail）：+132/−34，但单独只再赚约 10%，且引入 RefCell/作用域纪律风险；
   - 路线 A（所有权/&mut）：收益与 `Locals: Rc` 叠加后可能有限（需重测），要补 pattern_match 7 处 binder + unification η，0.5–1.5 人日。
   建议先在 `Locals: Rc` 落地后重测深探针，再决定是否值得继续。
3. L13 `clone_without_src_names` 可作后续小项（不需要源码名的内部上下文跳过 map 拷贝），不是主杠杆。

## 5. 产物

- 原型 worktree：`C:\ezl-src-locals`（未 commit；源码 diff 约 25 行）
- 二进制：`C:\ezl-target-locals\release\l07bench.exe`、`deepbench.exe`
- A/B 原始日志：`C:\ezl-src-bench\locals-ab\`
- 深探针生成/命令：`C:\ezl-src-bench\deepbench.rs`；L13 探针 `C:\ezl-l13deep\`
