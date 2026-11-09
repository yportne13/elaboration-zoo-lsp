# L07 深作用域优化落地记录（Locals: Rc + name_map/trail，2026-11-10）

> 用户决定"1 2 都做"后的落地记录。1 = 借 L13 参考版的 `Locals: Rc`；2 = 消掉 `src_names`
> 表深拷贝（采用 L08/L13 孪生的 `name_map + name_trail` 设计，而不是 L13 参考版——它没解）。
> 基线是上一提交 `aad50eac`（COW + FxHash 已落地）。

## 0. 两个提交

| commit | 内容 | diff |
|---|---|---|
| `65d4512a` | **Locals: Rc**（L13 参考版表示）：`Bind/Define` 的 `Box<Locals>` → `Rc<Locals>`，`close_ty` 克隆尾 Rc | 2 文件 +17/−8 |
| `d411debe` | **src_names → name_map + name_trail**：`Cxt` 共享 `NameState{map,trail}` + `name_mark`，bind/define/lookup 按 mark 惰性 unwind，O(1) 摊还；`subst_cxt` 通过轨迹可逆包裹 | 3 文件 +132/−34 |

> 先落 Locals Rc，再在它之上落 name_map/trail；所有权路线 A（+306/−67）**没有采用**：
> 深作用域收益与 Locals+trail 相当，但改动面/API 波及大得多。

## 1. 深作用域收益（min-of-3，交错正反序）

| 探针 | n | 基线 | Locals: Rc | + name_map/trail | 总 Δ vs 基线 |
|---|---:|---:|---:|---:|---:|
| 嵌套 λ | 250 | 37.811 | 20.840 | **18.289** | **−51.6%** |
| 嵌套 λ | 500 | 152.049 | 76.649 | **69.449** | **−54.3%** |
| 嵌套 λ | 1000 | 646.346 | 327.690 | **287.962** | **−55.4%** |
| 嵌套 let | 250 | 28.213 | 13.324 | **10.000** | **−64.5%** |
| 嵌套 let | 500 | 113.318 | 51.016 | **41.454** | **−63.4%** |
| 嵌套 let | 1000 | 467.698 | 204.557 | **167.464** | **−64.2%** |

- Locals Rc 单独：λ −45~−50%、let −53~−56%（vs 基线）。
- 再叠加 name_map/trail：λ 再 −9~−12%、let 再 −18~−25%。
- 对比所有权路线 A（λ 1000 287.4ms、let 1000 196.8ms）：组合方案 λ 持平、let **更快**
  （167.5ms），但 diff ~149 行 vs A 的 373 行，且不改 `check/Cxt` 公共路径。

## 2. 现有 l07bench 负载

Locals Rc + trail vs Locals-only：±5% 散点；church k12/k13 约 +3~11%，strchain/global 基本 0，
无一致回归。`l07bench` 节点数断言（闭式 + 双实现互检）全部通过。

## 3. 验证

| 套件 | 结果 |
|---|---|
| `cargo build --release --bin l07bench` | ✅ |
| `cargo test --release --lib L07_sum_type` | ✅ 70 passed |
| `l07_blackbox` / v2 / v3 | ✅ 48+1 / 51+2 / 116+1 |
| `l07_fast_parity` | ✅ 97 passed |
| `l07bench --workload all --max-k 13` | ✅ 节点断言全过 |

## 4. 风险与遗留

1. name_map/trail 采用"按 mark 惰性回滚"，正确性依赖**深度优先作用域纪律**（不在访问浅
   Cxt 后继续用深 Cxt）；已审计全部 bind 点 + debug_assert 兜底，release 无断言。后续若新增
   "保存 Cxt 跨兄弟作用域"的代码需复核。
2. `RefCell` 重入 panic 面：lookup 克隆后立即释放；新增访问点需遵守。
3. 深链仍非严格线性：`Locals` Rc 与名字表都已 O(1)/O(1)，但 T(2n)/T(n) 仍约 3–4×，说明还有
   第三个 O(n²) 项（未定位；需 profile；不影响本次落地收益）。
4. 本次只改 L07 参考版；孪生不受影响，parity 全绿。

## 5. 复现

```powershell
CARGO_TARGET_DIR=C:\ezl-target cargo test --release --lib L07_sum_type
CARGO_TARGET_DIR=C:\ezl-target cargo test --release --test l07_fast_parity
# 深探针（scratch，未入库）：deepbench.exe <n> <rounds>
```

证据：`docs/optimal-design/experiments/l07-locals-r13/`（Locals-Rc patch/A-B）、
`docs/optimal-design/experiments/l07-srcnames/`（trail patch/A-B）。
