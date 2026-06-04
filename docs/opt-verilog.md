# hdl-verilog.typort 加载性能分析 (2026-06-05)

## 实测数据

### 逐文件耗时

```
文件                    解析(s)    推断(s)    总计(s)    占比
─────────────────────────────────────────────────────────
hdl-verilog.typort      0.0356    ~48.4     ~48.5     97.1%
其余 23 个文件           0.0261    ~1.4      ~1.4      2.9%
─────────────────────────────────────────────────────────
总计                    0.0617    ~49.9     ~49.9    100.0%
```

`hdl-verilog.typort` 一个文件占总加载时间的 **97.1%** (48.5s)。

### 逐 decl 耗时

| Decl | 耗时 | 占比 |
|------|------|------|
| `def natToDec` | 0.000s | 0.0% |
| `def joinLines` | 0.010s | 0.0% |
| `def exprVL` | 1.448s | 3.0% |
| `def collectAssignLines` | 0.517s | 1.1% |
| `def assignsVL` | 0.052s | 0.1% |
| `def hasPorts` | 0.465s | 1.0% |
| `def collectPortLines` | 0.639s | 1.3% |
| `def joinPortLines` | 0.014s | 0.0% |
| `def portsVL` | 0.002s | 0.0% |
| `def collectWireLines` | 0.631s | 1.3% |
| `def collectRegLines` | 0.637s | 1.3% |
| `def collectClockLines` | 0.521s | 1.1% |
| `def wiresVL` | 0.039s | 0.1% |
| `def collectAlwaysLines` | 0.504s | 1.0% |
| `def alwaysVL` | 0.034s | 0.1% |
| `def regsVL` | 0.034s | 0.1% |
| `def clockedVL` | 0.035s | 0.1% |
| **`def moduleVL`** | **43.281s** | **88.6%** |
| **总计** | **48.863s** | 100% |

## moduleVL 的 43 秒根因分析

### 逐步骤分解

```
moduleVL infer 各步骤             耗时         元变量创建
────────────────────────────────────────────────────────
check_universe                   18.6µs       0
eval typ                           3µs        0
fake_bind                         42µs        0
→ check body                  42.44s        32,789  ← 全部在这里
wrap_match_in_call                5.9µs       0
solve_multi_trait                25.2µs       0 (已全解)
no_metas                        670.8µs       0 (验证通过)
nf+eval+decl                     28.9µs       0
```

42.44 秒全在 `check::<false>` 里面。

### 指数增长的元变量创建

通过追踪每次 `check` 调用后的元变量增量，发现完美 **2^n 指数增长**：

```
check[App]: +8     metas (lvl=20)
check[App]: +24    metas (lvl=19)
check[App]: +56    metas (lvl=18)
check[App]: +120   metas (lvl=17)
check[App]: +248   metas (lvl=16)
check[App]: +504   metas (lvl=15)
check[App]: +1016  metas (lvl=14)
check[App]: +2040  metas (lvl=13)
check[App]: +4088  metas (lvl=12)
check[App]: +8184  metas (lvl=11)
check[App]: +16376 metas (lvl=10)
check[App]: +32760 metas (lvl=10)
check[Let]: +32789 metas (lvl=9..1)  ← 只传递，不新增
check[Lam]: +32789 metas (lvl=0)
```

**全部 32,789 个元变量由 `check[App]` 创建**，来自 `moduleVL` 末尾的 **12 个嵌套 `+` 调用**：

```typort
"module " + m.name + " (\n" + port_decls + clk_port + reset_port +
"\n);\n" + wire_decls + reg_decls + assigns + clocked + always +
"endmodule\n"
```

### 指数增长成因

每个 `+` 解析为 `Raw::App(Raw::Obj(lhs, "+"), rhs)`。`check` 的通用分支 `(t, _)` 调用 `infer_expr`，而 `infer_expr(App)` 先 infer `Obj(lhs, "+")`，这又递归 infer `lhs`——lhs 是另一个 `+`，形成嵌套链。

每层外层 `+` 的 `infer_expr` **完整重做全部内层工作**，经过：

1. **`trait_wrap`** — 遍历 namespace 条目查找 `+` 方法，对每个条目创建隐式参数元变量并统一匹配。然后克隆整个 `trait_definition`，遍历全部 trait 调用 `synth`
2. **`insert_go`** — 递归为每个 `Pi(Impl)` 插入隐式元变量
3. **`unify_catch`** — 类型统一

每层 `+` 生成约 8 个基量。12 层嵌套导致总元变量数 **O(2^n)**：

```
8 × (2^12 - 1) = 8 × 4095 = 32,760 ≈ 32,789
```

## 对比 Lean 4 的做法

| 技术 | Lean 4 | 本项目缺失 |
|------|--------|-----------|
| **双向精化** | 已知类型时用 Checking (无递归)，未知时才 Inference | 通用分支 `(t,_)` 一律走 `infer_expr`，导致重推断 |
| **Let-normal form** | 复杂表达式拍平成顺序 let 绑定 | 12 个 `+` 保持嵌套树结构 |
| **Tabled typeclass resolution** | 缓存实例解析结果 | 每个 `+` 完整走 trait 查找 |
| **运算符展开** | `x + y` → `HAdd.hAdd x y` 直接调用 | `+` 走 `Obj → trait_wrap` 方法查找 |

## 修复方案

### 优先级 1（立竿见影）

`moduleVL` 末尾改用 `string_concat` 或 `joinLines` 替代 `+` 链。跳过 `Add` trait 解析，每个拼接 O(1)。

### 优先级 2（系统性修复 `+` 性能）

给 `check` 增加特化分支 `(App(Obj(lhs, op), rhs), known_type)`：已知类型下有同名方法时直接 Check，不走 `infer_expr`。这样每个嵌套 `+` 只做一次方法查找 + 两次子检查，**O(n) 而非 O(2^n)**。

### 优先级 3（优化 trait 解析）

- 给 `trait_wrap` 加方法查找缓存 `(Type, method_name) → trait_method`
- 避免每次克隆 `trait_definition`
- `can_satisfy` 快速预筛（已实现）
- 只跟踪 trait 类型元变量（已实现）
