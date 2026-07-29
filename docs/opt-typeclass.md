# Typeclass 求解优化笔记

## 问题 1：assertion_table 的线性扫描（已解决）

`find_assertion_entry` 使用 `vals_eq_ground` 结构比较线性扫描 `assertion_table`（一个 `Vec`）。通过在 `GeneratorNode` 和 `ConsumerNode` 中携带 `assertion_idx` 来修复，消除了目标已解决路径中的查找。

## 问题 2：`clean()` 丢弃所有缓存的工作

### 当前行为

`elaboration.rs` 中的 `trait_wrap` 在两个位置调用 `clean() + synth()`：

```
第 1102 行：代码补全的 `t.data.is_empty()`
第 1162 行：按 trait 的方法解析过滤
```

两者都使用以下模式：

```rust
self.trait_solver.clean();
self.trait_solver
    .synth(Assertion { name: x.clone(), arguments: [typ_raw, wildcard, ...] })
    .is_some()
```

### 为什么浪费

`synth()` 是一个完整的 tabled resolution 引擎，带有 assertion 表、生成器栈和循环。但在这些调用点，通配符 `Flex(MetaVar(u32::MAX), [])` 瞬间匹配了第一个实例的模式，所以 `synth()` 总是在一次迭代后返回。整个表的构建/拆卸完全是开销。

实际上，`synth()` 被用作一个简单的成员测试："这个 trait 是否有任何实例的 Self 类型匹配 `typ_raw`？"

对于有约 15 个 trait 和约 40 个实例的 `hdl-verilog.typort`，这意味着每次方法查找：
- 约 15 × 每个 trait 克隆所有实例
- 约 15 × 表构建 + 生成器推送 + 清理

### 建议修复

给 `Synth` 添加一个轻量级 `can_satisfy(&self, trait_name, typ_raw) -> bool` 方法，直接检查实例模式与 `typ_raw` 的匹配，无需构建求解表：

```rust
pub fn can_satisfy(&self, trait_name: &SmolStr, typ_raw: &Val) -> bool {
    let instances = match self.class_instances.get(trait_name) {
        Some(insts) => insts,
        None => return false,
    };
    let wildcard_val: Rc<Val> = Val::Flex(MetaVar(u32::MAX), List::new()).into();
    let out_params = self.trait_out_params.get(trait_name);

    for inst in instances {
        if inst.assertion.arguments.is_empty() { continue; }
        let mut subst = HashMap::new();
        let mut ok = true;
        for (i, i_arg) in inst.assertion.arguments.iter().enumerate() {
            let is_out = out_params
                .map(|op| op.get(i).copied().unwrap_or(false))
                .unwrap_or(false);
            let g_arg: &Val = if i == 0 && !is_out { typ_raw } else { &wildcard_val };
            if is_out && matches!(g_arg, Val::Flex(..)) { continue; }
            if !Self::val_match(g_arg, i_arg, &mut subst) {
                ok = false;
                break;
            }
        }
        if ok { return true; }
    }
    false
}
```

在两个调用点用 `can_satisfy()` 替换 `clean() + synth().is_some()`。

### 不受阻塞

`synth()` 和 `clean()` 保留不动——它们被 L10/L11/L12 代码路径使用，这些路径仍需完整求解算法。

## 问题 3：实例没有头部类型索引

### 当前状态

`class_instances: HashMap<SmolStr, Vec<Instance>>`——实例仅按 trait 名称分组。查找特定 Self 类型的实例需要扫描 `Vec` 中的所有条目。

### 建议

添加二级索引：`HashMap<(SmolStr, SmolStr), Vec<usize>>` 映射 `(trait_name, self_type_head_constructor)` → 实例 Vec 中的索引。在回退到 `val_match` 之前用于 O(1) 过滤。

## 问题 4：`solve_trait` 急切地完整展开每个候选实例

详见讨论中的单独分析。

## 问题 5：`fresh_meta` 急切地调用 `solve_trait`

当 `fresh_meta` 创建带有 trait 类型的 meta 时，它立即尝试实例求解。这应推迟到 `solve_multi_trait`，在统一化完成后进行批量求解。
