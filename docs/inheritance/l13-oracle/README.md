# L13 oracle 冻结基线

本目录是 L13 内核改动的**行为 oracle**：改完 L13 后跑
`powershell -NoProfile -ExecutionPolicy Bypass -File tools/l13_oracle_check.ps1`
即按这里的基线逐项比对。

## 内容

| 文件 | 内容 |
|---|---|
| `out_*.txt` | 5 个 example 的 `typort check` **完整输出**（比对时只把计时行归一化） |
| `l13_lib_tests.txt` | L13 lib 测试名全量（638 条，`cargo test --lib L13_namespace:: -- --list`） |
| `l13_inherited_tests.txt` | 从 L12 回灌的继承用例名（22 条） |

## 为什么在仓库里而不是 `target/`

2026-11-25 的 B 路线里，基线原本放在 `target/b-l13/baseline/`。那个位置有两个问题：

1. `cargo clean` / `CARGO_TARGET_DIR` 切换会清掉它；
2. 更严重的是 **`target/release/typort.exe` 被僵尸进程锁住时 `cargo build` 会静默失败**，
   于是 examples 一直在跑旧二进制。第 9/10 两轮因此得出了「examples 栈溢出」的错误结论，
   而真相是那个二进制属于更早的改动。

把基线放进仓库后，它跟着提交走，不会因构建目录变化而失效。

## 更新基线

只在**有意改变行为**时更新，且必须在提交说明里写清为什么：

```powershell
$env:CARGO_TARGET_DIR = 'target_b13'
foreach ($n in 'adder_proof','alu','hdl_ops','theorem_proving','typeclass_complex') {
  cmd /c ("target_b13\release\typort.exe check examples/$n.typort > docs/inheritance/l13-oracle/out_$n.txt 2>&1")
}
```

新增测试时同步更新 `l13_lib_tests.txt`，否则 oracle 脚本会报“多了 N 个测试”。

## 与链继承门禁的关系

两者互补：`tests/chain_inheritance.rs` 管**章节之间的继承面**（账本 + 白名单），
本目录管**L13 自身的行为**（examples 输出 + 测试名集合）。
