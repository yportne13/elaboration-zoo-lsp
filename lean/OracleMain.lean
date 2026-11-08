/-
  `OracleMain` — `engine-oracle` 可执行入口（M3）。

  构建：`lake build engine-oracle`（输出 `lean/.lake/build/bin/engine-oracle.exe`）；
  Rust 侧 `tests/lean_oracle_parity.rs` 在 `LEAN_ORACLE=1` 时调用它做差分测试。
-/
import Typort.Engine.Oracle

def main (args : List String) : IO UInt32 :=
  Typort.Engine.Oracle.runMain args
