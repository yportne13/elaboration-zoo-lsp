# Round-10 performance battery (2026-10-11)

30 timed dimensions over the release binaries at this HEAD.
All numbers are single-run medians reported by the bench binaries

| experiment | result | note |
|---|---|---|
| bench_l01 | rc=0 |   env_slice               0.189      0.226 |
| bench_l02 | rc=0 | k=15  n=65536    fast_ss=     2.816ms /     4.073 fast=     2.730ms*/     3.170  |
| bench_l03 | rc=0 | k=15  n=65536    fast_ss=     5.178ms /     5.184 fast=     3.238ms /     3.242  |
| bench_l04 | rc=0 | k=15  n=65536    fast_ss=     4.036ms /     4.382 fast=     3.439ms*/     3.685  |
| bench_l05 | rc=0 | k=15  n=65536    fast_ss=     4.335ms /     4.559 fast=     3.516ms /     3.753  |
| bench_l06 | rc=0 | k=13  n=16384    fast_ss=     0.807ms*/     1.632 fast=     1.234ms /     1.818  |
| bench_l07 | rc=0 | k=13  n=16384    fast_ss=     0.984ms*/     1.939 fast=     1.720ms /     2.069  |
| bench_l08 | rc=0 | k=13  n=16384    fast_ss=     1.088ms*/     1.854 fast=     1.123ms /     1.978  |
| bench_l09 | rc=0 | k=13  n=16384    fast_ss=     1.032ms*/     1.901 fast=     1.539ms /     1.663  |
| bench_l10 | rc=0 | k=13  n=16384    fast_ss=     1.076ms*/     1.870 fast=     1.352ms /     2.439  |
| bench_l11 | rc=0 | k=13  n=16384    fast_ss=     3.319ms /     3.879 fast=     3.930ms /     4.536  |
| bench_l12 | rc=0 | k=13  n=16384    fast_ss=     3.841ms /     4.073 fast=     3.916ms /     4.712  |
| bench_l13 | basic=0.655ms fast=0.239ms | proc=0.1s |
| church_scaling | k=9:0.246ms k=11:0.488ms k=13:1.912ms | doubling slope |
| workload_natadd | basic=0.841ms fast=0.243ms | ratio=3.5x |
| workload_gadt | basic=0.399ms fast=0.216ms | ratio=1.8x |
| workload_match | basic=0.184ms fast=0.138ms | ratio=1.3x |
| workload_enum | basic=0.510ms fast=0.277ms | ratio=1.8x |
| workload_struct | basic=9.356ms fast=2.647ms | ratio=3.5x |
| workload_strchain | basic=4.310ms fast=1.943ms | ratio=2.2x |
| workload_prelude-core | basic=50.584ms fast=19.252ms | ratio=2.6x |
| cold_start_empty | 4906ms | rc=0 |
| check_with_prelude | 4875ms median(3) | all=['4890', '4875', '4875'] |
| check_adder_proof.typort | 5313ms | rc=0 |
| check_theorem_proving.typort | 5156ms | rc=0 |
| check_typeclass_complex.typort | 5031ms | rc=0 |
| check_hdl_ops.typort | 5579ms | rc=0 |
| check_alu.typort | 4984ms | rc=0 |
| emit_16-counter.typort | 5109ms 12 lines | rc=0 |
| emit_12-memory.typort | 5282ms 17 lines | rc=0 |
| emit_01-basics.typort | 5265ms 18 lines | rc=0 |
| mem_tool_present | ok | L06–L13 性能版内存占用：分配计数/字节/直方图（确定性口径） |
| post_fix_guard | basic=52.080ms fast=18.270ms | proc=0.5s (compare with row prelude-core) |
