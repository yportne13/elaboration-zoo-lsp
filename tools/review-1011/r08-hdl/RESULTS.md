# r08-hdl — 实验结果

- probes: 30  PASS: 30  FAIL: 0  TIMEOUT: 0  NOEXPECT: 0

| id | verdict | time | probe | note |
|---|---|---|---|---|
| h01_add | PASS | 4.98s | a + b emits an addition |  |
| h02_sub | PASS | 5.00s | a - b emits subtraction |  |
| h03_mul | PASS | 4.97s | a * b emits multiplication with widened result |  |
| h04_inc_widen | PASS | 5.00s | +^ result is 9-bit wide |  |
| h05_and_or_xor | PASS | 5.00s | & | ^ bitwise ops |  |
| h06_shift | PASS | 5.00s | left shift by a UInt signal |  |
| h07_slice | PASS | 5.00s | slice[3,0] extracts low nibble |  |
| h08_bit_select | PASS | 4.95s | a[0] single-bit extraction |  |
| h09_concat | PASS | 5.00s | ## concatenation emits {a, b} |  |
| h10_compare | PASS | 5.00s | < comparison |  |
| h11_mux | PASS | 5.00s | .mux emits a c ? a : b conditional |  |
| h12_ternary | PASS | 4.97s | ? : desugars to mux |  |
| h13_reg | PASS | 5.02s | register: always @(posedge clk) with nonblocking assign |  |
| h14_reg_init | PASS | 4.98s | register with async reset value |  |
| h15_regnext | PASS | 5.03s | regNext delays by one cycle |  |
| h16_output_reg | PASS | 4.95s | output reg port emits a clocked output |  |
| h17_counter | PASS | 5.00s | counter wrap is (~value == 0) combinational |  |
| h18_mem_write | PASS | 5.02s | mem write port emits always @(posedge clk) |  |
| h19_mem_read_async | PASS | 5.02s | async read is a continuous assign |  |
| h20_asbits | PASS | 5.00s | UInt -> Bits cast |  |
| h21_sign_extend | PASS | 5.00s | SInt expand sign-extends to 5 bits |  |
| h22_literal_fold | PASS | 4.97s | constant addition folds or emits a literal |  |
| h23_submodule | PASS | 5.02s | instance declaration with a defined child module |  |
| h24_port_directions | PASS | 4.98s | input/output port directions |  |
| h25_width_mismatch | PASS | 4.94s | UInt[8] + UInt[4]: unsolved meta error (probe verdict) |  |
| h26_unassigned_output | PASS | 4.98s | undriven output accepted (probe verdict) |  |
| h27_bool_logic | PASS | 4.95s | boolean && maps to Verilog && |  |
| h28_eq_ops | PASS | 4.98s | === equality emits Verilog == |  |
| h29_enum_fsm_state | PASS | 4.95s | FSM skeleton elaborates (probe) |  |
| h30_bundle_ports | PASS | 5.16s | a := b direction probe verdict |  |