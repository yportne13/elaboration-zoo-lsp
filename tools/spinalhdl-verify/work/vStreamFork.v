module vStreamFork (
  input wire in_valid,
  input wire [7:0] in_payload,
  output wire in_ready,
  output wire o0_valid,
  input wire o0_ready,
  output wire [7:0] o0_payload,
  output wire o1_valid,
  input wire o1_ready,
  output wire [7:0] o1_payload
);
  wire fork_ready_0;
  wire fork_ready_1;
  assign in_ready = (fork_ready_0 && (fork_ready_1 && 1));
  assign fork_ready_0 = o0_ready;
  assign fork_ready_1 = o1_ready;
  assign o0_valid = in_valid;
  assign o0_payload = in_payload;
  assign o1_valid = in_valid;
  assign o1_payload = in_payload;
endmodule