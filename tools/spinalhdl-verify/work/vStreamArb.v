module vStreamArb (
  input wire a_valid,
  input wire [7:0] a_payload,
  output wire a_ready,
  input wire b_valid,
  input wire [7:0] b_payload,
  output wire b_ready,
  output wire m_valid,
  input wire m_ready,
  output wire [7:0] m_payload
);
  wire arb_ready;
  assign a_ready = ((a_valid && !!1) && arb_ready);
  assign b_ready = ((b_valid && !(!1 | a_valid)) && arb_ready);
  assign arb_ready = m_ready;
  assign m_valid = (a_valid | b_valid);
  assign m_payload = ((a_valid && !!1) ? a_payload : ((b_valid && !(!1 | a_valid)) ? b_payload : 0));
endmodule