module vStreamMux (
  input wire sel,
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
  wire mux_ready;
  assign a_ready = ((sel == 0) && mux_ready);
  assign b_ready = ((sel == 1) && mux_ready);
  assign mux_ready = m_ready;
  assign m_valid = ((sel == 0) ? a_valid : ((sel == 1) ? b_valid : 0));
  assign m_payload = ((sel == 0) ? a_payload : ((sel == 1) ? b_payload : 0));
endmodule