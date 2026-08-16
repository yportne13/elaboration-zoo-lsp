module vOhMuxOr (
  input wire [3:0] sel,
  input wire [7:0] a,
  input wire [7:0] b,
  input wire [7:0] c,
  input wire [7:0] d,
  output wire [7:0] o
);
  assign o = ((sel[0] ? a : 0) | ((sel[1] ? b : 0) | ((sel[2] ? c : 0) | ((sel[3] ? d : 0) | !1))));
endmodule