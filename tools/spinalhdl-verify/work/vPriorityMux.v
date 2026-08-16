module vPriorityMux (
  input wire [3:0] sel,
  input wire [7:0] a,
  input wire [7:0] b,
  input wire [7:0] c,
  input wire [7:0] d,
  input wire [7:0] dflt,
  output wire [7:0] o
);
  assign o = (sel[0] ? a : (sel[1] ? b : (sel[2] ? c : (sel[3] ? d : dflt))));
endmodule