module vMinMax (
  input wire [7:0] a,
  input wire [7:0] b,
  output wire [7:0] mn,
  output wire [7:0] mx
);
  assign mn = ((a < b) ? a : b);
  assign mx = ((a < b) ? b : a);
endmodule