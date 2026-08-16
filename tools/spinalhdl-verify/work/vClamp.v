module vClamp (
  input wire [7:0] a,
  input wire [7:0] lo,
  input wire [7:0] hi,
  output wire [7:0] cl
);
  assign cl = ((lo < ((a < hi) ? a : hi)) ? ((a < hi) ? a : hi) : lo);
endmodule