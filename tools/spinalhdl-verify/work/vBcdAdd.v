module vBcdAdd (
  input wire [3:0] a,
  input wire [3:0] b,
  input wire cin,
  output wire [3:0] s,
  output wire co
);
  assign s = ((({1'b0, a} + b) + (cin ? 1 : 0)) + (((({1'b0, a} + b) + (cin ? 1 : 0)) > 9) ? 6 : 0));
  assign co = ((({1'b0, a} + b) + (cin ? 1 : 0)) > 9);
endmodule