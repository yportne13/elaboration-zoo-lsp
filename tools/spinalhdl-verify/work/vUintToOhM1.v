module vUintToOhM1 (
  input wire [2:0] a,
  output wire [7:0] oh
);
  assign oh = ((1 << a) - 1);
endmodule