module vUintToOh (
  input wire [2:0] a,
  output wire [7:0] oh
);
  assign oh = (1 << a);
endmodule