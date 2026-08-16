module vEndianSwap (
  input wire [15:0] a,
  output wire [15:0] s
);
  assign s = {a[7:0], a[15:8]};
endmodule