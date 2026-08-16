module vLog2Ceil (
  input wire [7:0] a,
  output wire [3:0] lc
);
  assign lc = ((a[7] ? 7 : (a[6] ? 6 : (a[5] ? 5 : (a[4] ? 4 : (a[3] ? 3 : (a[2] ? 2 : (a[1] ? 1 : (a[0] ? 0 : 0)))))))) + (((a & (a - 1)) != 0) ? 1 : 0));
endmodule