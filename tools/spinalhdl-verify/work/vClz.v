module vClz (
  input wire [7:0] a,
  output wire [3:0] c
);
  assign c = (a[7] ? 0 : (a[6] ? 1 : (a[5] ? 2 : (a[4] ? 3 : (a[3] ? 4 : (a[2] ? 5 : (a[1] ? 6 : (a[0] ? 7 : 8))))))));
endmodule