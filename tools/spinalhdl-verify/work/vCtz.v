module vCtz (
  input wire [7:0] a,
  output wire [3:0] c
);
  assign c = (a[0] ? 0 : (a[1] ? 1 : (a[2] ? 2 : (a[3] ? 3 : (a[4] ? 4 : (a[5] ? 5 : (a[6] ? 6 : (a[7] ? 7 : 8))))))));
endmodule