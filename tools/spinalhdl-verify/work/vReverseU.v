module vReverseU (
  input wire [7:0] a,
  output wire [7:0] r
);
  assign r = {a[0], {a[1], {a[2], {a[3], {a[4], {a[5], {a[6], a[7]}}}}}}};
endmodule