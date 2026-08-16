module vMajority (
  input wire [6:0] a,
  output wire m
);
  assign m = (({1'b0, ({1'b0, ({1'b0, a[0]} + a[1])} + ({1'b0, a[2]} + a[3]))} + ({1'b0, ({1'b0, a[4]} + a[5])} + a[6])) >= 4);
endmodule