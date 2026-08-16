module vCountOneU (
  input wire [7:0] a,
  output wire [3:0] c
);
  assign c = ({1'b0, ({1'b0, ({1'b0, a[0]} + a[1])} + ({1'b0, a[2]} + a[3]))} + ({1'b0, ({1'b0, a[4]} + a[5])} + ({1'b0, a[6]} + a[7])));
endmodule