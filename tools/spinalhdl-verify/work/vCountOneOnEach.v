module vCountOneOnEach (
  input wire [3:0] a,
  output wire [2:0] c1,
  output wire [2:0] c2,
  output wire [2:0] c3,
  output wire [2:0] c4
);
  assign c1 = a[0];
  assign c2 = ({1'b0, a[0]} + a[1]);
  assign c3 = ({1'b0, ({1'b0, a[0]} + a[1])} + a[2]);
  assign c4 = ({1'b0, ({1'b0, a[0]} + a[1])} + ({1'b0, a[2]} + a[3]));
endmodule