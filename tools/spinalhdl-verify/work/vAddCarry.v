module vAddCarry (
  input wire [7:0] a,
  input wire [7:0] b,
  output wire [7:0] sum,
  output wire carry
);
  assign sum = ({1'b0, a} + b);
  assign carry = (a > (255 - b));
endmodule