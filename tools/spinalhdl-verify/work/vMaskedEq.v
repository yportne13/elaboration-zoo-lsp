module vMaskedEq (
  input wire [3:0] hard,
  output wire eq
);
  assign eq = ((hard & 6) == 2);
endmodule