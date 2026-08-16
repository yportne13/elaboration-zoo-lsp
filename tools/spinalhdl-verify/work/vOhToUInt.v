module vOhToUInt (
  input wire [7:0] oh,
  output wire [2:0] idx
);
  assign idx = {(oh[4] | (oh[5] | (oh[6] | (oh[7] | !1)))), {(oh[2] | (oh[3] | (oh[6] | (oh[7] | !1)))), (oh[1] | (oh[3] | (oh[5] | (oh[7] | !1))))}};
endmodule