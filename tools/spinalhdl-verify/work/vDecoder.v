module vDecoder (
  input wire [3:0] oh,
  output wire [1:0] idx
);
  assign idx = {(oh[2] | (oh[3] | !1)), (oh[1] | (oh[3] | !1))};
endmodule