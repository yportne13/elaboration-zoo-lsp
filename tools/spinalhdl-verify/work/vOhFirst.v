module vOhFirst (
  input wire [7:0] oh,
  output wire [7:0] f
);
  assign f = (oh & ~(oh - 1));
endmodule