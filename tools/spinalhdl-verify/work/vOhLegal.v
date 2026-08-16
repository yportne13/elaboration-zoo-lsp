module vOhLegal (
  input wire [7:0] oh,
  output wire legal
);
  assign legal = ((oh == 128) | ((oh == 64) | ((oh == 32) | ((oh == 16) | ((oh == 8) | ((oh == 4) | ((oh == 2) | ((oh == 1) | (oh == 0)))))))));
endmodule