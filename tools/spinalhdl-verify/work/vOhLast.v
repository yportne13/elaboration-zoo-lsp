module vOhLast (
  input wire [7:0] oh,
  output wire [7:0] l
);
  assign l = (oh & (1 << (oh[7] ? 7 : (oh[6] ? 6 : (oh[5] ? 5 : (oh[4] ? 4 : (oh[3] ? 3 : (oh[2] ? 2 : (oh[1] ? 1 : (oh[0] ? 0 : 0))))))))));
endmodule