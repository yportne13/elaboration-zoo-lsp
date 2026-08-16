module vGray (
  input wire [7:0] x,
  output wire [7:0] g,
  output wire [7:0] back
);
  assign g = ((x >> 1) ^ x);
  assign back = {g[7], {(g[6] ^ g[7]), {(g[5] ^ (g[6] ^ g[7])), {(g[4] ^ (g[5] ^ (g[6] ^ g[7]))), {(g[3] ^ (g[4] ^ (g[5] ^ (g[6] ^ g[7])))), {(g[2] ^ (g[3] ^ (g[4] ^ (g[5] ^ (g[6] ^ g[7]))))), {(g[1] ^ (g[2] ^ (g[3] ^ (g[4] ^ (g[5] ^ (g[6] ^ g[7])))))), (g[0] ^ (g[1] ^ (g[2] ^ (g[3] ^ (g[4] ^ (g[5] ^ (g[6] ^ g[7])))))))}}}}}}};
endmodule