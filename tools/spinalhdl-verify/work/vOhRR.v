module vOhRR (
  input wire [3:0] req,
  input wire [3:0] pri,
  output wire [3:0] g
);
  assign g = ((({req, req} & ~({req, req} - pri)) & 15) | (({req, req} & ~({req, req} - pri)) >> 4));
endmodule