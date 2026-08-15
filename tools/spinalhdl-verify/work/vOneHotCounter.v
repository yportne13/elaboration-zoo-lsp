module vOneHotCounter (
  input wire en,
  output wire [3:0] value,
  output wire willOverflow,
  input wire clk,
  input wire reset
);
  reg [3:0] ohc;
  assign value = ohc;
  assign willOverflow = (ohc[3] == 1);
  always @(posedge clk or posedge reset) begin
    if (reset) begin
      ohc <= 1;
    end else begin
      if (ohc[3] == 1) begin
        ohc <= 1;
      end
      if (!(ohc[3] == 1)) begin
        ohc <= (ohc << 1);
      end
    end
  end
endmodule