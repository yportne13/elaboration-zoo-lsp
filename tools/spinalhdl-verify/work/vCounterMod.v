module vCounterMod (
  input wire en,
  output wire [3:0] value,
  output wire willOverflow,
  input wire clk,
  input wire reset
);
  reg [3:0] cm;
  assign value = cm;
  assign willOverflow = (cm == 9);
  always @(posedge clk or posedge reset) begin
    if (reset) begin
      cm <= 0;
    end else begin
      if (cm == 9) begin
        cm <= 0;
      end
      if (!(cm == 9)) begin
        cm <= (cm + 1);
      end
    end
  end
endmodule