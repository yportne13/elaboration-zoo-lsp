module vDownCounter (
  input wire en,
  output wire [3:0] value,
  output wire willOverflow,
  input wire clk,
  input wire reset
);
  reg [3:0] dc;
  assign value = dc;
  assign willOverflow = (dc == 0);
  always @(posedge clk or posedge reset) begin
    if (reset) begin
      dc <= 9;
    end else begin
      if (dc == 0) begin
        dc <= 9;
      end
      if (!(dc == 0)) begin
        dc <= (dc - 1);
      end
    end
  end
endmodule