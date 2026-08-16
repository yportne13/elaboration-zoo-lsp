module vInterruptCtrl (
  input wire [3:0] inputs,
  input wire [3:0] clears,
  input wire [3:0] masks,
  output wire [3:0] pend,
  input wire clk,
  input wire reset
);
  reg [3:0] __pend;
  assign pend = (__pend & masks);
  always @(posedge clk or posedge reset) begin
    if (reset) begin
      __pend <= 0;
    end else begin
      __pend <= ((__pend & ~clears) | inputs);
    end
  end
endmodule