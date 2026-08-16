module vWatchdog (
  input wire feed,
  input wire [7:0] lim,
  output wire timeout,
  input wire clk,
  input wire reset
);
  reg [7:0] __cnt;
  reg __timeout;
  assign timeout = __timeout;
  always @(posedge clk or posedge reset) begin
    if (reset) begin
      __cnt <= 0;
      __timeout <= 0;
    end else begin
      if (__cnt == lim) begin
        __timeout <= 1;
      end
      if (__cnt == lim) begin
        __cnt <= 0;
      end
      if (feed) begin
        __timeout <= 0;
      end
      if (feed) begin
        __cnt <= 0;
      end
      if (!feed && !(__cnt == lim)) begin
        __cnt <= (__cnt + 1);
      end
    end
  end
endmodule