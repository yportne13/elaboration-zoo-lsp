module vTimer (
  input wire tick,
  input wire clr,
  input wire [7:0] lim,
  output wire full,
  output wire [7:0] value,
  input wire clk,
  input wire reset
);
  reg [7:0] t_cnt;
  reg t_inhibit;
  assign full = (((t_cnt == lim) && tick) && !t_inhibit);
  assign value = t_cnt;
  always @(posedge clk or posedge reset) begin
    if (reset) begin
      t_cnt <= 0;
      t_inhibit <= 0;
    end else begin
      if (tick) begin
        t_inhibit <= (t_cnt == lim);
      end
      if (tick) begin
        t_cnt <= ((t_cnt == lim) ? t_cnt : (t_cnt + 1));
      end
      if (clr) begin
        t_cnt <= 0;
      end
      if (clr) begin
        t_inhibit <= 0;
      end
    end
  end
endmodule