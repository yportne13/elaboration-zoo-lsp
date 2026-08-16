module vTimeout (
  input wire en,
  output wire ts,
  input wire clk,
  input wire reset
);
  reg t;
  reg [2:0] t_cnt;
  assign ts = t;
  always @(posedge clk or posedge reset) begin
    if (reset) begin
      t <= 0;
      t_cnt <= 0;
    end else begin
      if (t_cnt == 7) begin
        t <= 1;
      end
      if (t_cnt == 7) begin
        t_cnt <= 0;
      end
      if (!(t_cnt == 7)) begin
        t_cnt <= (t_cnt + 1);
      end
    end
  end
endmodule