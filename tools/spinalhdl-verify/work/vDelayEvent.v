module vDelayEvent (
  input wire ev,
  output wire de,
  input wire clk,
  input wire reset
);
  reg d_run;
  reg [1:0] d_cnt;
  assign de = (d_run && (d_cnt == 3));
  always @(posedge clk or posedge reset) begin
    if (reset) begin
      d_run <= 0;
      d_cnt <= 0;
    end else begin
      if (d_cnt == 3) begin
        d_run <= 0;
      end
      if (d_cnt == 3) begin
        d_cnt <= 0;
      end
      if (ev) begin
        d_run <= 1;
      end
      if (ev) begin
        d_cnt <= 0;
      end
      if (!ev && !(d_cnt == 3)) begin
        d_cnt <= (d_cnt + 1);
      end
    end
  end
endmodule