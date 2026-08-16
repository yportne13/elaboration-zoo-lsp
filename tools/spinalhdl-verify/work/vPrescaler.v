module vPrescaler (
  input wire [7:0] lim,
  output wire ov,
  input wire clk,
  input wire reset
);
  reg [7:0] p_cnt;
  assign ov = (p_cnt == lim);
  always @(posedge clk or posedge reset) begin
    if (reset) begin
      p_cnt <= 0;
    end else begin
      if ((p_cnt == lim) || !(p_cnt < lim)) begin
        p_cnt <= 0;
      end
      if (p_cnt < lim) begin
        p_cnt <= (p_cnt + 1);
      end
    end
  end
endmodule