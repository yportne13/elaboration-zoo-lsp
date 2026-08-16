module vJohnsonCounter (
  input wire en,
  output wire [3:0] value,
  output wire willOverflow,
  input wire clk,
  input wire reset
);
  reg [3:0] jc;
  assign value = jc;
  assign willOverflow = (jc[3] && !jc[2]);
  always @(posedge clk or posedge reset) begin
    if (reset) begin
      jc <= 0;
    end else begin
      if (jc[3] && !jc[2]) begin
        jc <= 0;
      end
      if (!(jc[3] && !jc[2])) begin
        jc <= {jc[2:0], !jc[3]};
      end
    end
  end
endmodule