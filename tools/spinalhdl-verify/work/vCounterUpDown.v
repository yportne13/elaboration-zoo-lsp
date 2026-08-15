module vCounterUpDown (
  input wire inc,
  input wire dec,
  output wire [3:0] value,
  output wire willOverflowIfInc,
  output wire willUnderflowIfDec,
  output wire willOverflow,
  output wire willUnderflow,
  input wire clk,
  input wire reset
);
  reg [3:0] ud;
  assign value = ud;
  assign willOverflowIfInc = (ud == 9);
  assign willUnderflowIfDec = (ud == 0);
  assign willOverflow = ((inc && !dec) && (ud == 9));
  assign willUnderflow = ((dec && !inc) && (ud == 0));
  always @(posedge clk or posedge reset) begin
    if (reset) begin
      ud <= 0;
    end else begin
      if ((inc && !dec) && (ud == 9)) begin
        ud <= 0;
      end
      if ((inc && !dec) && !(ud == 9)) begin
        ud <= (ud + 1);
      end
      if ((dec && !inc) && (ud == 0)) begin
        ud <= 9;
      end
      if ((dec && !inc) && !(ud == 0)) begin
        ud <= (ud - 1);
      end
    end
  end
endmodule