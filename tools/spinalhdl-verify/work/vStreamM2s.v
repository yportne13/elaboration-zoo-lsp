module vStreamM2s (
  input wire push_valid,
  input wire [7:0] push_payload,
  output wire push_ready,
  output wire pop_valid,
  input wire pop_ready,
  output wire [7:0] pop_payload,
  input wire clk,
  input wire reset
);
  reg pop_valid;
  reg [7:0] pop_data;
  assign push_ready = (pop_valid || pop_ready);
  assign pop_ready = pop_ready;
  assign pop_valid = pop_valid;
  assign pop_payload = pop_data;
  always @(posedge clk or posedge reset) begin
    if (reset) begin
      pop_valid <= 0;
    end else begin
      if (push_ready) begin
        pop_valid <= push_valid;
      end
      if (push_ready) begin
        pop_data <= push_payload;
      end
    end
  end
endmodule