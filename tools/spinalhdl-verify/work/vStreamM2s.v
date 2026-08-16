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
  wire piped_ready;
  reg piped_valid;
  reg [7:0] piped_data;
  assign push_ready = (piped_valid || piped_ready);
  assign piped_ready = pop_ready;
  assign pop_valid = piped_valid;
  assign pop_payload = piped_data;
  always @(posedge clk or posedge reset) begin
    if (reset) begin
      piped_valid <= 0;
    end else begin
      if (push_ready) begin
        piped_valid <= push_valid;
      end
      if (push_ready) begin
        piped_data <= push_payload;
      end
    end
  end
endmodule