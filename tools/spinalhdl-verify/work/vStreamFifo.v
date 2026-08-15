module vStreamFifo (
  input wire push_valid,
  input wire [7:0] push_payload,
  output wire push_ready,
  output wire pop_valid,
  input wire pop_ready,
  output wire [7:0] pop_payload,
  output wire [2:0] occ,
  input wire clk,
  input wire reset
);
  wire fifo_push_valid;
  wire fifo_push_ready;
  wire fifo_pop_valid;
  wire fifo_pop_ready;
  wire [7:0] fifo_push_payload;
  wire [7:0] fifo_pop_payload;
  reg [2:0] fifo_ptrPush;
  reg [2:0] fifo_ptrPop;
  reg [7:0] fifo_mem [0:3];
  assign fifo_pop_payload = fifo_mem[(fifo_ptrPop & 3)];
  assign fifo_push_ready = !((fifo_ptrPush ^ fifo_ptrPop) == 4);
  assign fifo_pop_valid = !(fifo_ptrPush == fifo_ptrPop);
  assign fifo_push_valid = push_valid;
  assign fifo_push_payload = push_payload;
  assign push_ready = fifo_push_ready;
  assign pop_valid = fifo_pop_valid;
  assign pop_payload = fifo_pop_payload;
  assign fifo_pop_ready = pop_ready;
  assign occ = (fifo_ptrPush - fifo_ptrPop);
  always @(posedge clk or posedge reset) begin
    if (reset) begin
      fifo_ptrPush <= 0;
      fifo_ptrPop <= 0;
    end else begin
      if ((fifo_push_valid && fifo_push_ready)) begin
        fifo_mem[(fifo_ptrPush & 3)] <= fifo_push_payload;
      end
      if (fifo_push_valid && fifo_push_ready) begin
        fifo_ptrPush <= (fifo_ptrPush + 1);
      end
      if (fifo_pop_valid && fifo_pop_ready) begin
        fifo_ptrPop <= (fifo_ptrPop + 1);
      end
    end
  end
endmodule