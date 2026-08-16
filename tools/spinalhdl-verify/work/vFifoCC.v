module vFifoCC (
  input wire pushValid,
  input wire [3:0] pushData,
  output wire pushReady,
  output wire popValid,
  output wire [3:0] popData,
  input wire clkA,
  input wire rstA,
  input wire clkB,
  input wire rstB
);
  wire pushReady_i;
  wire [3:0] pod_i;
  wire [2:0] occ;
  reg [1:0] _d_wrPtr;
  reg [1:0] _d_rdPtr;
  reg [1:0] _d_wrPtrSync1;
  reg [1:0] _d_wrPtrSync2;
  reg [1:0] _d_rdPtrSync1;
  reg [1:0] _d_rdPtrSync2;
  reg [3:0] _d_pop;
  reg [3:0] _d_mem [0:3];
  assign pod_i = _d_pop;
  assign popValid = !(_d_rdPtr == _d_wrPtrSync2);
  assign pushReady_i = !(_d_wrPtr == _d_rdPtrSync2);
  assign occ = (_d_wrPtr - _d_rdPtrSync2);
  assign pushReady = pushReady_i;
  assign popValid = popValid;
  assign popData = pod_i;
  always @(posedge clkA or posedge rstA) begin
    if (rstA) begin
      _d_wrPtr <= 0;
      _d_rdPtrSync1 <= 0;
      _d_rdPtrSync2 <= 0;
    end else begin
      _d_rdPtrSync1 <= _d_rdPtr;
      _d_rdPtrSync2 <= _d_rdPtrSync1;
      if (pushValid && !(_d_wrPtr == _d_rdPtrSync2)) begin
      _d_mem[_d_wrPtr] <= pushData;
      end
      if (pushValid && !(_d_wrPtr == _d_rdPtrSync2)) begin
        _d_wrPtr <= (_d_wrPtr + 1);
      end
      if (!(_d_rdPtr == _d_wrPtrSync2)) begin
        _d_rdPtr <= (_d_rdPtr + 1);
      end
    end
  end
  always @(posedge clkB or posedge rstB) begin
    if (rstB) begin
      _d_rdPtr <= 0;
    end else begin
      _d_wrPtrSync1 <= _d_wrPtr;
      _d_wrPtrSync2 <= _d_wrPtrSync1;
      _d_pop <= _d_mem[_d_rdPtr];
      if (!(_d_rdPtr == _d_wrPtrSync2)) begin
        _d_rdPtr <= (_d_rdPtr + 1);
      end
    end
  end
endmodule