module vPulseCC (
  input wire pulseIn,
  output wire pulseOut,
  input wire clkA,
  input wire clkB
);
  reg __toggle;
  reg __sync1;
  reg __sync2;
  assign pulseOut = (__sync1 ^ __sync2);
  always @(posedge clkA) begin
    if (pulseIn) begin
      __toggle <= ~__toggle;
    end
  end
  always @(posedge clkB) begin
    __sync1 <= __toggle;
    __sync2 <= __sync1;
  end
endmodule