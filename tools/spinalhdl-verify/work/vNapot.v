module vNapot (
  input wire [3:0] a,
  output wire [4:0] n
);
  assign n = ({(~a[0] | (~a[1] | (~a[2] | ~a[3]))), {(~a[0] | (~a[1] | ~a[2])), {(~a[0] | ~a[1]), ~a[0]}}} << 1);
endmodule