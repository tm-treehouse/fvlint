// SPDX-FileCopyrightText: 2026 The fvlint Authors
// SPDX-License-Identifier: ISC
//
// Truncation fixtures: arithmetic results stored in fewer bits.

// Bug: an 8-bit sum stored in 4 bits.
module trunc_bug (input clk, input [7:0] a, input [7:0] b, output reg [3:0] q);
  always @(posedge clk) q <= a + b;
endmodule

// Clean: stored only when the sum fits.
module trunc_guarded (input clk, input [7:0] a, input [7:0] b, output reg [3:0] q);
  always @(posedge clk) if (a < 8'd8 && b < 8'd8) q <= a + b;
endmodule

// Clean: an explicit slice of a named wire (no check), and `c + 1` into
// 5 bits (an unsized 1 makes Yosys add in 32 bits; only 5 can be set).
module trunc_explicit (input clk, input [7:0] a, input [7:0] b, input [3:0] c, output reg [3:0] q,
                       output reg [4:0] r);
  wire [7:0] s = a + b;
  always @(posedge clk) begin
    q <= s[3:0];
    r <= c + 1;
  end
endmodule

// A counter stepped by an unsized constant: counter_overflow's, not truncation's.
module trunc_counter (input clk, input rst, output reg [3:0] n);
  always @(posedge clk) if (rst) n <= 0; else if (n != 4'd9) n <= n + 1;
endmodule

// A decrement of another register: unguarded it borrows into the dropped
// bits (FAIL), guarded it doesn't.
module trunc_sub (input clk, input [3:0] c, output reg [3:0] q, output reg [3:0] p);
  always @(posedge clk) begin
    q <= c - 1;
    if (c != 4'd0) p <= c - 1;
  end
endmodule

// Signed: the dropped bits must copy the sign; small operands fit.
module trunc_signed (input clk, input signed [7:0] a, input signed [7:0] b, output reg signed [3:0] q,
                     output reg signed [3:0] p);
  always @(posedge clk) begin
    q <= a + b;
    if (a >= -8'sd4 && a <= 8'sd3 && b >= -8'sd4 && b <= 8'sd3) p <= a + b;
  end
endmodule
