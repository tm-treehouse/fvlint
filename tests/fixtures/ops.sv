// SPDX-FileCopyrightText: 2026 The fvlint Authors
// SPDX-License-Identifier: ISC
//
// Shift and division fixtures (shift_range, div_zero).

// Bug: a 4-bit amount shifts an 8-bit result by up to 15.
module shift_bug (input clk, input [7:0] d, input [3:0] s, output reg [7:0] y);
  always @(posedge clk) y <= d << s;
endmodule

// Clean: the amount can't reach the width (no check at all).
module shift_narrow (input clk, input [7:0] d, input [3:0] s, output reg [7:0] y);
  always @(posedge clk) y <= d >> s[2:0];
endmodule

// Clean: the large amounts never reach the result.
module shift_guarded (input clk, input [7:0] d, input [3:0] s, output reg [7:0] y);
  always @(posedge clk) y <= (s < 4'd8) ? d >> s : 8'd0;
endmodule

// Clean: the amount is a counter that wraps at 7.
module shift_counter (input clk, input rst, input [7:0] d, output reg [7:0] y);
  reg [3:0] n;
  always @(posedge clk) if (rst) n <= 4'd0; else n <= (n == 4'd7) ? 4'd0 : n + 4'd1;
  always @(posedge clk) y <= d << n;
endmodule

// Bug: a one-hot decode of a 3-bit index into 6 enables (`1 << idx`).
module shift_decode (input [2:0] idx, output [5:0] en);
  assign en = 6'd1 << idx;
endmodule

// Bug: divides by b whenever it is stored, even when b is 0.
module div_bug (input clk, input [7:0] a, input [3:0] b, output reg [7:0] q, output reg [3:0] r);
  always @(posedge clk) begin
    q <= a / b;
    r <= a % b;
  end
endmodule

// Clean: the quotient is only selected when b is not 0.
module div_guarded (input clk, input [7:0] a, input [3:0] b, output reg [7:0] q);
  always @(posedge clk) q <= (b != 4'd0) ? a / b : 8'hff;
endmodule

// Clean: the divisor is a register that is never 0 after reset.
module div_reg (input clk, input rst, input [7:0] a, input [3:0] d, output reg [7:0] q);
  reg [3:0] div;
  always @(posedge clk) if (rst) div <= 4'd1; else if (d != 4'd0) div <= d;
  always @(posedge clk) q <= a / div;
endmodule
