// SPDX-FileCopyrightText: 2026 The fvlint Authors
// SPDX-License-Identifier: ISC
//
// Arithmetic fixtures: signed counters and register-bounded counters.

// Clean: a signed position that legitimately steps through -1 -> 0.
// (An unsigned overflow check would flag the 8'hFF -> 8'h00 step.)
module cnt_signed_ok (input clk, input rst, input up, output reg signed [7:0] pos);
  always @(posedge clk)
    if (rst) pos <= -8'sd100;
    else if (up) pos <= (pos == 8'sd100) ? -8'sd100 : pos + 8'sd1;
endmodule

// BUG: signed accumulator overflows past +127 (e.g. 119 + 10).  As an
// unsigned value 119 -> 129 does not wrap, so an unsigned check misses it.
module acc_signed_bug (input clk, input rst, input big, input small, output reg signed [7:0] acc);
  always @(posedge clk)
    if (rst) acc <= 8'sd0;
    else if (acc < 8'sd120) begin
      if (big) acc <= acc + 8'sd10;
      else if (small) acc <= acc + 8'sd1;
    end
endmodule

// Clean: a timer whose limit is a register, reprogrammed only while stopped
// at zero.  Proving no overflow needs the relational invariant cnt <= limit_q.
// (An earlier version allowed `load` together with `en` at zero, which lets
// cnt step past a new limit of 0 -- fvlint found that.)
module prog_timer (input clk, input rst, input en, input load, input [5:0] limit_in,
                   output reg [5:0] cnt);
  reg [5:0] limit_q;
  always @(posedge clk)
    if (rst) begin
      limit_q <= 6'd10;
      cnt <= 6'd0;
    end else begin
      if (load && !en && cnt == 6'd0) limit_q <= limit_in;
      if (en) cnt <= (cnt == limit_q) ? 6'd0 : cnt + 6'd1;
    end
endmodule

// BUG: same timer, but the limit can be lowered while counting; the count
// then runs past the new limit and wraps at 63.
module prog_timer_bug (input clk, input rst, input en, input load, input [5:0] limit_in,
                       output reg [5:0] cnt);
  reg [5:0] limit_q;
  always @(posedge clk)
    if (rst) begin
      limit_q <= 6'd10;
      cnt <= 6'd0;
    end else begin
      if (load) limit_q <= limit_in;
      if (en) cnt <= (cnt == limit_q) ? 6'd0 : cnt + 6'd1;
    end
endmodule
