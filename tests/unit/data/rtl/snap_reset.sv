// SPDX-FileCopyrightText: 2026 The fvlint Authors
// SPDX-License-Identifier: ISC
//
// Unit-test snapshot source: an asynchronously asserted, synchronously
// released reset (two-stage synchronizer) driving a synchronous reset.

module snap_reset (input clk, input rst_n, input en, output [3:0] q_o);
  reg r1, r2;
  always @(posedge clk or negedge rst_n)
    if (!rst_n) {r2, r1} <= 2'b00;
    else        {r2, r1} <= {r1, 1'b1};
  wire rst_s = ~r2;

  reg [3:0] q;
  always @(posedge clk)
    if (rst_s) q <= 4'd0;
    else if (en && q != 4'd15) q <= q + 4'd1;

  // Cleared by reset but set by data: not a reset.
  reg seen;
  always @(posedge clk or negedge rst_n)
    if (!rst_n) seen <= 1'b0;
    else if (en) seen <= 1'b1;

  assign q_o = q ^ {3'b000, seen};
endmodule
