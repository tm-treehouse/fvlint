// SPDX-FileCopyrightText: 2026 The fvlint Authors
// SPDX-License-Identifier: ISC
//
// Variable part-select fixtures.

// Clean by construction: 2-bit select over 4 lanes.
module lane_sel_ok (input [31:0] data, input [1:0] sel, output [7:0] lane);
  assign lane = data[sel*8 +: 8];
endmodule

// BUG: a free-running 2-bit lane pointer walks 0..3 but only 3 lanes exist.
module lane_sel_bug (input clk, input rst, input adv, input [23:0] data, output [7:0] lane);
  reg [1:0] sel;
  always @(posedge clk)
    if (rst) sel <= 2'd0;
    else if (adv) sel <= sel + 2'd1;
  assign lane = data[sel*8 +: 8];
endmodule

// Clean: the pointer wraps at 2.
module lane_sel_fixed (input clk, input rst, input adv, input [23:0] data, output [7:0] lane);
  reg [1:0] sel;
  always @(posedge clk)
    if (rst) sel <= 2'd0;
    else if (adv) sel <= (sel == 2'd2) ? 2'd0 : sel + 2'd1;
  assign lane = data[sel*8 +: 8];
endmodule

// BUG: a 4-bit signed bit index reaches -8 (when neg is set).  The offset
// check must not accept its 2's-complement pattern 4'b1000 as offset 8
// (a false PROVEN in fvlint 0.2.0).
module idx_signed_bug (input [2:0] a, input neg, input [11:0] vec, output y);
  wire signed [3:0] idx = neg ? -4'sd8 : $signed({1'b0, a});
  assign y = vec[idx];
endmodule

// Clean: the same signed index, never negative.
module idx_signed_ok (input [2:0] a, input [11:0] vec, output y);
  wire signed [3:0] idx = $signed({1'b0, a});
  assign y = vec[idx];
endmodule
