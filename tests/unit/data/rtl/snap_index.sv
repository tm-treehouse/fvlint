// SPDX-FileCopyrightText: 2026 The fvlint Authors
// SPDX-License-Identifier: ISC
//
// Unit-test snapshot source: a bit-select with a narrow signed index (Yosys
// keeps the 4-bit signed offset) next to an unsigned one.

module snap_index (input [2:0] a, input neg, input [3:0] u, input [11:0] vec, output ys, output yu);
  wire signed [3:0] idx = neg ? -4'sd8 : $signed({1'b0, a});
  assign ys = vec[idx];
  assign yu = vec[u];
endmodule
