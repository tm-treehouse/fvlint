// SPDX-FileCopyrightText: 2026 The fvlint Authors
// SPDX-License-Identifier: ISC
//
// Parameterized logic: a check on logic disabled by a parameter must be
// skipped, even when the constant reaches the mux through a wire.

module lanes_param #(parameter USE_LANES = 0) (input clk, input [1:0] sel, input [23:0] data,
                                                output reg [7:0] y);
  wire lanes_on = USE_LANES;
  always @(posedge clk)
    if (lanes_on) y <= data[sel*8 +: 8];   // 3 lanes, 2-bit select: lane 3 is out of range
    else y <= data[7:0];
endmodule
