// SPDX-FileCopyrightText: 2026 The fvlint Authors
// SPDX-License-Identifier: ISC
//
// Environment constraint for ring_bug: the external read address is in range.
module fvlint_assumptions (input [6:0] ra);
  always @* assume (ra < 7'd100);
endmodule
