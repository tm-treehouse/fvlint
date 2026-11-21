// SPDX-FileCopyrightText: 2026 The fvlint Authors
// SPDX-License-Identifier: ISC
//
// For ring_bug: contradictory constraints.
module fvlint_assumptions (input [6:0] ra);
  always @* assume (ra < 7'd10);
  always @* assume (ra > 7'd20);
endmodule
