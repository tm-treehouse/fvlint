// SPDX-FileCopyrightText: 2026 The fvlint Authors
// SPDX-License-Identifier: ISC
//
// For ai_internal: fvlint_net names a net that doesn't exist (u_src.mod);
// it must be rejected with a suggestion, not ignored.
module fvlint_assumptions ((* fvlint_net = "u_src.mod" *) input [1:0] m);
  always @* assume (m != 2'd3);
endmodule
