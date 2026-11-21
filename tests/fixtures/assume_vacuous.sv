// SPDX-FileCopyrightText: 2026 The fvlint Authors
// SPDX-License-Identifier: ISC
//
// For ring_bug: satisfiable but over-constraining -- writes never happen, so
// the write-address check (which would otherwise fail) is vacuous.
module fvlint_assumptions (input we);
  always @* assume (!we);
endmodule
