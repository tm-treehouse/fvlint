// SPDX-FileCopyrightText: 2026 The fvlint Authors
// SPDX-License-Identifier: ISC
//
// For ring_bug: the port is called 'ra'; a misspelled port must be rejected,
// not silently ignored.
module fvlint_assumptions (input [6:0] raddr);
  always @* assume (raddr < 7'd100);
endmodule
