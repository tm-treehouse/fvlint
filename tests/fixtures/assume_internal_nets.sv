// SPDX-FileCopyrightText: 2026 The fvlint Authors
// SPDX-License-Identifier: ISC
//
// For ai_internal (assume_internal.sv): assumptions on internal nets, named
// by an fvlint_net attribute and by an escaped identifier.
module fvlint_assumptions (
  (* fvlint_net = "u_src.mode" *) input [1:0] mode,
  input \u_g.x
);
  always @* assume (mode != 2'd3);
  always @* assume (!\u_g.x );
endmodule
