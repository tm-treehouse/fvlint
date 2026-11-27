// SPDX-FileCopyrightText: 2026 The fvlint Authors
// SPDX-License-Identifier: ISC
//
// Assumption for br_assume (branches.sv): the command 3 is never sent.
module fvlint_assumptions (input [1:0] cmd);
  always @* assume (cmd != 2'd3);
endmodule
