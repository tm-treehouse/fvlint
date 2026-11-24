// SPDX-FileCopyrightText: 2026 The fvlint Authors
// SPDX-License-Identifier: ISC
//
// For ai_lib (assume_internal.sv): the interface rules of fvlint's
// assumption library.
module fvlint_assumptions (
  input clk, input rst, input valid, input ready, input [3:0] data,
  input [1:0] cfg, input p, input [2:0] s, input [1:0] r
);
  fvl_assume_handshake #(.W(4)) u_hs (clk, rst, valid, ready, data);
  fvl_assume_stable #(.W(2)) u_cfg (clk, rst, cfg);
  fvl_assume_pulse u_p (clk, rst, p);
  fvl_assume_onehot #(.W(3)) u_s (s);
  fvl_assume_range #(.W(2), .LO(0), .HI(2)) u_r (r);
endmodule
