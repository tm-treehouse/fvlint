// SPDX-FileCopyrightText: 2026 The fvlint Authors
// SPDX-License-Identifier: ISC
//
// fvlint assumption library: common interface rules, to instantiate inside
// your fvlint_assumptions module.  Every file passed with --assume can use
// these modules.  Example:
//
//   module fvlint_assumptions (
//     input clk, input rst_n,
//     input in_valid, input in_ready, input [7:0] in_data,
//     (* fvlint_net = "u_core.cfg_mode" *) input [1:0] cfg_mode
//   );
//     fvl_assume_handshake #(.W(8), .RST_ACTIVE(0)) u_in (clk, rst_n, in_valid, in_ready, in_data);
//     fvl_assume_stable #(.W(2), .RST_ACTIVE(0)) u_cfg (clk, rst_n, cfg_mode);
//   endmodule
//
// The clocked rules take the reset with RST_ACTIVE its active level (1 for an
// active-high reset, 0 for rst_n) and say nothing while it is active.  For a
// design without a reset, connect 1'b0 and leave RST_ACTIVE at 1.

// Exactly one bit of s is set.
module fvl_assume_onehot #(parameter integer W = 2) (input [W-1:0] s);
  always @* assume (s != {W{1'b0}} && (s & (s - 1'b1)) == {W{1'b0}});
endmodule

// At most one bit of s is set.
module fvl_assume_onehot0 #(parameter integer W = 2) (input [W-1:0] s);
  always @* assume ((s & (s - 1'b1)) == {W{1'b0}});
endmodule

// LO <= v <= HI, unsigned.
module fvl_assume_range #(parameter integer W = 1, parameter [W-1:0] LO = 0, parameter [W-1:0] HI = 0)
    (input [W-1:0] v);
  always @* assume (v >= LO && v <= HI);
endmodule

// v keeps the value it has in the first cycle after reset (a configuration
// input or strap that only changes while the design is in reset).
module fvl_assume_stable #(parameter integer W = 1, parameter RST_ACTIVE = 1)
    (input clk, input rst, input [W-1:0] v);
  reg seen = 1'b0;
  reg [W-1:0] q;
  always @(posedge clk)
    if (rst == RST_ACTIVE) seen <= 1'b0;
    else begin
      seen <= 1'b1;
      if (!seen) q <= v;
    end
  always @* if (seen && rst != RST_ACTIVE) assume (v == q);
endmodule

// A valid/ready source: once valid is raised it stays raised, with data
// unchanged, until a clock edge where ready is high.  For a request/acknowledge
// pair without data, connect 1'b0 to data.
module fvl_assume_handshake #(parameter integer W = 1, parameter RST_ACTIVE = 1)
    (input clk, input rst, input valid, input ready, input [W-1:0] data);
  reg pend = 1'b0;
  reg [W-1:0] q;
  always @(posedge clk) begin
    pend <= rst != RST_ACTIVE && valid && !ready;
    q <= data;
  end
  always @* if (pend && rst != RST_ACTIVE) assume (valid && data == q);
endmodule

// p is never high in two consecutive cycles.
module fvl_assume_pulse #(parameter RST_ACTIVE = 1) (input clk, input rst, input p);
  reg prev = 1'b0;
  always @(posedge clk) prev <= rst != RST_ACTIVE && p;
  always @* if (prev && rst != RST_ACTIVE) assume (!p);
endmodule
