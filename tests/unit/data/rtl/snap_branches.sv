// SPDX-FileCopyrightText: 2026 The fvlint Authors
// SPDX-License-Identifier: ISC
//
// Unit-test snapshot source: if/else arms, case items and ?: choices for the
// dead-branch detector.

module snap_branches #(parameter EN = 0)
                     (input clk, input rst_n, input go, input [1:0] op, input a, input b,
                      output reg [2:0] n, output reg [1:0] mode, output reg flag, output y, output reg z);
  // The reset arm is no branch: the select is the reset.
  always @(posedge clk)
    if (!rst_n) n <= 3'd0;
    else if (go) n <= (n == 3'd5) ? 3'd0 : n + 3'd1;

  // An else-if chain, and an arm that contradicts its path (dead by construction).
  always @(posedge clk)
    if (!rst_n) flag <= 1'b0;
    else if (n == 3'd7) flag <= 1'b1;
    else if (a && b) begin
      if (!(a && b)) flag <= 1'b0;
    end

  // Case items, one of them for two values, and a default (not checked).
  always @(posedge clk)
    case (op)
      2'd0: mode <= 2'd0;
      2'd1, 2'd2: mode <= 2'd1;
      default: mode <= 2'd3;
    endcase

  // A continuous ?: and a branch behind a parameter that is 0.
  assign y = a ? b : n[0];
  always @(posedge clk)
    if (EN && go) z <= a;
    else z <= b;
endmodule
