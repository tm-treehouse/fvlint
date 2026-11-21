// SPDX-FileCopyrightText: 2026 The fvlint Authors
// SPDX-License-Identifier: ISC
//
// Clocking fixtures.  SymbiYosys' default model steps every flip-flop on one
// global clock; these need the multi-clock model.

// BUG: credit_ok with the registered "not full" flag in a slower clock
// domain.  Between two slow edges the fast counter keeps incrementing on a
// stale flag and overflows.  (A single-clock model wrongly proves this.)
module credit_mc (input clk_fast, input clk_slow, input rst, input req, input rel,
                  output reg [2:0] used);
  reg ok_q;
  wire inc = req & ok_q;
  wire dec = rel & (used != 3'd0);
  always @(posedge clk_slow) if (rst) ok_q <= 1'b1; else ok_q <= (used < 3'd6);
  always @(posedge clk_fast)
    if (rst) used <= 3'd0;
    else if (inc && !dec) used <= used + 3'd1;
    else if (dec && !inc) used <= used - 3'd1;
endmodule

// Clean: the flag is updated on the falling edge of the same clock, so it is
// always fresh at the next rising edge.  Needs the multi-clock model (two
// edges) and must still be provable with it.
module credit_mixed_edge (input clk, input rst, input req, output reg [2:0] used);
  reg ok_n;
  always @(negedge clk) if (rst) ok_n <= 1'b1; else ok_n <= (used < 3'd6);
  always @(posedge clk)
    if (rst) used <= 3'd0;
    else if (req && ok_n) used <= used + 3'd1;
endmodule

// Clean: two independent counters in two clock domains.  Each check's cone
// has one clock, so the fast single-clock model is still exact.
module two_domains (input clk_a, input clk_b, input rst, input en_a, input en_b,
                    output reg [6:0] ca, output reg [6:0] cb);
  always @(posedge clk_a) if (rst) ca <= 7'd0; else if (en_a) ca <= (ca == 7'd99) ? 7'd0 : ca + 7'd1;
  always @(posedge clk_b) if (rst) cb <= 7'd0; else if (en_b) cb <= (cb == 7'd99) ? 7'd0 : cb + 7'd1;
endmodule
