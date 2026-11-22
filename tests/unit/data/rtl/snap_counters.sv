// SPDX-FileCopyrightText: 2026 The fvlint Authors
// SPDX-License-Identifier: ISC
//
// Unit-test snapshot source: counter shapes for the counter detector.

module snap_counters (input clk, input rst, input en, input load, input inc, input dec,
                      input [3:0] din, output [31:0] o);
  // Free-running: the increment condition does not depend on the counter.
  reg [3:0] free_q;
  always @(posedge clk) if (rst) free_q <= 4'd0; else if (en) free_q <= free_q + 4'd1;

  // Bounded: clears at 9.
  reg [3:0] mod_q;
  always @(posedge clk)
    if (rst) mod_q <= 4'd0;
    else if (mod_q == 4'd9) mod_q <= 4'd0;
    else if (en) mod_q <= mod_q + 4'd1;

  // Down counter with a load value.
  reg [3:0] down_q;
  always @(posedge clk)
    if (rst) down_q <= 4'd0;
    else if (load) down_q <= 4'd12;
    else if (down_q != 4'd0) down_q <= down_q - 4'd1;

  // Signed up/down accumulator.
  reg signed [5:0] acc;
  always @(posedge clk)
    if (rst) acc <= 6'sd0;
    else if (inc && acc != 6'sd31) acc <= acc + 6'sd1;
    else if (dec && acc != -6'sd32) acc <= acc - 6'sd1;

  // Counts up to a registered limit (relational lemma candidate).
  reg [3:0] lim, rel_q;
  always @(posedge clk) if (rst) lim <= 4'd0; else if (load) lim <= din;
  always @(posedge clk) if (rst) rel_q <= 4'd0; else if (rel_q < lim) rel_q <= rel_q + 4'd1;

  // One level of hierarchy (flattened names).
  snap_sub_cnt u_sub (.clk(clk), .rst(rst), .en(en), .q(o[31:28]));
  assign o[27:0] = {2'b00, free_q, mod_q, down_q, acc, lim, rel_q};
endmodule

module snap_sub_cnt (input clk, input rst, input en, output reg [3:0] q);
  always @(posedge clk) if (rst) q <= 4'd0; else if (en && q != 4'd15) q <= q + 4'd1;
endmodule
