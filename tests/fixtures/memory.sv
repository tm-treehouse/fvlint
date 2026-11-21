// SPDX-FileCopyrightText: 2026 The fvlint Authors
// SPDX-License-Identifier: ISC
//
// Memory addressing fixtures (non-power-of-two depth).

// Clean: write and read pointers wrap at 99 for a 100-entry buffer.
module ring_ok (input clk, input rst, input we, input re, input [7:0] wd, output [7:0] rd);
  reg [7:0] mem [0:99];
  reg [6:0] wp, rp;
  always @(posedge clk)
    if (rst) begin
      wp <= 7'd0;
      rp <= 7'd0;
    end else begin
      if (we) wp <= (wp == 7'd99) ? 7'd0 : wp + 7'd1;
      if (re) rp <= (rp == 7'd99) ? 7'd0 : rp + 7'd1;
    end
  always @(posedge clk) if (we) mem[wp] <= wd;
  assign rd = mem[rp];
endmodule

// BUG: write pointer wraps at 100 instead of 99, writing one past the end.
module ring_bug (input clk, input rst, input we, input [7:0] wd, input [6:0] ra, output [7:0] rd);
  reg [7:0] mem [0:99];
  reg [6:0] wp;
  always @(posedge clk)
    if (rst) wp <= 7'd0;
    else if (we) wp <= (wp == 7'd100) ? 7'd0 : wp + 7'd1;
  always @(posedge clk) if (we) mem[wp] <= wd;
  assign rd = mem[ra];
endmodule
