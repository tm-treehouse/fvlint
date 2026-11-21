// SPDX-FileCopyrightText: 2026 The fvlint Authors
// SPDX-License-Identifier: ISC
//
// Counter fixtures for the fvlint test suite.

// Clean: modulo-100 counter. Overflow is impossible because it clears at 99.
module cnt_mod100 (input clk, input rst, input en, output reg [6:0] q);
  always @(posedge clk)
    if (rst) q <= 7'd0;
    else if (en) q <= (q == 7'd99) ? 7'd0 : q + 7'd1;
endmodule

// BUG: the terminal count (200) does not fit in 7 bits, so the clear never
// fires and the counter wraps from 127 to 0.
module cnt_badlimit (input clk, input rst, input en, output reg [6:0] q);
  always @(posedge clk)
    if (rst) q <= 7'd0;
    else if (en) begin
      if (q == 8'd200) q <= 7'd0;
      else q <= q + 7'd1;
    end
endmodule

// Clean, but only provable with one extra register stage in the cone: the
// "not full" flag is registered, so at cone level 0 it is a free input.
module credit_ok (input clk, input rst, input req, input rel, output reg [2:0] used);
  reg ok_q;
  wire inc = req & ok_q;
  wire dec = rel & (used != 3'd0);
  always @(posedge clk)
    if (rst) begin
      used <= 3'd0;
      ok_q <= 1'b1;
    end else begin
      ok_q <= (used < 3'd6);
      if (inc && !dec) used <= used + 3'd1;
      else if (dec && !inc) used <= used - 3'd1;
    end
endmodule

// BUG: same as credit_ok but the registered threshold is off by one, so two
// back-to-back requests at used==6 overflow the 3-bit count.
module credit_bug (input clk, input rst, input req, input rel, output reg [2:0] used);
  reg ok_q;
  wire inc = req & ok_q;
  wire dec = rel & (used != 3'd0);
  always @(posedge clk)
    if (rst) begin
      used <= 3'd0;
      ok_q <= 1'b1;
    end else begin
      ok_q <= (used < 3'd7);
      if (inc && !dec) used <= used + 3'd1;
      else if (dec && !inc) used <= used - 3'd1;
    end
endmodule

// Free-running timebase: wrap-around is the point, so fvlint only notes it.
module timebase (input clk, input rst, output tick);
  reg [3:0] div;
  always @(posedge clk)
    if (rst) div <= 4'd0;
    else div <= div + 4'd1;
  assign tick = (div == 4'hf);
endmodule

// Wide bounded counter: needs a helper lemma (cnt <= 999) for k-induction.
module cnt_wide (input clk, input rst_n, input en, output reg [15:0] cnt);
  always @(posedge clk or negedge rst_n)
    if (!rst_n) cnt <= 16'd0;
    else if (en) begin
      if (cnt == 16'd999) cnt <= 16'd0;
      else cnt <= cnt + 16'd1;
    end
endmodule
