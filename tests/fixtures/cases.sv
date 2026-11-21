// SPDX-FileCopyrightText: 2026 The fvlint Authors
// SPDX-License-Identifier: ISC
//
// unique / parallel_case fixtures.

// BUG: overlapping casez items under `unique`: req = 3'b011 matches two
// items, which simulation flags and synthesis silently treats as parallel.
module arb_unique (input clk, input rst, input [2:0] req, output reg [1:0] gnt);
  always @(posedge clk)
    if (rst) gnt <= 2'd0;
    else
      unique casez (req)
        3'b1??:  gnt <= 2'd2;
        3'b?1?:  gnt <= 2'd1;
        3'b??1:  gnt <= 2'd0;
        default: gnt <= 2'd3;
      endcase
endmodule

// Clean: reverse-case decode of a one-hot rotating state. Safe only because
// the state register stays one-hot, which needs the register in the cone.
module dec_onehot (input clk, input rst, input go, output reg [2:0] y);
  reg [2:0] st;
  always @(posedge clk)
    if (rst) st <= 3'b001;
    else if (go) st <= {st[1:0], st[2]};
  always @* begin
    y = 3'd0;
    unique case (1'b1)
      st[0]: y = 3'd1;
      st[1]: y = 3'd2;
      st[2]: y = 3'd4;
    endcase
  end
endmodule

// Clean: the same overlapping patterns are fine when the case is only
// evaluated for one-hot requests (guarded by a valid bit).
module arb_guarded (input clk, input rst, input [2:0] req, output reg [1:0] gnt);
  wire onehot = (req == 3'b001) || (req == 3'b010) || (req == 3'b100);
  always @(posedge clk)
    if (rst) gnt <= 2'd0;
    else if (onehot)
      unique casez (req)
        3'b1??:  gnt <= 2'd2;
        3'b?1?:  gnt <= 2'd1;
        3'b??1:  gnt <= 2'd0;
        default: gnt <= 2'd3;
      endcase
endmodule
