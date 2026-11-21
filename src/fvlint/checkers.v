// SPDX-FileCopyrightText: 2026 The fvlint Authors
// SPDX-License-Identifier: ISC
//
// fvlint checker library.  Each generated proof instantiates exactly one
// target checker (instance fvl_tgt) plus zero or more lemma checkers
// (instances fvl_lem_<n>) inside a sliced copy of the design.
//
// Every checker has an enable built from a condition vector:
//   en = &(c ~^ POL)   (all condition bits equal their expected polarity)
// and an optional "any" vector e (en also requires |e).

module fvl_range #(
  parameter integer W  = 1,
  parameter [W-1:0] LO = 0,
  parameter [W-1:0] HI = 0,
  parameter integer NC = 1,
  parameter [NC-1:0] POL = 1,
  parameter integer NE = 1
) (
  input [W-1:0]  v,
  input [NC-1:0] c,
  input [NE-1:0] e
);
  wire en = (&(~(c ^ POL))) & (|e);
  always @* if (en) assert (v >= LO && v <= HI);
endmodule

module fvl_onehot0 #(
  parameter integer W  = 2,
  parameter integer NC = 1,
  parameter [NC-1:0] POL = 1
) (
  input [W-1:0]  s,
  input [NC-1:0] c
);
  wire en = &(~(c ^ POL));
  always @* if (en) assert ((s & (s - 1'b1)) == {W{1'b0}});
endmodule

module fvl_nonzero #(
  parameter integer W  = 1,
  parameter integer NC = 1,
  parameter [NC-1:0] POL = 1
) (
  input [W-1:0]  s,
  input [NC-1:0] c
);
  wire en = &(~(c ^ POL));
  always @* if (en) assert (|s);
endmodule

module fvl_member #(
  parameter integer W = 1,
  parameter integer N = 1,
  parameter [N*W-1:0] SET = 0,
  parameter integer NC = 1,
  parameter [NC-1:0] POL = 1
) (
  input [W-1:0]  v,
  input [NC-1:0] c
);
  wire en = &(~(c ^ POL));
  wire [N-1:0] hit;
  genvar i;
  generate
    for (i = 0; i < N; i = i + 1) begin : g
      assign hit[i] = (v == SET[i*W +: W]);
    end
  endgenerate
  always @* if (en) assert (|hit);
endmodule

// Assume the design starts in reset.
module fvl_reset_init #(parameter ACTIVE = 1) (input rst);
  always @* if ($initstate) assume (rst == ACTIVE);
endmodule
