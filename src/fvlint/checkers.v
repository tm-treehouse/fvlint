// SPDX-FileCopyrightText: 2026 The fvlint Authors
// SPDX-License-Identifier: ISC
//
// fvlint checker library.  A proof job instantiates checkers inside a sliced
// copy of the design: targets (fvl_t<n>), helper lemmas (fvl_l<n>) and
// vacuity probes (fvl_v<n>).
//
// Every checker computes
//   en = &(c ~^ POL) & |e     (the check applies: path conditions hold)
//   ok = ...                  (the property itself)
// and MODE selects what is emitted:
//   0: assert (en -> ok)      normal check / lemma
//   1: cover  (en && !ok)     counterexample replay on a larger cone
//   2: assert (!en)           vacuity probe: proven => the check can never apply

`define FVL_EMIT \
  generate \
    if (MODE == 0) begin : g_assert \
      always @* if (en) assert (ok); \
    end else if (MODE == 1) begin : g_cover \
      always @* cover (en && !ok); \
    end else begin : g_vacuity \
      always @* assert (!en); \
    end \
  endgenerate

module fvl_range #(
  parameter integer W  = 1,
  parameter [W-1:0] LO = 0,
  parameter [W-1:0] HI = 0,
  parameter integer SIGNED = 0,
  parameter integer NC = 1,
  parameter [NC-1:0] POL = 1,
  parameter integer NE = 1,
  parameter integer MODE = 0
) (
  input [W-1:0]  v,
  input [NC-1:0] c,
  input [NE-1:0] e
);
  wire en = (&(~(c ^ POL))) & (|e);
  wire ok = SIGNED ? ($signed(v) >= $signed(LO) && $signed(v) <= $signed(HI))
                   : (v >= LO && v <= HI);
  `FVL_EMIT
endmodule

// a <= b (relational lemma, e.g. counter <= limit register)
module fvl_rel #(
  parameter integer W = 1,
  parameter integer SIGNED = 0,
  parameter integer NC = 1,
  parameter [NC-1:0] POL = 1,
  parameter integer MODE = 0
) (
  input [W-1:0]  a,
  input [W-1:0]  b,
  input [NC-1:0] c
);
  wire en = &(~(c ^ POL));
  wire ok = SIGNED ? ($signed(a) <= $signed(b)) : (a <= b);
  `FVL_EMIT
endmodule

module fvl_onehot0 #(
  parameter integer W  = 2,
  parameter integer NC = 1,
  parameter [NC-1:0] POL = 1,
  parameter integer MODE = 0
) (
  input [W-1:0]  s,
  input [NC-1:0] c
);
  wire en = &(~(c ^ POL));
  wire ok = (s & (s - 1'b1)) == {W{1'b0}};
  `FVL_EMIT
endmodule

module fvl_nonzero #(
  parameter integer W  = 1,
  parameter integer NC = 1,
  parameter [NC-1:0] POL = 1,
  parameter integer MODE = 0
) (
  input [W-1:0]  s,
  input [NC-1:0] c
);
  wire en = &(~(c ^ POL));
  wire ok = |s;
  `FVL_EMIT
endmodule

module fvl_member #(
  parameter integer W = 1,
  parameter integer N = 1,
  parameter [N*W-1:0] SET = 0,
  parameter integer NC = 1,
  parameter [NC-1:0] POL = 1,
  parameter integer MODE = 0
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
  wire ok = |hit;
  `FVL_EMIT
endmodule

// Hold the design in reset for the first CYCLES global time steps; unless
// ANYTIME is set, reset then stays released (no mid-run or glitching resets).
module fvl_reset_init #(parameter ACTIVE = 1, parameter integer CYCLES = 1,
                        parameter integer ANYTIME = 0) (input rst);
  (* gclk *) wire gclk;
  reg [7:0] n = 8'd0;
  always @(posedge gclk) if (n != 8'hff) n <= n + 8'd1;
  always @* if (n < CYCLES) assume (rst == ACTIVE);
  else if (!ANYTIME) assume (rst != ACTIVE);
endmodule

// Environment sanity probe: reachable iff reset + assumptions are satisfiable.
module fvl_cover_true;
  (* gclk *) wire gclk;
  reg [7:0] n = 8'd0;
  always @(posedge gclk) if (n != 8'hff) n <= n + 8'd1;
  always @* cover (n == 8'd2);
endmodule
