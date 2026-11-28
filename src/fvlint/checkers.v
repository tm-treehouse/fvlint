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

// Reachability: can the condition c (every bit at POL) hold?  ok is 0, so
// the assertion (MODE 0) says it never does, and a counterexample is a trace
// that reaches it; the replay cover (MODE 1) is cover(en).
module fvl_reach #(
  parameter integer NC = 1,
  parameter [NC-1:0] POL = 1,
  parameter integer MODE = 0
) (
  input [NC-1:0] c
);
  wire en = &(~(c ^ POL));
  wire ok = 1'b0;
  `FVL_EMIT
endmodule

// A FIFO's occupancy, counted from its pointers: +1 when the write pointer
// moves (its next value wd differs from wq), -1 when the read pointer moves,
// 0 while the pointers are reset (all of r at RPOL).  OVER = 1: a write
// without a read while DEPTH entries are held; OVER = 0: a read while none
// is; judged while c (no reset active) holds.  After the first violation of
// either kind the count no longer matches the FIFO, so nothing after it is
// judged (that first one is reported, by one check or the other).  CW bits
// hold DEPTH.
//
// CAND strengthens the property with a guess at how the design counts:
// 1 its register n, 2 the pointer difference wq - rq (pointers with an
// extra wrap bit).  The stronger property is often inductive where the
// plain one isn't; when it can't be proven, fvlint proves the plain one.
module fvl_fifo #(
  parameter integer PW = 1,
  parameter integer RW = 1,
  parameter integer CW = 2,
  parameter integer DEPTH = 1,
  parameter integer OVER = 1,
  parameter integer NR = 1,
  parameter [NR-1:0] RPOL = 1,
  parameter integer CAND = 0,
  parameter integer NW = 1,
  parameter integer NC = 1,
  parameter [NC-1:0] POL = 1,
  parameter integer MODE = 0
) (
  input clk,
  input [PW-1:0] wd,
  input [PW-1:0] wq,
  input [RW-1:0] rd,
  input [RW-1:0] rq,
  input [NR-1:0] r,
  input [NW-1:0] n,
  input [NC-1:0] c
);
  wire live = &(~(c ^ POL));
  wire clear = &(~(r ^ RPOL));
  wire push = wd != wq;
  wire pop = rd != rq;
  reg [CW-1:0] occ = {CW{1'b0}};
  reg broken = 1'b0;
  wire over = push && !pop && occ >= DEPTH;
  wire under = pop && occ == {CW{1'b0}};
  always @(posedge clk)
    if (clear) begin
      occ <= {CW{1'b0}};
      broken <= 1'b0;
    end else begin
      occ <= occ + {{(CW-1){1'b0}}, push} - {{(CW-1){1'b0}}, pop};
      if (over || under) broken <= 1'b1;
    end
  wire [PW-1:0] diff = wq - rq;
  wire agree = CAND == 1 ? occ == n : CAND == 2 ? occ == diff : 1'b1;
  wire en = live && !clear && !broken && (CAND != 0 || (OVER ? (push && !pop) : pop));
  wire ok = (OVER ? !(push && !pop) || !over : !pop || !under) && agree;
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
module fvl_cover_true #(parameter integer N = 2);   // N < 255: the step to reach
  (* gclk *) wire gclk;
  reg [7:0] n = 8'd0;
  always @(posedge gclk) if (n != 8'hff) n <= n + 8'd1;
  always @* cover (n == N);
endmodule
