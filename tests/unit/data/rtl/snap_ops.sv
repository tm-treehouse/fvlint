// SPDX-FileCopyrightText: 2026 The fvlint Authors
// SPDX-License-Identifier: ISC
//
// Unit-test snapshot source: every common operator and storage element, so
// the tests can check that fvlint knows every cell type its elaboration flow
// produces (an unknown type is cut, i.e. treated as a free input).

module snap_ops (input clk, input rst, input rst_n, input g, input set, input clr, input ld,
                 input [3:0] a, input [3:0] b, input signed [3:0] sa, input [1:0] s, input [7:0] w,
                 output [127:0] o);
  wire [3:0] arith = a + b - (a * b) / (b | 4'd1) % 4'd3;
  wire signed [3:0] sarith = sa >>> 1;
  wire [7:0] power = a ** 2;
  wire [3:0] shifts = (a << b[1:0]) | (a >> s) | (a <<< 1);
  wire [3:0] bits = (a & b) ^ ~(a | b) ^ (a ~^ b);
  wire reds = &a | |b | ^a | ~^b | ~&a | ~|b;
  wire logic_ops = (a && b) || !s;
  wire cmps = (a < b) ^ (a <= b) ^ (a > b) ^ (a >= b) ^ (a == b) ^ (a != b) ^ (a === b) ^ (a !== b);
  wire [3:0] neg = -a;
  wire [3:0] pos = +a;
  wire [1:0] sel = w[s*2 +: 2];
  wire [3:0] mux = s[0] ? a : b;
  reg [3:0] pm;
  always @* case (s) 2'd0: pm = a; 2'd1: pm = b; 2'd2: pm = ~a; default: pm = ~b; endcase

  reg [3:0] q_dff;  always @(posedge clk) q_dff <= arith;
  reg [3:0] q_adff; always @(posedge clk or posedge rst) if (rst) q_adff <= 0; else q_adff <= bits;
  reg [3:0] q_nadf; always @(negedge clk or negedge rst_n) if (!rst_n) q_nadf <= 4'hf; else q_nadf <= shifts;
  reg q_sr;         always @(posedge clk or posedge set or posedge clr)
                      if (clr) q_sr <= 1'b0; else if (set) q_sr <= 1'b1; else q_sr <= reds;
  reg [3:0] q_ald;  always @(posedge clk or posedge ld) if (ld) q_ald <= b; else q_ald <= a;
  reg [3:0] lat;    always @* if (g) lat = a;
  reg [3:0] alat;   always @* if (rst) alat = 4'd0; else if (g) alat = b;
  reg [3:0] mem [0:4];
  always @(posedge clk) if (g) mem[s] <= a;
  wire [3:0] rd = mem[b[1:0]];

  assign o = {arith, sarith, power, shifts, bits, reds, logic_ops, cmps, neg, pos, sel, mux, pm,
              q_dff, q_adff, q_nadf, q_sr, q_ald, lat, alat, rd};
endmodule
