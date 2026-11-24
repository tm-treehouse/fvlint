// SPDX-FileCopyrightText: 2026 The fvlint Authors
// SPDX-License-Identifier: ISC
//
// Assumptions on internal nets and the assumption library.  Every check
// below fails without assumptions and is proven with them:
//   assume_internal_nets.sv  for ai_internal
//   assume_internal_lib.sv   for ai_lib

module ai_src (input clk, input [1:0] m_in, output reg [1:0] mode);
  always @(posedge clk) mode <= m_in;
endmodule

module ai_gate (input a, input b, output x);
  assign x = a & b;
endmodule

module ai_internal (
  input clk, input [1:0] m_in, input a, input b, input [11:0] vec,
  output [3:0] lane, output [3:0] pick, output x
);
  // A lane select on a register inside u_src: 3 lanes, mode can be 3.
  wire [1:0] mode;
  ai_src u_src (.clk(clk), .m_in(m_in), .mode(mode));
  assign lane = vec[mode * 4 +: 4];
  // A select on {a, b}; the assumption is on u_g.x = a & b, an internal net
  // the check does not read.  Without its logic in the slice, x would be a
  // free value and the assumption would not rule out {a, b} = 3.
  ai_gate u_g (.a(a), .b(b), .x(x));
  wire [1:0] ab = {a, b};
  assign pick = vec[ab * 4 +: 4];
endmodule

module ai_lib (
  input clk, input rst,
  input valid, input ready, input [3:0] data,
  input [1:0] cfg, input p, input [2:0] s, input [1:0] r,
  input [11:0] vec,
  output [3:0] o_hs, output [3:0] o_cfg, output [3:0] o_p, output reg [1:0] y, output [3:0] o_r
);
  // valid/ready: a pending transfer drops valid or changes its data.
  reg pend;
  reg [3:0] q;
  always @(posedge clk) if (rst) pend <= 1'b0; else pend <= valid && !ready;
  always @(posedge clk) q <= data;
  wire hs_bad = pend && (!valid || data != q);
  assign o_hs = vec[{hs_bad, hs_bad} * 4 +: 4];

  // A configuration input that changes after the first cycle out of reset.
  reg started;
  reg [1:0] cfg0;
  always @(posedge clk)
    if (rst) started <= 1'b0;
    else begin
      started <= 1'b1;
      if (!started) cfg0 <= cfg;
    end
  wire cfg_bad = started && cfg != cfg0;
  assign o_cfg = vec[{cfg_bad, cfg_bad} * 4 +: 4];

  // A pulse that is high two cycles in a row.
  reg prev;
  always @(posedge clk) if (rst) prev <= 1'b0; else prev <= p;
  wire p_bad = prev && p;
  assign o_p = vec[{p_bad, p_bad} * 4 +: 4];

  // One-hot select.
  always @* begin
    y = 2'd0;
    unique case (1'b1)
      s[0]: y = 2'd1;
      s[1]: y = 2'd2;
      s[2]: y = 2'd3;
    endcase
  end

  // A range: r is 0..2.
  assign o_r = vec[r * 4 +: 4];
endmodule
