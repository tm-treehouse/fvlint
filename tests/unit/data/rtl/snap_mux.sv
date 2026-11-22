// SPDX-FileCopyrightText: 2026 The fvlint Authors
// SPDX-License-Identifier: ISC
//
// Unit-test snapshot source: case statements, part-selects and a memory.

module snap_mux (input clk, input rst, input [2:0] req, input [1:0] sel, input [3:0] din,
                 input we, input [2:0] waddr, input [2:0] raddr,
                 output reg [1:0] gnt, output reg [1:0] y, output [3:0] lane, output [3:0] rd);
  // unique casez with overlapping items, registered result.
  always @(posedge clk)
    if (rst) gnt <= 2'd0;
    else
      unique casez (req)
        3'b1??:  gnt <= 2'd2;
        3'b?1?:  gnt <= 2'd1;
        3'b??1:  gnt <= 2'd0;
        default: gnt <= 2'd3;
      endcase

  // unique case without a default: also a full_case check.
  always @*
    unique case (1'b1)
      req[0]: y = 2'd1;
      req[1]: y = 2'd2;
    endcase

  // Variable part-select of a 3-lane vector with a 2-bit lane index.
  wire [11:0] lanes = {3{din}};
  assign lane = lanes[sel*4 +: 4];

  // Non-power-of-two memory.
  reg [3:0] mem [0:5];
  always @(posedge clk) if (we) mem[waddr] <= din;
  assign rd = mem[raddr];
endmodule
