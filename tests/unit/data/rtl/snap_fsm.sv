// SPDX-FileCopyrightText: 2026 The fvlint Authors
// SPDX-License-Identifier: ISC
//
// Unit-test snapshot source: an FSM with a synchronous active-low reset, a
// terminal state (DONE) and a decoded state that is never entered (ORPHAN).

module snap_fsm (input clk, input rst_n, input go, input stop, output busy, output done);
  localparam IDLE = 2'd0, RUN = 2'd1, DONE = 2'd2, ORPHAN = 2'd3;
  reg [1:0] st;
  always @(posedge clk)
    if (!rst_n) st <= IDLE;
    else
      case (st)
        IDLE:   if (go) st <= RUN;
        RUN:    if (stop) st <= DONE;
        DONE:   st <= DONE;
        ORPHAN: st <= IDLE;
      endcase
  assign busy = (st == RUN);
  assign done = (st == DONE);
endmodule
