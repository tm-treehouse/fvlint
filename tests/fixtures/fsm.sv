// SPDX-FileCopyrightText: 2026 The fvlint Authors
// SPDX-License-Identifier: ISC
//
// FSM fixtures.

// Two planted issues: ORPHAN has a case item but nothing ever enters it, and
// DONE is a trap (only reset leaves it).
module fsm_issues (input clk, input rst_n, input go, input stop, output busy);
  localparam IDLE = 2'd0, RUN = 2'd1, DONE = 2'd2, ORPHAN = 2'd3;
  reg [1:0] st;
  always @(posedge clk or negedge rst_n)
    if (!rst_n) st <= IDLE;
    else
      case (st)
        IDLE:   if (go) st <= RUN;
        RUN:    if (stop) st <= DONE;
        DONE:   st <= DONE;
        ORPHAN: st <= IDLE;
      endcase
  assign busy = (st == RUN);
endmodule

// Clean: every state reachable, every state can return to IDLE.
module fsm_clean (input clk, input rst_n, input go, input stop, input ack, output busy);
  localparam IDLE = 2'd0, RUN = 2'd1, WAIT = 2'd2;
  reg [1:0] st;
  always @(posedge clk or negedge rst_n)
    if (!rst_n) st <= IDLE;
    else
      case (st)
        IDLE:    if (go) st <= RUN;
        RUN:     if (stop) st <= WAIT;
        WAIT:    if (ack) st <= IDLE;
        default: st <= IDLE;
      endcase
  assign busy = (st != IDLE);
endmodule
