// SPDX-FileCopyrightText: 2026 The fvlint Authors
// SPDX-License-Identifier: ISC
//
// Dead-branch fixtures (--dead-branches).

// A counter that wraps at 5: the branch for 7 can never be taken, and the
// item for 6 of the case statement neither.  Everything else is live.
module br_count (input clk, input rst, input go, output reg [2:0] n, output reg [1:0] mode,
                 output reg flag);
  always @(posedge clk)
    if (rst) n <= 3'd0;
    else if (go) n <= (n == 3'd5) ? 3'd0 : n + 3'd1;
  always @(posedge clk)
    if (rst) flag <= 1'b0;
    else if (n == 3'd7) flag <= 1'b1;            // dead: n never reaches 7
    else if (n == 3'd4) flag <= 1'b0;
  always @(posedge clk)
    case (n)
      3'd0: mode <= 2'd0;
      3'd3: mode <= 2'd1;
      3'd6: mode <= 2'd2;                       // dead: n never reaches 6
      default: mode <= 2'd3;                    // (defaults are not checked)
    endcase
endmodule

// Every arm is live, one of them only after 40 cycles: past the first bounded
// search, so the proof rounds have to find it.
module br_deep (input clk, input rst, output reg [5:0] t, output reg late);
  always @(posedge clk)
    if (rst) t <= 6'd0;
    else if (t != 6'd63) t <= t + 6'd1;
  always @(posedge clk)
    if (rst) late <= 1'b0;
    else late <= (t == 6'd40) ? 1'b1 : late;
endmodule

// A condition that is always true once out of reset: its else arm is dead.
module br_always (input clk, input rst, input d, output reg q, output reg ok);
  always @(posedge clk)
    if (rst) ok <= 1'b1;
    else ok <= 1'b1;
  always @(posedge clk)
    if (ok) q <= d;
    else q <= 1'b0;                             // dead: ok is always 1 after reset
endmodule

// A select that only an assumption makes dead (see branches_assume.sv).
module br_assume (input clk, input rst, input [1:0] cmd, output reg [3:0] acc);
  always @(posedge clk)
    if (rst) acc <= 4'd0;
    else case (cmd)
      2'd0: acc <= acc;
      2'd1: acc <= acc + 4'd1;
      2'd2: acc <= acc - 4'd1;
      2'd3: acc <= 4'd0;                        // dead under the assumption cmd != 3
    endcase
endmodule

// Branches inside an FSM state the FSM never reaches: INFO (see
// fsm_unreachable), not a dead_branch finding of their own.  (The state
// register drives no port: Yosys extracts no FSM from one that does.)
module br_fsm (input clk, input rst, input go, input d, output busy, output reg q);
  localparam IDLE = 2'd0, RUN = 2'd1, DONE = 2'd2, ERR = 2'd3;
  reg [1:0] st;
  assign busy = (st == RUN);
  always @(posedge clk)
    if (rst) st <= IDLE;
    else case (st)
      IDLE: if (go) st <= RUN;
      RUN:  st <= DONE;
      DONE: st <= IDLE;
      default: st <= IDLE;
    endcase
  always @(posedge clk)
    if (rst) q <= 1'b0;
    else if (st == ERR) begin
      if (d) q <= 1'b1;                         // in an unreachable state
    end
endmodule
