// SPDX-FileCopyrightText: 2026 The fvlint Authors
// SPDX-License-Identifier: ISC
//
// Reset-model fixtures.

// Clean: a one-hot FSM reset through a 2-flop synchronizer.  Until the
// synchronized reset has propagated, the state register still holds its
// power-up value (000), which a one-cycle top-level reset model would report
// as a 'unique case' violation.  fvlint must hold reset long enough and keep
// checks off while the synchronized reset is active.
module rst_sync_onehot (input clk, input rst, input go, output reg [2:0] y);
  reg r1, r2;
  always @(posedge clk) begin
    r1 <= rst;
    r2 <= r1;
  end
  reg [2:0] st;
  always @(posedge clk)
    if (r2) st <= 3'b001;
    else if (go) st <= {st[1:0], st[2]};
  always @* begin
    unique case (1'b1)
      st[0]: y = 3'd1;
      st[1]: y = 3'd2;
      st[2]: y = 3'd4;
    endcase
  end
endmodule

// Same, with an asynchronously asserted, synchronously released active-low
// reset (the usual FPGA reset bridge).
module rst_bridge_counter (input clk, input arst_n, input en, output reg [6:0] q);
  reg [1:0] sync;
  always @(posedge clk or negedge arst_n)
    if (!arst_n) sync <= 2'b00;
    else sync <= {sync[0], 1'b1};
  wire rst_n = sync[1];
  always @(posedge clk)
    if (!rst_n) q <= 7'd0;
    else if (en) q <= (q == 7'd99) ? 7'd0 : q + 7'd1;
endmodule

// Same FSM as fsm.sv:fsm_issues but with a synchronous reset: the reset
// edge from every state must not hide the DONE trap.
module fsm_sync (input clk, input rst, input go, input stop, output busy);
  localparam IDLE = 2'd0, RUN = 2'd1, DONE = 2'd2, ORPHAN = 2'd3;
  reg [1:0] st;
  always @(posedge clk)
    if (rst) st <= IDLE;
    else
      case (st)
        IDLE:   if (go) st <= RUN;
        RUN:    if (stop) st <= DONE;
        DONE:   st <= DONE;
        ORPHAN: st <= IDLE;
      endcase
  assign busy = (st == RUN);
endmodule

// BUG: q copies a synchronizer stage but a data input (func) can also set it
// asynchronously, so it is not a reset.  Treating it as one switches every
// check off while func is high, hiding the out-of-range index (a false
// PROVEN in fvlint 0.2.0).
module rst_data_set (input clk, input rst, input func, input [11:0] vec, output reg y);
  reg r1;
  always @(posedge clk) r1 <= rst;
  reg q;
  always @(posedge clk or posedge func) if (func) q <= 1'b1; else q <= r1;
  wire [3:0] idx = func ? 4'd15 : {3'b000, q};
  always @(posedge clk) y <= vec[idx];
endmodule

// Clean: the offset leaves the vector only in cycle 3, while the synchronized
// reset (r1, r2) is still active, so the check is off then.  fvlint 0.2.0 left
// the synchronizer out of the proof and reported a false FAIL.
module rst_sync_window (input clk, input rst, input [11:0] vec, output reg y, output reg rdy);
  reg r1, r2;
  always @(posedge clk) begin r1 <= rst; r2 <= r1; end
  always @(posedge clk) rdy <= !r2;
  reg [2:0] t = 3'd0;
  always @(posedge clk) if (t != 3'd7) t <= t + 3'd1;
  wire [3:0] idx = (t == 3'd3) ? 4'd15 : 4'd0;
  always @(posedge clk) y <= vec[idx];
endmodule
