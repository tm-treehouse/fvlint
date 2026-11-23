// SPDX-FileCopyrightText: 2026 The fvlint Authors
// SPDX-License-Identifier: ISC
//
// Regression fixtures for the patterns found by running fvlint on PicoRV32.

// A case statement inside a state the FSM never reaches (PicoRV32's LD_RS2
// with ENABLE_REGS_DUALPORT=1), assigning two signals: one check, dead.
module dead_state (input clk, input rst, input go, input [1:0] sel, output reg [1:0] a, output reg b);
  localparam IDLE = 2'd0, RUN = 2'd1, SPARE = 2'd2;
  reg [1:0] st;
  always @(posedge clk)
    if (rst) begin
      st <= IDLE;
      a <= 2'd0;
      b <= 1'b0;
    end else
      case (st)
        IDLE: if (go) st <= RUN;
        RUN:  st <= IDLE;
        SPARE: begin
          (* parallel_case *)
          case (1'b1)
            sel[0]: begin a <= 2'd1; b <= 1'b1; end
            sel[1]: begin a <= 2'd2; b <= 1'b0; end
          endcase
          st <= IDLE;
        end
      endcase
endmodule

// PicoRV32's IRQ timer: the decrement is guarded by a parameter that is 0.
module param_timer #(parameter EN = 0) (input clk, input rst, input load, input [7:0] v, output [7:0] q);
  reg [7:0] t;
  always @(posedge clk)
    if (rst) t <= 8'd0;
    else if (load) t <= v;
    else if (EN && t) t <= t - 8'd1;
  assign q = t;
endmodule

// full_case on a signal first set to 'x (y: harmless) and on one first set to
// a value (z: simulation keeps 3 when no item matches, synthesis may not):
// one statement, which fails for z.  (In a clocked block with non-blocking
// assignments Yosys keeps the earlier value, so the hazard is combinational.)
module fc_mixed (input [1:0] s, input [3:0] d, output reg [1:0] y, output reg [1:0] z);
  always @* begin
    y = 2'bx;
    z = 2'd3;
    (* parallel_case, full_case *)
    case (1'b1)
      s[0]: begin y = 2'd1; z = d[1:0]; end
      s[1]: begin y = 2'd2; z = d[3:2]; end
    endcase
  end
endmodule

// unique case (full and parallel) on a signal first set to 'x: harmless.
module fc_unique_x (input [1:0] s, output reg [1:0] y);
  always @* begin
    y = 'x;
    unique case (1'b1)
      s[0]: y = 2'd1;
      s[1]: y = 2'd2;
    endcase
  end
endmodule

// PicoRV32's count_instr: a 64-bit counter that only resets to 0 and adds 1,
// compared against a limit software can set.  It can't wrap in fewer than
// 2^64 cycles, beyond the default horizon.
module wide_count (input clk, input rst, input tick, input set, input [63:0] v, output [63:0] n);
  reg [63:0] c, limit;
  always @(posedge clk)
    if (rst) begin
      c <= 64'd0;
      limit <= 64'd0;
    end else begin
      if (set) limit <= v;
      if (tick && c != limit) c <= c + 64'd1;
    end
  assign n = c;
endmodule

// simpleuart's divider counter: 32 bits, reset to 0 when it passes a
// software-set divider.  2^32 cycles to wrap: within the default horizon.
module uart_count (input clk, input rst, input [31:0] div, output reg tick);
  reg [31:0] cnt;
  always @(posedge clk)
    if (rst) begin
      cnt <= 32'd0;
      tick <= 1'b0;
    end else begin
      tick <= 1'b0;
      if (cnt > div) begin
        cnt <= 32'd0;
        tick <= 1'b1;
      end else
        cnt <= cnt + 32'd1;
    end
endmodule

// Two case statements assigning the same signals in different states of an
// FSM (PicoRV32's LD_RS1 and LD_RS2): named after the state they sit in.
module guard_names (input clk, input rst, input go, input [1:0] sel, output reg a, output reg b);
  reg [1:0] st;
  always @(posedge clk)
    if (rst) begin
      st <= 2'd0;
      a <= 1'b0;
      b <= 1'b0;
    end else
      case (st)
        2'd0: begin
          (* parallel_case *)
          case (1'b1)
            sel[0]: begin a <= 1'b1; b <= 1'b0; end
            sel[1]: begin a <= 1'b0; b <= 1'b1; end
          endcase
          if (go) st <= 2'd1;
        end
        2'd1: begin
          (* parallel_case *)
          case (1'b1)
            sel[0]: begin a <= 1'b0; b <= 1'b0; end
            sel[1]: begin a <= 1'b1; b <= 1'b1; end
          endcase
          st <= 2'd0;
        end
      endcase
endmodule

// One module instantiated twice: each instance's case statement is a check of
// its own, named after that instance's signal.  u_b's selects are one-hot by
// construction, so only u_a's statement fails.
module lane_pc (input [1:0] req, output reg [1:0] gnt);
  always @* begin
    gnt = 2'd0;
    (* parallel_case *)
    case (1'b1)
      req[0]: gnt = 2'd1;
      req[1]: gnt = 2'd2;
    endcase
  end
endmodule

module two_lanes (input [1:0] r, input t, output [1:0] ga, output [1:0] gb);
  lane_pc u_a (.req(r), .gnt(ga));
  lane_pc u_b (.req({t, ~t}), .gnt(gb));
endmodule

// A 64-bit counter that steps both ways (wide_count with a decrement): 0 - 1
// wraps to all ones, and the next increment overflows.  Three cycles, not
// 2^64: no horizon INFO.
module updown_wide (input clk, input rst, input up, input down, input set, input [63:0] v, output [63:0] n);
  reg [63:0] c, limit;
  always @(posedge clk)
    if (rst) begin
      c <= 64'd0;
      limit <= 64'd0;
    end else begin
      if (set) limit <= v;
      if (up && c != limit) c <= c + 64'd1;
      else if (down) c <= c - 64'd1;
    end
  assign n = c;
endmodule
