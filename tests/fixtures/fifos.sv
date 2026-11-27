// SPDX-FileCopyrightText: 2026 The fvlint Authors
// SPDX-License-Identifier: ISC
//
// FIFO fixtures: no write when full, no read when empty.

// Clean: a count tracks the entries; writes and reads are guarded by it.
module fifo_count (input clk, input rst, input we, input re, input [7:0] wd, output [7:0] rd,
                   output full, output empty);
  reg [7:0] mem [0:3];
  reg [1:0] wp, rp;
  reg [2:0] cnt;
  wire push = we && !full, pop = re && !empty;
  assign full = cnt == 3'd4;
  assign empty = cnt == 3'd0;
  always @(posedge clk)
    if (rst) begin
      wp <= 2'd0; rp <= 2'd0; cnt <= 3'd0;
    end else begin
      if (push) wp <= wp + 2'd1;
      if (pop) rp <= rp + 2'd1;
      cnt <= cnt + {2'd0, push} - {2'd0, pop};
    end
  always @(posedge clk) if (push) mem[wp] <= wd;
  assign rd = mem[rp];
endmodule

// Clean: pointers with an extra wrap bit, full and empty from the pointers.
module fifo_ptrs (input clk, input rst, input we, input re, input [7:0] wd, output [7:0] rd,
                  output full, output empty);
  reg [7:0] mem [0:7];
  reg [3:0] wp, rp;
  assign empty = wp == rp;
  assign full = (wp[2:0] == rp[2:0]) && (wp[3] != rp[3]);
  always @(posedge clk)
    if (rst) begin
      wp <= 4'd0; rp <= 4'd0;
    end else begin
      if (we && !full) wp <= wp + 4'd1;
      if (re && !empty) rp <= rp + 4'd1;
    end
  always @(posedge clk) if (we && !full) mem[wp[2:0]] <= wd;
  assign rd = mem[rp[2:0]];
endmodule

// Bug: reads are guarded, writes are not (overflow); with an off-by-one
// full flag in the second FIFO.
module fifo_nofull (input clk, input rst, input we, input re, input [7:0] wd, output [7:0] rd);
  reg [7:0] mem [0:3];
  reg [1:0] wp, rp;
  reg [2:0] cnt;
  wire pop = re && cnt != 3'd0;
  always @(posedge clk)
    if (rst) begin
      wp <= 2'd0; rp <= 2'd0; cnt <= 3'd0;
    end else begin
      if (we) wp <= wp + 2'd1;
      if (pop) rp <= rp + 2'd1;
      cnt <= cnt + {2'd0, we} - {2'd0, pop};
    end
  always @(posedge clk) if (we) mem[wp] <= wd;
  assign rd = mem[rp];
endmodule

module fifo_offbyone (input clk, input rst, input we, input re, input [7:0] wd, output [7:0] rd);
  reg [7:0] mem [0:3];
  reg [1:0] wp, rp;
  reg [2:0] cnt;
  wire push = we && cnt != 3'd5, pop = re && cnt != 3'd0;    // full should be 4
  always @(posedge clk)
    if (rst) begin
      wp <= 2'd0; rp <= 2'd0; cnt <= 3'd0;
    end else begin
      if (push) wp <= wp + 2'd1;
      if (pop) rp <= rp + 2'd1;
      cnt <= cnt + {2'd0, push} - {2'd0, pop};
    end
  always @(posedge clk) if (push) mem[wp] <= wd;
  assign rd = mem[rp];
endmodule

// Clean: three entries, pointers that wrap at 2.
module fifo_three (input clk, input rst, input we, input re, input [7:0] wd, output [7:0] rd);
  reg [7:0] mem [0:2];
  reg [1:0] wp, rp, cnt;
  wire push = we && cnt != 2'd3, pop = re && cnt != 2'd0;
  always @(posedge clk)
    if (rst) begin
      wp <= 2'd0; rp <= 2'd0; cnt <= 2'd0;
    end else begin
      if (push) wp <= (wp == 2'd2) ? 2'd0 : wp + 2'd1;
      if (pop) rp <= (rp == 2'd2) ? 2'd0 : rp + 2'd1;
      cnt <= cnt + {1'd0, push} - {1'd0, pop};
    end
  always @(posedge clk) if (push) mem[wp] <= wd;
  assign rd = mem[rp];
endmodule

// A flush loads both pointers in mid-run: no FIFO checks (the count can't
// follow it), only the memory and counter checks.
module fifo_flush (input clk, input rst, input flush, input we, input re, input [7:0] wd, output [7:0] rd);
  reg [7:0] mem [0:3];
  reg [1:0] wp, rp;
  always @(posedge clk)
    if (rst || flush) begin
      wp <= 2'd0; rp <= 2'd0;
    end else begin
      if (we) wp <= wp + 2'd1;
      if (re) rp <= rp + 2'd1;
    end
  always @(posedge clk) if (we) mem[wp] <= wd;
  assign rd = mem[rp];
endmodule
