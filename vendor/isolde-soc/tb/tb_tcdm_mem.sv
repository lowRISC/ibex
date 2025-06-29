// Copyleft 2024 ISOLDE
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//

module tb_tcdm_mem #(
    parameter BASE_ADDR = 0,  // Base address for memory access (default 0)
    parameter MEMORY_SIZE = 1024,  // Size of the memory (default 1024 entries)
    parameter DELAY_CYCLES = 0  // Number of clock cycles to delay  operations (default 2)
) (
    input logic                clk_i,
    input logic                rst_ni,
          isolde_tcdm_if.slave tcdm_slave_i
);

  logic [ 7:0] memory                                               [MEMORY_SIZE];





  logic [ 1:0] misalignment;
  logic [31:0] index;
  // Programmable delay counters for each read port
  logic [31:0] delay_counter;  // Delay counter for each memory port

  int          cnt_wr = 0;
  int          cnt_rd = 0;

  // Generate block for each memory port


  //assign tcdm_slave_i.rsp.gnt= tcdm_slave_i.req.req;  // Always grant access for simplicity
  assign misalignment = tcdm_slave_i.req.addr[1:0];  // Get the last 2 bits of the address

  always_comb begin
    if (rst_ni && tcdm_slave_i.req.req)
      tcdm_slave_i.rsp.gnt = (delay_counter == 0) ? tcdm_slave_i.req.req : 0;
    else tcdm_slave_i.rsp.gnt = 0;

    case (misalignment)
      2'b00: begin
        index = (tcdm_slave_i.req.addr - BASE_ADDR);
      end
      2'b01: begin
        // If addr is ...xx01, read from addr-1, addr, addr+1
        index = (tcdm_slave_i.req.addr - BASE_ADDR) - 1;
      end
      2'b10: begin
        // If addr is ...xx10, read from addr-2, addr-1, addr
        index = (tcdm_slave_i.req.addr - BASE_ADDR) - 2;
      end
      2'b11: begin
        // If addr is ...xx11, read from addr-3, addr-2, addr-1
        index = (tcdm_slave_i.req.addr - BASE_ADDR) - 3;
      end
    endcase

  end

  // Always block to process read and write operations
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      tcdm_slave_i.rsp.data  <= '0;
      tcdm_slave_i.rsp.valid <= '0;
    end else begin

      if (tcdm_slave_i.rsp.gnt) begin
        tcdm_slave_i.rsp.gnt <= 0;
        delay_counter <= DELAY_CYCLES;
        if (tcdm_slave_i.req.we) begin  // Write
          cnt_wr += 1;
          if (tcdm_slave_i.req.be[0]) memory[index] <= tcdm_slave_i.req.data[7:0];
          if (tcdm_slave_i.req.be[1]) memory[index+1] <= tcdm_slave_i.req.data[15:8];
          if (tcdm_slave_i.req.be[2]) memory[index+2] <= tcdm_slave_i.req.data[23:16];
          if (tcdm_slave_i.req.be[3]) memory[index+3] <= tcdm_slave_i.req.data[31:24];
          //loop back
          tcdm_slave_i.rsp.data  <= tcdm_slave_i.req.data;
          tcdm_slave_i.rsp.valid <= 1'b1;
        end else begin  //read

          cnt_rd += 1;
          tcdm_slave_i.rsp.data[7:0] <= memory[index];
          tcdm_slave_i.rsp.data[15:8] <= memory[index+1];
          tcdm_slave_i.rsp.data[23:16] <= memory[index+2];
          tcdm_slave_i.rsp.data[31:24] <= memory[index+3];

          tcdm_slave_i.rsp.valid <= 1'b1;
        end
      end else begin  //~tcdm_slave_i.rsp.gnt
        delay_counter <= tcdm_slave_i.req.req ? delay_counter - 1 : DELAY_CYCLES;
        tcdm_slave_i.rsp.data <= '0;
        tcdm_slave_i.rsp.valid <= 1'b0;
      end

    end
  end





endmodule  // tb_tcdm_verilator
