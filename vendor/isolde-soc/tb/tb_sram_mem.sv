// Copyleft 2024 ISOLDE
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//

module tb_sram_mem #(
    parameter ID = 0,  // ID of the memory bank (default 0)
    // Parameters for memory configuration
    parameter int unsigned N_PORTS = 1,  // Number of memory ports (default 1)
    parameter BASE_ADDR = 0,  // Base address for memory access (default 0)
    parameter MEMORY_SIZE = 1024,  // Size of the memory (default 1024 entries)
    parameter DELAY_CYCLES = 0  // Number of clock cycles to delay  operations (default 2)
) (
    input  logic                  clk_i,
    input  logic                  rst_ni,
    input  isolde_tcdm_pkg::req_t req_i [N_PORTS-1:0],
    output isolde_tcdm_pkg::rsp_t rsp_o [N_PORTS-1:0]
);

  logic [        7:0]       memory                                               [MEMORY_SIZE];





  logic [N_PORTS-1:0][ 1:0] misalignment;
  logic [N_PORTS-1:0][31:0] index;
  // Programmable delay counters for each read port
  logic [N_PORTS-1:0][31:0] delay_counter;  // Delay counter for each memory port

  int                       cnt_wr = 0;
  int                       cnt_rd = 0;

  // Generate block for each memory port

  generate
    for (genvar i = 0; i < N_PORTS; i++) begin : gen_mem_port
      //assign rsp_o.gnt= req_i.req;  // Always grant access for simplicity
      assign misalignment[i] = req_i[i].addr[1:0];  // Get the last 2 bits of the address

      always_comb begin
        if (rst_ni && req_i[i].req) rsp_o[i].gnt = (delay_counter[i] == 0) ? req_i[i].req : 0;
        else rsp_o[i].gnt = 0;

        // Assert that address is within valid range
        assert (req_i[i].addr >= BASE_ADDR)
        else
          $fatal(
              "ERROR: req_i[%0d].addr (0x%08h) is below BASE_ADDR (0x%08h)",
              i,
              req_i[i].addr,
              BASE_ADDR
          );

        case (misalignment[i])
          2'b00: begin
            index[i] = (req_i[i].addr - BASE_ADDR);
          end
          2'b01: begin
            // If addr is ...xx01, read from addr-1, addr, addr+1
            index[i] = (req_i[i].addr - BASE_ADDR) - 1;
          end
          2'b10: begin
            // If addr is ...xx10, read from addr-2, addr-1, addr
            index[i] = (req_i[i].addr - BASE_ADDR) - 2;
          end
          2'b11: begin
            // If addr is ...xx11, read from addr-3, addr-2, addr-1
            index[i] = (req_i[i].addr - BASE_ADDR) - 3;
          end
        endcase

      end

      // Always block to process read and write operations
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
          rsp_o[i].data  <= '0;
          rsp_o[i].valid <= '0;
        end else begin

          if (rsp_o[i].gnt) begin
            rsp_o[i].gnt <= 0;
            delay_counter[i] <= DELAY_CYCLES;
            if (req_i[i].we) begin  // Write
              cnt_wr += 1;
              if (req_i[i].be[0]) memory[index[i]] <= req_i[i].data[7:0];
              if (req_i[i].be[1]) memory[index[i]+1] <= req_i[i].data[15:8];
              if (req_i[i].be[2]) memory[index[i]+2] <= req_i[i].data[23:16];
              if (req_i[i].be[3]) memory[index[i]+3] <= req_i[i].data[31:24];
              //loop back
              rsp_o[i].data  <= req_i[i].data;
              rsp_o[i].valid <= 1'b1;
              $fwrite(fh_csv, "%t,%d,%h,%08h,%08h\n", $time, i, req_i[i].we, req_i[i].addr,
                      req_i[i].data);
            end else begin  //read

              cnt_rd += 1;
              rsp_o[i].data[7:0] <= memory[index[i]];
              rsp_o[i].data[15:8] <= memory[index[i]+1];
              rsp_o[i].data[23:16] <= memory[index[i]+2];
              rsp_o[i].data[31:24] <= memory[index[i]+3];

              rsp_o[i].valid <= 1'b1;
              $fwrite(fh_csv, "%t,%d,%h,%08h,%08h\n", $time, i, req_i[i].we, req_i[i].addr, {
                      memory[index[i]+3], memory[index[i]+2], memory[index[i]+1], memory[index[i]]
                      });
            end
          end else begin  //~rsp_o.gnt
            delay_counter[i] <= req_i[i].req ? delay_counter[i] - 1 : DELAY_CYCLES;
            rsp_o[i].data <= '0;
            rsp_o[i].valid <= 1'b0;
          end

        end
      end
    end  // gen_mem_port
  endgenerate

  int    fh_csv;  //filehandle
  string mem_filename;

  initial begin
    mem_filename = $sformatf("sram_id%0d.csv", ID);
    fh_csv = $fopen(mem_filename, "w");
    if (fh_csv == 0) begin
      $display("ERROR: Could not open %s for writing", mem_filename);
      $finish;
    end else begin
      $fwrite(fh_csv, "time,mem_port,we,addr,data\n");
    end
  end


endmodule  // tb_tcdm_verilator
