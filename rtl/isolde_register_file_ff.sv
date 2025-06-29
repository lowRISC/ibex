// Copyleft 2024
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * ISOLDE additional register file
 *
 * Register file with  15x 4*32 bit wide registers. 
 * This register file is based on flip flops. Use this register file when
 * targeting FPGA synthesis or Verilator simulation.
 */


`define GEN_READ_BLOCK(CHANNEL) \
  always_comb begin \
    if (isolde_rf_bus.raddr_``CHANNEL < RegCount) begin \
      isolde_rf_bus.rdata_``CHANNEL  = reg_file[isolde_rf_bus.raddr_``CHANNEL];  \
      isolde_rf_err_read = 1'b0; \
    end else begin \
      isolde_rf_bus.rdata_``CHANNEL  = '0;  \
      isolde_rf_err_read = 1'b1; \
    end \
  end


module isolde_register_file_ff
  import isolde_register_file_pkg::RegDataWidth, isolde_register_file_pkg::RegCount, isolde_register_file_pkg::RegSize, isolde_register_file_pkg::RegAddrWidth;
(
    // Clock and Reset
    input logic clk_i,  // Clock signal
    input logic rst_ni,  // Active-low reset signal
    //
    isolde_register_file_if isolde_rf_bus
);


  // Internal Register File: RegCount registers, each RegSize words of DataWidth bits
  logic [RegSize-1:0][RegDataWidth-1:0] reg_file[RegCount-1:0];
  // logic [RegAddrWidth-1:0] echo_addr;
  logic isolde_rf_err_write;  // Error signal for write process
  logic isolde_rf_err_read;  // Error signal for read process

  // Register Write Process (Sequential logic)
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      // Reset the register file (optional, depending on your design requirements)
      for (int i = 0; i < RegCount; i++) begin
        reg_file[i] <= '0;
      end
      isolde_rf_err_write <= 1'b0;
      //echo_addr <= 0;
    end else begin
      // Write data to the register file if write enable is active
      if (isolde_rf_bus.we_0) begin
        if (isolde_rf_bus.waddr_0 < RegCount) begin
          reg_file[isolde_rf_bus.waddr_0] <= isolde_rf_bus.wdata_0;
          //echo_addr <= isolde_rf_bus.waddr_0;
          //isolde_rf_bus.echo_0 <= isolde_rf_bus.wdata_0;
          isolde_rf_err_write <= 1'b0;
        end else begin
          // Error: write address out of range
          isolde_rf_err_write <= 1'b1;
        end
      end else begin
        isolde_rf_err_write <= 1'b0;
      end
    end
  end

  // //echo process
  always_comb begin
    if (isolde_rf_bus.we_0) begin
      isolde_rf_bus.echo_0 = isolde_rf_bus.wdata_0;
    end
  end
  // Register Read Processes (Combinational logic)
  `GEN_READ_BLOCK(0)
  `GEN_READ_BLOCK(1)
  `GEN_READ_BLOCK(2)
  `GEN_READ_BLOCK(3)
  `GEN_READ_BLOCK(4)

  // Combine read and write error signals
  assign isolde_rf_bus.isolde_rf_err = isolde_rf_err_write | isolde_rf_err_read;

endmodule
