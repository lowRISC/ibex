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




module isolde_register_file_ff 
import isolde_register_file_pkg::RegDataWidth, isolde_register_file_pkg::RegCount, isolde_register_file_pkg::RegSize, isolde_register_file_pkg::RegAddrWidth;
(
    // Clock and Reset
    input logic clk_i,  // Clock signal
    input logic rst_ni, // Active-low reset signal

    // Read port A
    input logic [RegAddrWidth-1:0] isolde_rf_raddr_a_i,  // Read address input
    output logic [RegSize-1:0][RegDataWidth-1:0] isolde_rf_rdata_a_o,  // Read data output

    // Write port W1
    input logic [RegAddrWidth-1:0]                isolde_rf_waddr_a_i,  // Write address input
    input logic [  RegSize-1:0][RegDataWidth-1:0] isolde_rf_wdata_a_i,  // Write data input
    input logic                                isolde_rf_we_a_i,     // Write enable signal

    // Error detection
    output logic isolde_rf_err_o  // Combined error signal for spurious writes or invalid reads
);


  // Internal Register File: RegCount registers, each RegSize words of DataWidth bits
  logic [RegSize-1:0][RegDataWidth-1:0] reg_file[RegCount-1:0];

  logic isolde_rf_err_write_o;  // Error signal for write process
  logic isolde_rf_err_read_o;  // Error signal for read process

  // Register Write Process (Sequential logic)
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      // Reset the register file (optional, depending on your design requirements)
      for (int i = 0; i < RegCount; i++) begin
        reg_file[i] <= '0;
      end
      isolde_rf_err_write_o <= 1'b0;
    end else begin
      // Write data to the register file if write enable is active
      if (isolde_rf_we_a_i) begin
        if (isolde_rf_waddr_a_i < RegCount) begin
          reg_file[isolde_rf_waddr_a_i] <= isolde_rf_wdata_a_i;
          isolde_rf_err_write_o <= 1'b0;
        end else begin
          // Error: write address out of range
          isolde_rf_err_write_o <= 1'b1;
        end
      end else begin
        isolde_rf_err_write_o <= 1'b0;
      end
    end
  end

  // Register Read Process (Combinational logic)
  always_comb begin
    if (isolde_rf_raddr_a_i < RegCount) begin
      isolde_rf_rdata_a_o  = reg_file[isolde_rf_raddr_a_i];  // Read data from the selected register
      isolde_rf_err_read_o = 1'b0;
    end else begin
      isolde_rf_rdata_a_o  = '0;  // Default output if address is out of range
      isolde_rf_err_read_o = 1'b1;
    end
  end

  // Combine read and write error signals
  assign isolde_rf_err_o = isolde_rf_err_write_o | isolde_rf_err_read_o;

endmodule
