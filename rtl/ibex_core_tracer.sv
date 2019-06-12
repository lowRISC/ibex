// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0


// ibex_tracer relies on the signals from the RISC-V Formal Interface
`define RVFI

/**
 * Top level module of the ibex RISC-V core with tracing enabled
 */
module ibex_core_tracer #(
    parameter int unsigned MHPMCounterNum   = 8,
    parameter int unsigned MHPMCounterWidth = 40,
    parameter bit RV32E                     = 0,
    parameter bit RV32M                     = 1,
    parameter int unsigned DmHaltAddr       = 32'h1A110800,
    parameter int unsigned DmExceptionAddr  = 32'h1A110808
) (
    // Clock and Reset
    input  logic        clk_i,
    input  logic        rst_ni,

    input  logic        test_en_i,     // enable all clock gates for testing

    // Core ID, Cluster ID and boot address are considered more or less static
    input  logic [ 3:0] core_id_i,
    input  logic [ 5:0] cluster_id_i,
    input  logic [31:0] boot_addr_i,

    // Instruction memory interface
    output logic        instr_req_o,
    input  logic        instr_gnt_i,
    input  logic        instr_rvalid_i,
    output logic [31:0] instr_addr_o,
    input  logic [31:0] instr_rdata_i,

    // Data memory interface
    output logic        data_req_o,
    input  logic        data_gnt_i,
    input  logic        data_rvalid_i,
    output logic        data_we_o,
    output logic [3:0]  data_be_o,
    output logic [31:0] data_addr_o,
    output logic [31:0] data_wdata_o,
    input  logic [31:0] data_rdata_i,
    input  logic        data_err_i,

    // Interrupt inputs
    input  logic        irq_i,                 // level sensitive IR lines
    input  logic [4:0]  irq_id_i,
    output logic        irq_ack_o,             // irq ack
    output logic [4:0]  irq_id_o,

    // Debug Interface
    input  logic        debug_req_i,

    // RISC-V Formal Interface
    // Does not comply with the coding standards of _i/_o suffixes, but follows
    // the convention of RISC-V Formal Interface Specification.
`ifdef RVFI
    output logic        rvfi_valid,
    output logic [63:0] rvfi_order,
    output logic [31:0] rvfi_insn,
    output logic        rvfi_trap,
    output logic        rvfi_halt,
    output logic        rvfi_intr,
    output logic [ 1:0] rvfi_mode,
    output logic [ 4:0] rvfi_rs1_addr,
    output logic [ 4:0] rvfi_rs2_addr,
    output logic [31:0] rvfi_rs1_rdata,
    output logic [31:0] rvfi_rs2_rdata,
    output logic [ 4:0] rvfi_rd_addr,
    output logic [31:0] rvfi_rd_wdata,
    output logic [31:0] rvfi_pc_rdata,
    output logic [31:0] rvfi_pc_wdata,
    output logic [31:0] rvfi_mem_addr,
    output logic [ 3:0] rvfi_mem_rmask,
    output logic [ 3:0] rvfi_mem_wmask,
    output logic [31:0] rvfi_mem_rdata,
    output logic [31:0] rvfi_mem_wdata,
`endif

    // CPU Control Signals
    input  logic        fetch_enable_i

);

  import ibex_defines::*;

  ibex_core #(
    .MHPMCounterNum(MHPMCounterNum),
    .MHPMCounterWidth(MHPMCounterWidth),
    .RV32E(RV32E),
    .RV32M(RV32M),
    .DmHaltAddr(DmHaltAddr),
    .DmExceptionAddr(DmExceptionAddr)
  ) u_ibex_core (
    .clk_i,
    .rst_ni,

    .test_en_i,

    .core_id_i,
    .cluster_id_i,
    .boot_addr_i,

    .instr_req_o,
    .instr_gnt_i,
    .instr_rvalid_i,
    .instr_addr_o,
    .instr_rdata_i,

    .data_req_o,
    .data_gnt_i,
    .data_rvalid_i,
    .data_we_o,
    .data_be_o,
    .data_addr_o,
    .data_wdata_o,
    .data_rdata_i,
    .data_err_i,

    .irq_i,
    .irq_id_i,
    .irq_ack_o,
    .irq_id_o,

    .debug_req_i,

`ifdef RVFI
    .rvfi_valid,
    .rvfi_order,
    .rvfi_insn,
    .rvfi_trap,
    .rvfi_halt,
    .rvfi_intr,
    .rvfi_mode,
    .rvfi_rs1_addr,
    .rvfi_rs2_addr,
    .rvfi_rs1_rdata,
    .rvfi_rs2_rdata,
    .rvfi_rd_addr,
    .rvfi_rd_wdata,
    .rvfi_pc_rdata,
    .rvfi_pc_wdata,
    .rvfi_mem_addr,
    .rvfi_mem_rmask,
    .rvfi_mem_wmask,
    .rvfi_mem_rdata,
    .rvfi_mem_wdata,
`endif

    .fetch_enable_i
  );


`ifndef VERILATOR
  ibex_tracer ibex_tracer_i (
      .clk_i            ( clk_i          ),
      .rst_ni           ( rst_ni         ),

      .fetch_enable_i   ( fetch_enable_i ),
      .core_id_i        ( core_id_i      ),
      .cluster_id_i     ( cluster_id_i   ),

      .valid_i          ( rvfi_valid     ),
      .pc_i             ( rvfi_pc_rdata  ),
      .instr_i          ( rvfi_insn      ),
      .rs1_value_i      ( rvfi_rs1_rdata ),
      .rs2_value_i      ( rvfi_rs2_rdata ),
      .ex_reg_addr_i    ( rvfi_rd_addr   ),
      .ex_reg_wdata_i   ( rvfi_rd_wdata  ),
      .ex_data_addr_i   ( rvfi_mem_addr  ),
      .ex_data_wdata_i  ( rvfi_mem_wdata ),
      .ex_data_rdata_i  ( rvfi_mem_rdata )
  );
`endif // VERILATOR

endmodule
