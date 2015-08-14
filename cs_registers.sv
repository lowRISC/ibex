////////////////////////////////////////////////////////////////////////////////
// Company:        IIS @ ETHZ - Federal Institute of Technology               //
//                                                                            //
// Engineer:       Sven Stucki - svstucki@student.ethz.ch.ch                  //
//                                                                            //
// Additional contributions by:                                               //
//                                                                            //
//                                                                            //
// Create Date:    25/05/2015                                                 //
// Design Name:    RISC-V processor core                                      //
// Module Name:    cs_registers.sv                                            //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Control and Status Registers (CSRs) loosely following the  //
//                 RiscV draft priviledged instruction set spec (v1.7)        //
//                                                                            //
//                                                                            //
// Revision:                                                                  //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

`include "defines.sv"


module cs_registers
(
  // Clock and Reset
  input logic         clk,
  input logic         rst_n,

  // Core and Cluster ID
  input logic   [4:0] core_id_i,
  input logic   [4:0] cluster_id_i,

  // Interface to special purpose registers (SRAM like)
  input logic  [11:0] csr_addr_i,
  input logic  [31:0] csr_wdata_i,
  input logic   [1:0] csr_op_i,
  output logic [31:0] csr_rdata_o,

  // Interrupts
  input logic  [31:0] curr_pc_if_i,
  input logic  [31:0] curr_pc_id_i,
  input logic         save_pc_if_i,
  input logic         save_pc_id_i, // TODO: check if both IF/ID pc save is needed
  output logic [31:0] epcr_o,

  // HWLoop Signals
  input  logic [`HWLOOP_REGS-1:0] [31:0] hwlp_start_addr_i,
  input  logic [`HWLOOP_REGS-1:0] [31:0] hwlp_end_addr_i,
  input  logic [`HWLOOP_REGS-1:0] [31:0] hwlp_counter_i,

  output  logic [31:0]                   hwlp_start_o,
  output  logic [31:0]                   hwlp_end_o,
  output  logic [31:0]                   hwlp_counter_o,
  output  logic [1:0]                    hwlp_regid_o,
  output  logic [2:0]                    hwlp_we_o
);


  logic is_constant;
  logic is_register;

  logic [31:0] constant_rdata_int;
  logic [31:0] register_rdata_int;

  logic is_readonly;
  logic illegal_address;

  // CSRs and index of CSR to access
  int csr_index; // TODO: check synthesis result
  logic [31:0] csr [0:`CSR_MAX_IDX];


  assign is_readonly = (csr_addr_i[11:10] == 2'b11);
  assign illegal_address = ~is_constant && ~is_register;


  // output mux
  always_comb
  begin
    csr_rdata_o = 32'bx;

    if (is_constant == 1'b1)
      csr_rdata_o = constant_rdata_int;
    else if (is_register == 1'b1)
      csr_rdata_o = register_rdata_int;
  end


  // address decoder for constant CSRs
  always_comb
  begin
    constant_rdata_int = '0;
    is_constant = 1'b1;
    unique case (csr_addr_i)
      12'hF00: constant_rdata_int = 32'h00_00_01_00;  // mcpuid: RV32I
      12'hF01: constant_rdata_int = 32'h00_00_80_00;  // mimpid: PULP3, anonymous source (no allocated ID)
      12'hF10: constant_rdata_int = {22'b0, cluster_id_i, core_id_i}; // mhartid: unique hardware thread id

      default: is_constant = 1'b0;
    endcase
  end

  // address decoder for regular CSRs
  always_comb
  begin
    csr_index = '0;
    is_register = 1'b1;
    unique case (csr_addr_i)
      12'h340: csr_index = `CSR_IDX_MSCRATCH;
      12'h341: csr_index = `CSR_IDX_MEPC;

      default: is_register = 1'b0;
    endcase
  end

  assign register_rdata_int = csr[csr_index];


  // directly output some registers
  assign epcr_o = csr[`CSR_IDX_MEPC];


  // actual registers
  always_ff @(posedge clk, negedge rst_n)
  begin
    if (rst_n == 1'b0)
    begin
      csr <= '{default: 32'b0}; // new SV syntax TODO: check synthesis result
    end
    else
    begin
      // write CSR through instruction
      if (is_readonly == 1'b0) begin
        unique case (csr_op_i)
          `CSR_OP_NONE:   ;
          `CSR_OP_WRITE:  csr[csr_index] <= csr_wdata_i;
          `CSR_OP_SET:    csr[csr_index] <= csr_wdata_i | register_rdata_int;
          `CSR_OP_CLEAR:  csr[csr_index] <= csr_wdata_i & ~(register_rdata_int);
        endcase
      end

      // writes from exception controller get priority

      // write exception PC
      if (save_pc_if_i == 1'b1)
        csr[`CSR_IDX_MEPC] <= curr_pc_if_i;
      else if (save_pc_id_i == 1'b1)
        csr[`CSR_IDX_MEPC] <= curr_pc_id_i;
    end
  end


  // synopsys translate_off
  // make sure decoding works correctly
  //assert property (!((is_constant == 1'b1) && (is_register == 1'b1))); // not supported by ModelSim :/
  // synopsys translate_on

endmodule
