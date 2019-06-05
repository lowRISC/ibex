// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Matthias Baer - baermatt@student.ethz.ch                   //
//                                                                            //
// Additional contributions by:                                               //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Markus Wegmann - markus.wegmann@technokrat.ch              //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    Top level module                                           //
// Project Name:   ibex                                                       //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Top level module of the RISC-V core.                       //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

`ifdef RISCV_FORMAL
  `define RVFI
`endif

/**
 * Top level module of the ibex RISC-V core
 */
module ibex_core #(
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

  // IF/ID signals
  logic        instr_valid_id;
  logic [31:0] instr_rdata_id;    // Instruction sampled inside IF stage
  logic        is_compressed_id;
  logic        illegal_c_insn_id; // Illegal compressed instruction sent to ID stage
  logic        illegal_insn_id;   // ID stage sees an illegal instruction
  logic [31:0] pc_if;             // Program counter in IF stage
  logic [31:0] pc_id;             // Program counter in ID stage

  logic        clear_instr_valid;
  logic        pc_set;
  pc_sel_e     pc_mux_id;         // Mux selector for next PC
  exc_pc_sel_e exc_pc_mux_id;     // Mux selector for exception PC
  exc_cause_e  exc_cause;         // Exception cause + IRQ ID for vectorized interrupt lines

  logic        lsu_load_err;
  logic        lsu_store_err;

  // ID performance counter signals
  logic        is_decoding;

  logic        data_misaligned;
  logic [31:0] misaligned_addr;

  // Jump and branch target and decision (EX->IF)
  logic [31:0] jump_target_ex;
  logic        branch_decision;

  logic        ctrl_busy;
  logic        if_busy;
  logic        lsu_busy;
  //core busy signals
  logic        core_busy;
  logic        core_ctrl_firstfetch, core_busy_int, core_busy_q;

  // ALU Control
  alu_op_e     alu_operator_ex;
  logic [31:0] alu_operand_a_ex;
  logic [31:0] alu_operand_b_ex;

  logic [31:0] alu_adder_result_ex; // Used to forward computed address to LSU
  logic [31:0] regfile_wdata_ex;

  // Multiplier Control
  logic        mult_en_ex;
  logic        div_en_ex;
  md_op_e      multdiv_operator_ex;
  logic [1:0]  multdiv_signed_mode_ex;
  logic [31:0] multdiv_operand_a_ex;
  logic [31:0] multdiv_operand_b_ex;

  // CSR control
  logic        csr_access_ex;
  csr_op_e     csr_op_ex;

  logic        csr_access;
  csr_op_e     csr_op;
  csr_num_e    csr_addr;
  logic [31:0] csr_rdata;
  logic [31:0] csr_wdata;
  logic        illegal_csr_insn_id; // CSR access to non-existent register,
                                    // with wrong priviledge level, or missing write permissions

  // Data Memory Control
  logic        data_we_ex;
  logic [1:0]  data_type_ex;
  logic        data_sign_ext_ex;
  logic [1:0]  data_reg_offset_ex;
  logic        data_req_ex;
  logic [31:0] data_wdata_ex;
  logic [31:0] regfile_wdata_lsu;

  // stall control
  logic        halt_if;
  logic        id_ready;
  logic        ex_ready;

  logic        if_valid;
  logic        id_valid;

  logic        data_valid_lsu;

  // Signals between instruction core interface and pipe (if and id stages)
  logic        instr_req_int;    // Id stage asserts a req to instruction core interface

  // Interrupts
  logic        m_irq_enable;
  logic [31:0] mepc, depc;

  logic        csr_save_cause;
  logic        csr_save_if;
  logic        csr_save_id;
  exc_cause_e  csr_cause;
  logic        csr_restore_mret_id;
  logic        csr_restore_dret_id;

  // debug mode and dcsr configuration
  dbg_cause_e  debug_cause;
  logic        debug_csr_save;
  logic        debug_single_step;
  logic        debug_ebreakm;

  // performance counter related signals
  logic        insn_ret;
  logic        perf_imiss;
  logic        perf_jump;
  logic        perf_branch;
  logic        perf_tbranch;
  logic        perf_load;
  logic        perf_store;

  // RISC-V Formal Interface signals
`ifdef RVFI
  logic [31:0] rvfi_insn_opcode;
  logic [15:0] compressed_instr;
  logic        rvfi_valid_int;
  logic [4:0]  rvfi_rs1_addr_id;
  logic [4:0]  rvfi_rs2_addr_id;
  logic [31:0] rvfi_rs1_data_d;
  logic [31:0] rvfi_rs1_data_id;
  logic [31:0] rvfi_rs1_data_q;
  logic [31:0] rvfi_rs2_data_d;
  logic [31:0] rvfi_rs2_data_id;
  logic [31:0] rvfi_rs2_data_q;
  logic [4:0]  rvfi_rd_addr_id;
  logic [4:0]  rvfi_rd_addr_q;
  logic [4:0]  rvfi_rd_addr_d;
  logic [31:0] rvfi_rd_wdata_id;
  logic [31:0] rvfi_rd_wdata_d;
  logic [31:0] rvfi_rd_wdata_q;
  logic        rvfi_rd_we_id;
  logic        rvfi_insn_new_d;
  logic        rvfi_insn_new_q;
  logic        rvfi_insn_clear_d;
  logic        rvfi_insn_clear_q;
  logic        rvfi_changed_insn;
  logic        rvfi_changed_pc;
  logic [31:0] rvfi_pc_id_q;
  logic [3:0]  rvfi_mem_mask_int;
  logic [31:0] rvfi_mem_rdata_d;
  logic [31:0] rvfi_mem_rdata_q;
  logic [31:0] rvfi_mem_wdata_d;
  logic [31:0] rvfi_mem_wdata_q;
  logic [31:0] rvfi_mem_addr_d;
  logic [31:0] rvfi_mem_addr_q;
`endif

  //////////////////////
  // Clock management //
  //////////////////////

  logic        clk;

  logic        clock_en;

  // if we are sleeping on a barrier let's just wait on the instruction
  // interface to finish loading instructions
  assign core_busy_int = if_busy | ctrl_busy | lsu_busy;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      core_busy_q <= 1'b0;
    end else begin
      core_busy_q <= core_busy_int;
    end
  end

  assign core_busy   = core_ctrl_firstfetch ? 1'b1 : core_busy_q;

  assign clock_en    = core_busy | irq_i | debug_req_i;

  // main clock gate of the core
  // generates all clocks except the one for the debug unit which is
  // independent
  prim_clock_gating core_clock_gate_i (
      .clk_i     ( clk_i           ),
      .en_i      ( clock_en        ),
      .test_en_i ( test_en_i       ),
      .clk_o     ( clk             )
  );

  //////////////
  // IF stage //
  //////////////

  ibex_if_stage #(
      .DmHaltAddr       ( DmHaltAddr      ),
      .DmExceptionAddr  ( DmExceptionAddr )
  ) if_stage_i (
      .clk_i                    ( clk               ),
      .rst_ni                   ( rst_ni            ),

      // boot address (trap vector location)
      .boot_addr_i              ( boot_addr_i       ),

      // instruction request control
      .req_i                    ( instr_req_int     ),

      // instruction cache interface
      .instr_req_o              ( instr_req_o       ),
      .instr_addr_o             ( instr_addr_o      ),
      .instr_gnt_i              ( instr_gnt_i       ),
      .instr_rvalid_i           ( instr_rvalid_i    ),
      .instr_rdata_i            ( instr_rdata_i     ),

      // outputs to ID stage
      .instr_valid_id_o         ( instr_valid_id    ),
      .instr_rdata_id_o         ( instr_rdata_id    ),
      .is_compressed_id_o       ( is_compressed_id  ),
`ifdef RVFI
      .instr_rdata_compressed_o ( compressed_instr  ),
`endif
      .illegal_c_insn_id_o      ( illegal_c_insn_id ),
      .pc_if_o                  ( pc_if             ),
      .pc_id_o                  ( pc_id             ),

      // control signals
      .clear_instr_valid_i      ( clear_instr_valid ),
      .pc_set_i                 ( pc_set            ),
      .exception_pc_reg_i       ( mepc              ), // exception return address
      .depc_i                   ( depc              ), // debug return address
      .pc_mux_i                 ( pc_mux_id         ), // sel for pc multiplexer
      .exc_pc_mux_i             ( exc_pc_mux_id     ),
      .exc_vec_pc_mux_i         ( exc_cause         ),

      // Jump targets
      .jump_target_ex_i         ( jump_target_ex    ),

      // pipeline stalls
      .halt_if_i                ( halt_if           ),
      .id_ready_i               ( id_ready          ),
      .if_valid_o               ( if_valid          ),

      .if_busy_o                ( if_busy           ),
      .perf_imiss_o             ( perf_imiss        )
  );


  //////////////
  // ID stage //
  //////////////

  ibex_id_stage #(
      .RV32E ( RV32E ),
      .RV32M ( RV32M )
  ) id_stage_i (
      .clk_i                        ( clk                  ),
      .rst_ni                       ( rst_ni               ),

      .test_en_i                    ( test_en_i            ),

      // Processor Enable
      .fetch_enable_i               ( fetch_enable_i       ),
      .ctrl_busy_o                  ( ctrl_busy            ),
      .core_ctrl_firstfetch_o       ( core_ctrl_firstfetch ),
      .is_decoding_o                ( is_decoding          ),
      .illegal_insn_o               ( illegal_insn_id      ),

      // Interface to instruction memory
      .instr_valid_i                ( instr_valid_id       ),
      .instr_rdata_i                ( instr_rdata_id       ),
      .instr_req_o                  ( instr_req_int        ),

      // Jumps and branches
      .branch_decision_i            ( branch_decision      ),

      // IF and ID control signals
      .clear_instr_valid_o          ( clear_instr_valid    ),
      .pc_set_o                     ( pc_set               ),
      .pc_mux_o                     ( pc_mux_id            ),
      .exc_pc_mux_o                 ( exc_pc_mux_id        ),
      .exc_cause_o                  ( exc_cause            ),

      .illegal_c_insn_i             ( illegal_c_insn_id    ),
      .is_compressed_i              ( is_compressed_id     ),

      .pc_id_i                      ( pc_id                ),

      // Stalls
      .halt_if_o                    ( halt_if              ),

      .id_ready_o                   ( id_ready             ),
      .ex_ready_i                   ( ex_ready             ),

      .id_valid_o                   ( id_valid             ),

      .alu_operator_ex_o            ( alu_operator_ex      ),
      .alu_operand_a_ex_o           ( alu_operand_a_ex     ),
      .alu_operand_b_ex_o           ( alu_operand_b_ex     ),

      .mult_en_ex_o                 ( mult_en_ex             ),
      .div_en_ex_o                  ( div_en_ex              ),
      .multdiv_operator_ex_o        ( multdiv_operator_ex    ),
      .multdiv_signed_mode_ex_o     ( multdiv_signed_mode_ex ),
      .multdiv_operand_a_ex_o       ( multdiv_operand_a_ex   ),
      .multdiv_operand_b_ex_o       ( multdiv_operand_b_ex   ),

      // CSR ID/EX
      .csr_access_ex_o              ( csr_access_ex        ),
      .csr_op_ex_o                  ( csr_op_ex            ),
      .csr_cause_o                  ( csr_cause            ),
      .csr_save_if_o                ( csr_save_if          ), // control signal to save pc
      .csr_save_id_o                ( csr_save_id          ), // control signal to save pc
      .csr_restore_mret_id_o        ( csr_restore_mret_id  ), // control signal to restore pc
      .csr_restore_dret_id_o        ( csr_restore_dret_id  ), // control signal to restore pc
      .csr_save_cause_o             ( csr_save_cause       ),
      .illegal_csr_insn_i           ( illegal_csr_insn_id  ),

      // LSU
      .data_req_ex_o                ( data_req_ex          ), // to load store unit
      .data_we_ex_o                 ( data_we_ex           ), // to load store unit
      .data_type_ex_o               ( data_type_ex         ), // to load store unit
      .data_sign_ext_ex_o           ( data_sign_ext_ex     ), // to load store unit
      .data_reg_offset_ex_o         ( data_reg_offset_ex   ), // to load store unit
      .data_wdata_ex_o              ( data_wdata_ex        ), // to load store unit

      .data_misaligned_i            ( data_misaligned      ),
      .misaligned_addr_i            ( misaligned_addr      ),

      .lsu_load_err_i               ( lsu_load_err         ),
      .lsu_store_err_i              ( lsu_store_err        ),

      // Interrupt Signals
      .irq_i                        ( irq_i                ), // incoming interrupts
      .irq_id_i                     ( irq_id_i             ),
      .m_irq_enable_i               ( m_irq_enable         ),
      .irq_ack_o                    ( irq_ack_o            ),
      .irq_id_o                     ( irq_id_o             ),

      // Debug Signal
      .debug_cause_o                ( debug_cause          ),
      .debug_csr_save_o             ( debug_csr_save       ),
      .debug_req_i                  ( debug_req_i          ),
      .debug_single_step_i          ( debug_single_step    ),
      .debug_ebreakm_i              ( debug_ebreakm        ),

      // write data to commit in the register file
      .regfile_wdata_lsu_i          ( regfile_wdata_lsu    ),
      .regfile_wdata_ex_i           ( regfile_wdata_ex     ),
      .csr_rdata_i                  ( csr_rdata            ),

`ifdef RVFI
      .rfvi_reg_raddr_ra_o          ( rvfi_rs1_addr_id     ),
      .rfvi_reg_rdata_ra_o          ( rvfi_rs1_data_id     ),
      .rfvi_reg_raddr_rb_o          ( rvfi_rs2_addr_id     ),
      .rfvi_reg_rdata_rb_o          ( rvfi_rs2_data_id     ),
      .rfvi_reg_waddr_rd_o          ( rvfi_rd_addr_id      ),
      .rfvi_reg_wdata_rd_o          ( rvfi_rd_wdata_id     ),
      .rfvi_reg_we_o                ( rvfi_rd_we_id        ),
`endif

      // Performance Counters
      .perf_jump_o                  ( perf_jump            ),
      .perf_branch_o                ( perf_branch          ),
      .perf_tbranch_o               ( perf_tbranch         )
  );


  ibex_ex_block #(
      .RV32M ( RV32M )
  ) ex_block_i (
      .clk_i                      ( clk                   ),
      .rst_ni                     ( rst_ni                ),
      // Alu signals from ID stage
      //TODO: hot encoding
      .alu_operator_i             ( alu_operator_ex       ),
      .multdiv_operator_i         ( multdiv_operator_ex   ),
      .alu_operand_a_i            ( alu_operand_a_ex      ),
      .alu_operand_b_i            ( alu_operand_b_ex      ),

      // Multipler
      .mult_en_i                  ( mult_en_ex            ),
      .div_en_i                   ( div_en_ex             ),
      .multdiv_signed_mode_i      ( multdiv_signed_mode_ex),
      .multdiv_operand_a_i        ( multdiv_operand_a_ex  ),
      .multdiv_operand_b_i        ( multdiv_operand_b_ex  ),
      .alu_adder_result_ex_o      ( alu_adder_result_ex   ), // from ALU to LSU
      .regfile_wdata_ex_o         ( regfile_wdata_ex      ),

      // To IF: Jump and branch target and decision
      .jump_target_o              ( jump_target_ex        ),
      .branch_decision_o          ( branch_decision       ),

      .lsu_en_i                   ( data_req_ex           ),
      .lsu_ready_ex_i             ( data_valid_lsu        ),
      .ex_ready_o                 ( ex_ready              )
  );

  /////////////////////
  // Load/store unit //
  /////////////////////

  ibex_load_store_unit  load_store_unit_i (
      .clk_i                 ( clk                ),
      .rst_ni                ( rst_ni             ),

      //output to data memory
      .data_req_o            ( data_req_o         ),
      .data_gnt_i            ( data_gnt_i         ),
      .data_rvalid_i         ( data_rvalid_i      ),
      .data_err_i            ( data_err_i         ),

      .data_addr_o           ( data_addr_o        ),
      .data_we_o             ( data_we_o          ),
      .data_be_o             ( data_be_o          ),
      .data_wdata_o          ( data_wdata_o       ),
      .data_rdata_i          ( data_rdata_i       ),

      // signal from ex stage
      .data_we_ex_i          ( data_we_ex         ),
      .data_type_ex_i        ( data_type_ex       ),
      .data_wdata_ex_i       ( data_wdata_ex      ),
      .data_reg_offset_ex_i  ( data_reg_offset_ex ),
      .data_sign_ext_ex_i    ( data_sign_ext_ex   ),

      .data_rdata_ex_o       ( regfile_wdata_lsu  ),
      .data_req_ex_i         ( data_req_ex        ),

      .adder_result_ex_i     ( alu_adder_result_ex),

      .data_misaligned_o     ( data_misaligned    ),
      .misaligned_addr_o     ( misaligned_addr    ),

      // exception signals
      .load_err_o            ( lsu_load_err       ),
      .store_err_o           ( lsu_store_err      ),

      // control signals
      .data_valid_o          ( data_valid_lsu     ),
      .lsu_update_addr_o     (                    ),
      .busy_o                ( lsu_busy           )
  );


  /////////////////////////////////////////
  // CSRs (Control and Status Registers) //
  /////////////////////////////////////////

  assign csr_access = csr_access_ex;
  assign csr_wdata  = alu_operand_a_ex;
  assign csr_op     = csr_op_ex;
  assign csr_addr   = csr_num_e'(csr_access_ex ? alu_operand_b_ex[11:0] : 12'b0);

  assign perf_load  = data_req_o & data_gnt_i & (~data_we_o);
  assign perf_store = data_req_o & data_gnt_i & data_we_o;

  // An instruction has been executed and retired if the ID stage gets a new instruction and
  // the previously seen instruction was valid.
  assign insn_ret   = if_valid & ~illegal_insn_id;

  ibex_cs_registers #(
      .MHPMCounterNum   ( MHPMCounterNum   ),
      .MHPMCounterWidth ( MHPMCounterWidth ),
      .RV32E            ( RV32E            ),
      .RV32M            ( RV32M            )
  ) cs_registers_i (
      .clk_i                   ( clk                 ),
      .rst_ni                  ( rst_ni              ),

      // Core and Cluster ID from outside
      .core_id_i               ( core_id_i           ),
      .cluster_id_i            ( cluster_id_i        ),
      // boot address
      .boot_addr_i             ( boot_addr_i         ),
      // Interface to CSRs (SRAM like)
      .csr_access_i            ( csr_access          ),
      .csr_addr_i              ( csr_addr            ),
      .csr_wdata_i             ( csr_wdata           ),
      .csr_op_i                ( csr_op              ),
      .csr_rdata_o             ( csr_rdata           ),

      // Interrupt related control signals
      .m_irq_enable_o          ( m_irq_enable        ),
      .mepc_o                  ( mepc                ),

      // debug
      .debug_cause_i           ( debug_cause         ),
      .debug_csr_save_i        ( debug_csr_save      ),
      .depc_o                  ( depc                ),
      .debug_single_step_o     ( debug_single_step   ),
      .debug_ebreakm_o         ( debug_ebreakm       ),

      .pc_if_i                 ( pc_if               ),
      .pc_id_i                 ( pc_id               ),

      .csr_save_if_i           ( csr_save_if         ),
      .csr_save_id_i           ( csr_save_id         ),
      .csr_restore_mret_i      ( csr_restore_mret_id ),
      .csr_restore_dret_i      ( csr_restore_dret_id ),
      .csr_cause_i             ( csr_cause           ),
      .csr_save_cause_i        ( csr_save_cause      ),
      .illegal_csr_insn_o      ( illegal_csr_insn_id ),

      // performance counter related signals
      .insn_ret_i              ( insn_ret            ),
      .id_valid_i              ( id_valid            ),
      .is_compressed_i         ( is_compressed_id    ),
      .is_decoding_i           ( is_decoding         ),

      .imiss_i                 ( perf_imiss          ),
      .pc_set_i                ( pc_set              ),
      .jump_i                  ( perf_jump           ),
      .branch_i                ( perf_branch         ),
      .branch_taken_i          ( perf_tbranch        ),
      .mem_load_i              ( perf_load           ),
      .mem_store_i             ( perf_store          ),
      .lsu_busy_i              ( lsu_busy            )
  );

`ifdef RVFI
  always_ff @(posedge clk) begin
    rvfi_halt      <= '0;
    rvfi_trap      <= '0;
    rvfi_intr      <= irq_ack_o;
    rvfi_order     <= rst_ni ? rvfi_order + rvfi_valid : '0;
    rvfi_insn      <= rvfi_insn_opcode;
    rvfi_mode      <= PRIV_LVL_M;
    rvfi_rs1_addr  <= rvfi_rs1_addr_id;
    rvfi_rs2_addr  <= rvfi_rs2_addr_id;
    rvfi_pc_rdata  <= pc_id;
    rvfi_mem_rmask <= rvfi_mem_mask_int;
    rvfi_mem_wmask <= data_we_o ? rvfi_mem_mask_int : 4'b0000;
    rvfi_valid     <= rvfi_valid_int;
    rvfi_rs1_rdata <= rvfi_rs1_data_d;
    rvfi_rs2_rdata <= rvfi_rs2_data_d;
  end

  assign rvfi_pc_wdata  = pc_id;
  assign rvfi_rd_wdata  = rvfi_rd_wdata_q;
  assign rvfi_rd_addr   = rvfi_rd_addr_q;
  assign rvfi_mem_rdata = rvfi_mem_rdata_q;
  assign rvfi_mem_wdata = rvfi_mem_wdata_q;
  assign rvfi_mem_addr  = rvfi_mem_addr_q;

  // Keep the mem data stable for each instruction cycle
  always_comb begin
    if (rvfi_insn_new) begin
      rvfi_mem_addr_d  = alu_adder_result_ex;
      rvfi_mem_rdata_d = regfile_wdata_lsu;
      rvfi_mem_wdata_d = data_wdata_ex;
    end else begin
      rvfi_mem_addr_d  = rvfi_mem_addr_q;
      rvfi_mem_rdata_d = rvfi_mem_rdata_q;
      rvfi_mem_wdata_d = rvfi_mem_wdata_q;
    end
  end
  always_ff @(posedge clk) begin
    rvfi_mem_addr_q  <= rvfi_mem_addr_d;
    rvfi_mem_rdata_q <= rvfi_mem_rdata_d;
    rvfi_mem_wdata_q <= rvfi_mem_wdata_d;
  end
  // Byte enable based on data type
  always_comb begin
    unique case (data_type_ex)
      2'b00:   rvfi_mem_mask_int = 4'b1111;
      2'b01:   rvfi_mem_mask_int = 4'b0011;
      2'b10:   rvfi_mem_mask_int = 4'b0001;
      default: rvfi_mem_mask_int = 4'b0000;
    endcase
  end

  assign rvfi_valid_int = id_valid && if_valid && !illegal_c_insn_id;

  always_comb begin
    if (is_compressed_id) begin
      rvfi_insn_opcode = {16'b0, compressed_instr};
    end else begin
      rvfi_insn_opcode = instr_rdata_id;
    end
  end

  // Source register data are kept stable for each instruction cycle
  always_comb begin
    if (rvfi_insn_new_d) begin
      rvfi_rs1_data_d = rvfi_rs1_data_id;
      rvfi_rs2_data_d = rvfi_rs2_data_id;
    end else begin
      rvfi_rs1_data_d = rvfi_rs1_data_q;
      rvfi_rs2_data_d = rvfi_rs2_data_q;
    end
  end
  always_ff @(posedge clk) begin
    rvfi_rs1_data_q <= rvfi_rs1_data_d;
    rvfi_rs2_data_q <= rvfi_rs2_data_d;
  end

  // RD write register is refreshed only once per cycle and
  // then it is kept stable for the cycle.
  always_comb begin
    if (rvfi_insn_new_d) begin
      if (rvfi_rd_we_id) begin
        rvfi_rd_addr_d    = '0;
        rvfi_rd_wdata_d   = '0;
        rvfi_insn_clear_d = 1'b0;
      end else begin
        rvfi_rd_addr_d = rvfi_rd_addr_id;
        if (!rvfi_rd_addr_id) begin
          rvfi_rd_wdata_d = '0;
        end else begin
          rvfi_rd_wdata_d = rvfi_rd_wdata_id;
        end
        rvfi_insn_clear_d = 1'b1;
      end
    end else begin
      rvfi_rd_addr_d    = rvfi_rd_addr_q;
      rvfi_rd_wdata_d   = rvfi_rd_wdata_q;
      rvfi_insn_clear_d = 1'b0;
    end
  end
  always_ff @(posedge clk) begin
    rvfi_insn_clear_q <= rvfi_insn_clear_d;
    rvfi_rd_addr_q    <= rvfi_rd_addr_d;
    rvfi_rd_wdata_q   <= rvfi_rd_wdata_d;
  end

  // New instruction signalling based on changes of
  // instruction data, program counter and valid signal
  always_comb begin
    if (rvfi_changed_insn || rvfi_changed_pc || rvfi_valid ) begin
      rvfi_insn_new_d = 1'b1;
    end else if (rvfi_insn_clear_q) begin
      rvfi_insn_new_d = 1'b0;
    end else begin
      rvfi_insn_new_d = rvfi_insn_new_q;
    end
  end
  always_ff @(posedge clk) begin
    rvfi_insn_new_q <= rvfi_insn_new_d;
  end

  // Change in instruction code
  assign rvfi_changed_insn = rvfi_insn != rvfi_insn_opcode;

  // Change in program counter
  always_ff @(posedge clk) begin
    rvfi_pc_id_q <= pc_id;
  end
  assign rvfi_changed_pc = rvfi_pc_id_q != pc_id;
`endif


`ifndef VERILATOR
`ifdef TRACE_EXECUTION
  ibex_tracer ibex_tracer_i (
      .clk_i            ( clk_i                                ), // always-on clk for tracer
      .rst_ni           ( rst_ni                               ),

      .fetch_enable_i   ( fetch_enable_i                       ),
      .core_id_i        ( core_id_i                            ),
      .cluster_id_i     ( cluster_id_i                         ),

      .pc_i             ( id_stage_i.pc_id_i                   ),
      .instr_i          ( id_stage_i.instr                     ),
      .compressed_i     ( id_stage_i.is_compressed_i           ),
      .id_valid_i       ( id_stage_i.id_valid_o                ),
      .is_decoding_i    ( id_stage_i.is_decoding_o             ),
      .is_branch_i      ( id_stage_i.branch_in_id              ),
      .branch_taken_i   ( id_stage_i.branch_set_q              ),
      .pipe_flush_i     ( id_stage_i.controller_i.pipe_flush_i ),
      .mret_insn_i      ( id_stage_i.controller_i.mret_insn_i  ),
      .dret_insn_i      ( id_stage_i.controller_i.dret_insn_i  ),
      .ecall_insn_i     ( id_stage_i.controller_i.ecall_insn_i ),
      .ebrk_insn_i      ( id_stage_i.controller_i.ebrk_insn_i  ),
      .csr_status_i     ( id_stage_i.controller_i.csr_status_i ),
      .rs1_value_i      ( id_stage_i.operand_a_fw_id           ),
      .rs2_value_i      ( id_stage_i.operand_b_fw_id           ),

      .lsu_value_i      ( data_wdata_ex                        ),

      .ex_reg_addr_i    ( id_stage_i.regfile_waddr_mux         ),
      .ex_reg_we_i      ( id_stage_i.regfile_we_mux            ),
      .ex_reg_wdata_i   ( id_stage_i.regfile_wdata_mux         ),
      .data_valid_lsu_i ( data_valid_lsu                       ),
      .ex_data_addr_i   ( data_addr_o                          ),
      .ex_data_req_i    ( data_req_o                           ),
      .ex_data_gnt_i    ( data_gnt_i                           ),
      .ex_data_we_i     ( data_we_o                            ),

      .ex_data_wdata_i  ( data_wdata_o                         ),

      .lsu_reg_wdata_i  ( regfile_wdata_lsu                    ),

      .imm_i_type_i     ( id_stage_i.imm_i_type                ),
      .imm_s_type_i     ( id_stage_i.imm_s_type                ),
      .imm_b_type_i     ( id_stage_i.imm_b_type                ),
      .imm_u_type_i     ( id_stage_i.imm_u_type                ),
      .imm_j_type_i     ( id_stage_i.imm_j_type                ),
      .zimm_rs1_type_i  ( id_stage_i.zimm_rs1_type             )
  );
`endif
`endif

endmodule
