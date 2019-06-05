// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Renzo Andri - andrire@student.ethz.ch                      //
//                                                                            //
// Additional contributions by:                                               //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    Instruction Decode Stage                                   //
// Project Name:   ibex                                                       //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Decode stage of the core. It decodes the instructions      //
//                 and hosts the register file.                               //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

// Source/Destination register instruction index
`define REG_S1 19:15
`define REG_S2 24:20
`define REG_D  11:07
`ifdef RISCV_FORMAL
  `define RVFI
`endif


/**
 * Instruction Decode Stage
 *
 * Decode stage of the core. It decodes the instructions and hosts the register
 * file.
 */
module ibex_id_stage #(
    parameter bit RV32E = 0,
    parameter bit RV32M = 1
) (
    input  logic                      clk_i,
    input  logic                      rst_ni,

    input  logic                      test_en_i,

    input  logic                      fetch_enable_i,
    output logic                      ctrl_busy_o,
    output logic                      core_ctrl_firstfetch_o,
    output logic                      is_decoding_o,
    output logic                      illegal_insn_o,

    // Interface to IF stage
    input  logic                      instr_valid_i,
    input  logic [31:0]               instr_rdata_i, // comes from pipeline of IF stage
    output logic                      instr_req_o,

    // Jumps and branches
    input  logic                      branch_decision_i,

    // IF and ID stage signals
    output logic                      clear_instr_valid_o,
    output logic                      pc_set_o,
    output ibex_defines::pc_sel_e     pc_mux_o,
    output ibex_defines::exc_pc_sel_e exc_pc_mux_o,

    input  logic                      illegal_c_insn_i,
    input  logic                      is_compressed_i,

    input  logic [31:0]               pc_id_i,

    // Stalls
    output logic                      halt_if_o,  // controller requests a halt of the IF stage
    output logic                      id_ready_o, // ID stage is ready for the next instruction
    input  logic                      ex_ready_i,
    output logic                      id_valid_o, // ID stage is done

    // ALU
    output ibex_defines::alu_op_e     alu_operator_ex_o,
    output logic [31:0]               alu_operand_a_ex_o,
    output logic [31:0]               alu_operand_b_ex_o,

    // MUL, DIV
    output logic                      mult_en_ex_o,
    output logic                      div_en_ex_o,
    output ibex_defines::md_op_e      multdiv_operator_ex_o,
    output logic  [1:0]               multdiv_signed_mode_ex_o,
    output logic [31:0]               multdiv_operand_a_ex_o,
    output logic [31:0]               multdiv_operand_b_ex_o,

    // CSR
    output logic                      csr_access_ex_o,
    output ibex_defines::csr_op_e     csr_op_ex_o,
    output ibex_defines::exc_cause_e  csr_cause_o,
    output logic                      csr_save_if_o,
    output logic                      csr_save_id_o,
    output logic                      csr_restore_mret_id_o,
    output logic                      csr_restore_dret_id_o,
    output logic                      csr_save_cause_o,
    input  logic                      illegal_csr_insn_i,

    // Interface to load store unit
    output logic                      data_req_ex_o,
    output logic                      data_we_ex_o,
    output logic [1:0]                data_type_ex_o,
    output logic                      data_sign_ext_ex_o,
    output logic [1:0]                data_reg_offset_ex_o,
    output logic [31:0]               data_wdata_ex_o,

    input  logic                      data_misaligned_i,
    input  logic [31:0]               misaligned_addr_i,

    // Interrupt signals
    input  logic                      irq_i,
    input  logic [4:0]                irq_id_i,
    input  logic                      m_irq_enable_i,
    output logic                      irq_ack_o,
    output logic [4:0]                irq_id_o,
    output ibex_defines::exc_cause_e  exc_cause_o,

    input  logic                      lsu_load_err_i,
    input  logic                      lsu_store_err_i,

    // Debug Signal
    output ibex_defines::dbg_cause_e  debug_cause_o,
    output logic                      debug_csr_save_o,
    input  logic                      debug_req_i,
    input  logic                      debug_single_step_i,
    input  logic                      debug_ebreakm_i,

    // Write back signal
    input  logic [31:0]               regfile_wdata_lsu_i,
    input  logic [31:0]               regfile_wdata_ex_i,
    input  logic [31:0]               csr_rdata_i,

`ifdef RVFI
    output logic [4:0]                rfvi_reg_raddr_ra_o,
    output logic [31:0]               rfvi_reg_rdata_ra_o,
    output logic [4:0]                rfvi_reg_raddr_rb_o,
    output logic [31:0]               rfvi_reg_rdata_rb_o,
    output logic [4:0]                rfvi_reg_waddr_rd_o,
    output logic [31:0]               rfvi_reg_wdata_rd_o,
    output logic                      rfvi_reg_we_o,
`endif

    // Performance Counters
    output logic                      perf_jump_o,    // executing a jump instr
    output logic                      perf_branch_o,  // executing a branch instr
    output logic                      perf_tbranch_o  // executing a taken branch instr
);

  import ibex_defines::*;

  logic [31:0] instr;

  // Decoder/Controller ID stage internal signals
  logic        deassert_we;

  logic        illegal_insn_dec;
  logic        illegal_reg_rv32e;
  logic        ebrk_insn;
  logic        mret_insn_dec;
  logic        dret_insn_dec;
  logic        ecall_insn_dec;
  logic        pipe_flush_dec;

  logic        branch_in_id;
  logic        branch_set_n;
  logic        branch_set_q;
  logic        branch_mux_dec;
  logic        jump_set;
  logic        jump_mux_dec;
  logic        jump_in_id;

  logic        instr_multicyle;
  logic        load_stall;
  logic        multdiv_stall;
  logic        branch_stall;
  logic        jump_stall;

  logic        halt_id;
  //FSM signals to write back multi cycles instructions
  logic        regfile_we;

  typedef enum logic {RF_LSU, RF_EX} select_e;
  select_e select_data_rf;

  // Immediate decoding and sign extension
  logic [31:0] imm_i_type;
  logic [31:0] imm_s_type;
  logic [31:0] imm_b_type;
  logic [31:0] imm_u_type;
  logic [31:0] imm_j_type;
  logic [31:0] zimm_rs1_type;

  logic [31:0] imm_a;       // contains the immediate for operand b
  logic [31:0] imm_b;       // contains the immediate for operand b

  // Signals running between controller and exception controller
  logic       irq_req_ctrl;
  logic [4:0] irq_id_ctrl;
  logic       exc_ack, exc_kill;// handshake

  // Register file interface
  logic [4:0]  regfile_addr_ra_id;
  logic [4:0]  regfile_addr_rb_id;

  logic [4:0]  regfile_alu_waddr_id;
  logic        regfile_we_id;

  logic [31:0] regfile_data_ra_id;
  logic [31:0] regfile_data_rb_id;

  // ALU Control
  alu_op_e     alu_operator;
  op_a_sel_e   alu_op_a_mux_sel;
  op_b_sel_e   alu_op_b_mux_sel;

  imm_a_sel_e  imm_a_mux_sel;
  imm_b_sel_e  imm_b_mux_sel;

  // Multiplier Control
  logic        mult_int_en;      // use integer multiplier
  logic        div_int_en;      // use integer division or reminder
  logic        multdiv_int_en;
  md_op_e      multdiv_operator;
  logic [1:0]  multdiv_signed_mode;

  // Data Memory Control
  logic        data_we_id;
  logic [1:0]  data_type_id;
  logic        data_sign_ext_id;
  logic [1:0]  data_reg_offset_id;
  logic        data_req_id;

  // CSR control
  logic        csr_access;
  csr_op_e     csr_op;
  logic        csr_status;

  // Forwarding
  op_fw_sel_e  operand_a_fw_mux_sel;

  logic [31:0] operand_a_fw_id;
  logic [31:0] operand_b_fw_id;

  logic [31:0] alu_operand_a;
  logic [31:0] alu_operand_b;

  assign instr = instr_rdata_i;

  // immediate extraction and sign extension
  assign imm_i_type = { {20 {instr[31]}}, instr[31:20] };
  assign imm_s_type = { {20 {instr[31]}}, instr[31:25], instr[11:7] };
  assign imm_b_type = { {19 {instr[31]}}, instr[31], instr[7], instr[30:25], instr[11:8], 1'b0 };
  assign imm_u_type = { instr[31:12], 12'b0 };
  assign imm_j_type = { {12 {instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0 };

  // immediate for CSR manipulatin (zero extended)
  assign zimm_rs1_type = { 27'b0, instr[`REG_S1] };

  ///////////////////////////////
  // Source register selection //
  ///////////////////////////////
  assign regfile_addr_ra_id = instr[`REG_S1];
  assign regfile_addr_rb_id = instr[`REG_S2];

  ///////////////////////////
  // Destination registers //
  ///////////////////////////
  assign regfile_alu_waddr_id = instr[`REG_D];

  //if (RV32E)
  //  assign illegal_reg_rv32e = (regfile_addr_ra_id[4] |
  //                              regfile_addr_rb_id[4] |
  //                              regfile_alu_waddr_id[4]);
  //else
  assign illegal_reg_rv32e = 1'b0;

  // kill instruction in the IF/ID stage by setting the instr_valid_id control
  // signal to 0 for instructions that are done
  assign clear_instr_valid_o = id_ready_o | halt_id;

  ///////////////
  // Operand A //
  ///////////////

  // ALU_Op_a Mux
  always_comb begin : alu_operand_a_mux
    unique case (alu_op_a_mux_sel)
      OP_A_REGA_OR_FWD:  alu_operand_a = operand_a_fw_id;
      OP_A_CURRPC:       alu_operand_a = pc_id_i;
      OP_A_IMM:          alu_operand_a = imm_a;
      default:           alu_operand_a = 'X;
    endcase
  end

  assign imm_a = (imm_a_mux_sel == IMM_A_Z) ? zimm_rs1_type : '0;

  // Operand a forwarding mux used with LSU instructions
  assign operand_a_fw_id
      = (operand_a_fw_mux_sel == SEL_MISALIGNED) ? misaligned_addr_i : regfile_data_ra_id;

  ///////////////
  // Operand B //
  ///////////////

  // Immediate Mux for operand B
  always_comb begin : immediate_b_mux
    unique case (imm_b_mux_sel)
      IMM_B_I:      imm_b = imm_i_type;
      IMM_B_S:      imm_b = imm_s_type;
      IMM_B_B:      imm_b = imm_b_type;
      IMM_B_U:      imm_b = imm_u_type;
      IMM_B_J:      imm_b = imm_j_type;
      IMM_B_PCINCR: imm_b = (is_compressed_i && !data_misaligned_i) ? 32'h2 : 32'h4;
      default:      imm_b = imm_i_type;
    endcase
  end

  // ALU_Op_b Mux
  assign alu_operand_b = (alu_op_b_mux_sel == OP_B_IMM) ? imm_b : regfile_data_rb_id;
  assign operand_b_fw_id = regfile_data_rb_id;

  ///////////////
  // Registers //
  ///////////////

  logic [31:0] regfile_wdata_mux;
  logic        regfile_we_mux;
  logic  [4:0] regfile_waddr_mux;

  //TODO: add assertion
  // Register File mux
  always_comb begin
    regfile_we_mux      = regfile_we;
    regfile_waddr_mux   = regfile_alu_waddr_id;
    if (select_data_rf == RF_LSU) begin
      regfile_wdata_mux = regfile_wdata_lsu_i;
    end else if (csr_access) begin
      regfile_wdata_mux = csr_rdata_i;
    end else begin
      regfile_wdata_mux = regfile_wdata_ex_i;
    end
  end

  ibex_register_file #( .RV32E ( RV32E ) ) registers_i (
      .clk_i        ( clk_i              ),
      .rst_ni       ( rst_ni             ),

      .test_en_i    ( test_en_i          ),

      // Read port a
      .raddr_a_i    ( regfile_addr_ra_id ),
      .rdata_a_o    ( regfile_data_ra_id ),
      // Read port b
      .raddr_b_i    ( regfile_addr_rb_id ),
      .rdata_b_o    ( regfile_data_rb_id ),
      // write port
      .waddr_a_i    ( regfile_waddr_mux ),
      .wdata_a_i    ( regfile_wdata_mux ),
      .we_a_i       ( regfile_we_mux    )
  );

`ifdef RVFI
  assign rfvi_reg_raddr_ra_o = regfile_addr_ra_id;
  assign rfvi_reg_rdata_ra_o = regfile_data_ra_id;
  assign rfvi_reg_raddr_rb_o = regfile_addr_rb_id;
  assign rfvi_reg_rdata_rb_o = regfile_data_rb_id;
  assign rfvi_reg_waddr_rd_o = regfile_waddr_mux;
  assign rfvi_reg_wdata_rd_o = regfile_wdata_mux;
  assign rfvi_reg_we_o       = regfile_we;
`endif

  assign multdiv_int_en  = mult_int_en | div_int_en;

  /////////////
  // Decoder //
  /////////////

  ibex_decoder #( .RV32M ( RV32M ) ) decoder_i (
      // controller related signals
      .deassert_we_i                   ( deassert_we               ),
      .data_misaligned_i               ( data_misaligned_i         ),
      .branch_mux_i                    ( branch_mux_dec            ),
      .jump_mux_i                      ( jump_mux_dec              ),

      .illegal_insn_o                  ( illegal_insn_dec          ),
      .ebrk_insn_o                     ( ebrk_insn                 ),
      .mret_insn_o                     ( mret_insn_dec             ),
      .dret_insn_o                     ( dret_insn_dec             ),
      .ecall_insn_o                    ( ecall_insn_dec            ),
      .pipe_flush_o                    ( pipe_flush_dec            ),

      // from IF/ID pipeline
      .instr_rdata_i                   ( instr                     ),
      .illegal_c_insn_i                ( illegal_c_insn_i          ),

      // ALU signals
      .alu_operator_o                  ( alu_operator              ),
      .alu_op_a_mux_sel_o              ( alu_op_a_mux_sel          ),
      .alu_op_b_mux_sel_o              ( alu_op_b_mux_sel          ),

      .imm_a_mux_sel_o                 ( imm_a_mux_sel             ),
      .imm_b_mux_sel_o                 ( imm_b_mux_sel             ),

      .mult_int_en_o                   ( mult_int_en               ),
      .div_int_en_o                    ( div_int_en                ),
      .multdiv_operator_o              ( multdiv_operator          ),
      .multdiv_signed_mode_o           ( multdiv_signed_mode       ),
      // Register file control signals
      .regfile_we_o                    ( regfile_we_id             ),

      // CSR control signals
      .csr_access_o                    ( csr_access                ),
      .csr_op_o                        ( csr_op                    ),
      .csr_status_o                    ( csr_status                ),

      // Data bus interface
      .data_req_o                      ( data_req_id               ),
      .data_we_o                       ( data_we_id                ),
      .data_type_o                     ( data_type_id              ),
      .data_sign_extension_o           ( data_sign_ext_id          ),
      .data_reg_offset_o               ( data_reg_offset_id        ),

      // jump/branches
      .jump_in_id_o                    ( jump_in_id                ),
      .branch_in_id_o                  ( branch_in_id              )
  );


  ///////////////////////
  // CSR operand check //
  ///////////////////////
  always_comb begin : csr_operand_check
    csr_op_ex_o = csr_op;

    // CSRRSI/CSRRCI must not write 0 to CSRs (uimm[4:0]=='0)
    // CSRRS/CSRRC must not write from x0 to CSRs (rs1=='0)
    if ((csr_op == CSR_OP_SET || csr_op == CSR_OP_CLEAR) &&
        instr[`REG_S1] == '0) begin
      csr_op_ex_o = CSR_OP_READ;
    end
  end

  ////////////////
  // Controller //
  ////////////////
  assign illegal_insn_o = illegal_insn_dec | illegal_reg_rv32e | illegal_csr_insn_i;

  ibex_controller controller_i (
      .clk_i                          ( clk_i                  ),
      .rst_ni                         ( rst_ni                 ),

      .fetch_enable_i                 ( fetch_enable_i         ),
      .ctrl_busy_o                    ( ctrl_busy_o            ),
      .first_fetch_o                  ( core_ctrl_firstfetch_o ),
      .is_decoding_o                  ( is_decoding_o          ),

      // decoder related signals
      .deassert_we_o                  ( deassert_we            ),
      .illegal_insn_i                 ( illegal_insn_o         ),
      .ecall_insn_i                   ( ecall_insn_dec         ),
      .mret_insn_i                    ( mret_insn_dec          ),
      .dret_insn_i                    ( dret_insn_dec          ),
      .pipe_flush_i                   ( pipe_flush_dec         ),
      .ebrk_insn_i                    ( ebrk_insn              ),
      .csr_status_i                   ( csr_status             ),

      // from IF/ID pipeline
      .instr_valid_i                  ( instr_valid_i          ),

      // from prefetcher
      .instr_req_o                    ( instr_req_o            ),

      // to prefetcher
      .pc_set_o                       ( pc_set_o               ),
      .pc_mux_o                       ( pc_mux_o               ),
      .exc_pc_mux_o                   ( exc_pc_mux_o           ),
      .exc_cause_o                    ( exc_cause_o            ),

      // LSU
      .data_misaligned_i              ( data_misaligned_i      ),
      .load_err_i                     ( lsu_load_err_i         ),
      .store_err_i                    ( lsu_store_err_i        ),

      // jump/branch control
      .branch_in_id_i                 ( branch_in_id           ),
      .branch_set_i                   ( branch_set_q           ),
      .jump_set_i                     ( jump_set               ),

      .instr_multicyle_i              ( instr_multicyle        ),

      .irq_i                          ( irq_i                  ),
      // Interrupt Controller Signals
      .irq_req_ctrl_i                 ( irq_req_ctrl           ),
      .irq_id_ctrl_i                  ( irq_id_ctrl            ),
      .m_IE_i                         ( m_irq_enable_i         ),

      .irq_ack_o                      ( irq_ack_o              ),
      .irq_id_o                       ( irq_id_o               ),

      .exc_ack_o                      ( exc_ack                ),
      .exc_kill_o                     ( exc_kill               ),

      // CSR Controller Signals
      .csr_save_cause_o               ( csr_save_cause_o       ),
      .csr_cause_o                    ( csr_cause_o            ),
      .csr_save_if_o                  ( csr_save_if_o          ),
      .csr_save_id_o                  ( csr_save_id_o          ),
      .csr_restore_mret_id_o          ( csr_restore_mret_id_o  ),
      .csr_restore_dret_id_o          ( csr_restore_dret_id_o  ),

      // Debug Signal
      .debug_cause_o                  ( debug_cause_o          ),
      .debug_csr_save_o               ( debug_csr_save_o       ),
      .debug_req_i                    ( debug_req_i            ),
      .debug_single_step_i            ( debug_single_step_i    ),
      .debug_ebreakm_i                ( debug_ebreakm_i        ),

      // Forwarding signals
      .operand_a_fw_mux_sel_o         ( operand_a_fw_mux_sel   ),

      // Stall signals
      .halt_if_o                      ( halt_if_o              ),
      .halt_id_o                      ( halt_id                ),

      .id_ready_i                     ( id_ready_o             ),

      // Performance Counters
      .perf_jump_o                    ( perf_jump_o            ),
      .perf_tbranch_o                 ( perf_tbranch_o         )
  );

  //////////////////////////
  // Interrupt controller //
  //////////////////////////

  ibex_int_controller int_controller_i (
      .clk_i                ( clk_i              ),
      .rst_ni               ( rst_ni             ),

      // to controller
      .irq_req_ctrl_o       ( irq_req_ctrl       ),
      .irq_id_ctrl_o        ( irq_id_ctrl        ),

      .ctrl_ack_i           ( exc_ack            ),
      .ctrl_kill_i          ( exc_kill           ),

      // Interrupt signals
      .irq_i                ( irq_i              ),
      .irq_id_i             ( irq_id_i           ),

      .m_IE_i               ( m_irq_enable_i     )
  );

  ///////////
  // ID-EX //
  ///////////

  assign data_we_ex_o                = data_we_id;
  assign data_type_ex_o              = data_type_id;
  assign data_sign_ext_ex_o          = data_sign_ext_id;
  assign data_wdata_ex_o             = regfile_data_rb_id;
  assign data_req_ex_o               = data_req_id;
  assign data_reg_offset_ex_o        = data_reg_offset_id;

  assign alu_operator_ex_o           = alu_operator;
  assign alu_operand_a_ex_o          = alu_operand_a;
  assign alu_operand_b_ex_o          = alu_operand_b;

  assign csr_access_ex_o             = csr_access;

  assign mult_en_ex_o                = mult_int_en;
  assign div_en_ex_o                 = div_int_en;

  assign multdiv_operator_ex_o       = multdiv_operator;
  assign multdiv_signed_mode_ex_o    = multdiv_signed_mode;
  assign multdiv_operand_a_ex_o      = regfile_data_ra_id;
  assign multdiv_operand_b_ex_o      = regfile_data_rb_id;

  typedef enum logic { IDLE, WAIT_MULTICYCLE } id_fsm_e;
  id_fsm_e id_wb_fsm_cs, id_wb_fsm_ns;

  ////////////////////////////////
  // ID-EX/WB Pipeline Register //
  ////////////////////////////////
  always_ff @(posedge clk_i or negedge rst_ni) begin : id_wb_pipeline_reg
    if (!rst_ni) begin
      id_wb_fsm_cs  <= IDLE;
      branch_set_q  <= 1'b0;
    end else begin
      id_wb_fsm_cs  <= id_wb_fsm_ns;
      branch_set_q  <= branch_set_n;
    end
  end

  //////////////////
  // ID-EX/WB FSM //
  //////////////////
  always_comb begin : id_wb_fsm
    id_wb_fsm_ns    = id_wb_fsm_cs;
    regfile_we      = regfile_we_id;
    load_stall      = 1'b0;
    multdiv_stall   = 1'b0;
    jump_stall      = 1'b0;
    branch_stall    = 1'b0;
    select_data_rf  = RF_EX;
    instr_multicyle = 1'b0;
    branch_set_n    = 1'b0;
    branch_mux_dec  = 1'b0;
    jump_set        = 1'b0;
    jump_mux_dec    = 1'b0;
    perf_branch_o   = 1'b0;

    unique case (id_wb_fsm_cs)

      IDLE: begin
        jump_mux_dec   = 1'b1;
        branch_mux_dec = 1'b1;
        unique case (1'b1)
          data_req_id: begin
            //LSU operation
            regfile_we      = 1'b0;
            id_wb_fsm_ns    = WAIT_MULTICYCLE;
            load_stall      = 1'b1;
            instr_multicyle = 1'b1;
          end
          branch_in_id: begin
            //Cond Branch operation
            id_wb_fsm_ns    = branch_decision_i ? WAIT_MULTICYCLE : IDLE;
            branch_stall    = branch_decision_i;
            instr_multicyle = branch_decision_i;
            branch_set_n    = branch_decision_i;
            perf_branch_o   = 1'b1;
          end
          multdiv_int_en: begin
            //MUL or DIV operation
            regfile_we      = 1'b0;
            id_wb_fsm_ns    = WAIT_MULTICYCLE;
            multdiv_stall   = 1'b1;
            instr_multicyle = 1'b1;
          end
          jump_in_id: begin
            //UnCond Branch operation
            regfile_we      = 1'b0;
            id_wb_fsm_ns    = WAIT_MULTICYCLE;
            jump_stall      = 1'b1;
            instr_multicyle = 1'b1;
            jump_set        = 1'b1;
          end
          default:;
        endcase
      end

      WAIT_MULTICYCLE: begin
        if (ex_ready_i) begin
          regfile_we     = regfile_we_id;
          id_wb_fsm_ns   = IDLE;
          load_stall     = 1'b0;
          multdiv_stall  = 1'b0;
          select_data_rf = data_req_id ? RF_LSU : RF_EX;
        end else begin
          regfile_we      = 1'b0;
          instr_multicyle = 1'b1;
          unique case (1'b1)
            data_req_id:
              load_stall    = 1'b1;
            multdiv_int_en:
              multdiv_stall = 1'b1;
            default:;
          endcase
        end
      end

      default:;
    endcase
  end

  // stall control
  assign id_ready_o = ~load_stall & ~branch_stall & ~jump_stall & ~multdiv_stall;

  assign id_valid_o = ~halt_id & id_ready_o;

  ////////////////
  // Assertions //
  ////////////////
`ifndef VERILATOR
  // make sure that branch decision is valid when jumping
  assert property (
    @(posedge clk_i) (branch_decision_i !== 1'bx || branch_in_id == 1'b0) ) else
      $display("Branch decision is X");

`ifdef CHECK_MISALIGNED
  assert property (
    @(posedge clk_i) (~data_misaligned_i) ) else
      $display("Misaligned memory access at %x",pc_id_i);
`endif

  // the instruction delivered to the ID stage should always be valid
  assert property (
    @(posedge clk_i) (instr_valid_i & (~illegal_c_insn_i)) |-> (!$isunknown(instr_rdata_i)) ) else
      $display("Instruction is valid, but has at least one X");

  // make sure multicycles enable signals are unique
  assert property (
    @(posedge clk_i) ~(data_req_ex_o & multdiv_int_en )) else
      $display("Multicycles enable signals are not unique");

`endif

endmodule
