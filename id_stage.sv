// Copyright 2015 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the “License”); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Renzo Andri - andrire@student.ethz.ch                      //
//                                                                            //
// Additional contributions by:                                               //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                                                                            //
// Design Name:    Instruction Decode Stage                                   //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Decode stage of the core. It decodes the instructions      //
//                 and hosts the register file.                               //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

`include "riscv_config.sv"

import riscv_defines::*;


// CONFIG_REGION: RV32E
`ifdef RV32E
// Source/Destination register instruction index
`define REG_S1 18:15
`define REG_S2 23:20
`define REG_S3 28:25
`define REG_D  10:07
`else
// Source/Destination register instruction index
`define REG_S1 19:15
`define REG_S2 24:20
`define REG_S3 29:25
`define REG_D  11:07
`endif // RV32E


module riscv_id_stage
#(
  // CONFIG_REGION: RV32E
  `ifdef RV32E
  parameter REG_ADDR_WIDTH      = 4
  `else
  parameter REG_ADDR_WIDTH      = 5
  `endif // RV32E

  // CONFIG_REGION: HWLP_SUPPORT
  `ifdef HWLP_SUPPORT
  ,
  parameter N_HWLP      = 2,
  parameter N_HWLP_BITS = $clog2(N_HWLP)
  `endif // HWLP_SUPPORT
)
(
    input  logic        clk,
    input  logic        rst_n,

    input  logic        test_en_i,

    input  logic        fetch_enable_i,
    output logic        ctrl_busy_o,
    output logic        is_decoding_o,

    // Interface to IF stage
    // CONFIG_REGION: HWLP_SUPPORT
  	`ifdef HWLP_SUPPORT
    input  logic [N_HWLP-1:0] hwlp_dec_cnt_i,
    input  logic              is_hwlp_i,
    `endif // HWLP_SUPPORT
    input  logic              instr_valid_i,
    input  logic       [31:0] instr_rdata_i,      // comes from pipeline of IF stage
    output logic              instr_req_o,

    // Jumps and branches
    output logic        branch_in_ex_o,
    input  logic        branch_decision_i,
    // CONFIG_REGION: JUMP_IN_ID
    `ifdef JUMP_IN_ID
    output logic [31:0] jump_target_o,
    `endif // JUMP_IN_ID

    // IF and ID stage signals
    output logic        clear_instr_valid_o,
    output logic        pc_set_o,
    output logic [2:0]  pc_mux_o,
    output logic [1:0]  exc_pc_mux_o,
    output logic [4:0]  exc_vec_pc_mux_o,

    input  logic        illegal_c_insn_i,
    input  logic        is_compressed_i,

    input  logic [31:0] pc_if_i,
    input  logic [31:0] pc_id_i,

    // Stalls
    output logic        halt_if_o,      // controller requests a halt of the IF stage

    output logic        id_ready_o,     // ID stage is ready for the next instruction
    input  logic        ex_ready_i,     // EX stage is ready for the next instruction

    input  logic        if_ready_i,     // IF stage is done
    input  logic        if_valid_i,     // IF stage is done
    output logic        id_valid_o,     // ID stage is done
    input  logic        ex_valid_i,     // EX stage is done
    input  logic        wb_valid_i,     // WB stage is done

    // Pipeline ID/EX
    output logic [31:0] pc_ex_o,

    output logic [31:0] alu_operand_a_ex_o,
    output logic [31:0] alu_operand_b_ex_o,
    output logic [31:0] alu_operand_c_ex_o, // Still needed if 2r1w reg file used

    // CONFIG_REGION: BIT_SUPPORT
  	`ifdef BIT_SUPPORT
    output logic [ 4:0] bmask_a_ex_o,
    output logic [ 4:0] bmask_b_ex_o,
    `endif // BIT_SUPPORT

    // CONFIG_REGION: VEC_SUPPORT
  	`ifdef VEC_SUPPORT
    output logic [ 1:0] imm_vec_ext_ex_o,
    output logic [ 1:0] alu_vec_mode_ex_o,
    `endif // VEC_SUPPORT

    // CONFIG_REGION: THREE_PORT_REG_FILE
    `ifdef THREE_PORT_REG_FILE
    output logic [(REG_ADDR_WIDTH-1):0]  regfile_waddr_ex_o,
    `endif // THREE_PORT_REG_FILE
    output logic        regfile_we_ex_o,

    output logic [(REG_ADDR_WIDTH-1):0]  regfile_alu_waddr_ex_o,
    output logic        regfile_alu_we_ex_o,

    // ALU
    output logic [ALU_OP_WIDTH-1:0] alu_operator_ex_o,

    // CONFIG_REGION: MUL_SUPPORT
  	`ifdef MUL_SUPPORT
    // MUL
    output logic [ 2:0] mult_operator_ex_o,
    output logic [31:0] mult_operand_a_ex_o,
    output logic [31:0] mult_operand_b_ex_o,
    output logic [31:0] mult_operand_c_ex_o,
    output logic        mult_en_ex_o,
    output logic        mult_sel_subword_ex_o,
    output logic [ 1:0] mult_signed_mode_ex_o,
    output logic [ 4:0] mult_imm_ex_o,

    output logic [31:0] mult_dot_op_a_ex_o,
    output logic [31:0] mult_dot_op_b_ex_o,
    output logic [31:0] mult_dot_op_c_ex_o,
    output logic [ 1:0] mult_dot_signed_ex_o,
    `endif // MUL_SUPPORT

    // CONFIG_REGION: SPLITTED_ADDER
    `ifdef  SPLITTED_ADDER
    output logic        alu_req_ex_o,
    `endif

    // CSR ID/EX
    output logic        csr_access_ex_o,
    output logic [1:0]  csr_op_ex_o,

    // CONFIG_REGION: HWLP_SUPPORT
  	`ifdef HWLP_SUPPORT
    // hwloop signals
    output logic [N_HWLP-1:0] [31:0] hwlp_start_o,
    output logic [N_HWLP-1:0] [31:0] hwlp_end_o,
    output logic [N_HWLP-1:0] [31:0] hwlp_cnt_o,

    // hwloop signals from CS register
    input  logic   [N_HWLP_BITS-1:0] csr_hwlp_regid_i,
    input  logic               [2:0] csr_hwlp_we_i,
    input  logic              [31:0] csr_hwlp_data_i,
    `endif // HWLP_SUPPORT

    // Interface to load store unit
    output logic        data_req_ex_o,
    output logic        data_we_ex_o,
    output logic [1:0]  data_type_ex_o,
    output logic        data_sign_ext_ex_o,
    // CONFIG_REGION: ONLY_ALIGNED
    `ifndef ONLY_ALIGNED
    output logic [1:0]  data_reg_offset_ex_o,
    `endif // ONLY_ALIGNED
    output logic        data_load_event_ex_o,

    // CONFIG_REGION: ONLY_ALIGNED
    `ifndef ONLY_ALIGNED
    output logic        data_misaligned_ex_o,
    `endif // ONLY_ALIGNED

    // CONFIG_REGION: PREPOST_SUPPORT
    `ifdef PREPOST_SUPPORT
    output logic        prepost_useincr_ex_o,
    `endif // PREPOST_SUPPORT

    // CONFIG_REGION: ONLY_ALIGNED
    `ifndef ONLY_ALIGNED
    input  logic        data_misaligned_i,
    // CONFIG_REGION: MERGE_ID_EX
    `ifdef MERGE_ID_EX
    input  logic        misaligned_addr_i,
    `endif
    `endif // ONLY_ALIGNED


    // Interrupt signals
    input  logic [31:0] irq_i,
    input  logic        irq_enable_i,

    output logic [5:0]  exc_cause_o,
    output logic        save_exc_cause_o,

    output logic        exc_save_if_o,
    output logic        exc_save_id_o,
    output logic        exc_save_takenbranch_o,
    output logic        exc_restore_id_o,

    input  logic        lsu_load_err_i,
    input  logic        lsu_store_err_i,

    // Debug Unit Signals
    input  logic [DBG_SETS_W-1:0] dbg_settings_i,
    input  logic        dbg_req_i,
    output logic        dbg_ack_o,
    input  logic        dbg_stall_i,
    output logic        dbg_trap_o,

    input  logic        dbg_reg_rreq_i,
    input  logic [(REG_ADDR_WIDTH-1):0] dbg_reg_raddr_i,
    output logic [31:0] dbg_reg_rdata_o,

    input  logic        dbg_reg_wreq_i,
    input  logic [(REG_ADDR_WIDTH-1):0] dbg_reg_waddr_i,
    input  logic [31:0] dbg_reg_wdata_i,

    input  logic        dbg_jump_req_i,

    // Forward Signals
    input  logic [(REG_ADDR_WIDTH-1):0]  regfile_waddr_wb_i,
    input  logic        regfile_we_wb_i,
    input  logic [31:0] regfile_wdata_wb_i, // From wb_stage: selects data from data memory, ex_stage result and sp rdata


    input  logic [(REG_ADDR_WIDTH-1):0]  regfile_alu_waddr_fw_i,
    input  logic        regfile_alu_we_fw_i,
    input  logic [31:0] regfile_alu_wdata_fw_i,

    // from ALU
    // CONFIG_REGION: MUL_SUPPORT
  	`ifdef MUL_SUPPORT
    input  logic        mult_multicycle_i,    // when we need multiple cycles in the multiplier and use op c as storage
    `endif // MUL_SUPPORT

    // Performance Counters
    output logic        perf_jump_o,          // we are executing a jump instruction
    output logic        perf_jr_stall_o,      // jump-register-hazard
    output logic        perf_ld_stall_o       // load-use-hazard
);

  logic [31:0] instr;

  // Decoder/Controller ID stage internal signals
  logic        deassert_we;

  logic        illegal_insn_dec;
  logic        ebrk_insn;
  logic        eret_insn_dec;
  logic        ecall_insn_dec;
  logic        pipe_flush_dec;

  logic        rega_used_dec;
  logic        regb_used_dec;
  // CONFIG_REGION: THREE_PORT_REG_FILE
  `ifdef THREE_PORT_REG_FILE
  logic        regc_used_dec;
  `endif // THREE_PORT_REG_FILE
  // CONFIG_REGION: BIT_SUPPORT
  `ifdef BIT_SUPPORT
  logic        bmask_needed_dec;
  `endif // BIT_SUPPORT

  logic        branch_taken_ex;
  logic [1:0]  jump_in_id;
  logic [1:0]  jump_in_dec;


  // CONFIG_REGION: MERGE_ID_EX
  `ifndef ONLY_ALIGNED
  logic        misaligned_stall;
  `endif
  logic        jr_stall;
  logic        load_stall;

  logic        halt_id;


  // Immediate decoding and sign extension
  logic [31:0] imm_i_type;
  logic [31:0] imm_iz_type;
  logic [31:0] imm_s_type;
  logic [31:0] imm_sb_type;
  logic [31:0] imm_u_type;
  logic [31:0] imm_uj_type;
  logic [31:0] imm_z_type;
  logic [31:0] imm_s2_type;
  logic [31:0] imm_bi_type;
  logic [31:0] imm_s3_type;
  logic [31:0] imm_vs_type;
  logic [31:0] imm_vu_type;
  // CONFIG_REGION: MATH_SPECIAL_SUPPORT
  `ifdef MATH_SPECIAL_SUPPORT
  logic [31:0] imm_shuffleb_type;
  logic [31:0] imm_shuffleh_type;
  logic [31:0] imm_shuffle_type;
  logic [31:0] imm_clip_type;
  `endif // MATH_SPECIAL_SUPPORT

  logic [31:0] imm_a;       // contains the immediate for operand b
  logic [31:0] imm_b;       // contains the immediate for operand b

  // CONFIG_REGION: NO_JUMP_ADDER
  `ifndef NO_JUMP_ADDER
  logic [31:0] jump_target;       // calculated jump target (-> EX -> IF)
  `endif


  // Signals running between controller and exception controller
  logic        exc_req, ext_req, exc_ack;  // handshake

  // Register file interface
  logic [(REG_ADDR_WIDTH-1):0]  regfile_addr_ra_id;
  logic [(REG_ADDR_WIDTH-1):0]  regfile_addr_rb_id;
  // CONFIG_REGION: THREE_PORT_REG_FILE
  `ifdef THREE_PORT_REG_FILE
  logic [(REG_ADDR_WIDTH-1):0]  regfile_addr_rc_id;
  `endif // THREE_PORT_REG_FILE

  // CONFIG_REGION: THREE_PORT_REG_FILE
  `ifdef THREE_PORT_REG_FILE
  logic [(REG_ADDR_WIDTH-1):0]  regfile_waddr_id;
  `endif // THREE_PORT_REG_FILE
  logic [(REG_ADDR_WIDTH-1):0]  regfile_alu_waddr_id;
  logic        regfile_alu_we_id;

  logic [31:0] regfile_data_ra_id;
  logic [31:0] regfile_data_rb_id;
  // CONFIG_REGION: THREE_PORT_REG_FILE
  `ifdef THREE_PORT_REG_FILE
  logic [31:0] regfile_data_rc_id;
  `endif // THREE_PORT_REG_FILE

  // ALU Control
  logic [ALU_OP_WIDTH-1:0] alu_operator;
  logic [2:0]  alu_op_a_mux_sel;
  logic [2:0]  alu_op_b_mux_sel;
  logic [1:0]  alu_op_c_mux_sel;
  // CONFIG_REGION: THREE_PORT_REG_FILE
  `ifdef THREE_PORT_REG_FILE
  logic [1:0]  regc_mux;
  `endif // THREE_PORT_REG_FILE

  logic [0:0]  imm_a_mux_sel;
  logic [3:0]  imm_b_mux_sel;
  // CONFIG_REGION: NO_JUMP_ADDER
  `ifndef NO_JUMP_ADDER
  logic [1:0]  jump_target_mux_sel;
  `endif

  // CONFIG_REGION: MUL_SUPPORT
  `ifdef MUL_SUPPORT
    // Multiplier Control
    logic [2:0]  mult_operator;    // multiplication operation selection
    logic        mult_en;          // multiplication is used instead of ALU
    logic        mult_int_en;      // use integer multiplier
    logic        mult_sel_subword; // Select a subword when doing multiplications
    logic [1:0]  mult_signed_mode; // Signed mode multiplication at the output of the controller, and before the pipe registers
    logic        mult_dot_en;      // use dot product
    logic [1:0]  mult_dot_signed;  // Signed mode dot products (can be mixed types)
  `endif // MUL_SUPPORT

  // Register Write Control
  logic        regfile_we_id;
  // CONFIG_REGION: THREE_PORT_REG_FILE
  `ifdef THREE_PORT_REG_FILE
  logic        regfile_alu_waddr_mux_sel;
  `endif // THREE_PORT_REG_FILE

  // Data Memory Control
  logic        data_we_id;
  logic [1:0]  data_type_id;
  logic        data_sign_ext_id;
  // CONFIG_REGION: ONLY_ALIGNED
  `ifndef ONLY_ALIGNED
  logic [1:0]  data_reg_offset_id;
  `endif // ONLY_ALIGNED
  logic        data_req_id;
  logic        data_load_event_id;

  // CONFIG_REGION: HWLP_SUPPORT
  `ifdef HWLP_SUPPORT
  // hwloop signals
  logic [N_HWLP_BITS-1:0] hwloop_regid, hwloop_regid_int;
  logic             [2:0] hwloop_we, hwloop_we_int;
  logic                   hwloop_target_mux_sel;
  logic                   hwloop_start_mux_sel;
  logic                   hwloop_cnt_mux_sel;

  logic            [31:0] hwloop_target;
  logic            [31:0] hwloop_start, hwloop_start_int;
  logic            [31:0] hwloop_end;
  logic            [31:0] hwloop_cnt, hwloop_cnt_int;

  logic                   hwloop_valid;
  `endif // HWLP_SUPPORT

  // CSR control
  logic        csr_access;
  logic [1:0]  csr_op;

  // CONFIG_REGION: PREPOST_SUPPORT
  `ifdef PREPOST_SUPPORT
  logic        prepost_useincr;
  `endif // PREPOST_SUPPORT

  // Forwarding
  logic [1:0]  operand_a_fw_mux_sel;
  logic [1:0]  operand_b_fw_mux_sel;
  // CONFIG_REGION: THREE_PORT_REG_FILE
  `ifdef THREE_PORT_REG_FILE
  logic [1:0]  operand_c_fw_mux_sel;
  `endif // THREE_PORT_REG_FILE
  
  logic [31:0] operand_a_fw_id;
  logic [31:0] operand_b_fw_id;
  // CONFIG_REGION: THREE_PORT_REG_FILE
  `ifdef THREE_PORT_REG_FILE
  logic [31:0] operand_c_fw_id;
  `endif // THREE_PORT_REG_FILE
  
  logic [31:0] operand_b;
  // CONFIG_REGION: VEC_SUPPORT
  `ifdef VEC_SUPPORT
    logic [31:0] operand_b_vec;
  `endif // VEC_SUPPORT

  logic [31:0] alu_operand_a;
  logic [31:0] alu_operand_b;
  logic [31:0] alu_operand_c; // Still needed if 2r1w reg file used

  // Immediates for ID
  // CONFIG_REGION: BIT_SUPPORT
  `ifdef BIT_SUPPORT
  logic [0:0]  bmask_a_mux;
  logic [1:0]  bmask_b_mux;
  logic        alu_bmask_a_mux_sel;
  logic        alu_bmask_b_mux_sel;
  `endif // BIT_SUPPORT
  
  // CONFIG_REGION: MUL_SUPPORT
  `ifdef MUL_SUPPORT
    logic [0:0]  mult_imm_mux;
  `endif // MUL_SUPPORT
  
  // CONFIG_REGION: BIT_SUPPORT
  `ifdef BIT_SUPPORT
  logic [ 4:0] bmask_a_id_imm;
  logic [ 4:0] bmask_b_id_imm;
  logic [ 4:0] bmask_a_id;
  logic [ 4:0] bmask_b_id;
  `endif // BIT_SUPPORT

  // CONFIG_REGION: VEC_SUPPORT
  `ifdef VEC_SUPPORT
  logic [ 1:0] imm_vec_ext_id;
  `endif // VEC_SUPPORT
  // CONFIG_REGION: MUL_SUPPORT
  `ifdef MUL_SUPPORT
  logic [ 4:0] mult_imm_id;
  `endif // MUL_SUPPORT

  // CONFIG_REGION: VEC_SUPPORT
  `ifdef VEC_SUPPORT
  logic [ 1:0] alu_vec_mode;
  logic        scalar_replication;
  `endif // VEC_SUPPORT

  // Forwarding detection signals
  // CONFIG_REGION: THREE_PORT_REG_FILE
  `ifdef THREE_PORT_REG_FILE
  logic        reg_d_ex_is_reg_a_id;
  logic        reg_d_ex_is_reg_b_id;
  logic        reg_d_ex_is_reg_c_id;
  logic        reg_d_wb_is_reg_a_id;
  logic        reg_d_wb_is_reg_b_id;
  logic        reg_d_wb_is_reg_c_id;
  logic        reg_d_alu_is_reg_a_id;
  logic        reg_d_alu_is_reg_b_id;
  logic        reg_d_alu_is_reg_c_id;
  `else 
  // CONFIG_REGION: MERGE_ID_EX
  `ifdef MERGE_ID_EX
  logic        reg_d_wb_is_reg_a_id;
  logic        reg_d_wb_is_reg_b_id;
  `else
  logic        reg_d_wb_is_reg_a_id;
  logic        reg_d_wb_is_reg_b_id;
  logic        reg_d_alu_is_reg_a_id;
  logic        reg_d_alu_is_reg_b_id;
  `endif // MERGE_ID_EX
  `endif // THREE_PORT_REG_FILE

  assign instr = instr_rdata_i;

  // immediate extraction and sign extension
  assign imm_i_type  = { {20 {instr[31]}}, instr[31:20] };
  assign imm_iz_type = {            20'b0, instr[31:20] };
  assign imm_s_type  = { {20 {instr[31]}}, instr[31:25], instr[11:7] };
  assign imm_sb_type = { {19 {instr[31]}}, instr[31], instr[7], instr[30:25], instr[11:8], 1'b0 };
  assign imm_u_type  = { instr[31:12], 12'b0 };
  assign imm_uj_type = { {12 {instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0 };

  // immediate for CSR manipulatin (zero extended)
  assign imm_z_type = { 27'b0, instr[`REG_S1] };

  assign imm_s2_type = { 27'b0, instr[24:20] };
  assign imm_bi_type = { {27{instr[24]}}, instr[24:20] };
  assign imm_s3_type = { 27'b0, instr[29:25] };
  assign imm_vs_type = { {26 {instr[24]}}, instr[24:20], instr[25] };
  assign imm_vu_type = { 26'b0, instr[24:20], instr[25] };

  // CONFIG_REGION: MATH_SPECIAL_SUPPORT
  `ifdef MATH_SPECIAL_SUPPORT
  // same format as rS2 for shuffle needs, expands immediate
  assign imm_shuffleb_type = {6'b0, instr[28:27], 6'b0, instr[24:23], 6'b0, instr[22:21], 6'b0, instr[20], instr[25]};
  assign imm_shuffleh_type = {15'h0, instr[20], 15'h0, instr[25]};
  `endif // MATH_SPECIAL_SUPPORT

  // CONFIG_REGION: MATH_SPECIAL_SUPPORT
  `ifdef MATH_SPECIAL_SUPPORT
  // clipping immediate, uses a small barrel shifter to pre-process the
  // immediate and an adder to subtract 1
  // The end result is a mask that has 1's set in the lower part
  // TODO: check if this can be shared with the bit-manipulation unit
  assign imm_clip_type = (32'h1 << instr[24:20]) - 1;
  `endif // MATH_SPECIAL_SUPPORT

  //---------------------------------------------------------------------------
  // source register selection
  //---------------------------------------------------------------------------
  assign regfile_addr_ra_id = instr[`REG_S1];
  assign regfile_addr_rb_id = instr[`REG_S2];


  // CONFIG_REGION: THREE_PORT_REG_FILE
  `ifdef THREE_PORT_REG_FILE
  // register C mux
  always_comb
    begin
      unique case (regc_mux)
        REGC_ZERO:  regfile_addr_rc_id = '0;
        REGC_RD:    regfile_addr_rc_id = instr[`REG_D];
        REGC_S1:    regfile_addr_rc_id = instr[`REG_S1];
        default:    regfile_addr_rc_id = '0;
      endcase
    end
  `endif // THREE_PORT_REG_FILE

  //---------------------------------------------------------------------------
  // destination registers
  //---------------------------------------------------------------------------

  
  // CONFIG_REGION: THREE_PORT_REG_FILE
  `ifdef THREE_PORT_REG_FILE
  assign regfile_waddr_id = instr[`REG_D];

  // Second Register Write Address Selection
  // Used for prepost load/store and multiplier

  assign regfile_alu_waddr_id = regfile_alu_waddr_mux_sel ?
    regfile_waddr_id : regfile_addr_ra_id;

  `else 
  assign regfile_alu_waddr_id = instr[`REG_D];
  `endif // THREE_PORT_REG_FILE

  // Forwarding control signals
  // CONFIG_REGION: THREE_PORT_REG_FILE
  `ifdef THREE_PORT_REG_FILE
  assign reg_d_ex_is_reg_a_id  = (regfile_waddr_ex_o     == regfile_addr_ra_id) && (rega_used_dec == 1'b1) && (regfile_addr_ra_id != '0);
  assign reg_d_ex_is_reg_b_id  = (regfile_waddr_ex_o     == regfile_addr_rb_id) && (regb_used_dec == 1'b1) && (regfile_addr_rb_id != '0);
  assign reg_d_ex_is_reg_c_id  = (regfile_waddr_ex_o     == regfile_addr_rc_id) && (regc_used_dec == 1'b1) && (regfile_addr_rc_id != '0);
  assign reg_d_wb_is_reg_a_id  = (regfile_waddr_wb_i     == regfile_addr_ra_id) && (rega_used_dec == 1'b1) && (regfile_addr_ra_id != '0);
  assign reg_d_wb_is_reg_b_id  = (regfile_waddr_wb_i     == regfile_addr_rb_id) && (regb_used_dec == 1'b1) && (regfile_addr_rb_id != '0);
  assign reg_d_wb_is_reg_c_id  = (regfile_waddr_wb_i     == regfile_addr_rc_id) && (regc_used_dec == 1'b1) && (regfile_addr_rc_id != '0);
  assign reg_d_alu_is_reg_a_id = (regfile_alu_waddr_fw_i == regfile_addr_ra_id) && (rega_used_dec == 1'b1) && (regfile_addr_ra_id != '0);
  assign reg_d_alu_is_reg_b_id = (regfile_alu_waddr_fw_i == regfile_addr_rb_id) && (regb_used_dec == 1'b1) && (regfile_addr_rb_id != '0);
  assign reg_d_alu_is_reg_c_id = (regfile_alu_waddr_fw_i == regfile_addr_rc_id) && (regc_used_dec == 1'b1) && (regfile_addr_rc_id != '0);
  `else // THREE_PORT_REG_FILE
  // CONFIG_REGION: MERGE_ID_EX
  `ifdef MERGE_ID_EX
  assign reg_d_wb_is_reg_a_id  = (regfile_waddr_wb_i     == regfile_addr_ra_id) && (rega_used_dec == 1'b1) && (regfile_addr_ra_id != '0);
  assign reg_d_wb_is_reg_b_id  = (regfile_waddr_wb_i     == regfile_addr_rb_id) && (regb_used_dec == 1'b1) && (regfile_addr_rb_id != '0);
  `else
  assign reg_d_wb_is_reg_a_id  = (regfile_waddr_wb_i     == regfile_addr_ra_id) && (rega_used_dec == 1'b1) && (regfile_addr_ra_id != '0);
  assign reg_d_wb_is_reg_b_id  = (regfile_waddr_wb_i     == regfile_addr_rb_id) && (regb_used_dec == 1'b1) && (regfile_addr_rb_id != '0);
  assign reg_d_alu_is_reg_a_id = (regfile_alu_waddr_fw_i == regfile_addr_ra_id) && (rega_used_dec == 1'b1) && (regfile_addr_ra_id != '0);
  assign reg_d_alu_is_reg_b_id = (regfile_alu_waddr_fw_i == regfile_addr_rb_id) && (regb_used_dec == 1'b1) && (regfile_addr_rb_id != '0);
  `endif // MERGE_ID_EX
  `endif // THREE_PORT_REG_FILE



  // kill instruction in the IF/ID stage by setting the instr_valid_id control
  // signal to 0 for instructions that are done
  assign clear_instr_valid_o = id_ready_o | halt_id;

  assign branch_taken_ex = branch_in_ex_o & branch_decision_i;

  // CONFIG_REGION: MUL_SUPPORT
  `ifdef MUL_SUPPORT
    assign mult_en = mult_int_en | mult_dot_en;
  `endif // MUL_SUPPORT


  // CONFIG_REGION: HWLP_SUPPORT
  `ifdef HWLP_SUPPORT

  ///////////////////////////////////////////////
  //  _   ___        ___     ___   ___  ____   //
  // | | | \ \      / / |   / _ \ / _ \|  _ \  //
  // | |_| |\ \ /\ / /| |  | | | | | | | |_) | //
  // |  _  | \ V  V / | |__| |_| | |_| |  __/  //
  // |_| |_|  \_/\_/  |_____\___/ \___/|_|     //
  //                                           //
  ///////////////////////////////////////////////

  // hwloop register id
  assign hwloop_regid_int = instr[7];   // rd contains hwloop register id

  // hwloop target mux
  always_comb
    begin
      case (hwloop_target_mux_sel)
        1'b0: hwloop_target = pc_id_i + {imm_iz_type[30:0], 1'b0};
        1'b1: hwloop_target = pc_id_i + {imm_z_type[30:0], 1'b0};
      endcase
    end

  // hwloop start mux
  always_comb
  begin
    case (hwloop_start_mux_sel)
      1'b0: hwloop_start_int = hwloop_target;   // for PC + I imm
      1'b1: hwloop_start_int = pc_if_i;         // for next PC
    endcase
  end


  // hwloop cnt mux
  always_comb
  begin : hwloop_cnt_mux
    case (hwloop_cnt_mux_sel)
      1'b0: hwloop_cnt_int = imm_iz_type;
      1'b1: hwloop_cnt_int = operand_a_fw_id;
    endcase;
  end

  // multiplex between access from instructions and access via CSR registers
  assign hwloop_start = hwloop_we_int[0] ? hwloop_start_int : csr_hwlp_data_i;
  assign hwloop_end   = hwloop_we_int[1] ? hwloop_target    : csr_hwlp_data_i;
  assign hwloop_cnt   = hwloop_we_int[2] ? hwloop_cnt_int   : csr_hwlp_data_i;
  assign hwloop_regid = (|hwloop_we_int) ? hwloop_regid_int : csr_hwlp_regid_i;
  assign hwloop_we    = (|hwloop_we_int) ? hwloop_we_int    : csr_hwlp_we_i;
  `endif // HWLP_SUPPORT


  //////////////////////////////////////////////////////////////////
  //      _                         _____                    _    //
  //     | |_   _ _ __ ___  _ __   |_   _|_ _ _ __ __ _  ___| |_  //
  //  _  | | | | | '_ ` _ \| '_ \    | |/ _` | '__/ _` |/ _ \ __| //
  // | |_| | |_| | | | | | | |_) |   | | (_| | | | (_| |  __/ |_  //
  //  \___/ \__,_|_| |_| |_| .__/    |_|\__,_|_|  \__, |\___|\__| //
  //                       |_|                    |___/           //
  //////////////////////////////////////////////////////////////////

  // CONFIG_REGION: NO_JUMP_ADDER
  `ifndef NO_JUMP_ADDER
  always_comb
  begin : jump_target_mux
    unique case (jump_target_mux_sel)
      JT_JAL:  jump_target = pc_id_i + imm_uj_type;
      JT_COND: jump_target = pc_id_i + imm_sb_type;
      // JALR: Cannot forward RS1, since the path is too long
      JT_JALR: jump_target = regfile_data_ra_id + imm_i_type;
      default:  jump_target = regfile_data_ra_id + imm_i_type;
    endcase
  end
  `endif

  // CONFIG_REGION: JUMP_IN_ID
  `ifdef JUMP_IN_ID
  assign jump_target_o = jump_target;
  `endif // JUMP_IN_ID

  ////////////////////////////////////////////////////////
  //   ___                                 _      _     //
  //  / _ \ _ __   ___ _ __ __ _ _ __   __| |    / \    //
  // | | | | '_ \ / _ \ '__/ _` | '_ \ / _` |   / _ \   //
  // | |_| | |_) |  __/ | | (_| | | | | (_| |  / ___ \  //
  //  \___/| .__/ \___|_|  \__,_|_| |_|\__,_| /_/   \_\ //
  //       |_|                                          //
  ////////////////////////////////////////////////////////

  // ALU_Op_a Mux
  always_comb
  begin : alu_operand_a_mux
    case (alu_op_a_mux_sel)
      OP_A_REGA_OR_FWD:  alu_operand_a = operand_a_fw_id;
      OP_A_REGB_OR_FWD:  alu_operand_a = operand_b_fw_id;
      // CONFIG_REGION: THREE_PORT_REG_FILE
      `ifdef THREE_PORT_REG_FILE
      OP_A_REGC_OR_FWD:  alu_operand_a = operand_c_fw_id;
      `endif // THREE_PORT_REG_FILE
      OP_A_CURRPC:       alu_operand_a = pc_id_i;
      OP_A_IMM:          alu_operand_a = imm_a;
      default:           alu_operand_a = operand_a_fw_id;
    endcase; // case (alu_op_a_mux_sel)
  end

  always_comb
    begin : immediate_a_mux
      unique case (imm_a_mux_sel)
        IMMA_Z:      imm_a = imm_z_type;
        IMMA_ZERO:   imm_a = '0;
        default:      imm_a = '0;
      endcase
    end

  // Operand a forwarding mux
  always_comb
    begin : operand_a_fw_mux
      case (operand_a_fw_mux_sel)
        SEL_FW_EX:    operand_a_fw_id = regfile_alu_wdata_fw_i;
        // CONFIG_REGION: ONLY_ALIGNED
        `ifndef ONLY_ALIGNED
        SEL_MISALIGNED:    operand_a_fw_id = misaligned_addr_i;
        `endif
        SEL_FW_WB:    operand_a_fw_id = regfile_wdata_wb_i;
        SEL_REGFILE:  operand_a_fw_id = regfile_data_ra_id;
        default:       operand_a_fw_id = regfile_data_ra_id;
      endcase; // case (operand_a_fw_mux_sel)
    end

  //////////////////////////////////////////////////////
  //   ___                                 _   ____   //
  //  / _ \ _ __   ___ _ __ __ _ _ __   __| | | __ )  //
  // | | | | '_ \ / _ \ '__/ _` | '_ \ / _` | |  _ \  //
  // | |_| | |_) |  __/ | | (_| | | | | (_| | | |_) | //
  //  \___/| .__/ \___|_|  \__,_|_| |_|\__,_| |____/  //
  //       |_|                                        //
  //////////////////////////////////////////////////////

  // Immediate Mux for operand B
  // TODO: check if sign-extension stuff works well here, maybe able to save
  // some area here
  always_comb
    begin : immediate_b_mux
      unique case (imm_b_mux_sel)
        IMMB_I:      imm_b = imm_i_type;
        IMMB_S:      imm_b = imm_s_type;
        IMMB_U:      imm_b = imm_u_type;
        // CONFIG_REGION: NO_JUMP_ADDER
        `ifndef NO_JUMP_ADDER
        // CONFIG_REGION: ONLY_ALIGNED
        `ifndef ONLY_ALIGNED
        IMMB_PCINCR: imm_b = (is_compressed_i && (~data_misaligned_i)) ? 32'h2 : 32'h4;
        `else 
        IMMB_PCINCR: imm_b = (is_compressed_i) ? 32'h2 : 32'h4;
        `endif // ONLY_ALIGNED
        `endif // NO_JUMP_ADDER

        IMMB_S2:     imm_b = imm_s2_type;
        IMMB_BI:     imm_b = imm_bi_type;
        IMMB_S3:     imm_b = imm_s3_type;
        IMMB_VS:     imm_b = imm_vs_type;
        IMMB_VU:     imm_b = imm_vu_type;
        // CONFIG_REGION: MATH_SPECIAL_SUPPORT
        `ifdef MATH_SPECIAL_SUPPORT
        IMMB_SHUF:   imm_b = imm_shuffle_type;
        IMMB_CLIP:   imm_b = {1'b0, imm_clip_type[31:1]};
        `endif // MATH_SPECIAL_SUPPORT
        // CONFIG_REGION: NO_JUMP_ADDER
        `ifdef NO_JUMP_ADDER
        IMMB_UJ:     imm_b = imm_uj_type;
        IMMB_SB:     imm_b = imm_sb_type;
        `endif
        default:     imm_b = imm_i_type;
      endcase
    end

  // ALU_Op_b Mux
  always_comb
  	begin : alu_operand_b_mux
      case (alu_op_b_mux_sel)
        OP_B_REGA_OR_FWD:  operand_b = operand_a_fw_id;
        OP_B_REGB_OR_FWD:  operand_b = operand_b_fw_id;
        // CONFIG_REGION: THREE_PORT_REG_FILE
        `ifdef THREE_PORT_REG_FILE
        OP_B_REGC_OR_FWD:  operand_b = operand_c_fw_id;
        `endif // THREE_PORT_REG_FILE
        OP_B_IMM:          operand_b = imm_b;
        OP_B_BMASK:        operand_b = $unsigned(operand_b_fw_id[4:0]);
        default:           operand_b = operand_b_fw_id;
      endcase // case (alu_op_b_mux_sel)
  	end


  // scalar replication for operand B and shuffle type
  always_comb
    begin
      // CONFIG_REGION: VEC_SUPPORT
      `ifdef VEC_SUPPORT
        if (alu_vec_mode == VEC_MODE8) begin
          operand_b_vec    = {4{operand_b[7:0]}};
          // CONFIG_REGION: MATH_SPECIAL_SUPPORT
          `ifdef MATH_SPECIAL_SUPPORT
          imm_shuffle_type = imm_shuffleb_type;
          `endif // MATH_SPECIAL_SUPPORT
        end
        else begin
          operand_b_vec    = {2{operand_b[15:0]}};
          // CONFIG_REGION: MATH_SPECIAL_SUPPORT
          `ifdef MATH_SPECIAL_SUPPORT
          imm_shuffle_type = imm_shuffleh_type;
          `endif // MATH_SPECIAL_SUPPORT
        end
      `else
        // CONFIG_REGION: MATH_SPECIAL_SUPPORT
        `ifdef MATH_SPECIAL_SUPPORT       
        imm_shuffle_type = imm_shuffleh_type;
        `endif // MATH_SPECIAL_SUPPORT
      `endif // VEC_SUPPORT
    end

  // CONFIG_REGION: VEC_SUPPORT
  `ifdef VEC_SUPPORT
    // choose normal or scalar replicated version of operand b
    assign alu_operand_b = (scalar_replication == 1'b1) ? operand_b_vec : operand_b;
  `else
    assign alu_operand_b = operand_b;
  `endif // VEC_SUPPORT


  // Operand b forwarding mux
  always_comb
    begin : operand_b_fw_mux
      case (operand_b_fw_mux_sel)
        // CONFIG_REGION: MERGE_ID_EX
        `ifndef MERGE_ID_EX
        SEL_FW_EX:    operand_b_fw_id = regfile_alu_wdata_fw_i;
        `endif // MERGE_ID_EX
        SEL_FW_WB:    operand_b_fw_id = regfile_wdata_wb_i;
        SEL_REGFILE:  operand_b_fw_id = regfile_data_rb_id;
        default:       operand_b_fw_id = regfile_data_rb_id;
      endcase; // case (operand_b_fw_mux_sel)
    end


  //////////////////////////////////////////////////////
  //   ___                                 _    ____  //
  //  / _ \ _ __   ___ _ __ __ _ _ __   __| |  / ___| //
  // | | | | '_ \ / _ \ '__/ _` | '_ \ / _` | | |     //
  // | |_| | |_) |  __/ | | (_| | | | | (_| | | |___  //
  //  \___/| .__/ \___|_|  \__,_|_| |_|\__,_|  \____| //
  //       |_|                                        //
  //////////////////////////////////////////////////////

  // CONFIG_REGION: THREE_PORT_REG_FILE
  `ifdef THREE_PORT_REG_FILE
  // ALU OP C Mux
  always_comb
    begin : alu_operand_c_mux
      case (alu_op_c_mux_sel)
        OP_C_REGC_OR_FWD:  alu_operand_c = operand_c_fw_id;
        OP_C_REGB_OR_FWD:  alu_operand_c = operand_b_fw_id;
        OP_C_JT:           alu_operand_c = jump_target;
        default:           alu_operand_c = operand_c_fw_id;
      endcase // case (alu_op_c_mux_sel)
    end

  // Operand c forwarding mux
  always_comb
    begin : operand_c_fw_mux
      case (operand_c_fw_mux_sel)
        SEL_FW_EX:    operand_c_fw_id = regfile_alu_wdata_fw_i;
        SEL_FW_WB:    operand_c_fw_id = regfile_wdata_wb_i;
        SEL_REGFILE:  operand_c_fw_id = regfile_data_rc_id;
        default:       operand_c_fw_id = regfile_data_rc_id;
      endcase; // case (operand_c_fw_mux_sel)
    end

  `else
  // ALU OP C Mux
  always_comb
    begin : alu_operand_c_mux
      case (alu_op_c_mux_sel)
        OP_C_REGB_OR_FWD:  alu_operand_c = operand_b_fw_id;
        // CONFIG_REGION: NO_JUMP_ADDER
        `ifdef NO_JUMP_ADDER
        OP_C_JT:           alu_operand_c = pc_if_i; // this is the return address
        `else
        OP_C_JT:           alu_operand_c = jump_target;
        `endif
        default:           alu_operand_c = operand_b_fw_id;
      endcase // case (alu_op_c_mux_sel)
    end

  `endif // THREE_PORT_REG_FILE


  ///////////////////////////////////////////////////////////////////////////
  //  ___                              _ _       _              ___ ____   //
  // |_ _|_ __ ___  _ __ ___   ___  __| (_) __ _| |_ ___  ___  |_ _|  _ \  //
  //  | || '_ ` _ \| '_ ` _ \ / _ \/ _` | |/ _` | __/ _ \/ __|  | || | | | //
  //  | || | | | | | | | | | |  __/ (_| | | (_| | ||  __/\__ \  | || |_| | //
  // |___|_| |_| |_|_| |_| |_|\___|\__,_|_|\__,_|\__\___||___/ |___|____/  //
  //                                                                       //
  ///////////////////////////////////////////////////////////////////////////

  // CONFIG_REGION: BIT_SUPPORT
  `ifdef BIT_SUPPORT
  always_comb
  begin
    unique case (bmask_a_mux)
      BMASK_A_ZERO: bmask_a_id_imm = '0;
      BMASK_A_S3:   bmask_a_id_imm = imm_s3_type[4:0];
      default:      bmask_a_id_imm = '0;
    endcase
  end

  always_comb
  begin
    unique case (bmask_b_mux)
      BMASK_B_ZERO: bmask_b_id_imm = '0;
      BMASK_B_ONE:  bmask_b_id_imm = 5'd1;
      BMASK_B_S2:   bmask_b_id_imm = imm_s2_type[4:0];
      BMASK_B_S3:   bmask_b_id_imm = imm_s3_type[4:0];
      default:      bmask_b_id_imm = '0;
    endcase
  end

  always_comb
  begin
    unique case (alu_bmask_a_mux_sel)
      BMASK_A_IMM: bmask_a_id = bmask_a_id_imm;
      BMASK_A_REG: bmask_a_id = operand_b_fw_id[9:5];
      default:     bmask_a_id = bmask_a_id_imm;
    endcase
  end

  always_comb
  begin
    unique case (alu_bmask_b_mux_sel)
      BMASK_B_IMM: bmask_b_id = bmask_b_id_imm;
      BMASK_B_REG: bmask_b_id = operand_b_fw_id[4:0];
      default:     bmask_b_id = bmask_b_id_imm;
    endcase
  end

  `endif // BIT_SUPPORT


  // CONFIG_REGION: VEC_SUPPORT
  `ifdef VEC_SUPPORT
    assign imm_vec_ext_id = imm_vu_type[1:0];
  `endif // VEC_SUPPORT

  // CONFIG_REGION: MUL_SUPPORT
  `ifdef MUL_SUPPORT
    always_comb
      begin
        unique case (mult_imm_mux)
          MIMM_ZERO: mult_imm_id = '0;
          MIMM_S3:   mult_imm_id = imm_s3_type[4:0];
          default:    mult_imm_id = '0;
        endcase
      end
  `endif // MUL_SUPPORT

    /////////////////////////////////////////////////////////
    //  ____  _____ ____ ___ ____ _____ _____ ____  ____   //
    // |  _ \| ____/ ___|_ _/ ___|_   _| ____|  _ \/ ___|  //
    // | |_) |  _|| |  _ | |\___ \ | | |  _| | |_) \___ \  //
    // |  _ <| |__| |_| || | ___) || | | |___|  _ < ___) | //
    // |_| \_\_____\____|___|____/ |_| |_____|_| \_\____/  //
    //                                                     //
    /////////////////////////////////////////////////////////
    riscv_register_file  registers_i
      (
        .clk          ( clk                ),
        .rst_n        ( rst_n              ),

        .test_en_i    ( test_en_i          ),

        // Read port a
        .raddr_a_i    ( regfile_addr_ra_id ),
        .rdata_a_o    ( regfile_data_ra_id ),

        // CONFIG_REGION: THREE_PORT_REG_FILE
        `ifdef THREE_PORT_REG_FILE
        // Read port b
        .raddr_b_i    ( regfile_addr_rb_id ),
        .rdata_b_o    ( regfile_data_rb_id ),

        // Read port c
        .raddr_c_i    ( (dbg_reg_rreq_i == 1'b0) ? regfile_addr_rc_id : dbg_reg_raddr_i ),
        .rdata_c_o    ( regfile_data_rc_id ),
        `else 
        .raddr_b_i    ( (dbg_reg_rreq_i == 1'b0) ? regfile_addr_rb_id : dbg_reg_raddr_i ),
        .rdata_b_o    ( regfile_data_rb_id ),
        `endif // THREE_PORT_REG_FILE


        // CONFIG_REGION: THREE_PORT_REG_FILE
        `ifdef THREE_PORT_REG_FILE
        // Write port a
        .waddr_a_i    ( regfile_waddr_wb_i ),
        .wdata_a_i    ( regfile_wdata_wb_i ),
        .we_a_i       ( regfile_we_wb_i    ),

        // Write port b
        .waddr_b_i    ( (dbg_reg_wreq_i == 1'b0) ? regfile_alu_waddr_fw_i : dbg_reg_waddr_i ),
        .wdata_b_i    ( (dbg_reg_wreq_i == 1'b0) ? regfile_alu_wdata_fw_i : dbg_reg_wdata_i ),
        .we_b_i       ( (dbg_reg_wreq_i == 1'b0) ? regfile_alu_we_fw_i    : 1'b1            )

        `else
        // Write port a (multiplex between ALU and LSU). Conflict is resolved by stalling in EX.
        .waddr_a_i    ( (dbg_reg_wreq_i == 1'b0) ? ( (regfile_we_wb_i == 1'b1) ? regfile_waddr_wb_i : regfile_alu_waddr_fw_i) : dbg_reg_waddr_i ),
        .wdata_a_i    ( (dbg_reg_wreq_i == 1'b0) ? ( (regfile_we_wb_i == 1'b1) ? regfile_wdata_wb_i : regfile_alu_wdata_fw_i) : dbg_reg_wdata_i  ),
        .we_a_i       ( (dbg_reg_wreq_i == 1'b0) ? (regfile_we_wb_i || regfile_alu_we_fw_i) : 1'b1                                               )
        `endif // THREE_PORT_REG_FILE
      );

  // CONFIG_REGION: THREE_PORT_REG_FILE
  `ifdef THREE_PORT_REG_FILE
  assign dbg_reg_rdata_o = regfile_data_rc_id;
  `else 
  assign dbg_reg_rdata_o = regfile_data_rb_id;
  `endif // THREE_PORT_REG_FILE


  ///////////////////////////////////////////////
  //  ____  _____ ____ ___  ____  _____ ____   //
  // |  _ \| ____/ ___/ _ \|  _ \| ____|  _ \  //
  // | | | |  _|| |  | | | | | | |  _| | |_) | //
  // | |_| | |__| |__| |_| | |_| | |___|  _ <  //
  // |____/|_____\____\___/|____/|_____|_| \_\ //
  //                                           //
  ///////////////////////////////////////////////

  riscv_decoder decoder_i
  (
    // CONFIG_REGION: RV32E
    `ifdef RV32E
    .clk                             ( clk                       ),
    `endif
    // controller related signals
    .deassert_we_i                   ( deassert_we               ),
    // CONFIG_REGION: ONLY_ALIGNED
    `ifndef ONLY_ALIGNED
    .data_misaligned_i               ( data_misaligned_i         ),
    `endif // ONLY_ALIGNED
    // CONFIG_REGION: MUL_SUPPORT
    `ifdef MUL_SUPPORT
    .mult_multicycle_i               ( mult_multicycle_i         ),
    `endif // MUL_SUPPORT

    .illegal_insn_o                  ( illegal_insn_dec          ),
    .ebrk_insn_o                     ( ebrk_insn                 ),
    .eret_insn_o                     ( eret_insn_dec             ),
    .ecall_insn_o                    ( ecall_insn_dec            ),
    .pipe_flush_o                    ( pipe_flush_dec            ),

    .rega_used_o                     ( rega_used_dec             ),
    .regb_used_o                     ( regb_used_dec             ),
    // CONFIG_REGION: THREE_PORT_REG_FILE
    `ifdef THREE_PORT_REG_FILE
    .regc_used_o                     ( regc_used_dec             ),
    `endif // THREE_PORT_REG_FILE

    // CONFIG_REGION: BIT_SUPPORT
    `ifdef BIT_SUPPORT
    .bmask_needed_o                  ( bmask_needed_dec          ),
    .bmask_a_mux_o                   ( bmask_a_mux               ),
    .bmask_b_mux_o                   ( bmask_b_mux               ),
    .alu_bmask_a_mux_sel_o           ( alu_bmask_a_mux_sel       ),
    .alu_bmask_b_mux_sel_o           ( alu_bmask_b_mux_sel       ),
    `endif // BIT_SUPPORT

    // from IF/ID pipeline
    .instr_rdata_i                   ( instr                     ),
    .illegal_c_insn_i                ( illegal_c_insn_i          ),

    // ALU signals
    .alu_operator_o                  ( alu_operator              ),
    .alu_op_a_mux_sel_o              ( alu_op_a_mux_sel          ),
    .alu_op_b_mux_sel_o              ( alu_op_b_mux_sel          ),
    .alu_op_c_mux_sel_o              ( alu_op_c_mux_sel          ),

    // CONFIG_REGION: VEC_SUPPORT
    `ifdef VEC_SUPPORT
    .alu_vec_mode_o                  ( alu_vec_mode              ),
    .scalar_replication_o            ( scalar_replication        ),
    `endif // VEC_SUPPORT
    .imm_a_mux_sel_o                 ( imm_a_mux_sel             ),
    .imm_b_mux_sel_o                 ( imm_b_mux_sel             ),
    // CONFIG_REGION: THREE_PORT_REG_FILE
    `ifdef THREE_PORT_REG_FILE
    .regc_mux_o                      ( regc_mux                  ),
    `endif // THREE_PORT_REG_FILE

    // CONFIG_REGION: MUL_SUPPORT
    `ifdef MUL_SUPPORT
    // MUL signals
    .mult_operator_o                 ( mult_operator             ),
    .mult_int_en_o                   ( mult_int_en               ),
    .mult_sel_subword_o              ( mult_sel_subword          ),
    .mult_signed_mode_o              ( mult_signed_mode          ),
    .mult_imm_mux_o                  ( mult_imm_mux              ),
    .mult_dot_en_o                   ( mult_dot_en               ),
    .mult_dot_signed_o               ( mult_dot_signed           ),
    `endif // MUL_SUPPORT

    // Register file control signals
    .regfile_mem_we_o                ( regfile_we_id             ),
    .regfile_alu_we_o                ( regfile_alu_we_id         ),
    `ifdef THREE_PORT_REG_FILE
    .regfile_alu_waddr_sel_o         ( regfile_alu_waddr_mux_sel ),
    `endif // THREE_PORT_REG_FILE

    // CSR control signals
    .csr_access_o                    ( csr_access                ),
    .csr_op_o                        ( csr_op                    ),

    // Data bus interface
    .data_req_o                      ( data_req_id               ),
    .data_we_o                       ( data_we_id                ),
    // CONFIG_REGION: PREPOST_SUPPORT
    `ifdef PREPOST_SUPPORT
    .prepost_useincr_o               ( prepost_useincr           ),
    `endif // PREPOST_SUPPORT
    .data_type_o                     ( data_type_id              ),
    .data_sign_extension_o           ( data_sign_ext_id          ),
    // CONFIG_REGION: ONLY_ALIGNED
    `ifndef ONLY_ALIGNED
    .data_reg_offset_o               ( data_reg_offset_id        ),
    `endif // ONLY_ALIGNED
    .data_load_event_o               ( data_load_event_id        ),


    // CONFIG_REGION: HWLP_SUPPORT
    `ifdef HWLP_SUPPORT
    // hwloop signals
    .hwloop_we_o                     ( hwloop_we_int             ),
    .hwloop_target_mux_sel_o         ( hwloop_target_mux_sel     ),
    .hwloop_start_mux_sel_o          ( hwloop_start_mux_sel      ),
    .hwloop_cnt_mux_sel_o            ( hwloop_cnt_mux_sel        ),
    `endif // HWLP_SUPPORT

    // jump/branches
    .jump_in_dec_o                   ( jump_in_dec               ),
    .jump_in_id_o                    ( jump_in_id                ),
    .jump_target_mux_sel_o           ( jump_target_mux_sel       )

  );

  ////////////////////////////////////////////////////////////////////
  //    ____ ___  _   _ _____ ____   ___  _     _     _____ ____    //
  //   / ___/ _ \| \ | |_   _|  _ \ / _ \| |   | |   | ____|  _ \   //
  //  | |  | | | |  \| | | | | |_) | | | | |   | |   |  _| | |_) |  //
  //  | |__| |_| | |\  | | | |  _ <| |_| | |___| |___| |___|  _ <   //
  //   \____\___/|_| \_| |_| |_| \_\\___/|_____|_____|_____|_| \_\  //
  //                                                                //
  ////////////////////////////////////////////////////////////////////

  riscv_controller controller_i
  (
    .clk                            ( clk                    ),
    .rst_n                          ( rst_n                  ),

    .fetch_enable_i                 ( fetch_enable_i         ),
    .ctrl_busy_o                    ( ctrl_busy_o            ),
    .is_decoding_o                  ( is_decoding_o          ),

    // decoder related signals
    .deassert_we_o                  ( deassert_we            ),
    .illegal_insn_i                 ( illegal_insn_dec       ),
    .eret_insn_i                    ( eret_insn_dec          ),
    .pipe_flush_i                   ( pipe_flush_dec         ),

    .rega_used_i                    ( rega_used_dec          ),
    .regb_used_i                    ( regb_used_dec          ),
    // CONFIG_REGION: THREE_PORT_REG_FILE
    `ifdef THREE_PORT_REG_FILE
    .regc_used_i                    ( regc_used_dec          ),
    `endif // THREE_PORT_REG_FILE

    // from IF/ID pipeline
    .instr_valid_i                  ( instr_valid_i          ),
    .instr_rdata_i                  ( instr                  ),

    // from prefetcher
    .instr_req_o                    ( instr_req_o            ),

    // to prefetcher
    .pc_set_o                       ( pc_set_o               ),
    .pc_mux_o                       ( pc_mux_o               ),

    // LSU
    .data_req_ex_i                  ( data_req_ex_o          ),
    // CONFIG_REGION: ONLY_ALIGNED
    `ifndef ONLY_ALIGNED
    .data_misaligned_i              ( data_misaligned_i      ),
    `endif // ONLY_ALIGNED
    .data_load_event_i              ( data_load_event_ex_o   ),

    // ALU
    // CONFIG_REGION: MUL_SUPPORT
    `ifdef MUL_SUPPORT
    .mult_multicycle_i              ( mult_multicycle_i      ),
    `endif // MUL_SUPPORT

    // jump/branch control
    .branch_taken_ex_i              ( branch_taken_ex        ),
    .jump_in_id_i                   ( jump_in_id             ),
    .jump_in_dec_i                  ( jump_in_dec            ),

    // Exception Controller Signals
    .exc_req_i                      ( exc_req                ),
    .ext_req_i                      ( ext_req                ),
    .exc_ack_o                      ( exc_ack                ),

    .exc_save_if_o                  ( exc_save_if_o          ),
    .exc_save_id_o                  ( exc_save_id_o          ),
    .exc_save_takenbranch_o         ( exc_save_takenbranch_o ),
    .exc_restore_id_o               ( exc_restore_id_o       ),

    // Debug Unit Signals
    .dbg_req_i                      ( dbg_req_i              ),
    .dbg_ack_o                      ( dbg_ack_o              ),
    .dbg_stall_i                    ( dbg_stall_i            ),
    .dbg_jump_req_i                 ( dbg_jump_req_i         ),

    // Forwarding signals from regfile
    // CONFIG_REGION: THREE_PORT_REG_FILE
    `ifdef THREE_PORT_REG_FILE
    .regfile_waddr_ex_i             ( regfile_waddr_ex_o     ), // Write address for register file from ex-wb- pipeline registers
    `endif // THREE_PORT_REG_FILE
    .regfile_we_ex_i                ( regfile_we_ex_o        ),
    .regfile_waddr_wb_i             ( regfile_waddr_wb_i     ), // Write address for register file from ex-wb- pipeline registers
    .regfile_we_wb_i                ( regfile_we_wb_i        ),

    // regfile port 2 (or multiplexer signal in case of a 2r1w)
    .regfile_alu_waddr_fw_i         ( regfile_alu_waddr_fw_i ),
    .regfile_alu_we_fw_i            ( regfile_alu_we_fw_i    ),

    // Forwarding detection signals
    // CONFIG_REGION: THREE_PORT_REG_FILE
    `ifdef THREE_PORT_REG_FILE
    .reg_d_ex_is_reg_a_i            ( reg_d_ex_is_reg_a_id   ),
    .reg_d_ex_is_reg_b_i            ( reg_d_ex_is_reg_b_id   ),
    .reg_d_ex_is_reg_c_i            ( reg_d_ex_is_reg_c_id   ),
    .reg_d_wb_is_reg_a_i            ( reg_d_wb_is_reg_a_id   ),
    .reg_d_wb_is_reg_b_i            ( reg_d_wb_is_reg_b_id   ),
    .reg_d_wb_is_reg_c_i            ( reg_d_wb_is_reg_c_id   ),
    .reg_d_alu_is_reg_a_i           ( reg_d_alu_is_reg_a_id  ),
    .reg_d_alu_is_reg_b_i           ( reg_d_alu_is_reg_b_id  ),
    .reg_d_alu_is_reg_c_i           ( reg_d_alu_is_reg_c_id  ),
    `else
    // CONFIG_REGION: MERGE_ID_EX
    `ifdef MERGE_ID_EX
    .reg_d_wb_is_reg_a_i            ( reg_d_wb_is_reg_a_id   ),
    .reg_d_wb_is_reg_b_i            ( reg_d_wb_is_reg_b_id   ),    
    `else
    .reg_d_wb_is_reg_a_i            ( reg_d_wb_is_reg_a_id   ),
    .reg_d_wb_is_reg_b_i            ( reg_d_wb_is_reg_b_id   ),    
    .reg_d_alu_is_reg_a_i           ( reg_d_alu_is_reg_a_id  ),
    .reg_d_alu_is_reg_b_i           ( reg_d_alu_is_reg_b_id  ),
    `endif // MERGE_ID_EX
    `endif // THREE_PORT_REG_FILE


    // Forwarding signals
    .operand_a_fw_mux_sel_o         ( operand_a_fw_mux_sel   ),
    .operand_b_fw_mux_sel_o         ( operand_b_fw_mux_sel   ),
    // CONFIG_REGION: THREE_PORT_REG_FILE
    `ifdef THREE_PORT_REG_FILE
    .operand_c_fw_mux_sel_o         ( operand_c_fw_mux_sel   ),
    `endif // THREE_PORT_REG_FILE

    // Stall signals
    .halt_if_o                      ( halt_if_o              ),
    .halt_id_o                      ( halt_id                ),

    // CONFIG_REGION: ONLY_ALIGNED
    `ifndef ONLY_ALIGNED
    .misaligned_stall_o             ( misaligned_stall       ),
    `endif // ONLY_ALIGNED
    .jr_stall_o                     ( jr_stall               ),
    .load_stall_o                   ( load_stall             ),

    .id_ready_i                     ( id_ready_o             ),

    .if_valid_i                     ( if_valid_i             ),
    .ex_valid_i                     ( ex_valid_i             ),
    .wb_valid_i                     ( wb_valid_i             ),

    // Performance Counters
    .perf_jump_o                    ( perf_jump_o            ),
    .perf_jr_stall_o                ( perf_jr_stall_o        ),
    .perf_ld_stall_o                ( perf_ld_stall_o        )
  );

  ///////////////////////////////////////////////////////////////////////
  //  _____               ____            _             _ _            //
  // | ____|_  _____     / ___|___  _ __ | |_ _ __ ___ | | | ___ _ __  //
  // |  _| \ \/ / __|   | |   / _ \| '_ \| __| '__/ _ \| | |/ _ \ '__| //
  // | |___ >  < (__ _  | |__| (_) | | | | |_| | | (_) | | |  __/ |    //
  // |_____/_/\_\___(_)  \____\___/|_| |_|\__|_|  \___/|_|_|\___|_|    //
  //                                                                   //
  ///////////////////////////////////////////////////////////////////////

  riscv_exc_controller exc_controller_i
  (
    .clk                  ( clk              ),
    .rst_n                ( rst_n            ),

    // to controller
    .req_o                ( exc_req          ),
    .ext_req_o            ( ext_req          ),
    .ack_i                ( exc_ack          ),

    .trap_o               ( dbg_trap_o       ),

    // to IF stage
    .pc_mux_o             ( exc_pc_mux_o     ),
    .vec_pc_mux_o         ( exc_vec_pc_mux_o ),

    // Interrupt signals
    .irq_i                ( irq_i            ),
    .irq_enable_i         ( irq_enable_i     ),

    .ebrk_insn_i          ( is_decoding_o & ebrk_insn        ),
    .illegal_insn_i       ( is_decoding_o & illegal_insn_dec ),
    .ecall_insn_i         ( is_decoding_o & ecall_insn_dec   ),
    .eret_insn_i          ( is_decoding_o & eret_insn_dec    ),

    .lsu_load_err_i       ( lsu_load_err_i   ),
    .lsu_store_err_i      ( lsu_store_err_i  ),

    .cause_o              ( exc_cause_o      ),
    .save_cause_o         ( save_exc_cause_o ),

    .dbg_settings_i       ( dbg_settings_i   )
  );


  // CONFIG_REGION: HWLP_SUPPORT
  `ifdef HWLP_SUPPORT

  //////////////////////////////////////////////////////////////////////////
  //          ____ ___  _   _ _____ ____   ___  _     _     _____ ____    //
  //         / ___/ _ \| \ | |_   _|  _ \ / _ \| |   | |   | ____|  _ \   //
  // HWLOOP-| |  | | | |  \| | | | | |_) | | | | |   | |   |  _| | |_) |  //
  //        | |__| |_| | |\  | | | |  _ <| |_| | |___| |___| |___|  _ <   //
  //         \____\___/|_| \_| |_| |_| \_\\___/|_____|_____|_____|_| \_\  //
  //                                                                      //
  //////////////////////////////////////////////////////////////////////////

  riscv_hwloop_regs
  #(
    .N_REGS ( N_HWLP )
  )
  hwloop_regs_i
  (
    .clk                   ( clk                       ),
    .rst_n                 ( rst_n                     ),

    // from ID
    .hwlp_start_data_i     ( hwloop_start              ),
    .hwlp_end_data_i       ( hwloop_end                ),
    .hwlp_cnt_data_i       ( hwloop_cnt                ),
    .hwlp_we_i             ( hwloop_we                 ),
    .hwlp_regid_i          ( hwloop_regid              ),

    // from controller
    .valid_i               ( hwloop_valid              ),

    // to hwloop controller
    .hwlp_start_addr_o     ( hwlp_start_o              ),
    .hwlp_end_addr_o       ( hwlp_end_o                ),
    .hwlp_counter_o        ( hwlp_cnt_o                ),

    // from hwloop controller
    .hwlp_dec_cnt_i        ( hwlp_dec_cnt_i            )
  );

  assign hwloop_valid = instr_valid_i & clear_instr_valid_o & is_hwlp_i;
  `endif // HWLP_SUPPORT

  // CONFIG_REGION: MERGE_ID_EX
  `ifndef MERGE_ID_EX

  /////////////////////////////////////////////////////////////////////////////////
  //   ___ ____        _______  __  ____ ___ ____  _____ _     ___ _   _ _____   //
  //  |_ _|  _ \      | ____\ \/ / |  _ \_ _|  _ \| ____| |   |_ _| \ | | ____|  //
  //   | || | | |_____|  _|  \  /  | |_) | || |_) |  _| | |    | ||  \| |  _|    //
  //   | || |_| |_____| |___ /  \  |  __/| ||  __/| |___| |___ | || |\  | |___   //
  //  |___|____/      |_____/_/\_\ |_|  |___|_|   |_____|_____|___|_| \_|_____|  //
  //                                                                             //
  /////////////////////////////////////////////////////////////////////////////////


  always_ff @(posedge clk, negedge rst_n)
  begin : ID_EX_PIPE_REGISTERS
    if (rst_n == 1'b0)
    begin
      alu_operator_ex_o           <= ALU_SLTU;
      alu_operand_a_ex_o          <= '0;
      alu_operand_b_ex_o          <= '0;
      alu_operand_c_ex_o          <= '0; // Still needed for jump target if 2r1w reg file used
      
      // CONFIG_REGION: BIT_SUPPORT
      `ifdef BIT_SUPPORT
      bmask_a_ex_o                <= '0;
      bmask_b_ex_o                <= '0;
      `endif // BIT_SUPPORT
      
      // CONFIG_REGION: VEC_SUPPORT
      `ifdef VEC_SUPPORT
      imm_vec_ext_ex_o            <= '0;
      alu_vec_mode_ex_o           <= '0;
      `endif // VEC_SUPPORT

      // CONFIG_REGION: MUL_SUPPORT
      `ifdef MUL_SUPPORT
      mult_operator_ex_o          <= '0;
      mult_operand_a_ex_o         <= '0;
      mult_operand_b_ex_o         <= '0;
      mult_operand_c_ex_o         <= '0;
      mult_en_ex_o                <= 1'b0;
      mult_sel_subword_ex_o       <= 1'b0;
      mult_signed_mode_ex_o       <= 2'b00;
      mult_imm_ex_o               <= '0;
      mult_dot_op_a_ex_o          <= '0;
      mult_dot_op_b_ex_o          <= '0;
      mult_dot_op_c_ex_o          <= '0;
      mult_dot_signed_ex_o        <= '0;
      `endif // MUL_SUPPORT

      // CONFIG_REGION: THREE_PORT_REG_FILE
      `ifdef THREE_PORT_REG_FILE
      regfile_waddr_ex_o          <= 5'b0;
      `endif // THREE_PORT_REG_FILE
      regfile_we_ex_o             <= 1'b0;  
      regfile_alu_waddr_ex_o      <= 5'b0;
      regfile_alu_we_ex_o         <= 1'b0;
      // CONFIG_REGION: PREPOST_SUPPORT
      `ifdef PREPOST_SUPPORT
      prepost_useincr_ex_o        <= 1'b0;
      `endif // PREPOST_SUPPORT
      csr_access_ex_o             <= 1'b0;
      csr_op_ex_o                 <= CSR_OP_NONE;
      data_we_ex_o                <= 1'b0;
      data_type_ex_o              <= 2'b0;
      data_sign_ext_ex_o          <= 1'b0;
      // CONFIG_REGION: ONLY_ALIGNED
      `ifndef ONLY_ALIGNED
      data_reg_offset_ex_o        <= 2'b0;
      `endif // ONLY_ALIGNED
      data_req_ex_o               <= 1'b0;
      data_load_event_ex_o        <= 1'b0;
      // CONFIG_REGION: ONLY_ALIGNED
      `ifndef ONLY_ALIGNED
      data_misaligned_ex_o        <= 1'b0;
      `endif // ONLY_ALIGNED
      pc_ex_o                     <= '0;
      branch_in_ex_o              <= 1'b0;
    end
    // CONFIG_REGION: ONLY_ALIGNED
    `ifndef ONLY_ALIGNED
    else if (data_misaligned_i) begin
      // misaligned data access case
      if (ex_ready_i)
      begin // misaligned access case, only unstall alu operands
        // if we are using post increments, then we have to use the
        // original value of the register for the second memory access
        // => keep it stalled

        // CONFIG_REGION: PREPOST_SUPPORT
        `ifdef PREPOST_SUPPORT
        if (prepost_useincr_ex_o == 1'b1)
        begin
          alu_operand_a_ex_o        <= alu_operand_a;
        end
        `else
        alu_operand_a_ex_o        <= alu_operand_a;
        `endif // PREPOST_SUPPORT
        alu_operand_b_ex_o          <= alu_operand_b;
        regfile_alu_we_ex_o         <= regfile_alu_we_id;
        // CONFIG_REGION: PREPOST_SUPPORT
        `ifdef PREPOST_SUPPORT
        prepost_useincr_ex_o        <= prepost_useincr;
        `endif // PREPOST_SUPPORT
        data_misaligned_ex_o        <= 1'b1;
      end
    end
    `endif // ONLY_ALIGNED

    // CONFIG_REGION: MUL_SUPPORT
    `ifdef MUL_SUPPORT
    else if (mult_multicycle_i) begin
      mult_operand_c_ex_o <= alu_operand_c;
    end
    `endif // MUL_SUPPORT

    else begin
      // normal pipeline unstall case
      if (id_valid_o)
      begin // unstall the whole pipeline

        // CONFIG_REGION: MUL_SUPPORT
        `ifdef MUL_SUPPORT
        if (~mult_en)
        `else
        if (1'b1)
        `endif // MUL_SUPPORT
        begin // only change those registers when we actually need to
          alu_operator_ex_o         <= alu_operator;
          alu_operand_a_ex_o        <= alu_operand_a;
          alu_operand_b_ex_o        <= alu_operand_b;
          alu_operand_c_ex_o        <= alu_operand_c;
          
          // CONFIG_REGION: BIT_SUPPORT
          `ifdef BIT_SUPPORT
          bmask_a_ex_o              <= bmask_a_id;
          bmask_b_ex_o              <= bmask_b_id;
          `endif // BIT_SUPPORT
          
          // CONFIG_REGION: VEC_SUPPORT
          `ifdef VEC_SUPPORT
          imm_vec_ext_ex_o          <= imm_vec_ext_id;
          alu_vec_mode_ex_o         <= alu_vec_mode;
          `endif // VEC_SUPPORT
        end



        // CONFIG_REGION: MUL_SUPPORT
        `ifdef MUL_SUPPORT
        mult_en_ex_o                <= mult_en;
        if (mult_int_en) begin  // when we are multiplying we don't need the ALU
          mult_operator_ex_o        <= mult_operator;
          mult_sel_subword_ex_o     <= mult_sel_subword;
          mult_signed_mode_ex_o     <= mult_signed_mode;
          mult_operand_a_ex_o       <= alu_operand_a;
          mult_operand_b_ex_o       <= alu_operand_b;
          mult_operand_c_ex_o       <= alu_operand_c;
          mult_imm_ex_o             <= mult_imm_id;
        end
        if (mult_dot_en) begin
          mult_operator_ex_o        <= mult_operator;
          mult_dot_signed_ex_o      <= mult_dot_signed;
          mult_dot_op_a_ex_o        <= alu_operand_a;
          mult_dot_op_b_ex_o        <= alu_operand_b;
          mult_dot_op_c_ex_o        <= alu_operand_c;
        end
        `endif // MUL_SUPPORT
        

        regfile_we_ex_o             <= regfile_we_id;
        regfile_alu_we_ex_o         <= regfile_alu_we_id;

        // CONFIG_REGION: THREE_PORT_REG_FILE
        `ifdef THREE_PORT_REG_FILE
        if (regfile_we_id) begin
          regfile_waddr_ex_o        <= regfile_waddr_id;
        end
        if (regfile_alu_we_id) begin
          regfile_alu_waddr_ex_o    <= regfile_alu_waddr_id;
        end
        `else 
        if (regfile_we_id | regfile_alu_we_id) begin
          regfile_alu_waddr_ex_o    <= regfile_alu_waddr_id;
        end
        `endif // THREE_PORT_REG_FILE


        // CONFIG_REGION: PREPOST_SUPPORT
        `ifdef PREPOST_SUPPORT
        prepost_useincr_ex_o        <= prepost_useincr;
        `endif // PREPOST_SUPPORT
        csr_access_ex_o             <= csr_access;
        csr_op_ex_o                 <= csr_op;
        data_req_ex_o               <= data_req_id;
        if (data_req_id)
        begin // only needed for LSU when there is an active request
          data_we_ex_o              <= data_we_id;
          data_type_ex_o            <= data_type_id;
          data_sign_ext_ex_o        <= data_sign_ext_id;
          // CONFIG_REGION: ONLY_ALIGNED
          `ifndef ONLY_ALIGNED
          data_reg_offset_ex_o      <= data_reg_offset_id;
          `endif // ONLY_ALIGNED
          data_load_event_ex_o      <= data_load_event_id;
        end else begin
          data_load_event_ex_o      <= 1'b0;
        end
        // CONFIG_REGION: ONLY_ALIGNED
        `ifndef ONLY_ALIGNED
        data_misaligned_ex_o        <= 1'b0;
        `endif // ONLY_ALIGNED

        // CONFIG_REGION: JUMP_IN_ID
        `ifdef JUMP_IN_ID
        if ((jump_in_id == BRANCH_COND) || data_load_event_id) begin
          pc_ex_o                   <= pc_id_i;
        end
        `else 
        if ((jump_in_id == BRANCH_COND) || (jump_in_id == BRANCH_JAL) || (jump_in_id == BRANCH_JALR) || data_load_event_id) begin
          pc_ex_o                   <= pc_id_i;
        end
        `endif
        branch_in_ex_o              <= jump_in_id == BRANCH_COND;
        
      end else if(ex_ready_i) begin
        // EX stage is ready but we don't have a new instruction for it,
        // so we set all write enables to 0, but unstall the pipe
        regfile_we_ex_o             <= 1'b0;
        regfile_alu_we_ex_o         <= 1'b0;
        csr_op_ex_o                 <= CSR_OP_NONE;
        data_req_ex_o               <= 1'b0;
        data_load_event_ex_o        <= 1'b0;
        // CONFIG_REGION: ONLY_ALIGNED
        `ifndef ONLY_ALIGNED
        data_misaligned_ex_o        <= 1'b0;
        `endif // ONLY_ALIGNED
        branch_in_ex_o              <= 1'b0;
      end
    end
  end

  // CONFIG_REGION: SPLITTED_ADDER
  `ifdef  SPLITTED_ADDER
  
  always_ff @(posedge clk or negedge rst_n) begin
    if(~rst_n) begin
      alu_req_ex_o <= 0;
    end else begin
      alu_req_ex_o <= id_valid_o & ~deassert_we;
    end
  end
  `endif

  `else // MERGE_ID_EX

  /////////////////////////////////////
  //   ___ ____        _______  __   //
  //  |_ _|  _ \      | ____\ \/ /   //
  //   | || | | |_____|  _|  \  /    // - merging network
  //   | || |_| |_____| |___ /  \    //
  //  |___|____/      |_____/_/\_\   //
  //                                 //
  /////////////////////////////////////


  always_comb
  begin
    alu_operator_ex_o           = ALU_SLTU;
    alu_operand_c_ex_o          = '0; // Still needed for jump target if 2r1w reg file used

    regfile_we_ex_o             = 1'b0;  
    regfile_alu_waddr_ex_o      = regfile_alu_waddr_id;

    csr_access_ex_o             = 1'b0;
    csr_op_ex_o                 = CSR_OP_NONE;
    data_we_ex_o                = data_we_id;
    data_type_ex_o              = data_type_id;
    data_sign_ext_ex_o          = data_sign_ext_id;

    // CONFIG_REGION: ONLY_ALIGNED
    `ifndef ONLY_ALIGNED
    data_reg_offset_ex_o        = 2'b0;
    `endif // ONLY_ALIGNED

      
    alu_operator_ex_o           = alu_operator;
    alu_operand_a_ex_o          = alu_operand_a;
    alu_operand_b_ex_o          = alu_operand_b;
    alu_operand_c_ex_o          = alu_operand_c;

    regfile_we_ex_o             = regfile_we_id;
    regfile_alu_we_ex_o         = regfile_alu_we_id;

    csr_access_ex_o             = csr_access;
    csr_op_ex_o                 = csr_op;
    data_req_ex_o               = data_req_id;


    // CONFIG_REGION: ONLY_ALIGNED
    `ifndef ONLY_ALIGNED
    data_reg_offset_ex_o      = data_reg_offset_id;
    `endif // ONLY_ALIGNED
    data_load_event_ex_o      = (data_req_id ? data_load_event_id : 1'b0);

    // CONFIG_REGION: ONLY_ALIGNED
    `ifndef ONLY_ALIGNED
    data_misaligned_ex_o    = data_misaligned_i;
    `endif // ONLY_ALIGNED

    pc_ex_o                     = pc_id_i;
    branch_in_ex_o              = (jump_in_id == BRANCH_COND);
  end


  `endif // MERGE_ID_EX


  // stall control
  // CONFIG_REGION: ONLY_ALIGNED
  `ifndef ONLY_ALIGNED
  // CONFIG_REGION: MERGE_ID_EX
  `ifdef MERGE_ID_EX
  assign id_ready_o = ((~misaligned_stall) & (~jr_stall) & (~load_stall) & ex_ready_i);
  `else
  assign id_ready_o = ((~misaligned_stall) & (~jr_stall) & (~load_stall) & ex_ready_i);
  `endif
  `else
  // CONFIG_REGION: MERGE_ID_EX
  `ifdef MERGE_ID_EX
  assign id_ready_o = ((~jr_stall) & (~load_stall) & ex_ready_i);
  `else 
  assign id_ready_o = ((~jr_stall) & (~load_stall) & ex_ready_i);
  `endif
  `endif // ONLY_ALIGNED
  

  assign id_valid_o = (~halt_id) & id_ready_o;

  //----------------------------------------------------------------------------
  // Assertions
  //----------------------------------------------------------------------------

  // make sure that branch decision is valid when jumping
  assert property (
    @(posedge clk) (branch_in_ex_o) |-> (branch_decision_i !== 1'bx) ) else $display("Branch decision is X");

  // the instruction delivered to the ID stage should always be valid
  assert property (
    @(posedge clk) (instr_valid_i & (~illegal_c_insn_i)) |-> (!$isunknown(instr_rdata_i)) ) else $display("Instruction is valid, but has at least one X");

endmodule
