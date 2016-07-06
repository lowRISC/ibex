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
// Engineer        Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                                                                            //
// Additional contributions by:                                               //
//                 Matthias Baer - baermatt@student.ethz.ch                   //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                                                                            //
// Design Name:    Decoder                                                    //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Decoder                                                    //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

import riscv_defines::*;

module riscv_decoder
(
  // singals running to/from controller
  input  logic        deassert_we_i,           // deassert we, we are stalled or not active
  input  logic        data_misaligned_i,       // misaligned data load/store in progress
  input  logic        mult_multicycle_i,       // multiplier taking multiple cycles, using op c as storage

  output logic        illegal_insn_o,          // illegal instruction encountered
  output logic        ebrk_insn_o,             // trap instruction encountered
  output logic        eret_insn_o,             // return from exception instruction encountered
  output logic        ecall_insn_o,            // environment call (syscall) instruction encountered
  output logic        pipe_flush_o,            // pipeline flush is requested

  output logic        rega_used_o,             // rs1 is used by current instruction
  output logic        regb_used_o,             // rs2 is used by current instruction
  output logic        regc_used_o,             // rs3 is used by current instruction

  output logic        bmask_needed_o,          // registers for bit manipulation mask is needed
  output logic [ 0:0] bmask_a_mux_o,           // bit manipulation mask a mux
  output logic [ 1:0] bmask_b_mux_o,           // bit manipulation mask a mux

  // from IF/ID pipeline
  input  logic [31:0] instr_rdata_i,           // instruction read from instr memory/cache
  input  logic        illegal_c_insn_i,        // compressed instruction decode failed

  // ALU signals
  output logic [ALU_OP_WIDTH-1:0] alu_operator_o, // ALU operation selection
  output logic [1:0]  alu_op_a_mux_sel_o,      // operand a selection: reg value, PC, immediate or zero
  output logic [1:0]  alu_op_b_mux_sel_o,      // operand b selection: reg value or immediate
  output logic [1:0]  alu_op_c_mux_sel_o,      // operand c selection: reg value or jump target
  output logic [1:0]  alu_vec_mode_o,          // selects between 32 bit, 16 bit and 8 bit vectorial modes
  output logic        scalar_replication_o,    // scalar replication enable
  output logic [0:0]  imm_a_mux_sel_o,         // immediate selection for operand a
  output logic [3:0]  imm_b_mux_sel_o,         // immediate selection for operand b
  output logic [1:0]  regc_mux_o,              // register c selection: S3, RD or 0

  // MUL related control signals
  output logic [2:0]  mult_operator_o,         // Multiplication operation selection
  output logic        mult_int_en_o,           // perform integer multiplication
  output logic        mult_dot_en_o,           // perform dot multiplication
  output logic [0:0]  mult_imm_mux_o,          // Multiplication immediate mux selector
  output logic        mult_sel_subword_o,      // Select subwords for 16x16 bit of multiplier
  output logic [1:0]  mult_signed_mode_o,      // Multiplication in signed mode
  output logic [1:0]  mult_dot_signed_o,       // Dot product in signed mode

  // register file related signals
  output logic        regfile_mem_we_o,        // write enable for regfile
  output logic        regfile_alu_we_o,        // write enable for 2nd regfile port
  output logic        regfile_alu_waddr_sel_o, // Select register write address for ALU/MUL operations

  // CSR manipulation
  output logic        csr_access_o,            // access to CSR
  output logic [1:0]  csr_op_o,                // operation to perform on CSR

  // LD/ST unit signals
  output logic        data_req_o,              // start transaction to data memory
  output logic        data_we_o,               // data memory write enable
  output logic        prepost_useincr_o,       // when not active bypass the alu result for address calculation
  output logic [1:0]  data_type_o,             // data type on data memory: byte, half word or word
  output logic        data_sign_extension_o,   // sign extension on read data from data memory
  output logic [1:0]  data_reg_offset_o,       // offset in byte inside register for stores
  output logic        data_load_event_o,       // data request is in the special event range

  // hwloop signals
  output logic [2:0]  hwloop_we_o,             // write enable for hwloop regs
  output logic        hwloop_target_mux_sel_o, // selects immediate for hwloop target
  output logic        hwloop_start_mux_sel_o,  // selects hwloop start address input
  output logic        hwloop_cnt_mux_sel_o,    // selects hwloop counter input

  // jump/branches
  output logic [1:0]  jump_in_dec_o,           // jump_in_id without deassert
  output logic [1:0]  jump_in_id_o,            // jump is being calculated in ALU
  output logic [1:0]  jump_target_mux_sel_o    // jump target selection
);

  // write enable/request control
  logic       regfile_mem_we;
  logic       regfile_alu_we;
  logic       data_req;
  logic [2:0] hwloop_we;

  logic       ebrk_insn;
  logic       eret_insn;
  logic       pipe_flush;

  logic [1:0] jump_in_id;

  logic [1:0] csr_op;


  /////////////////////////////////////////////
  //   ____                     _            //
  //  |  _ \  ___  ___ ___   __| | ___ _ __  //
  //  | | | |/ _ \/ __/ _ \ / _` |/ _ \ '__| //
  //  | |_| |  __/ (_| (_) | (_| |  __/ |    //
  //  |____/ \___|\___\___/ \__,_|\___|_|    //
  //                                         //
  /////////////////////////////////////////////

  always_comb
  begin
    jump_in_id                  = BRANCH_NONE;
    jump_target_mux_sel_o       = JT_JAL;

    alu_operator_o              = ALU_SLTU;
    alu_op_a_mux_sel_o          = OP_A_REGA_OR_FWD;
    alu_op_b_mux_sel_o          = OP_B_REGB_OR_FWD;
    alu_op_c_mux_sel_o          = OP_C_REGC_OR_FWD;
    alu_vec_mode_o              = VEC_MODE32;
    scalar_replication_o        = 1'b0;
    regc_mux_o                  = REGC_ZERO;
    imm_a_mux_sel_o             = IMMA_ZERO;
    imm_b_mux_sel_o             = IMMB_I;

    mult_operator_o             = MUL_I;
    mult_int_en_o               = 1'b0;
    mult_dot_en_o               = 1'b0;
    mult_imm_mux_o              = MIMM_ZERO;
    mult_signed_mode_o          = 2'b00;
    mult_sel_subword_o          = 1'b0;
    mult_dot_signed_o           = 2'b00;

    regfile_mem_we              = 1'b0;
    regfile_alu_we              = 1'b0;
    regfile_alu_waddr_sel_o     = 1'b1;

    prepost_useincr_o           = 1'b1;

    hwloop_we                   = 3'b0;
    hwloop_target_mux_sel_o     = 1'b0;
    hwloop_start_mux_sel_o      = 1'b0;
    hwloop_cnt_mux_sel_o        = 1'b0;

    csr_access_o                = 1'b0;
    csr_op                      = CSR_OP_NONE;

    data_we_o                   = 1'b0;
    data_type_o                 = 2'b00;
    data_sign_extension_o       = 1'b0;
    data_reg_offset_o           = 2'b00;
    data_req                    = 1'b0;
    data_load_event_o           = 1'b0;

    illegal_insn_o              = 1'b0;
    ebrk_insn                   = 1'b0;
    eret_insn                   = 1'b0;
    ecall_insn_o                = 1'b0;
    pipe_flush                  = 1'b0;

    rega_used_o                 = 1'b0;
    regb_used_o                 = 1'b0;
    regc_used_o                 = 1'b0;
    bmask_needed_o              = 1'b1; // TODO: only use when necessary
    bmask_a_mux_o               = BMASK_A_ZERO;
    bmask_b_mux_o               = BMASK_B_ZERO;


    unique case (instr_rdata_i[6:0])

      //////////////////////////////////////
      //      _ _   _ __  __ ____  ____   //
      //     | | | | |  \/  |  _ \/ ___|  //
      //  _  | | | | | |\/| | |_) \___ \  //
      // | |_| | |_| | |  | |  __/ ___) | //
      //  \___/ \___/|_|  |_|_|   |____/  //
      //                                  //
      //////////////////////////////////////

      OPCODE_JAL: begin   // Jump and Link
        jump_target_mux_sel_o = JT_JAL;
        jump_in_id            = BRANCH_JAL;
        // Calculate and store PC+4
        alu_op_a_mux_sel_o  = OP_A_CURRPC;
        alu_op_b_mux_sel_o  = OP_B_IMM;
        imm_b_mux_sel_o     = IMMB_PCINCR;
        alu_operator_o      = ALU_ADD;
        regfile_alu_we      = 1'b1;
        // Calculate jump target (= PC + UJ imm)
      end

      OPCODE_JALR: begin  // Jump and Link Register
        jump_target_mux_sel_o = JT_JALR;
        jump_in_id            = BRANCH_JALR;
        // Calculate and store PC+4
        alu_op_a_mux_sel_o  = OP_A_CURRPC;
        alu_op_b_mux_sel_o  = OP_B_IMM;
        imm_b_mux_sel_o     = IMMB_PCINCR;
        alu_operator_o      = ALU_ADD;
        regfile_alu_we      = 1'b1;
        // Calculate jump target (= RS1 + I imm)
        rega_used_o         = 1'b1;

        if (instr_rdata_i[14:12] != 3'b0) begin
          jump_in_id       = BRANCH_NONE;
          regfile_alu_we   = 1'b0;
          illegal_insn_o   = 1'b1;
        end
      end

      OPCODE_BRANCH: begin // Branch
        jump_target_mux_sel_o = JT_COND;
        jump_in_id            = BRANCH_COND;
        alu_op_c_mux_sel_o    = OP_C_JT;
        rega_used_o           = 1'b1;
        regb_used_o           = 1'b1;

        unique case (instr_rdata_i[14:12])
          3'b000: alu_operator_o = ALU_EQ;
          3'b001: alu_operator_o = ALU_NE;
          3'b100: alu_operator_o = ALU_LTS;
          3'b101: alu_operator_o = ALU_GES;
          3'b110: alu_operator_o = ALU_LTU;
          3'b111: alu_operator_o = ALU_GEU;
          3'b010: begin
            alu_operator_o      = ALU_EQ;
            regb_used_o         = 1'b0;
            alu_op_b_mux_sel_o  = OP_B_IMM;
            imm_b_mux_sel_o     = IMMB_BI;
          end
          3'b011: begin
            alu_operator_o      = ALU_NE;
            regb_used_o         = 1'b0;
            alu_op_b_mux_sel_o  = OP_B_IMM;
            imm_b_mux_sel_o     = IMMB_BI;
          end
          default: begin
            illegal_insn_o = 1'b1;
          end
        endcase
      end


      //////////////////////////////////
      //  _     ____    ______ _____  //
      // | |   |  _ \  / / ___|_   _| //
      // | |   | | | |/ /\___ \ | |   //
      // | |___| |_| / /  ___) || |   //
      // |_____|____/_/  |____/ |_|   //
      //                              //
      //////////////////////////////////

      OPCODE_STORE,
      OPCODE_STORE_POST: begin
        data_req       = 1'b1;
        data_we_o      = 1'b1;
        rega_used_o    = 1'b1;
        regb_used_o    = 1'b1;
        alu_operator_o = ALU_ADD;

        // pass write data through ALU operand c
        alu_op_c_mux_sel_o = OP_C_REGB_OR_FWD;

        // post-increment setup
        if (instr_rdata_i[6:0] == OPCODE_STORE_POST) begin
          prepost_useincr_o       = 1'b0;
          regfile_alu_waddr_sel_o = 1'b0;
          regfile_alu_we          = 1'b1;
        end

        if (instr_rdata_i[14] == 1'b0) begin
          // offset from immediate
          imm_b_mux_sel_o     = IMMB_S;
          alu_op_b_mux_sel_o  = OP_B_IMM;
        end else begin
          // offset from register
          regc_used_o        = 1'b1;
          alu_op_b_mux_sel_o = OP_B_REGC_OR_FWD;
          regc_mux_o         = REGC_RD;
        end

        // store size
        unique case (instr_rdata_i[13:12])
          2'b00: data_type_o = 2'b10; // SB
          2'b01: data_type_o = 2'b01; // SH
          2'b10: data_type_o = 2'b00; // SW
          default: begin
            data_req       = 1'b0;
            data_we_o      = 1'b0;
            illegal_insn_o = 1'b1;
          end
        endcase
      end

      OPCODE_LOAD,
      OPCODE_LOAD_POST: begin
        data_req        = 1'b1;
        regfile_mem_we  = 1'b1;
        rega_used_o     = 1'b1;
        data_type_o     = 2'b00;

        // offset from immediate
        alu_operator_o      = ALU_ADD;
        alu_op_b_mux_sel_o  = OP_B_IMM;
        imm_b_mux_sel_o     = IMMB_I;

        // post-increment setup
        if (instr_rdata_i[6:0] == OPCODE_LOAD_POST) begin
          prepost_useincr_o       = 1'b0;
          regfile_alu_waddr_sel_o = 1'b0;
          regfile_alu_we          = 1'b1;
        end

        // sign/zero extension
        data_sign_extension_o = ~instr_rdata_i[14];

        // load size
        unique case (instr_rdata_i[13:12])
          2'b00:   data_type_o = 2'b10; // LB
          2'b01:   data_type_o = 2'b01; // LH
          2'b10:   data_type_o = 2'b00; // LW
          default: data_type_o = 2'b00; // illegal or reg-reg
        endcase

        // reg-reg load (different encoding)
        if (instr_rdata_i[14:12] == 3'b111) begin
          // offset from RS2
          regb_used_o        = 1'b1;
          alu_op_b_mux_sel_o = OP_B_REGB_OR_FWD;

          // sign/zero extension
          data_sign_extension_o = ~instr_rdata_i[30];

          // load size
          unique case (instr_rdata_i[31:25])
            7'b0000_000,
            7'b0100_000: data_type_o = 2'b10; // LB, LBU
            7'b0001_000,
            7'b0101_000: data_type_o = 2'b01; // LH, LHU
            7'b0010_000: data_type_o = 2'b00; // LW
            default: begin
              illegal_insn_o = 1'b1;
            end
          endcase
        end

        // special p.elw (event load)
        if (instr_rdata_i[14:12] == 3'b110)
          data_load_event_o = 1'b1;

        if (instr_rdata_i[14:12] == 3'b011) begin
          // LD -> RV64 only
          illegal_insn_o = 1'b1;
        end
      end


      //////////////////////////
      //     _    _    _   _  //
      //    / \  | |  | | | | //
      //   / _ \ | |  | | | | //
      //  / ___ \| |__| |_| | //
      // /_/   \_\_____\___/  //
      //                      //
      //////////////////////////

      OPCODE_LUI: begin  // Load Upper Immediate
        alu_op_a_mux_sel_o  = OP_A_IMM;
        alu_op_b_mux_sel_o  = OP_B_IMM;
        imm_a_mux_sel_o     = IMMA_ZERO;
        imm_b_mux_sel_o     = IMMB_U;
        alu_operator_o      = ALU_ADD;
        regfile_alu_we      = 1'b1;
      end

      OPCODE_AUIPC: begin  // Add Upper Immediate to PC
        alu_op_a_mux_sel_o  = OP_A_CURRPC;
        alu_op_b_mux_sel_o  = OP_B_IMM;
        imm_b_mux_sel_o     = IMMB_U;
        alu_operator_o      = ALU_ADD;
        regfile_alu_we      = 1'b1;
      end

      OPCODE_OPIMM: begin // Register-Immediate ALU Operations
        alu_op_b_mux_sel_o  = OP_B_IMM;
        imm_b_mux_sel_o     = IMMB_I;
        regfile_alu_we      = 1'b1;
        rega_used_o         = 1'b1;

        unique case (instr_rdata_i[14:12])
          3'b000: alu_operator_o = ALU_ADD;  // Add Immediate
          3'b010: alu_operator_o = ALU_SLTS; // Set to one if Lower Than Immediate
          3'b011: alu_operator_o = ALU_SLTU; // Set to one if Lower Than Immediate Unsigned
          3'b100: alu_operator_o = ALU_XOR;  // Exclusive Or with Immediate
          3'b110: alu_operator_o = ALU_OR;   // Or with Immediate
          3'b111: alu_operator_o = ALU_AND;  // And with Immediate

          3'b001: begin
            alu_operator_o = ALU_SLL;  // Shift Left Logical by Immediate
            if (instr_rdata_i[31:25] != 7'b0)
              illegal_insn_o = 1'b1;
          end

          3'b101: begin
            if (instr_rdata_i[31:25] == 7'b0)
              alu_operator_o = ALU_SRL;  // Shift Right Logical by Immediate
            else if (instr_rdata_i[31:25] == 7'b010_0000)
              alu_operator_o = ALU_SRA;  // Shift Right Arithmetically by Immediate
            else
              illegal_insn_o = 1'b1;
          end

          default: illegal_insn_o = 1'b1;
        endcase
      end

      OPCODE_OP: begin  // Register-Register ALU operation
        regfile_alu_we = 1'b1;
        rega_used_o    = 1'b1;

        if (instr_rdata_i[31]) begin
          // bit-manipulation instructions
          alu_op_b_mux_sel_o  = OP_B_IMM;
          bmask_needed_o      = 1'b1;
          bmask_a_mux_o       = BMASK_A_S3;
          bmask_b_mux_o       = BMASK_B_S2;

          unique case (instr_rdata_i[14:12])
            3'b000: begin
              alu_operator_o  = ALU_BEXT;
              imm_b_mux_sel_o = IMMB_S2;
              bmask_b_mux_o   = BMASK_B_ZERO;
            end
            3'b001: begin
              alu_operator_o  = ALU_BEXTU;
              imm_b_mux_sel_o = IMMB_S2;
              bmask_b_mux_o   = BMASK_B_ZERO;
            end

            3'b010: begin
              alu_operator_o      = ALU_BINS;
              imm_b_mux_sel_o     = IMMB_S2;
              regc_used_o         = 1'b1;
              regc_mux_o          = REGC_RD;
            end

            3'b011: begin alu_operator_o = ALU_BCLR; end
            3'b100: begin alu_operator_o = ALU_BSET; end

            default: illegal_insn_o = 1'b1;
          endcase
        end
        else
        begin // non bit-manipulation instructions

          if (~instr_rdata_i[28])
            regb_used_o = 1'b1;

          unique case ({instr_rdata_i[30:25], instr_rdata_i[14:12]})
            // RV32I ALU operations
            {6'b00_0000, 3'b000}: alu_operator_o = ALU_ADD;   // Add
            {6'b10_0000, 3'b000}: alu_operator_o = ALU_SUB;   // Sub
            {6'b00_0000, 3'b010}: alu_operator_o = ALU_SLTS;  // Set Lower Than
            {6'b00_0000, 3'b011}: alu_operator_o = ALU_SLTU;  // Set Lower Than Unsigned
            {6'b00_0000, 3'b100}: alu_operator_o = ALU_XOR;   // Xor
            {6'b00_0000, 3'b110}: alu_operator_o = ALU_OR;    // Or
            {6'b00_0000, 3'b111}: alu_operator_o = ALU_AND;   // And
            {6'b00_0000, 3'b001}: alu_operator_o = ALU_SLL;   // Shift Left Logical
            {6'b00_0000, 3'b101}: alu_operator_o = ALU_SRL;   // Shift Right Logical
            {6'b10_0000, 3'b101}: alu_operator_o = ALU_SRA;   // Shift Right Arithmetic

            // supported RV32M instructions
            {6'b00_0001, 3'b000}: begin // mul
              mult_int_en_o   = 1'b1;
              mult_operator_o = MUL_MAC32;
              regc_mux_o      = REGC_ZERO;
            end
            {6'b00_0001, 3'b001}: begin // mulh
              regc_used_o        = 1'b1;
              regc_mux_o         = REGC_ZERO;
              mult_signed_mode_o = 2'b11;
              mult_int_en_o      = 1'b1;
              mult_operator_o    = MUL_H;
            end
            {6'b00_0001, 3'b010}: begin // mulhsu
              regc_used_o        = 1'b1;
              regc_mux_o         = REGC_ZERO;
              mult_signed_mode_o = 2'b01;
              mult_int_en_o      = 1'b1;
              mult_operator_o    = MUL_H;
            end
            {6'b00_0001, 3'b011}: begin // mulhu
              regc_used_o        = 1'b1;
              regc_mux_o         = REGC_ZERO;
              mult_signed_mode_o = 2'b00;
              mult_int_en_o      = 1'b1;
              mult_operator_o    = MUL_H;
            end
            {6'b00_0001, 3'b100}: begin // div
              alu_op_a_mux_sel_o = OP_A_REGB_OR_FWD;
              alu_op_b_mux_sel_o = OP_B_REGC_OR_FWD;
              regc_mux_o         = REGC_S1;
              regc_used_o        = 1'b1;
              regb_used_o        = 1'b1;
              rega_used_o        = 1'b0;
              alu_operator_o     = ALU_DIV;
            end
            {6'b00_0001, 3'b101}: begin // divu
              alu_op_a_mux_sel_o = OP_A_REGB_OR_FWD;
              alu_op_b_mux_sel_o = OP_B_REGC_OR_FWD;
              regc_mux_o         = REGC_S1;
              regc_used_o        = 1'b1;
              regb_used_o        = 1'b1;
              rega_used_o        = 1'b0;
              alu_operator_o = ALU_DIVU;
            end
            {6'b00_0001, 3'b110}: begin // rem
              alu_op_a_mux_sel_o = OP_A_REGB_OR_FWD;
              alu_op_b_mux_sel_o = OP_B_REGC_OR_FWD;
              regc_mux_o         = REGC_S1;
              regc_used_o        = 1'b1;
              regb_used_o        = 1'b1;
              rega_used_o        = 1'b0;
              alu_operator_o = ALU_REM;
            end
            {6'b00_0001, 3'b111}: begin // remu
              alu_op_a_mux_sel_o = OP_A_REGB_OR_FWD;
              alu_op_b_mux_sel_o = OP_B_REGC_OR_FWD;
              regc_mux_o         = REGC_S1;
              regc_used_o        = 1'b1;
              regb_used_o        = 1'b1;
              rega_used_o        = 1'b0;
              alu_operator_o = ALU_REMU;
            end

            // PULP specific instructions
            {6'b10_0001, 3'b000}: begin // p.mac
              regc_used_o     = 1'b1;
              regc_mux_o      = REGC_RD;
              mult_int_en_o   = 1'b1;
              mult_operator_o = MUL_MAC32;
            end
            {6'b10_0001, 3'b001}: begin // p.msu
              regc_used_o     = 1'b1;
              regc_mux_o      = REGC_RD;
              mult_int_en_o   = 1'b1;
              mult_operator_o = MUL_MSU32;
            end

            {6'b00_0010, 3'b010}: alu_operator_o = ALU_SLETS; // Set Lower Equal Than
            {6'b00_0010, 3'b011}: alu_operator_o = ALU_SLETU; // Set Lower Equal Than Unsigned
            {6'b00_0010, 3'b100}: alu_operator_o = ALU_MIN;   // Min
            {6'b00_0010, 3'b101}: alu_operator_o = ALU_MINU;  // Min Unsigned
            {6'b00_0010, 3'b110}: alu_operator_o = ALU_MAX;   // Max
            {6'b00_0010, 3'b111}: alu_operator_o = ALU_MAXU;  // Max Unsigned

            {6'b00_0100, 3'b101}: alu_operator_o = ALU_ROR;   // Rotate Right

            // PULP specific instructions using only one source register
            {6'b00_1000, 3'b000}: alu_operator_o = ALU_FF1;   // Find First 1
            {6'b00_1000, 3'b001}: alu_operator_o = ALU_FL1;   // Find Last 1
            {6'b00_1000, 3'b010}: alu_operator_o = ALU_CLB;   // Count Leading Bits
            {6'b00_1000, 3'b011}: alu_operator_o = ALU_CNT;   // Count set bits (popcount)
            {6'b00_1000, 3'b100}: begin alu_operator_o = ALU_EXTS; alu_vec_mode_o = VEC_MODE16; end // Sign-extend Half-word
            {6'b00_1000, 3'b101}: begin alu_operator_o = ALU_EXT;  alu_vec_mode_o = VEC_MODE16; end // Zero-extend Half-word
            {6'b00_1000, 3'b110}: begin alu_operator_o = ALU_EXTS; alu_vec_mode_o = VEC_MODE8;  end // Sign-extend Byte
            {6'b00_1000, 3'b111}: begin alu_operator_o = ALU_EXT;  alu_vec_mode_o = VEC_MODE8;  end // Zero-extend Byte

            {6'b00_0010, 3'b000}: alu_operator_o = ALU_ABS;   // p.abs

            {6'b00_1010, 3'b001}: begin // p.clip
              alu_operator_o     = ALU_CLIP;
              alu_op_b_mux_sel_o = OP_A_IMM;
              imm_b_mux_sel_o    = IMMB_CLIP;
            end

            {6'b00_1010, 3'b010}: begin // p.clipu
              alu_operator_o     = ALU_CLIPU;
              alu_op_b_mux_sel_o = OP_A_IMM;
              imm_b_mux_sel_o    = IMMB_CLIP;
            end

            default: begin
              illegal_insn_o = 1'b1;
            end
          endcase
        end
      end

      OPCODE_PULP_OP: begin  // PULP specific ALU instructions with three source operands
        regfile_alu_we = 1'b1;
        rega_used_o    = 1'b1;
        regb_used_o    = 1'b1;

        case (instr_rdata_i[13:12])
          2'b00: begin // multiply with subword selection
            mult_sel_subword_o = instr_rdata_i[30];
            mult_signed_mode_o = {2{instr_rdata_i[31]}};

            mult_imm_mux_o = MIMM_S3;
            regc_mux_o     = REGC_ZERO;
            mult_int_en_o  = 1'b1;

            if (instr_rdata_i[14])
              mult_operator_o = MUL_IR;
            else
              mult_operator_o = MUL_I;
          end

          2'b01: begin // MAC with subword selection
            mult_sel_subword_o = instr_rdata_i[30];
            mult_signed_mode_o = {2{instr_rdata_i[31]}};

            regc_used_o     = 1'b1;
            regc_mux_o      = REGC_RD;
            mult_imm_mux_o  = MIMM_S3;
            mult_int_en_o   = 1'b1;

            if (instr_rdata_i[14])
              mult_operator_o = MUL_IR;
            else
              mult_operator_o = MUL_I;
          end

          2'b10: begin // add with normalization and rounding
            // decide between using unsigned and rounding, and combinations
            // thereof
            case ({instr_rdata_i[31],instr_rdata_i[14]})
              2'b00: alu_operator_o = ALU_ADD;
              2'b01: alu_operator_o = ALU_ADDR;
              2'b10: alu_operator_o = ALU_ADDU;
              2'b11: alu_operator_o = ALU_ADDUR;
            endcase

            bmask_a_mux_o = BMASK_A_ZERO;
            bmask_b_mux_o = BMASK_B_S3;
          end

          2'b11: begin // sub with normalization and rounding
            // decide between using unsigned and rounding, and combinations
            // thereof
            case ({instr_rdata_i[31],instr_rdata_i[14]})
              2'b00: alu_operator_o = ALU_SUB;
              2'b01: alu_operator_o = ALU_SUBR;
              2'b10: alu_operator_o = ALU_SUBU;
              2'b11: alu_operator_o = ALU_SUBUR;
            endcase

            bmask_a_mux_o = BMASK_A_ZERO;
            bmask_b_mux_o = BMASK_B_S3;
          end

          default: begin
            regfile_alu_we = 1'b0;
            illegal_insn_o = 1'b1;
          end
        endcase
      end

      OPCODE_VECOP: begin
        regfile_alu_we      = 1'b1;
        rega_used_o         = 1'b1;
        imm_b_mux_sel_o     = IMMB_VS;

        // vector size
        if (instr_rdata_i[12]) begin
          alu_vec_mode_o  = VEC_MODE8;
          mult_operator_o = MUL_DOT8;
        end else begin
          alu_vec_mode_o = VEC_MODE16;
          mult_operator_o = MUL_DOT16;
        end

        // distinguish normal vector, sc and sci modes
        if (instr_rdata_i[14]) begin
          scalar_replication_o = 1'b1;

          if (instr_rdata_i[13]) begin
            // immediate scalar replication, .sci
            alu_op_b_mux_sel_o = OP_B_IMM;
          end else begin
            // register scalar replication, .sc
            regb_used_o = 1'b1;
          end
        end else begin
          // normal register use
          regb_used_o = 1'b1;
        end

        // now decode the instruction
        unique case (instr_rdata_i[31:26])
          6'b00000_0: begin alu_operator_o = ALU_ADD;  imm_b_mux_sel_o = IMMB_VS; end // pv.add
          6'b00001_0: begin alu_operator_o = ALU_SUB;  imm_b_mux_sel_o = IMMB_VS; end // pv.sub
          6'b00010_0: begin alu_operator_o = ALU_ADD;  imm_b_mux_sel_o = IMMB_VS; bmask_b_mux_o = BMASK_B_ONE; end // pv.avg
          6'b00011_0: begin alu_operator_o = ALU_ADDU; imm_b_mux_sel_o = IMMB_VU; bmask_b_mux_o = BMASK_B_ONE; end // pv.avgu
          6'b00100_0: begin alu_operator_o = ALU_MIN;  imm_b_mux_sel_o = IMMB_VS; end // pv.min
          6'b00101_0: begin alu_operator_o = ALU_MINU; imm_b_mux_sel_o = IMMB_VU; end // pv.minu
          6'b00110_0: begin alu_operator_o = ALU_MAX;  imm_b_mux_sel_o = IMMB_VS; end // pv.max
          6'b00111_0: begin alu_operator_o = ALU_MAXU; imm_b_mux_sel_o = IMMB_VU; end // pv.maxu
          6'b01000_0: begin alu_operator_o = ALU_SRL;  imm_b_mux_sel_o = IMMB_VS; end // pv.srl
          6'b01001_0: begin alu_operator_o = ALU_SRA;  imm_b_mux_sel_o = IMMB_VS; end // pv.sra
          6'b01010_0: begin alu_operator_o = ALU_SLL;  imm_b_mux_sel_o = IMMB_VS; end // pv.sll
          6'b01011_0: begin alu_operator_o = ALU_OR;   imm_b_mux_sel_o = IMMB_VS; end // pv.or
          6'b01100_0: begin alu_operator_o = ALU_XOR;  imm_b_mux_sel_o = IMMB_VS; end // pv.xor
          6'b01101_0: begin alu_operator_o = ALU_AND;  imm_b_mux_sel_o = IMMB_VS; end // pv.and
          6'b01110_0: begin alu_operator_o = ALU_ABS;  imm_b_mux_sel_o = IMMB_VS; end // pv.abs

          // shuffle/pack
          6'b11101_0,       // pv.shuffleI1
          6'b11110_0,       // pv.shuffleI2
          6'b11111_0,       // pv.shuffleI3
          6'b11000_0: begin // pv.shuffle, pv.shuffleI0
            alu_operator_o       = ALU_SHUF;
            imm_b_mux_sel_o      = IMMB_SHUF;
            regb_used_o          = 1'b1;
            scalar_replication_o = 1'b0;
          end
          6'b11001_0: begin // pv.shuffle2
            alu_operator_o       = ALU_SHUF2;
            regb_used_o          = 1'b1;
            regc_used_o          = 1'b1;
            regc_mux_o           = REGC_RD;
            scalar_replication_o = 1'b0;
          end
          6'b11010_0: begin // pv.pack
            alu_operator_o = ALU_PCKLO;
            regb_used_o    = 1'b1;
          end
          6'b11011_0: begin // pv.packhi
            alu_operator_o = ALU_PCKHI;
            regb_used_o    = 1'b1;
            regc_used_o    = 1'b1;
            regc_mux_o     = REGC_RD;
          end
          6'b11100_0: begin // pv.packlo
            alu_operator_o = ALU_PCKLO;
            regb_used_o    = 1'b1;
            regc_used_o    = 1'b1;
            regc_mux_o     = REGC_RD;
          end

          6'b01111_0: begin // pv.extract
            alu_operator_o = ALU_EXTS;
          end

          6'b10010_0: begin // pv.extractu
            alu_operator_o = ALU_EXT;
          end

          6'b10110_0: begin // pv.insert
            alu_operator_o     = ALU_INS;
            regc_used_o        = 1'b1;
            regc_mux_o         = REGC_RD;
            alu_op_b_mux_sel_o = OP_B_REGC_OR_FWD;
          end

          6'b10000_0: begin // pv.dotup
            mult_dot_en_o     = 1'b1;
            mult_dot_signed_o = 2'b00;
          end
          6'b10001_0: begin // pv.dotusp
            mult_dot_en_o     = 1'b1;
            mult_dot_signed_o = 2'b01;
          end
          6'b10011_0: begin // pv.dotsp
            mult_dot_en_o     = 1'b1;
            mult_dot_signed_o = 2'b11;
          end
          6'b10100_0: begin // pv.sdotup
            mult_dot_en_o     = 1'b1;
            mult_dot_signed_o = 2'b00;
            regc_used_o       = 1'b1;
            regc_mux_o        = REGC_RD;
          end
          6'b10101_0: begin // pv.sdotusp
            mult_dot_en_o     = 1'b1;
            mult_dot_signed_o = 2'b01;
            regc_used_o       = 1'b1;
            regc_mux_o        = REGC_RD;
          end
          6'b10111_0: begin // pv.sdotsp
            mult_dot_en_o     = 1'b1;
            mult_dot_signed_o = 2'b11;
            regc_used_o       = 1'b1;
            regc_mux_o        = REGC_RD;
          end

          // comparisons, always have bit 26 set
          6'b00000_1: begin alu_operator_o = ALU_EQ;  imm_b_mux_sel_o     = IMMB_VS; end // pv.cmpeq
          6'b00001_1: begin alu_operator_o = ALU_NE;  imm_b_mux_sel_o     = IMMB_VS; end // pv.cmpne
          6'b00010_1: begin alu_operator_o = ALU_GTS; imm_b_mux_sel_o     = IMMB_VS; end // pv.cmpgt
          6'b00011_1: begin alu_operator_o = ALU_GES; imm_b_mux_sel_o     = IMMB_VS; end // pv.cmpge
          6'b00100_1: begin alu_operator_o = ALU_LTS; imm_b_mux_sel_o     = IMMB_VS; end // pv.cmplt
          6'b00101_1: begin alu_operator_o = ALU_LES; imm_b_mux_sel_o     = IMMB_VS; end // pv.cmple
          6'b00110_1: begin alu_operator_o = ALU_GTU; imm_b_mux_sel_o     = IMMB_VU; end // pv.cmpgtu
          6'b00111_1: begin alu_operator_o = ALU_GEU; imm_b_mux_sel_o     = IMMB_VU; end // pv.cmpgeu
          6'b01000_1: begin alu_operator_o = ALU_LTU; imm_b_mux_sel_o     = IMMB_VU; end // pv.cmpltu
          6'b01001_1: begin alu_operator_o = ALU_LEU; imm_b_mux_sel_o     = IMMB_VU; end // pv.cmpleu

          default: illegal_insn_o = 1'b1;
        endcase
      end


      ////////////////////////////////////////////////
      //  ____  ____  _____ ____ ___    _    _      //
      // / ___||  _ \| ____/ ___|_ _|  / \  | |     //
      // \___ \| |_) |  _|| |    | |  / _ \ | |     //
      //  ___) |  __/| |__| |___ | | / ___ \| |___  //
      // |____/|_|   |_____\____|___/_/   \_\_____| //
      //                                            //
      ////////////////////////////////////////////////

      OPCODE_SYSTEM: begin
        if (instr_rdata_i[14:12] == 3'b000)
        begin
          // non CSR related SYSTEM instructions
          unique case (instr_rdata_i[31:0])
            32'h00_00_00_73:  // ECALL
            begin
              // environment (system) call
              ecall_insn_o = 1'b1;
            end

            32'h00_10_00_73:  // ebreak
            begin
              // debugger trap
              ebrk_insn = 1'b1;
            end

            32'h10_00_00_73:  // eret
            begin
              eret_insn = 1'b1;
            end

            32'h10_20_00_73:  // wfi
            begin
              // flush pipeline
              pipe_flush = 1'b1;
            end

            default:
            begin
              illegal_insn_o = 1'b1;
            end
          endcase
        end
        else
        begin
          // instruction to read/modify CSR
          csr_access_o        = 1'b1;
          regfile_alu_we      = 1'b1;
          alu_op_b_mux_sel_o  = OP_B_IMM;
          imm_a_mux_sel_o     = IMMA_Z;
          imm_b_mux_sel_o     = IMMB_I;    // CSR address is encoded in I imm

          if (instr_rdata_i[14] == 1'b1) begin
            // rs1 field is used as immediate
            alu_op_a_mux_sel_o = OP_A_IMM;
          end else begin
            rega_used_o        = 1'b1;
            alu_op_a_mux_sel_o = OP_A_REGA_OR_FWD;
          end

          unique case (instr_rdata_i[13:12])
            2'b01:   csr_op   = CSR_OP_WRITE;
            2'b10:   csr_op   = CSR_OP_SET;
            2'b11:   csr_op   = CSR_OP_CLEAR;
            default: illegal_insn_o = 1'b1;
          endcase
        end

      end


      ///////////////////////////////////////////////
      //  _   ___        ___     ___   ___  ____   //
      // | | | \ \      / / |   / _ \ / _ \|  _ \  //
      // | |_| |\ \ /\ / /| |  | | | | | | | |_) | //
      // |  _  | \ V  V / | |__| |_| | |_| |  __/  //
      // |_| |_|  \_/\_/  |_____\___/ \___/|_|     //
      //                                           //
      ///////////////////////////////////////////////

      OPCODE_HWLOOP: begin
        hwloop_target_mux_sel_o = 1'b0;

        unique case (instr_rdata_i[14:12])
          3'b000: begin
            // lp.starti: set start address to PC + I-type immediate
            hwloop_we[0]           = 1'b1;
            hwloop_start_mux_sel_o = 1'b0;
          end

          3'b001: begin
            // lp.endi: set end address to PC + I-type immediate
            hwloop_we[1]         = 1'b1;
          end

          3'b010: begin
            // lp.count: initialize counter from rs1
            hwloop_we[2]         = 1'b1;
            hwloop_cnt_mux_sel_o = 1'b1;
            rega_used_o          = 1'b1;
          end

          3'b011: begin
            // lp.counti: initialize counter from I-type immediate
            hwloop_we[2]         = 1'b1;
            hwloop_cnt_mux_sel_o = 1'b0;
          end

          3'b100: begin
            // lp.setup: initialize counter from rs1, set start address to
            // next instruction and end address to PC + I-type immediate
            hwloop_we              = 3'b111;
            hwloop_start_mux_sel_o = 1'b1;
            hwloop_cnt_mux_sel_o   = 1'b1;
            rega_used_o            = 1'b1;
          end

          3'b101: begin
            // lp.setupi: initialize counter from immediate, set start address to
            // next instruction and end address to PC + I-type immediate
            hwloop_we               = 3'b111;
            hwloop_target_mux_sel_o = 1'b1;
            hwloop_start_mux_sel_o  = 1'b1;
            hwloop_cnt_mux_sel_o    = 1'b0;
          end

          default: begin
            illegal_insn_o = 1'b1;
          end
        endcase
      end

      default: begin
        illegal_insn_o = 1'b1;
      end
    endcase

    // make sure invalid compressed instruction causes an exception
    if (illegal_c_insn_i) begin
      illegal_insn_o = 1'b1;
    end

    // misaligned access was detected by the LSU
    // TODO: this section should eventually be moved out of the decoder
    if (data_misaligned_i == 1'b1)
    begin
      // only part of the pipeline is unstalled, make sure that the
      // correct operands are sent to the AGU
      alu_op_a_mux_sel_o  = OP_A_REGA_OR_FWD;
      alu_op_b_mux_sel_o  = OP_B_IMM;
      imm_b_mux_sel_o     = IMMB_PCINCR;

      // if prepost increments are used, we do not write back the
      // second address since the first calculated address was
      // the correct one
      regfile_alu_we = 1'b0;

      // if post increments are used, we must make sure that for
      // the second memory access we do use the adder
      prepost_useincr_o = 1'b1;
      // we do not want to replicate operand_b
      scalar_replication_o = 1'b0;
    end else if (mult_multicycle_i) begin
      alu_op_c_mux_sel_o = OP_C_REGC_OR_FWD;
    end
  end

  // deassert we signals (in case of stalls)
  assign regfile_mem_we_o  = (deassert_we_i) ? 1'b0          : regfile_mem_we;
  assign regfile_alu_we_o  = (deassert_we_i) ? 1'b0          : regfile_alu_we;
  assign data_req_o        = (deassert_we_i) ? 1'b0          : data_req;
  assign hwloop_we_o       = (deassert_we_i) ? 3'b0          : hwloop_we;
  assign csr_op_o          = (deassert_we_i) ? CSR_OP_NONE  : csr_op;
  assign jump_in_id_o      = (deassert_we_i) ? BRANCH_NONE  : jump_in_id;
  assign ebrk_insn_o       = (deassert_we_i) ? 1'b0          : ebrk_insn;
  assign eret_insn_o       = (deassert_we_i) ? 1'b0          : eret_insn;  // TODO: do not deassert?
  assign pipe_flush_o      = (deassert_we_i) ? 1'b0          : pipe_flush; // TODO: do not deassert?

  assign jump_in_dec_o     = jump_in_id;

endmodule // controller
