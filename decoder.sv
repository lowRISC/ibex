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

`include "riscv_defines.sv"

module riscv_decoder
(
  // singals running to/from controller
  input  logic        deassert_we_i,           // deassert we, we are stalled or not active
  input  logic        data_misaligned_i,       // misaligned data load/store in progress

  output logic        illegal_insn_o,          // illegal instruction encountered
  output logic        trap_insn_o,             // trap instruction encountered
  output logic        eret_insn_o,             // return from exception instruction encountered
  output logic        ecall_insn_o,            // environment call (syscall) instruction encountered
  output logic        pipe_flush_o,            // pipeline flush is requested

  output logic        rega_used_o,             // rs1 is used by current instruction
  output logic        regb_used_o,             // rs2 is used by current instruction
  output logic        regc_used_o,             // rs3 is used by current instruction

  // from IF/ID pipeline
  input  logic [31:0] instr_rdata_i,           // instruction read from instr memory/cache
  input  logic        illegal_c_insn_i,        // compressed instruction decode failed

  // ALU signals
  output logic [`ALU_OP_WIDTH-1:0] alu_operator_o, // ALU operation selection
  output logic [1:0]  alu_op_a_mux_sel_o,      // operand a selection: reg value, PC, immediate or zero
  output logic [1:0]  alu_op_b_mux_sel_o,      // operand b selection: reg value or immediate
  output logic [1:0]  alu_op_c_mux_sel_o,      // operand c selection: reg value or jump target
  output logic [2:0]  immediate_mux_sel_o,     // immediate selection for operand b

  output logic        vector_mode_o,           // selects between 32 bit, 16 bit and 8 bit vectorial modes

  // MUL related control signals
  output logic        mult_en_o,               // perform multiplication
  output logic        mult_mac_en_o,           // accumulate multiplication result
  output logic [1:0]  mult_sel_subword_o,      // Select subwords for 16x16 bit of multiplier
  output logic [1:0]  mult_signed_mode_o,      // Multiplication in signed mode

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

  logic       trap_insn;
  logic       eret_insn;
  logic       pipe_flush;

  logic [1:0] jump_in_id;

  logic [`ALU_OP_WIDTH-1:0] alu_operator;
  logic       mult_en;
  logic       mult_mac_en;
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
    jump_in_id                  = `BRANCH_NONE;
    jump_target_mux_sel_o       = `JT_JAL;

    alu_operator                = `ALU_NOP;
    alu_op_a_mux_sel_o          = `OP_A_REGA_OR_FWD;
    alu_op_b_mux_sel_o          = `OP_B_REGB_OR_FWD;
    alu_op_c_mux_sel_o          = `OP_C_REGC_OR_FWD;

    immediate_mux_sel_o         = `IMM_I;

    vector_mode_o               = 1'b0;

    mult_en                     = 1'b0;
    mult_signed_mode_o          = 2'b00;
    mult_sel_subword_o          = 2'b00;
    mult_mac_en                 = 1'b0;

    regfile_mem_we              = 1'b0;
    regfile_alu_we              = 1'b0;
    regfile_alu_waddr_sel_o     = 1'b1;

    prepost_useincr_o           = 1'b1;

    hwloop_we                   = 3'b0;
    hwloop_target_mux_sel_o     = 1'b0;
    hwloop_start_mux_sel_o      = 1'b0;
    hwloop_cnt_mux_sel_o        = 1'b0;

    csr_access_o                = 1'b0;
    csr_op                      = `CSR_OP_NONE;

    data_we_o                   = 1'b0;
    data_type_o                 = 2'b00;
    data_sign_extension_o       = 1'b0;
    data_reg_offset_o           = 2'b00;
    data_req                    = 1'b0;

    illegal_insn_o              = 1'b0;
    trap_insn                   = 1'b0;
    eret_insn                   = 1'b0;
    ecall_insn_o                = 1'b0;
    pipe_flush                  = 1'b0;

    rega_used_o                 = 1'b0;
    regb_used_o                 = 1'b0;
    regc_used_o                 = 1'b0;


    unique case (instr_rdata_i[6:0])

      //////////////////////////////////////
      //      _ _   _ __  __ ____  ____   //
      //     | | | | |  \/  |  _ \/ ___|  //
      //  _  | | | | | |\/| | |_) \___ \  //
      // | |_| | |_| | |  | |  __/ ___) | //
      //  \___/ \___/|_|  |_|_|   |____/  //
      //                                  //
      //////////////////////////////////////

      `OPCODE_JAL: begin   // Jump and Link
        jump_target_mux_sel_o = `JT_JAL;
        jump_in_id            = `BRANCH_JAL;
        // Calculate and store PC+4
        alu_op_a_mux_sel_o  = `OP_A_CURRPC;
        alu_op_b_mux_sel_o  = `OP_B_IMM;
        immediate_mux_sel_o = `IMM_PCINCR;
        alu_operator        = `ALU_ADD;
        regfile_alu_we      = 1'b1;
        // Calculate jump target (= PC + UJ imm)
        alu_op_c_mux_sel_o  = `OP_C_JT;
      end

      `OPCODE_JALR: begin  // Jump and Link Register
        jump_target_mux_sel_o = `JT_JALR;
        jump_in_id            = `BRANCH_JALR;
        // Calculate and store PC+4
        alu_op_a_mux_sel_o  = `OP_A_CURRPC;
        alu_op_b_mux_sel_o  = `OP_B_IMM;
        immediate_mux_sel_o = `IMM_PCINCR;
        alu_operator        = `ALU_ADD;
        regfile_alu_we      = 1'b1;
        // Calculate jump target (= RS1 + I imm)
        rega_used_o         = 1'b1;
        alu_op_c_mux_sel_o  = `OP_C_JT;

        if (instr_rdata_i[14:12] != 3'b0) begin
          jump_in_id       = `BRANCH_NONE;
          regfile_alu_we   = 1'b0;
          illegal_insn_o   = 1'b0;
        end
      end

      `OPCODE_BRANCH: begin // Branch
        jump_target_mux_sel_o = `JT_COND;
        jump_in_id            = `BRANCH_COND;
        alu_op_c_mux_sel_o    = `OP_C_JT;
        rega_used_o           = 1'b1;
        regb_used_o           = 1'b1;

        unique case (instr_rdata_i[14:12])
          3'b000: alu_operator = `ALU_EQ;
          3'b001: alu_operator = `ALU_NE;
          3'b100: alu_operator = `ALU_LTS;
          3'b101: alu_operator = `ALU_GES;
          3'b110: alu_operator = `ALU_LTU;
          3'b111: alu_operator = `ALU_GEU;

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

      `OPCODE_STORE,
      `OPCODE_STORE_POST: begin
        data_req     = 1'b1;
        data_we_o    = 1'b1;
        rega_used_o  = 1'b1;
        regb_used_o  = 1'b1;
        alu_operator = `ALU_ADD;

        // pass write data through ALU operand c
        alu_op_c_mux_sel_o = `OP_C_REGB_OR_FWD;

        // post-increment setup
        if (instr_rdata_i[6:0] == `OPCODE_STORE_POST) begin
          prepost_useincr_o       = 1'b0;
          regfile_alu_waddr_sel_o = 1'b0;
          regfile_alu_we          = 1'b1;
        end

        if (instr_rdata_i[14] == 1'b0) begin
          // offset from immediate
          immediate_mux_sel_o = `IMM_S;
          alu_op_b_mux_sel_o  = `OP_B_IMM;
        end else begin
          // offset from register
          regc_used_o        = 1'b1;
          alu_op_b_mux_sel_o = `OP_B_REGC_OR_FWD;
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

      `OPCODE_LOAD,
      `OPCODE_LOAD_POST: begin
        data_req        = 1'b1;
        regfile_mem_we  = 1'b1;
        rega_used_o     = 1'b1;
        data_type_o     = 2'b00;

        // offset from immediate
        alu_operator        = `ALU_ADD;
        alu_op_b_mux_sel_o  = `OP_B_IMM;
        immediate_mux_sel_o = `IMM_I;

        // post-increment setup
        if (instr_rdata_i[6:0] == `OPCODE_LOAD_POST) begin
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
          alu_op_b_mux_sel_o = `OP_B_REGB_OR_FWD;

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
              data_type_o    = 2'b00;
              // illegal instruction
              data_req       = 1'b0;
              regfile_mem_we = 1'b0;
              regfile_alu_we = 1'b0;
              illegal_insn_o = 1'b1;
            end
          endcase
        end

        if (instr_rdata_i[14:12] == 3'b011 || instr_rdata_i[14:12] == 3'b110)
        begin
          // LD, LWU -> RV64 only
          data_req       = 1'b0;
          regfile_mem_we = 1'b0;
          regfile_alu_we = 1'b0;
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

      `OPCODE_LUI: begin  // Load Upper Immediate
        alu_op_a_mux_sel_o  = `OP_A_ZERO;
        alu_op_b_mux_sel_o  = `OP_B_IMM;
        immediate_mux_sel_o = `IMM_U;
        alu_operator        = `ALU_ADD;
        regfile_alu_we      = 1'b1;
      end

      `OPCODE_AUIPC: begin  // Add Upper Immediate to PC
        alu_op_a_mux_sel_o  = `OP_A_CURRPC;
        alu_op_b_mux_sel_o  = `OP_B_IMM;
        immediate_mux_sel_o = `IMM_U;
        alu_operator        = `ALU_ADD;
        regfile_alu_we      = 1'b1;
      end

      `OPCODE_OPIMM: begin // Reigster-Immediate ALU Operations
        alu_op_b_mux_sel_o  = `OP_B_IMM;
        immediate_mux_sel_o = `IMM_I;
        regfile_alu_we      = 1'b1;
        rega_used_o         = 1'b1;

        unique case (instr_rdata_i[14:12])
          3'b000: alu_operator = `ALU_ADD;  // Add Immediate
          3'b010: alu_operator = `ALU_SLTS; // Set to one if Lower Than Immediate
          3'b011: alu_operator = `ALU_SLTU; // Set to one if Lower Than Immediate Unsigned
          3'b100: alu_operator = `ALU_XOR;  // Exclusive Or with Immediate
          3'b110: alu_operator = `ALU_OR;   // Or with Immediate
          3'b111: alu_operator = `ALU_AND;  // And with Immediate

          3'b001: begin
            alu_operator = `ALU_SLL;  // Shift Left Logical by Immediate
            if (instr_rdata_i[31:25] != 7'b0)
              illegal_insn_o = 1'b1;
          end

          3'b101: begin
            if (instr_rdata_i[31:25] == 7'b0)
              alu_operator = `ALU_SRL;  // Shift Right Logical by Immediate
            else if (instr_rdata_i[31:25] == 7'b010_0000)
              alu_operator = `ALU_SRA;  // Shift Right Arithmetically by Immediate
            else
              illegal_insn_o = 1'b1;
          end

          default: illegal_insn_o = 1'b1;
        endcase
      end

      `OPCODE_OP: begin  // Register-Register ALU operation
        regfile_alu_we = 1'b1;
        rega_used_o    = 1'b1;
        regb_used_o    = 1'b1;

        if (instr_rdata_i[28])
          regb_used_o  = 1'b0;

        unique case ({instr_rdata_i[31:25], instr_rdata_i[14:12]})
          // RV32I ALU operations
          {7'b000_0000, 3'b000}: alu_operator = `ALU_ADD;   // Add
          {7'b010_0000, 3'b000}: alu_operator = `ALU_SUB;   // Sub
          {7'b000_0000, 3'b010}: alu_operator = `ALU_SLTS;  // Set Lower Than
          {7'b000_0000, 3'b011}: alu_operator = `ALU_SLTU;  // Set Lower Than Unsigned
          {7'b000_0000, 3'b100}: alu_operator = `ALU_XOR;   // Xor
          {7'b000_0000, 3'b110}: alu_operator = `ALU_OR;    // Or
          {7'b000_0000, 3'b111}: alu_operator = `ALU_AND;   // And
          {7'b000_0000, 3'b001}: alu_operator = `ALU_SLL;   // Shift Left Logical
          {7'b000_0000, 3'b101}: alu_operator = `ALU_SRL;   // Shift Right Logical
          {7'b010_0000, 3'b101}: alu_operator = `ALU_SRA;   // Shift Right Arithmetic

          // supported RV32M instructions
          {7'b000_0001, 3'b000}: mult_en      = 1'b1;       // Multiplication

          // PULP specific instructions
          {7'b000_0010, 3'b000}: alu_operator = `ALU_AVG;   // Average
          {7'b000_0010, 3'b001}: alu_operator = `ALU_AVGU;  // Average Unsigned
          {7'b000_0010, 3'b010}: alu_operator = `ALU_SLETS; // Set Lower Equal Than
          {7'b000_0010, 3'b011}: alu_operator = `ALU_SLETU; // Set Lower Equal Than Unsigned
          {7'b000_0010, 3'b100}: alu_operator = `ALU_MIN;   // Min
          {7'b000_0010, 3'b101}: alu_operator = `ALU_MINU;  // Min Unsigned
          {7'b000_0010, 3'b110}: alu_operator = `ALU_MAX;   // Max
          {7'b000_0010, 3'b111}: alu_operator = `ALU_MAXU;  // Max Unsigned

          {7'b000_0100, 3'b101}: alu_operator = `ALU_ROR;   // Rotate Right

          // PULP specific instructions using only one source register
          {7'b000_1000, 3'b000}: alu_operator = `ALU_FF1;   // Find First 1
          {7'b000_1000, 3'b001}: alu_operator = `ALU_FL1;   // Find Last 1
          {7'b000_1000, 3'b010}: alu_operator = `ALU_CLB;   // Count Leading Bits
          {7'b000_1000, 3'b011}: alu_operator = `ALU_CNT;   // Count set bits (popcount)
          {7'b000_1000, 3'b100}: alu_operator = `ALU_EXTHS; // Sign-extend Half-word
          {7'b000_1000, 3'b101}: alu_operator = `ALU_EXTHZ; // Zero-extend Half-word
          {7'b000_1000, 3'b110}: alu_operator = `ALU_EXTBS; // Sign-extend Byte
          {7'b000_1000, 3'b111}: alu_operator = `ALU_EXTBZ; // Zero-extend Byte

          {7'b000_1010, 3'b000}: alu_operator = `ALU_ABS;   // Absolute

          default: begin
            regfile_alu_we = 1'b0;
            illegal_insn_o = 1'b1;
          end
        endcase
      end

      `OPCODE_PULP_OP: begin  // PULP specific ALU instructions with three source operands
        regfile_alu_we = 1'b1;
        rega_used_o    = 1'b1;
        regb_used_o    = 1'b1;
        regc_used_o    = 1'b1;

        case (instr_rdata_i[14:12])
          3'b000: begin // MAC
            mult_en     = 1'b1;
            mult_mac_en = 1'b1;
          end

          3'b100,
          3'b101,
          3'b110,
          3'b111: begin // MAC with subword selection
            vector_mode_o      = 1'b1;
            mult_sel_subword_o = instr_rdata_i[13:12];
            mult_signed_mode_o = instr_rdata_i[31:30];

            mult_en     = 1'b1;
            mult_mac_en = 1'b1;
          end

          default: begin
            regfile_alu_we = 1'b0;
            illegal_insn_o = 1'b1;
          end
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

      `OPCODE_SYSTEM: begin
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
              trap_insn = 1'b1;
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
          alu_op_b_mux_sel_o  = `OP_B_IMM;
          immediate_mux_sel_o = `IMM_I;    // CSR address is encoded in I imm

          if (instr_rdata_i[14] == 1'b1) begin
            // rs1 field is used as immediate
            alu_op_a_mux_sel_o = `OP_A_ZIMM;
          end else begin
            rega_used_o        = 1'b1;
            alu_op_a_mux_sel_o = `OP_A_REGA_OR_FWD;
          end

          unique case (instr_rdata_i[13:12])
            2'b01:   csr_op   = `CSR_OP_WRITE;
            2'b10:   csr_op   = `CSR_OP_SET;
            2'b11:   csr_op   = `CSR_OP_CLEAR;
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

      `OPCODE_HWLOOP: begin
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
      alu_op_a_mux_sel_o  = `OP_A_REGA_OR_FWD;
      alu_op_b_mux_sel_o  = `OP_B_IMM;
      immediate_mux_sel_o = `IMM_PCINCR;

      // if prepost increments are used, we do not write back the
      // second address since the first calculated address was
      // the correct one
      regfile_alu_we  = 1'b0;

      // if post increments are used, we must make sure that for
      // the second memory access we do use the adder
      prepost_useincr_o   = 1'b1;
    end
  end

  // deassert we signals (in case of stalls)
  assign regfile_mem_we_o  = (deassert_we_i) ? 1'b0          : regfile_mem_we;
  assign regfile_alu_we_o  = (deassert_we_i) ? 1'b0          : regfile_alu_we;
  assign data_req_o        = (deassert_we_i) ? 1'b0          : data_req;
  assign alu_operator_o    = (deassert_we_i) ? `ALU_NOP      : alu_operator;
  assign mult_en_o         = (deassert_we_i) ? 1'b0          : mult_en;
  assign mult_mac_en_o     = (deassert_we_i) ? 1'b0          : mult_mac_en;
  assign hwloop_we_o       = (deassert_we_i) ? 3'b0          : hwloop_we;
  assign csr_op_o          = (deassert_we_i) ? `CSR_OP_NONE  : csr_op;
  assign jump_in_id_o      = (deassert_we_i) ? `BRANCH_NONE  : jump_in_id;
  assign trap_insn_o       = (deassert_we_i) ? 1'b0          : trap_insn;
  assign eret_insn_o       = (deassert_we_i) ? 1'b0          : eret_insn;  // TODO: do not deassert?
  assign pipe_flush_o      = (deassert_we_i) ? 1'b0          : pipe_flush; // TODO: do not deassert?

  assign jump_in_dec_o     = jump_in_id;

endmodule // controller
