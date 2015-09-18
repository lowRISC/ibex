////////////////////////////////////////////////////////////////////////////////
// Company:        IIS @ ETHZ - Federal Institute of Technology               //
//                                                                            //
// Engineer        Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                                                                            //
// Additional contributions by:                                               //
//                 Matthias Baer - baermatt@student.ethz.ch                   //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                                                                            //
//                                                                            //
// Create Date:    19/09/2013                                                 //
// Design Name:    RISC-V processor core                                      //
// Module Name:    decoder.sv                                                 //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Decoder                                                    //
//                                                                            //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - File Created, separated controller and decoder             //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

`include "defines.sv"

module riscv_decoder
(
  // singals running to/from controller
  input  logic        deassert_we_i,              // deassert we, we are stalled or not active
  input  logic        data_misaligned_i,          // misaligned data load/store in progress

  output logic        illegal_insn_o,             // illegal instruction encountered
  output logic        trap_insn_o,                // trap instruction encountered
  output logic        eret_insn_o,                // trap instruction encountered
  output logic        pipe_flush_o,               // pipeline flush is requested (e.g. WFI instruction)

  output logic        rega_used_o,                // register A is used by current instruction
  output logic        regb_used_o,                // register B is used by current instruction
  output logic        regc_used_o,                // register C is used by current instruction


  // from IF/ID pipeline
  input  logic [31:0] instr_rdata_i,              // Instruction read from instr memory/cache: (sampled in the if stage)
  input  logic        illegal_c_insn_i,           // compressed instruction decode failed

  // ALU signals
  output logic [`ALU_OP_WIDTH-1:0] alu_operator_o,             // Operator in the EX stage for the ALU block
  output logic [1:0]               alu_op_a_mux_sel_o,         // Operator a is selected between reg value, PC or immediate
  output logic [1:0]               alu_op_b_mux_sel_o,         // Operator b is selected between reg value or immediate
  output logic                     alu_op_c_mux_sel_o,         // Operator c is selected between reg value or PC
  output logic [2:0]               immediate_mux_sel_o,

  output logic [1:0]               vector_mode_o,              // selects between 32 bit, 16 bit and 8 bit vectorial modes
  output logic                     scalar_replication_o,       // activates scalar_replication for vectorial mode
  output logic [1:0]               alu_cmp_mode_o,             // selects comparison mode for ALU (i.e. full, any, all)

  // MUL related control signals
  output logic        mult_en_o,                   // Perform a multiplication operation
  output logic [1:0]  mult_sel_subword_o,          // Select subwords for 16x16 bit of multiplier
  output logic [1:0]  mult_signed_mode_o,          // Multiplication in signed mode
  output logic        mult_mac_en_o,               // Use the accumulator after multiplication

  // register file related signals
  output logic        regfile_mem_we_o,            // Write Enable to regfile
  output logic        regfile_alu_we_o,            // Write Enable to regfile 2nd port
  output logic        regfile_alu_waddr_sel_o,     // Select register write address for ALU/MUL operations

  // CSR manipulation
  output logic        csr_access_o,                // perform an access to CSR
  output logic [1:0]  csr_op_o,                    // operation to perform on CSR

  // LD/ST unit signals
  output logic        data_req_o,                  // Request for a transaction to data memory
  output logic        data_we_o,                   // Write enable to data memory
  output logic        prepost_useincr_o,           // When not active bypass the alu result for address calculation = op_a
  output logic [1:0]  data_type_o,                 // Data type on data memory: byte, half word or word
  output logic        data_sign_extension_o,       // Sign extension on read data from data memory
  output logic [1:0]  data_reg_offset_o,           // Offset in bytes inside register for stores

  // hwloop signals
  output logic [2:0]  hwloop_we_o,                 // write enable for hwloop regs
  output logic        hwloop_start_mux_sel_o,      // selects hwloop start address input
  output logic        hwloop_end_mux_sel_o,        // selects hwloop end address input
  output logic        hwloop_cnt_mux_sel_o,        // selects hwloop counter input

  // jump/branches
  output logic [1:0]  jump_in_dec_o,               // jump_in_id without deassert
  output logic [1:0]  jump_in_id_o,                // jump is being calculated in ALU
  output logic [1:0]  jump_target_mux_sel_o        // jump target selection
);

  // write enable/request control
  logic       regfile_mem_we;
  logic       regfile_alu_we;
  logic       data_req;
  logic       data_we;
  logic [2:0] hwloop_we;

  logic       trap_insn;
  logic       eret_insn;
  logic       pipe_flush;

  logic [1:0] jump_in_id;

  logic [`ALU_OP_WIDTH-1:0] alu_operator;
  logic                     mult_en;
  logic [1:0]               csr_op;


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

    vector_mode_o               = `VEC_MODE32;
    scalar_replication_o        = 1'b0;
    alu_cmp_mode_o              = `ALU_CMP_FULL;

    mult_en                     = 1'b0;
    mult_signed_mode_o          = 2'b00;
    mult_sel_subword_o          = 2'b00;
    mult_mac_en_o               = 1'b0;

    regfile_mem_we              = 1'b0;
    regfile_alu_we              = 1'b0;
    regfile_alu_waddr_sel_o     = 1'b1;

    prepost_useincr_o           = 1'b1;

    hwloop_we                   = 3'b0;
    hwloop_start_mux_sel_o      = 1'b0;
    hwloop_end_mux_sel_o        = 1'b0;
    hwloop_cnt_mux_sel_o        = 1'b0;

    csr_access_o                = 1'b0;
    csr_op                      = `CSR_OP_NONE;

    data_we                     = 1'b0;
    data_type_o                 = 2'b00;
    data_sign_extension_o       = 1'b0;
    data_reg_offset_o           = 2'b00;
    data_req                    = 1'b0;

    illegal_insn_o              = 1'b0;
    trap_insn                   = 1'b0;
    eret_insn                   = 1'b0;
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
        data_we      = 1'b1;
        rega_used_o  = 1'b1;
        regb_used_o  = 1'b1;
        alu_operator = `ALU_ADD;

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
            data_we        = 1'b0;
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
              data_req         = 1'b0;
              regfile_mem_we   = 1'b0;
              regfile_alu_we   = 1'b0;
              illegal_insn_o   = 1'b1;
            end
          endcase
        end

        if (instr_rdata_i[14:12] == 3'b011 || instr_rdata_i[14:12] == 3'b110)
        begin
          // LD, LWU -> RV64 only
          data_req         = 1'b0;
          regfile_mem_we   = 1'b0;
          regfile_alu_we   = 1'b0;
          illegal_insn_o   = 1'b1;
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

        unique case ({instr_rdata_i[31:25], instr_rdata_i[14:12]})
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

          {7'b000_0001, 3'b000}: mult_en      = 1'b1;       // Multiplication

          default: begin
            regfile_alu_we = 1'b0;
            illegal_insn_o = 1'b1;
          end
        endcase
      end

      /*

      `OPCODE_ALU: begin   // Arithmetic Operation
        rega_used_o  = 1'b1;
        regb_used_o  = 1'b1;

        case (instr_rdata_i[9:8])
          2'b00: begin    // ALU Operation
            regfile_alu_we = 1'b1;

            casex (instr_rdata_i[3:0])
              4'b110X: begin // l.ext{b,h,w}{s,z}
                 alu_operator   = {3'b010, instr_rdata_i[7:6], instr_rdata_i[0]};
                 regb_used_o    = 1'b0; // register b is not used
              end
              4'b1111: begin // l.ff1
                alu_operator = `ALU_FF1;
              end
            endcase // casex (instr_rdata_i[3:2])
          end

          2'b01: begin // l.fl1, l.clb, l.cnt
            regfile_alu_we = 1'b1;
            regb_used_o    = 1'b0;

            case (instr_rdata_i[3:0])
              4'b1101: alu_operator = `ALU_CNT;
              4'b1110: alu_operator = `ALU_CLB;
              4'b1111: alu_operator = `ALU_FL1;

              default: begin
                // synopsys translate_off
                $display("%t: Illegal ALU instruction received.", $time);
                // synopsys translate_on
                regfile_alu_we = 1'b0; // disable Write Enable for illegal instruction
                illegal_insn_o = 1'b1;
              end
            endcase //~case(instr_rdata_i[3:0])
          end

          2'b10: begin // Min, Max, Abs, Avg
            regfile_alu_we = 1'b1;

            case (instr_rdata_i[3:0])
              4'b0000: alu_operator = `ALU_MIN;
              4'b0001: alu_operator = `ALU_MINU;
              4'b0010: alu_operator = `ALU_MAX;
              4'b0011: alu_operator = `ALU_MAXU;
              4'b0100: alu_operator = `ALU_AVG;
              4'b0101: alu_operator = `ALU_AVGU;

              4'b1000: begin
                regb_used_o  = 1'b0;
                alu_operator = `ALU_ABS;
              end

              default: begin
                // synopsys translate_off
                $display("%t: Illegal ALU instruction received.", $time);
                // synopsys translate_on
                regfile_alu_we = 1'b0; // disable Write Enable for illegal instruction
                illegal_insn_o = 1'b1;
              end
            endcase //~case(instr_rdata_i[3:0])
          end
        endcase; // case (instr_rdata_i[9:8])
      end

      `OPCODE_MAC: begin   // MAC instruction
        mult_is_running    = 1'b1;

        rega_used_o        = 1'b1;
        regb_used_o        = 1'b1;

        regfile_alu_waddr_sel_o = 2'b01;
        regfile_alu_we          = 1'b1;

        case (instr_rdata_i[6:5])
          2'b00: begin // MAC
            case (instr_rdata_i[3:0])
              4'b1000: begin // l.mac
                mult_mac_en_o = 1'b1;
                regc_used_o   = 1'b1;
                set_carry     = 1'b1;
                set_overflow  = 1'b1;
              end

              4'b1001: begin // l.mac.c
                mult_use_carry_o = 1'b1;
                mult_mac_en_o    = 1'b1;
                regc_used_o      = 1'b1;
                set_carry        = 1'b1;
                set_overflow     = 1'b1;
              end

              default: begin
                // synopsys translate_off
                $display("%t: Illegal MAC instruction received.", $time);
                // synopsys translate_on
                regfile_alu_we = 1'b0;
                illegal_insn_o = 1'b1;
              end
            endcase // case (instr_rdata_i[3:0])
          end

          2'b01: begin // MAC with subword selection
            vector_mode_o      = `VEC_MODE216;
            mult_mac_en_o      = 1'b1;
            regc_used_o        = 1'b1;
            mult_sel_subword_o = instr_rdata_i[2:1];
            mult_signed_mode_o = instr_rdata_i[4:3];
            mult_use_carry_o   = instr_rdata_i[0];
            set_carry          = 1'b1;
            set_overflow       = 1'b1;
          end

          2'b11: begin // mult with subword selection
            vector_mode_o      = `VEC_MODE216;
            mult_sel_subword_o = instr_rdata_i[2:1];
            mult_signed_mode_o = instr_rdata_i[4:3];
          end

          default: begin
            // synopsys translate_off
            $display("%t: Illegal MAC instruction received.", $time);
            // synopsys translate_on
            regfile_alu_we = 1'b0;
            illegal_insn_o = 1'b1;
          end
        endcase
      end

      `OPCODE_VEC: begin // vectorial alu operations
        rega_used_o    = 1'b1;
        regfile_alu_we = 1'b1;

        if (instr_rdata_i[0] == 1'b0) // choose vector size
          vector_mode_o = `VEC_MODE16;
        else
          vector_mode_o = `VEC_MODE8;

        if ((instr_rdata_i[7:6] == 2'b01) || (instr_rdata_i[7:6] == 2'b10)) // replicate scalar 2 or 4 times
          scalar_replication_o = 1'b1;

        if (instr_rdata_i[7:6] == 2'b10) // use immediate as operand b
        begin
          alu_op_b_mux_sel_o   = `OP_B_IMM;
          immediate_mux_sel_o  = `IMM_VEC;
        end
        else
          regb_used_o = 1'b1;

        // now decode the sub opcodes
        case (instr_rdata_i[5:1])
          5'b00000: alu_operator = `ALU_ADD;
          5'b00001: alu_operator = `ALU_SUB;
          5'b00010: alu_operator = `ALU_AVG;
          5'b00011: alu_operator = `ALU_MIN;
          5'b00100: alu_operator = `ALU_MAX;
          5'b00101: alu_operator = `ALU_SRL;
          5'b00110: alu_operator = `ALU_SRA;
          5'b00111: alu_operator = `ALU_SLL;

          5'b01000: begin // lv32.mul
            regfile_alu_waddr_sel_o = 2'b01;
            mult_is_running         = 1'b1;
          end

          5'b01001: alu_operator = `ALU_OR;
          5'b01010: alu_operator = `ALU_XOR;
          5'b01011: alu_operator = `ALU_AND;

          5'b01100: begin // lv32.ins
            alu_operator         = `ALU_INS;
            scalar_replication_o = 1'b1;
          end

          5'b10000: begin // lv32.abs
            regb_used_o  = 1'b0; // abs does not use operand b
            alu_operator = `ALU_ABS;
          end

          5'b10001: begin // lv32.ext
            regb_used_o  = 1'b0;
            alu_operator = `ALU_EXT;
          end

          default: begin // unknown instruction encountered
            regfile_alu_we = 1'b0;
            illegal_insn_o = 1'b1;
            // synopsys translate_off
            $display("%t: Unknown vector opcode 0x%h.", $time, instr_rdata_i[5:1]);
            // synopsys translate_on
          end
        endcase // instr_rdata[5:1]
      end

      `OPCODE_VCMP: begin // Vectorial comparisons, i.e. lv32.cmp_*, lv32.all_*, lv32.any_*
        rega_used_o    = 1'b1;
        regfile_alu_we = 1'b1;

        if (instr_rdata_i[0] == 1'b0) // choose vector size
          vector_mode_o = `VEC_MODE16;
        else
          vector_mode_o = `VEC_MODE8;

        if ((instr_rdata_i[7:6] == 2'b01) || (instr_rdata_i[7:6] == 2'b10)) // replicate scalar 2 or 4 times
          scalar_replication_o = 1'b1;

        if (instr_rdata_i[7:6] == 2'b10) // use immediate as operand b
        begin
          alu_op_b_mux_sel_o   = `OP_B_IMM;
          immediate_mux_sel_o  = `IMM_VEC;
        end
        else
          regb_used_o = 1'b1;

        // now decode the sub opcodes for the ALU
        case (instr_rdata_i[3:1])
          3'b000: alu_operator = `ALU_EQ;
          3'b001: alu_operator = `ALU_NE;
          3'b010: alu_operator = `ALU_GTS;
          3'b011: alu_operator = `ALU_GES;
          3'b100: alu_operator = `ALU_LTS;
          3'b101: alu_operator = `ALU_LES;

          default: begin // unknown instruction encountered
            illegal_insn_o = 1'b1;
            // synopsys translate_off
            $display("%t: Unknown vector opcode 0x%h.", $time, instr_rdata_i[5:1]);
            // synopsys translate_on
          end
        endcase //~case(instr_rdata_i[3:1])

        alu_cmp_mode_o = instr_rdata_i[5:4]; // which kind of comparison do we have here, i.e. full, any, all

        if((instr_rdata_i[5:4] == `ALU_CMP_ANY) || (instr_rdata_i[5:4] == `ALU_CMP_ALL))
          set_flag = 1'b1; // set the flag for lv32.all_* and lv32.any_*
      end

      */


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
              // TODO: Handle in controller
            end

            32'h00_10_00_73:  // EBREAK
            begin
              // debugger trap
              trap_insn = 1'b1;
            end

            32'h10_00_00_73:  // ERET
            begin
              eret_insn = 1'b1;
            end

            32'h10_20_00_73:  // WFI
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
        jump_target_mux_sel_o = `JT_HWLP; // get PC + I imm from jump target adder

        unique case (instr_rdata_i[14:12])
          3'b000: begin
            // lp.starti: set start address to PC + I-type immediate
            hwloop_we[0]           = 1'b1;
            hwloop_start_mux_sel_o = 1'b0;
            // $display("%t: hwloop start address: %h", $time, instr_rdata_i);
          end
          3'b001: begin
            // lp.endi: set end address to PC + I-type immediate
            hwloop_we[1]         = 1'b1;
            hwloop_end_mux_sel_o = 1'b0; // jump target
            // $display("%t: hwloop end address: %h", $time, instr_rdata_i);
          end
          3'b010: begin
            // lp.count initialize counter from rs1
            hwloop_we[2]         = 1'b1;
            hwloop_cnt_mux_sel_o = 1'b1;
            rega_used_o          = 1'b1;
            // $display("%t: hwloop counter: %h", $time, instr_rdata_i);
          end
          3'b011: begin
            // lp.counti initialize counter from I-type immediate
            hwloop_we[2]         = 1'b1;
            hwloop_cnt_mux_sel_o = 1'b0;
            // $display("%t: hwloop counter imm: %h", $time, instr_rdata_i);
          end
          3'b100: begin
            // lp.setup: initialize counter from rs1, set start address to
            // next instruction and end address to PC + I-type immediate
            hwloop_we              = 3'b111;
            hwloop_start_mux_sel_o = 1'b1;
            hwloop_end_mux_sel_o   = 1'b0;
            hwloop_cnt_mux_sel_o   = 1'b1;
            rega_used_o            = 1'b1;
            // $display("%t: hwloop setup: %h", $time, instr_rdata_i);
          end
          3'b101: begin
            // lp.setupi: initialize counter from I-type immediate, set start
            // address to next instruction and end address to PC + shifted
            // z-type immediate
            hwloop_we              = 3'b111;
            hwloop_start_mux_sel_o = 1'b1;
            hwloop_end_mux_sel_o   = 1'b1;
            hwloop_cnt_mux_sel_o   = 1'b0;
            illegal_insn_o         = 1'b1; // TODO: PC + z-imm currently not supported
            // $display("%t: hwloop setup imm: %h", $time, instr_rdata_i);
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
  assign data_we_o         = (deassert_we_i) ? 1'b0          : data_we; // TODO: is this needed?
  assign alu_operator_o    = (deassert_we_i) ? `ALU_NOP      : alu_operator;
  assign mult_en_o         = (deassert_we_i) ? 1'b0          : mult_en;
  assign hwloop_we_o       = (deassert_we_i) ? 3'b0          : hwloop_we;
  assign csr_op_o          = (deassert_we_i) ? `CSR_OP_NONE  : csr_op;
  assign jump_in_id_o      = (deassert_we_i) ? `BRANCH_NONE  : jump_in_id;
  assign trap_insn_o       = (deassert_we_i) ? 1'b0          : trap_insn;
  assign eret_insn_o       = (deassert_we_i) ? 1'b0          : eret_insn;  // TODO: do not deassert?
  assign pipe_flush_o      = (deassert_we_i) ? 1'b0          : pipe_flush; // TODO: do not deassert?

  assign jump_in_dec_o     = jump_in_id;

endmodule // controller
