////////////////////////////////////////////////////////////////////////////////
// Company:        IIS @ ETHZ - Federal Institute of Technology               //
//                                                                            //
// Engineer:       Matthias Baer - baermatt@student.ethz.ch                   //
//                                                                            //
// Additional contributions by:                                               //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                                                                            //
//                                                                            //
//                                                                            //
// Create Date:    19/09/2013                                                 //
// Design Name:    Pipelined OpenRISC Processor                               //
// Module Name:    controller.sv                                              //
// Project Name:   OR10N                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    CPU Controller of the pipelined processor                  //
//                                                                            //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - File Created                                               //
// Revision v0.2 - (August 8th 2014) Changed port and signal names, added     //
//                 comments                                                   //
// Revision v0.3 - (December 1th 2014) Merged debug unit                      //
// Revision v0.4 - (January  6th 2015) Added vectorial instructions           //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

`include "defines.sv"

module controller
(
  input  logic                         clk,
  input  logic                         rst_n,

  input  logic                         fetch_enable_i,             // Start the decoding
  output logic                         eoc_o,                      // End of computation: triggered by a special instruction
  output logic                         core_busy_o,                // Core is busy processing instructions

  input  logic [31:0]                  instr_rdata_i,              // Instruction read from instr memory/cache: (sampled in the if stage)
  output logic                         instr_req_o,                // Fetch instruction Request:
  input  logic                         instr_gnt_i,                // grant from icache
  input  logic                         instr_ack_i,                // Acknow from instr memory or cache (means that data is available)

  output logic [2:0]                   pc_mux_sel_o,               // Selector in the Fetch stage to select the rigth PC (normal, jump ...)
  output logic                         pc_mux_boot_o,              // load boot address as PC, goes to the IF stage

  // ALU signals
  output logic [`ALU_OP_WIDTH-1:0]     alu_operator_o,             // Operator in the Ex stage for the ALU block
  output logic                         extend_immediate_o,         // Extend a 16 bit immediate to 32 bit
  output logic [1:0]                   alu_op_a_mux_sel_o,         // Operator a is selected between reg value, PC or immediate
  output logic [1:0]                   alu_op_b_mux_sel_o,         // Operator b is selected between reg value or immediate
  output logic                         alu_pc_mux_sel_o,           // selects IF or ID PC for ALU computations
  output logic [3:0]                   immediate_mux_sel_o,

  output logic [1:0]                   vector_mode_o,              // selects between 32 bit, 16 bit and 8 bit vectorial modes
  output logic                         scalar_replication_o,       // activates scalar_replication for vectorial mode
  output logic [1:0]                   alu_cmp_mode_o,             // selects comparison mode for ALU (i.e. full, any, all)

  // Mupliplicator related control signals
  output logic                         mult_is_running_o,          // Multiplication operation is running
  input  logic                         mult_is_running_ex_i,       // Multiplication operation is running in EX
  output logic [1:0]                   mult_sel_subword_o,         // Select subwords for 16x16 bit of multiplier
  output logic [1:0]                   mult_signed_mode_o,         // Multiplication in signed mode
  output logic                         mult_use_carry_o,           // Use carry for MAC
  output logic                         mult_mac_en_o,              // Use the accumulator after multiplication

  output logic                         regfile_wdata_mux_sel_o,    // Mul selctor used in WB stage to select regfile wdata from ex result (ALU-MUL), from data memory, or special registers
  input  logic                         regfile_wdata_mux_sel_ex_i, // FW signal: Mul selctor used in WB stage to select regfile wdata from ex result (ALU-MUL), from data memory, or special registers
  output logic                         regfile_we_o,               // Write Enable to regfile
  output logic [1:0]                   regfile_alu_waddr_mux_sel_o, // Select register write address for ALU/MUL operations

  output logic                         regfile_alu_we_o,           // Write Enable to regfile 2nd port

  output logic                         prepost_useincr_o,          // When not active bypass the alu result=op_a
  input  logic                         data_misaligned_i,

  output logic                         sp_we_o,                     // Write enable to special purpose register
  input  logic                         sp_we_ex_i,                  // Manipulated sp_we from ex stage : FW

  // LD/ST unit signals
  output logic                         data_we_o,                   // Write enable to data memory
  output logic [1:0]                   data_type_o,                 // Data type on data memory: byte, half word or word
  output logic                         data_sign_extension_o,       // Sign extension on read data from data memory
  output logic [1:0]                   data_reg_offset_o,           // Offset in bytes inside register for stores
  output logic                         data_req_o,                  // Request for a transaction to data memory
  input  logic                         data_ack_i,                  // Data memory request-acknowledge
  input  logic                         data_req_ex_i,               // Delayed copy of the data_req_o
  input  logic                         data_rvalid_i,               // rvalid from data memory

  // hwloop signals
  output logic [2:0]                   hwloop_we_o,                 // write enables for hwloop regs
  output logic [1:0]                   hwloop_regid_o,              // identifies the hwloop reg set
  output logic                         hwloop_wb_mux_sel_o,         // select data to write to hwloop regs
  output logic [1:0]                   hwloop_cnt_mux_sel_o,        // selects hwloop counter input
  input  logic                         hwloop_jump_i,               // modify pc_mux_sel to select the hwloop addr

  // Interrupt signals
  input  logic                         irq_present_i,               // there is an IRQ, so if we are sleeping we should wake up now

  // Exception Controller Signals
  output logic                         jump_in_id_o,                // jump instruction in ID stage
  output logic                         illegal_insn_o,              // illegal instruction encountered
  output logic                         trap_insn_o,                 // trap instruction encountered
  output logic                         pipe_flush_o,                // pipe flush requested by controller
  input logic                          pc_valid_i,                  // is the next_pc currently valid?
  output logic                         clear_isr_running_o,         // an l.rfe instruction was encountered, exit ISR
  input  logic                         pipe_flushed_i,              // Pipe is flushed

  // Debug Unit Signals
  input  logic                         dbg_stall_i,                 // Pipeline stall is requested
  input  logic                         dbg_set_npc_i,               // Change PC to value from debug unit

  // SPR Signals
  input  logic                         sr_flag_fw_i,                // forwared branch signal
  input  logic                         sr_flag_i,                   // branch signal
  input  logic                         set_flag_ex_i,               // alu is currently updating the flag if 1
  output logic                         set_flag_o,                  // to special purpose registers --> flag
  output logic                         set_carry_o,                 // to special purpose registers --> carry
  output logic                         set_overflow_o,              // to special purpose registers --> overflow
  output logic                         restore_sr_o,                // restores status register after interrupt

  // Forwarding signals from regfile
  input  logic [4:0]                   regfile_waddr_ex_i,          // FW: write address from EX stage
  input  logic                         regfile_we_ex_i,             // FW: write enable from  EX stage
  input  logic [4:0]                   regfile_waddr_wb_i,          // FW: write address from WB stage
  input  logic                         regfile_we_wb_i,             // FW: write enable from  WB stage
  input  logic [4:0]                   regfile_alu_waddr_fw_i,      // FW: ALU/MUL write address from EX stage
  input  logic                         regfile_alu_we_fw_i,         // FW: ALU/MUL write enable from  EX stage
  output logic [1:0]                   operand_a_fw_mux_sel_o,      // regfile ra data selector form ID stage
  output logic [1:0]                   operand_b_fw_mux_sel_o,      // regfile rb data selector form ID stage
  output logic [1:0]                   operand_c_fw_mux_sel_o,      // regfile rc data selector form ID stage

  output logic                         drop_instruction_o,          // prevent instruction to enter ID stage
`ifdef BRANCH_PREDICTION
  output logic                         wrong_branch_taken_o,        // 1 if the wrong branch was selected
  output logic                         take_branch_o,               // 1 if branch should be taken
`endif
  output logic                         stall_if_o,                  // Stall IF stage (deassert requests)
  output logic                         stall_id_o,                  // Stall ID stage (and instr and data memory interface) ( ID_STAGE )
  output logic                         stall_ex_o,                  // Stall ex stage                                       ( EX_STAGE )
  output logic                         stall_wb_o                   // Stall write to register file due contentions      ( WB_STAGE )
);

  // FSM state encoding
  enum  logic [1:0]  { RESET, IDLE, FIRST_FETCH, DECODE}     ctrl_fsm_cs, ctrl_fsm_ns;

  logic reg_d_ex_is_reg_a_id;
  logic reg_d_ex_is_reg_b_id;
  logic reg_d_ex_is_reg_c_id;
  logic reg_d_wb_is_reg_a_id;
  logic reg_d_wb_is_reg_b_id;
  logic reg_d_wb_is_reg_c_id;
  logic reg_d_alu_is_reg_a_id;
  logic reg_d_alu_is_reg_b_id;
  logic reg_d_alu_is_reg_c_id;

  logic [`ALU_OP_WIDTH-1:0] alu_operator;
  logic                     mult_is_running;
  logic                     regfile_we;
  logic                     regfile_alu_we;
  logic                     data_we;
  logic                     data_req;
  logic                     set_flag;
  logic                     set_overflow;
  logic                     set_carry;
  logic                     deassert_we;

  logic       lsu_stall;
  logic       misalign_stall;
  logic       mtspr_stall;
  logic       mfspr_stall;
  logic       instr_ack_stall;
  logic       load_stall;
  logic       jr_stall;

  logic       set_npc;
`ifdef BRANCH_PREDICTION
  logic       wrong_branch_taken;
`endif
  logic       rega_used;
  logic       regb_used;
  logic       regc_used;

  ////////////////////////////////////////////////////////////////////////////////////////////
  //   ____ ___  ____  _____    ____ ___  _   _ _____ ____   ___  _     _     _____ ____    //
  //  / ___/ _ \|  _ \| ____|  / ___/ _ \| \ | |_   _|  _ \ / _ \| |   | |   | ____|  _ \   //
  // | |  | | | | |_) |  _|   | |  | | | |  \| | | | | |_) | | | | |   | |   |  _| | |_) |  //
  // | |__| |_| |  _ <| |___  | |__| |_| | |\  | | | |  _ <| |_| | |___| |___| |___|  _ <   //
  //  \____\___/|_| \_\_____|  \____\___/|_| \_| |_| |_| \_\\___/|_____|_____|_____|_| \_\  //
  //                                                                                        //
  ////////////////////////////////////////////////////////////////////////////////////////////
  always_comb
  begin
    // Default values
    eoc_o                        = 1'b0;

    instr_req_o                  = 1'b1;

    pc_mux_sel_o                 = `INCR_PC;
    pc_mux_boot_o                = 1'b0;

    alu_operator                 = `ALU_NOP;
    extend_immediate_o           = 1'b0;
    alu_op_a_mux_sel_o           = `OP_A_REGA_OR_FWD;
    alu_op_b_mux_sel_o           = `OP_B_REGB_OR_FWD;
    alu_pc_mux_sel_o             = 1'b1;

    vector_mode_o                = `VEC_MODE32;
    scalar_replication_o         = 1'b0;
    alu_cmp_mode_o               = `ALU_CMP_FULL;

    mult_is_running              = 1'b0;
    mult_signed_mode_o           = 2'b00;
    mult_sel_subword_o           = 2'b00;
    mult_use_carry_o             = 1'b0;
    mult_mac_en_o                = 1'b0;

    regfile_wdata_mux_sel_o      = 1'b1;
    regfile_we                   = 1'b0;
    regfile_alu_we               = 1'b0;
    regfile_alu_waddr_mux_sel_o  = 2'b01;

    prepost_useincr_o            = 1'b1;

    hwloop_we_o                  = 3'b0;
    hwloop_regid_o               = 2'b0;
    hwloop_wb_mux_sel_o          = 1'b0;
    hwloop_cnt_mux_sel_o         = 2'b00;
    immediate_mux_sel_o          = `IMM_I;

    sp_we_o                      = 1'b0;

    data_we                      = 1'b0;
    data_type_o                  = 2'b00;
    data_sign_extension_o        = 1'b0;
    data_reg_offset_o            = 2'b00;
    data_req                     = 1'b0;

    set_flag                     = 1'b0;
    set_overflow                 = 1'b0;
    set_carry                    = 1'b0;

    restore_sr_o                 = 1'b0;
    clear_isr_running_o          = 1'b0;

    illegal_insn_o               = 1'b0;
    trap_insn_o                  = 1'b0;
    pipe_flush_o                 = 1'b0;

    ctrl_fsm_ns                  = ctrl_fsm_cs;

    rega_used                    = 1'b0;
    regb_used                    = 1'b0;
    regc_used                    = 1'b0;
`ifdef BRANCH_PREDICTION
    wrong_branch_taken_o         = 1'b0;
    take_branch_o                = 1'b0;
`endif

    case (ctrl_fsm_cs)
      RESET:
      begin
        // We were just reset and have to copy the boot address from
        // outside to our PC
        // We do not yet start fetching instructions as the next_pc is invalid!
        instr_req_o   = 1'b0;
        pc_mux_boot_o = 1'b1;

        if (fetch_enable_i == 1'b1)
          ctrl_fsm_ns = IDLE;
      end

      IDLE:
      begin
        // we begin execution when either fetch_enable is high or an
        // interrupt has arrived
        instr_req_o     = fetch_enable_i || irq_present_i;
        pc_mux_sel_o    = `NO_INCR;

        if (fetch_enable_i || irq_present_i)
        begin
          ctrl_fsm_ns  = FIRST_FETCH;
        end
      end // case: IDLE

      FIRST_FETCH:
      begin
        // Stall because of IF miss
        if (instr_ack_i == 1'b1)
        begin
          ctrl_fsm_ns = DECODE;
        end

        // hwloop detected, jump to start address!
        // Attention: This has to be done in the DECODE and the FIRST_FETCH states
        if (hwloop_jump_i == 1'b1)
          pc_mux_sel_o  = `HWLOOP_ADDR;
      end

      DECODE:
      begin
        unique case (instr_rdata_i[6:0])

          //////////////////////////////////////
          //      _ _   _ __  __ ____  ____   //
          //     | | | | |  \/  |  _ \/ ___|  //
          //  _  | | | | | |\/| | |_) \___ \  //
          // | |_| | |_| | |  | |  __/ ___) | //
          //  \___/ \___/|_|  |_|_|   |____/  //
          //////////////////////////////////////

          `OPCODE_JAL: begin   // Jump and Link
            if (instr_rdata_i ==? `INSTR_JAL) begin
              pc_mux_sel_o        = `PC_FROM_ALU;
              alu_op_a_mux_sel_o  = `OP_A_CURRPC;
              alu_op_b_mux_sel_o  = `OP_B_IMM;
              immediate_mux_sel_o = `IMM_UJ;
              alu_operator        = `ALU_JAL;
              regfile_alu_we      = 1'b1;
            end else begin
              illegal_insn_o      = 1'b1;
            end
          end

          `OPCODE_JALR: begin  // Jump and Link Register
            if (instr_rdata_i ==? `INSTR_JALR) begin
              pc_mux_sel_o        = `PC_FROM_ALU;
              alu_op_b_mux_sel_o  = `OP_B_IMM;
              immediate_mux_sel_o = `IMM_I;
              alu_operator        = `ALU_JAL;
              regfile_alu_we      = 1'b1;
              rega_used           = 1'b1;
            end else begin
              illegal_insn_o      = 1'b1;
            end
          end

          /*

          `OPCODE_JR:
          begin    // Jump Register
            pc_mux_sel_o = `PC_FROM_REGFILE;
            regb_used    = 1'b1;
          end

          `OPCODE_JALR: begin  // Jump and Link Register
            pc_mux_sel_o                 = `PC_FROM_REGFILE;
            alu_op_a_mux_sel_o           = `OP_A_CURRPC;
            alu_op_b_mux_sel_o           = `OP_B_IMM;
            immediate_mux_sel_o          = `IMM_HEX4;
            alu_operator                 = `ALU_ADD;
            regfile_alu_waddr_mux_sel_o  = 2'b10; // select r9 to write back return address
            regfile_alu_we               = 1'b1;
            regb_used                    = 1'b1;
          end

`ifndef BRANCH_PREDICTION
          `OPCODE_BNF:
          begin   // Branch if No Flag
             if (sr_flag_fw_i == 1'b0)
               pc_mux_sel_o = `PC_FROM_IMM;
          end

          `OPCODE_BF:
          begin    // Branch if Flag
             if (sr_flag_fw_i == 1'b1)
               pc_mux_sel_o = `PC_FROM_IMM;
          end
`else // BRANCH_PREDICTION
          `OPCODE_BNF:
          begin   // Branch if No Flag
            if (set_flag_ex_i == 1'b0)
              if (sr_flag_i == 1'b0)
                pc_mux_sel_o = `PC_FROM_IMM;
              else
                pc_mux_sel_o = `INCR_PC;
            else // default branch
            begin
              pc_mux_sel_o = instr_rdata_i[25] ? `PC_FROM_IMM : `INCR_PC;
              // decision was wrong
              wrong_branch_taken_o = (sr_flag_fw_i ^ instr_rdata_i[25]) ? 1'b0 : 1'b1;
              take_branch_o = instr_rdata_i[25] ? `INCR_PC : `PC_FROM_IMM;
            end
          end

          `OPCODE_BF:
          begin    // Branch if Flag
            if (set_flag_ex_i == 1'b0)
              if (sr_flag_i == 1'b1)
                pc_mux_sel_o = `PC_FROM_IMM;
              else
                pc_mux_sel_o = `INCR_PC;
            else // default branch
            begin
              pc_mux_sel_o = instr_rdata_i[25] ? `PC_FROM_IMM : `INCR_PC;
              // decision was wrong
              wrong_branch_taken_o = (sr_flag_fw_i ^ instr_rdata_i[25]) ? 1'b1 : 1'b0;
              take_branch_o = instr_rdata_i[25] ? `INCR_PC : `PC_FROM_IMM;
            end
          end
`endif

          `OPCODE_NOP:
          begin   // No Operation
            // if (instr_rdata_i[25:24] == 2'b01)
            //   $display("%t: Executing l.nop with 0x%h.", $time, instr_rdata_i[15:0]);
            // else
            //   $display("%t: Illegal l.nop received.", $time);
          end

          `OPCODE_EOC: begin   // End of Computation (Custom Instruction 1)
            eoc_o        = 1'b1;
            pc_mux_sel_o = `NO_INCR;
          end

          `OPCODE_RFE:
          begin
            pc_mux_sel_o        = `EXC_PC_REG; // restore PC from EPCR
            restore_sr_o        = 1'b1;
            clear_isr_running_o = 1'b1;
          end

           */

          //////////////////////////////////
          //  _     ____    ______ _____  //
          // | |   |  _ \  / / ___|_   _| //
          // | |   | | | |/ /\___ \ | |   //
          // | |___| |_| / /  ___) || |   //
          // |_____|____/_/  |____/ |_|   //
          //                              //
          //////////////////////////////////

          `OPCODE_STORE: begin
            alu_op_b_mux_sel_o  = `OP_B_IMM;
            immediate_mux_sel_o = `IMM_S;
            alu_operator        = `ALU_ADD;
            data_req            = 1'b1;
            data_we             = 1'b1;
            rega_used           = 1'b1;
            regb_used           = 1'b1;

            unique case (instr_rdata_i) inside
              `INSTR_SW:  data_type_o = 2'b00;
              `INSTR_SH:  data_type_o = 2'b01;
              `INSTR_SB:  data_type_o = 2'b10;
              default: begin
                data_req  = 1'b0;
                data_we   = 1'b0;
                rega_used = 1'b0;
                regb_used = 1'b0;
                illegal_insn_o = 1'b1;
              end
            endcase // unique case (instr_rdata_i)
          end

          `OPCODE_LOAD: begin
            alu_op_b_mux_sel_o       = `OP_B_IMM;
            immediate_mux_sel_o      = `IMM_I;
            alu_operator             = `ALU_ADD;
            data_req                 = 1'b1;
            regfile_wdata_mux_sel_o  = 1'b1;
            regfile_we               = 1'b1;
            rega_used                = 1'b1;
            data_type_o              = 2'b00;
            data_sign_extension_o    = 1'b1;

            unique case (instr_rdata_i) inside
              `INSTR_LW: ;                    // Load Word
              `INSTR_LH: data_type_o = 2'b01; // Load Half-Word Sign-Extended
              `INSTR_LB: data_type_o = 2'b10; // Load Byte Sign-Extended

              `INSTR_LHU: begin               // Load Half-Word Zero-Extended
                data_type_o              = 2'b01;
                data_sign_extension_o    = 1'b0;
              end

              `INSTR_LBU: begin               // Load Byte Zero-Extended
                data_type_o              = 2'b10;
                data_sign_extension_o    = 1'b0;
              end

              default: begin
                data_req   = 1'b0;
                regfile_we = 1'b0;
                rega_used  = 1'b0;
                illegal_insn_o = 1'b1;
              end
            endcase // unique case (instr_rdata_i)
          end

          /*

          // Pre/Post-Increment Stores and Register-Register Stores
          `OPCODE_STPOST, `OPCODE_STPRE: begin
            alu_operator                = `ALU_ADD;  // addr is generated in ID stage so no need for addr gen in alu TODO: always use ID stage addr
            data_req                    = 1'b1;
            regfile_alu_waddr_mux_sel_o = 2'b00;
            rega_used                   = 1'b1;
            regb_used                   = 1'b1;
            data_we                     = 1'b1;      // write to memory


            if (instr_rdata_i[31:26] == `OPCODE_STPOST)
            begin
              prepost_useincr_o = 1'b0; // if post increment instruction, don't use the modified address
            end

            case (instr_rdata_i[5:4])
              default: begin
                alu_op_b_mux_sel_o   = `OP_B_IMM;
                immediate_mux_sel_o  = `IMM_5N6S;  // offset in 11bit immediate
                regfile_alu_we   = 1'b1;  // write new addr value into regfile using portB
              end

              2'b11: begin // register-register store with post increment
                regc_used = 1'b1;
                alu_op_b_mux_sel_o = `OP_B_REGC_OR_FWD;
                regfile_alu_we = 1'b1;  // write new addr value into regfile using portB
              end

              2'b01: begin // register-register store without pre/post-increment
                alu_op_b_mux_sel_o = `OP_B_REGC_OR_FWD;
                regc_used          = 1'b1;
              end
            endcase // case (instr_rdata_i[5:4])

            // Word, Half Word or Byte store
            case (instr_rdata_i[3:2])
              default: data_type_o = 2'b00;
              2'b00:   data_type_o = 2'b00; // word
              2'b10:   data_type_o = 2'b01; // half word
              2'b11:   data_type_o = 2'b10; // byte
            endcase // case(instr_rdata_i[4:3]

            // offset inside value to be stored, e.g. l.sh1, l.sb1 and so on
            data_reg_offset_o      = instr_rdata_i[1:0];
          end

          // Pre/Post-Increment Loads and Register-Register Loads
          `OPCODE_LDPOST, `OPCODE_LDPRE: begin
            alu_operator                = `ALU_ADD;  // addr is generated in ID stage so no need for addr gen in alu TODO: always use ID stage addr
            data_req                    = 1'b1;
            rega_used                   = 1'b1;
            regfile_wdata_mux_sel_o     = 1'b1; // get data from wb
            regfile_alu_waddr_mux_sel_o = 2'b00;
            regfile_we                  = 1'b1;  // write regfile portA with data coming from mem

            if (instr_rdata_i[31:26] == `OPCODE_LDPOST)
              prepost_useincr_o = 1'b0; // if post increment instruction, don't use the modified address

            // Since we also support register-register loads without
            // pre/post-increment, we have to distinguish the two cases
            // here. If no pre/post is used, we don't write back to
            // the second write port of the RF
            if (instr_rdata_i[5:4] == 2'b01) // normal case
              regfile_alu_we   = 1'b0;
            else // pre/post case
              regfile_alu_we   = 1'b1;  // write new addr value into regfile using portB

            if (instr_rdata_i[4] == 1'b0)
            begin
              alu_op_b_mux_sel_o   = `OP_B_IMM;
              immediate_mux_sel_o  = `IMM_11S;  // offset in 11bit immediate
            end
            else
            begin
              alu_op_b_mux_sel_o = `OP_B_REGB_OR_FWD; // offset in rB register
              regb_used          = 1'b1;
            end

            // Word, Half Word or Byte load
            case (instr_rdata_i[3:2])
              default: data_type_o = 2'b00;
              2'b00:   data_type_o = 2'b00; // word
              2'b10:   data_type_o = 2'b01; // half word
              2'b11:   data_type_o = 2'b10; // byte
            endcase // case(instr_rdata_i[4:3]

            // sign extension
            data_sign_extension_o  = instr_rdata_i[1];
          end


           */

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
            alu_pc_mux_sel_o    = 1'b1;
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
            rega_used           = 1'b1;

            unique case (instr_rdata_i) inside
              `INSTR_ADDI:  alu_operator = `ALU_ADD;  // Add Immediate
              `INSTR_SLTI:  alu_operator = `ALU_SLTS; // Set to one if Lower Than Immediate
              `INSTR_SLTIU: alu_operator = `ALU_SLTU; // Set to one if Lower Than Immediate Unsigned
              `INSTR_XORI:  alu_operator = `ALU_XOR;  // Exclusive Or with Immediate
              `INSTR_ORI:   alu_operator = `ALU_OR;   // Or with Immediate
              `INSTR_ANDI:  alu_operator = `ALU_AND;  // And with Immediate
              `INSTR_SLLI:  alu_operator = `ALU_SLL;  // Shift Left Logical by Immediate
              `INSTR_SRLI:  alu_operator = `ALU_SRL;  // Shift Right Logical by Immediate
              `INSTR_SRAI:  alu_operator = `ALU_SRA;  // Shift Right Arithmetically by Immediate
              default: begin
                regfile_alu_we = 1'b0;
                illegal_insn_o = 1'b1;
              end
            endcase // unique case (instr_rdata_i)
          end // case: `OPCODE_OPIMM

          /*
          `OPCODE_ADDIC: begin // Add Immediate and Carry
            alu_op_b_mux_sel_o       = `OP_B_IMM;
            immediate_mux_sel_o      = `IMM_16;
            alu_operator             = `ALU_ADDC;
            regfile_alu_we           = 1'b1;
            set_overflow             = 1'b1;
            set_carry                = 1'b1;
            rega_used                = 1'b1;
          end
          */

          `OPCODE_OP: begin  // ALU register-register operation
            regfile_alu_we = 1'b1;
            rega_used      = 1'b1;
            regb_used      = 1'b1;

            unique case (instr_rdata_i) inside
              `INSTR_ADD:  alu_operator = `ALU_ADD;  // Add
              `INSTR_SUB:  alu_operator = `ALU_SUB;  // Sub
              `INSTR_SLL:  alu_operator = `ALU_SLL;  // Shift Left Logical
              `INSTR_SLT:  alu_operator = `ALU_SLTS; // Set Lower Than
              `INSTR_SLTU: alu_operator = `ALU_SLTU; // Set Lower Than Unsigned
              `INSTR_XOR:  alu_operator = `ALU_XOR;  // Xor
              `INSTR_SRL:  alu_operator = `ALU_SRL;  // Shift Right Logical
              `INSTR_SRA:  alu_operator = `ALU_SRA;  // Shift Right Arithmetic
              `INSTR_OR:   alu_operator = `ALU_OR;   // Or
              `INSTR_AND:  alu_operator = `ALU_AND;  // And
              default: begin
                // synopsys translate_off
                $display("%t: Illegal OP instruction: %b", $time, instr_rdata_i);
                // synopsys translate_on
                regfile_alu_we = 1'b0;
                illegal_insn_o = 1'b1;
              end
            endcase // unique case (instr_rdata_i)
          end


          /*

          `OPCODE_MOVHI:
          begin
            if (instr_rdata_i[16] == 1'b0)
            begin // Move Immediate High
              extend_immediate_o       = 1'b1;
              alu_op_a_mux_sel_o       = `OP_A_IMM16;
              alu_operator             = `ALU_MOVHI;
              regfile_alu_we           = 1'b1;
            end
            else
            begin
              // synopsys translate_off
              $display("%t: Illegal l.movhi received.", $time);
              // synopsys translate_on
              illegal_insn_o = 1'b1;
            end
          end

          `OPCODE_MULI: begin  // Multiply Immediate Signed
            alu_op_b_mux_sel_o   = `OP_B_IMM;
            immediate_mux_sel_o  = `IMM_16;
            mult_is_running      = 1'b1;

            regfile_alu_we              = 1'b1;
            regfile_alu_waddr_mux_sel_o = 2'b01;
            rega_used                   = 1'b1;
          end

          `OPCODE_ALU: begin   // Arithmetic Operation
            rega_used  = 1'b1;
            regb_used  = 1'b1;

            case (instr_rdata_i[9:8])
              2'b00: begin    // ALU Operation
                regfile_alu_we = 1'b1;

                casex (instr_rdata_i[3:0])
                  4'b0XXX: begin // Standard Operation
                    alu_operator   = {3'b000, instr_rdata_i[2:0]};

                    if ((instr_rdata_i[2:0] ==? 3'b00X) || (instr_rdata_i[2:0] == 3'b010)) begin // l.add, l.addc & l.sub
                      set_overflow = 1'b1;
                      set_carry    = 1'b1;
                    end
                  end
                  4'b1000: begin // Shift Operation
                     alu_operator   = {4'b0010, instr_rdata_i[7:6]};
                  end
                  4'b110X: begin // l.ext{b,h,w}{s,z}
                     alu_operator   = {3'b010, instr_rdata_i[7:6], instr_rdata_i[0]};
                     regb_used      = 1'b0; // register b is not used
                  end
                  4'b1110: begin // l.cmov
                     alu_operator   = `ALU_CMOV;
                  end
                  4'b1111: begin // l.ff1
                    alu_operator = `ALU_FF1;
                  end
                  default: begin
                    // synopsys translate_off
                    $display("%t: Illegal ALU instruction received.", $time);
                    // synopsys translate_on
                    regfile_alu_we = 1'b0; // disable Write Enable for illegal instruction
                    illegal_insn_o = 1'b1;
                  end
                endcase // casex (instr_rdata_i[3:2])
              end

              2'b01: begin // l.fl1, l.clb, l.cnt
                regfile_alu_we = 1'b1;
                regb_used      = 1'b0;

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
                    regb_used    = 1'b0;
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

              2'b11: begin    // Multiplication
                if ((instr_rdata_i[3:0] == 4'b0110) || (instr_rdata_i[3:0] == 4'b1011))
                begin // Is multiplication and no division
                  mult_is_running   = 1'b1;

                  if ((instr_rdata_i[3:0] == 4'b0110) || (instr_rdata_i[3:0] == 4'b1011)) // l.mul & l.mulu
                  begin
                    regfile_alu_we              = 1'b1;
                    regfile_alu_waddr_mux_sel_o = 2'b01;
                  end
                end
                else
                begin
                  // synopsys translate_off
                  $display("%t: Division instruction received, this is not supported.", $time);
                  // synopsys translate_on
                  illegal_insn_o = 1'b1;
                end
              end
            endcase; // case (instr_rdata_i[9:8])
          end

          `OPCODE_MAC: begin   // MAC instruction
            mult_is_running    = 1'b1;

            rega_used          = 1'b1;
            regb_used          = 1'b1;

            regfile_alu_waddr_mux_sel_o = 2'b01;
            regfile_alu_we              = 1'b1;

            case (instr_rdata_i[6:5])
              2'b00: begin // MAC
                case (instr_rdata_i[3:0])
                  4'b1000: begin // l.mac
                    mult_mac_en_o = 1'b1;
                    regc_used     = 1'b1;
                    set_carry     = 1'b1;
                    set_overflow  = 1'b1;
                  end

                  4'b1001: begin // l.mac.c
                    mult_use_carry_o = 1'b1;
                    mult_mac_en_o    = 1'b1;
                    regc_used        = 1'b1;
                    set_carry        = 1'b1;
                    set_overflow     = 1'b1;
                  end

                  default: begin
                    // synopsys translate_off
                    $display("%t: Illegal MAC instruction received.", $time);
                    // synopsys translate_on
                    regfile_alu_we = 1'b0;
                    illegal_insn_o     = 1'b1;
                  end
                endcase // case (instr_rdata_i[3:0])
              end

              2'b01: begin // MAC with subword selection
                vector_mode_o      = `VEC_MODE216;
                mult_mac_en_o      = 1'b1;
                regc_used          = 1'b1;
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
                illegal_insn_o     = 1'b1;
              end
            endcase
          end

          `OPCODE_SFI: begin   // Set Flag Immediate-Instructions
            if (instr_rdata_i[25] == 1'b0) begin
              alu_op_b_mux_sel_o    = `OP_B_IMM;
              immediate_mux_sel_o   = `IMM_16;
              alu_operator          = {2'b10, instr_rdata_i[24:21]};
              set_flag              = 1'b1;
              rega_used             = 1'b1;
            end
            else begin
              // synopsys translate_off
              $display("%t: Illegal Set Flag Immediate instruction received.", $time);
              // synopsys translate_on
              illegal_insn_o     = 1'b1;
            end
          end

          `OPCODE_SF: begin    // Set Flag Instruction
            if (instr_rdata_i[25] == 1'b0) begin
              alu_operator          = {2'b10, instr_rdata_i[24:21]};
              set_flag              = 1'b1;
              rega_used             = 1'b1;
              regb_used             = 1'b1;
            end
            else begin
              // synopsys translate_off
              $display("%t: Illegal Set Flag instruction received.", $time);
              // synopsys translate_on
              illegal_insn_o = 1'b1;
            end
          end

          `OPCODE_VEC: begin // vectorial alu operations
            rega_used      = 1'b1;
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
              regb_used = 1'b1;

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
                regfile_alu_waddr_mux_sel_o = 2'b01;
                mult_is_running             = 1'b1;
              end

              5'b01001: alu_operator = `ALU_OR;
              5'b01010: alu_operator = `ALU_XOR;
              5'b01011: alu_operator = `ALU_AND;

              5'b01100: begin // lv32.ins
                alu_operator         = `ALU_INS;
                scalar_replication_o = 1'b1;
              end

              5'b10000: begin // lv32.abs
                regb_used    = 1'b0; // abs does not use operand b
                alu_operator = `ALU_ABS;
              end

              5'b10001: begin // lv32.ext
                regb_used    = 1'b0;
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
            rega_used      = 1'b1;
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
              regb_used = 1'b1;

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

          ////////////////////////////////////////////////
          //  ____  ____  _____ ____ ___    _    _      //
          // / ___||  _ \| ____/ ___|_ _|  / \  | |     //
          // \___ \| |_) |  _|| |    | |  / _ \ | |     //
          //  ___) |  __/| |__| |___ | | / ___ \| |___  //
          // |____/|_|   |_____\____|___/_/   \_\_____| //
          //                                            //
          ////////////////////////////////////////////////

          `OPCODE_MTSPR: begin // Move To Special-Purpose Register
            alu_operator             = `ALU_OR;
            alu_op_b_mux_sel_o       = `OP_B_IMM;
            sp_we_o                  = 1'b1;
            rega_used                = 1'b1;
            regb_used                = 1'b1;
          end

          `OPCODE_MFSPR: begin // Move From Special-Purpose Register
            alu_operator             = `ALU_OR;
            alu_op_b_mux_sel_o       = `OP_B_IMM;
            immediate_mux_sel_o      = `IMM_16;
            regfile_wdata_mux_sel_o  = 1'b0;
            regfile_we               = 1'b1;
            rega_used                = 1'b1;
          end

          `OPCODE_SYNC:
          begin
            if (instr_rdata_i[25] == 1'b1) // sync operation
            begin // l.psync, flush pipeline. Actually this also does l.msync
              pipe_flush_o = 1'b1;
            end
            else
            begin
              if (instr_rdata_i[24:16] == 9'h100)
              begin
                // l.trap
                // Currently we ignore the immediate
                trap_insn_o = 1'b1;
              end
              else
                illegal_insn_o = 1'b1;
            end
          end

          ///////////////////////////////////////////////
          //  _   ___        ___     ___   ___  ____   //
          // | | | \ \      / / |   / _ \ / _ \|  _ \  //
          // | |_| |\ \ /\ / /| |  | | | | | | | |_) | //
          // |  _  | \ V  V / | |__| |_| | |_| |  __/  //
          // |_| |_|  \_/\_/  |_____\___/ \___/|_|     //
          ///////////////////////////////////////////////

          `OPCODE_HWLOOP: begin // hwloop instructions

            hwloop_regid_o  = instr_rdata_i[22:21];     // set hwloop register id

            case (instr_rdata_i[25:23])
              3'b000,3'b110,3'b111: begin // lp.start set start address
                 hwloop_wb_mux_sel_o = 1'b1;
                 hwloop_we_o[0]      = 1'b1;                     // set we for start addr reg
                 alu_op_a_mux_sel_o  = `OP_A_CURRPC;
                 alu_op_b_mux_sel_o  = `OP_B_IMM;
                 alu_operator        = `ALU_ADD;
                 alu_pc_mux_sel_o    = 1'b1;
                 immediate_mux_sel_o = `IMM_21S;
                 // $display("%t: hwloop start address: %h", $time, instr_rdata_i);
              end
              3'b001: begin // lp.end set end address
                 hwloop_wb_mux_sel_o = 1'b1;
                 hwloop_we_o[1]      = 1'b1;                     // set we for end addr reg
                 alu_op_a_mux_sel_o  = `OP_A_CURRPC;
                 alu_op_b_mux_sel_o  = `OP_B_IMM;
                 alu_operator        = `ALU_ADD;
                 alu_pc_mux_sel_o    = 1'b1;
                 immediate_mux_sel_o = `IMM_21S;
                 // $display("%t: hwloop end address: %h", $time, instr_rdata_i);
              end
              3'b010: begin // lp.counti initialize counter from immediate
                 hwloop_cnt_mux_sel_o = 2'b01;
                 hwloop_we_o[2]       = 1'b1;                     // set we for counter reg
                 // $display("%t: hwloop counter imm: %h", $time, instr_rdata_i);
              end
              3'b011: begin // lp.count initialize counter from register
                 hwloop_cnt_mux_sel_o = 2'b11;
                 hwloop_we_o[2]       = 1'b1;                     // set we for counter reg
                 rega_used            = 1'b1;
                 // $display("%t: hwloop counter: %h", $time, instr_rdata_i);
              end
              3'b100: begin // lp.setupi
                 hwloop_wb_mux_sel_o  = 1'b0;
                 hwloop_cnt_mux_sel_o = 2'b10;
                 hwloop_we_o          = 3'b111;                     // set we for counter/start/end reg
                 alu_op_a_mux_sel_o   = `OP_A_CURRPC;
                 alu_op_b_mux_sel_o   = `OP_B_IMM;
                 alu_operator         = `ALU_ADD;
                 alu_pc_mux_sel_o     = 1'b1;
                 immediate_mux_sel_o  = `IMM_8Z;
                 // $display("%t: hwloop setup imm: %h", $time, instr_rdata_i);
              end
              3'b101: begin // lp.setup
                 hwloop_wb_mux_sel_o  = 1'b0;
                 hwloop_cnt_mux_sel_o = 2'b11;
                 hwloop_we_o          = 3'b111;                     // set we for counter/start/end reg
                 alu_op_a_mux_sel_o   = `OP_A_CURRPC;
                 alu_op_b_mux_sel_o   = `OP_B_IMM;
                 alu_operator         = `ALU_ADD;
                 alu_pc_mux_sel_o     = 1'b1;
                 immediate_mux_sel_o  = `IMM_16Z;
                 rega_used            = 1'b1;
                 // $display("%t: hwloop setup: %h", $time, instr_rdata_i);
              end
            endcase
          end

          */

          default: begin
            illegal_insn_o = 1'b1;
            // TODO: Replace with exception
            pc_mux_sel_o = `NO_INCR;
          end

        endcase; // case (instr_rdata_i[6:0])

        if (illegal_insn_o == 1'b1) begin
          // synopsys translate_off
          $display("%t: Illegal instruction:", $time, instr_rdata_i);
          prettyPrintInstruction(instr_rdata_i);
          $stop;
          // synopsys translate_on
        end

        // misaligned access was detected by the LSU
        if (data_misaligned_i == 1'b1)
        begin
          // only part of the pipeline is unstalled, make sure that the
          // correct operands are sent to the AGU
          alu_op_a_mux_sel_o  = `OP_A_REGA_OR_FWD;
          alu_op_b_mux_sel_o  = `OP_B_IMM;
          immediate_mux_sel_o = `IMM_I;   // TODO: FIXME

          // if prepost increments are used, we do not write back the
          // second address since the first calculated address was
          // the correct one
          regfile_alu_we  = 1'b0;

          // if post increments are used, we must make sure that for
          // the second memory access we do use the adder
          prepost_useincr_o   = 1'b1;
        end

        if ( set_npc == 1'b1 )
          pc_mux_sel_o = `NO_INCR;

        // hwloop detected, jump to start address!
        if (hwloop_jump_i == 1'b1)
          pc_mux_sel_o  = `HWLOOP_ADDR;

`ifdef BRANCH_PREDICTION
        if (wrong_branch_taken)
          pc_mux_sel_o = `PC_BRANCH_PRED;
`endif
        // the pipeline is flushed and we are requested to go to sleep
        if ((pipe_flushed_i == 1'b1) && (fetch_enable_i == 1'b0))
          ctrl_fsm_ns = IDLE;
      end
    endcase
   end

   assign core_busy_o = (ctrl_fsm_cs != IDLE);

   ////////////////////////////////////////////////////////////////////////////////////////////
   // Generate Stall Signals!                                                                //
   ////////////////////////////////////////////////////////////////////////////////////////////
   always_comb
   begin
     mfspr_stall   = 1'b0;
     mtspr_stall   = 1'b0;
     load_stall    = 1'b0;
     jr_stall      = 1'b0;
     deassert_we   = 1'b0;


     /*
     // Stall because of l.mfspr with dependency
     if ((regfile_wdata_mux_sel_ex_i == 1'b0) && (regfile_we_ex_i == 1'b1) &&
         ((reg_d_ex_is_reg_a_id == 1'b1) || (reg_d_ex_is_reg_b_id == 1'b1) || (reg_d_ex_is_reg_c_id == 1'b1)) )
     begin
       deassert_we     = 1'b1;
       mfspr_stall     = 1'b1;
     end

     // Stall because of l.mtspr (always...)
     // mtspr in ex stage, normal instruction in id stage which can change an spr reg
     if ((sp_we_ex_i == 1'b1) && (instr_rdata_i[31:26] != `OPCODE_MTSPR))
     begin
       deassert_we     = 1'b1;
       mtspr_stall     = 1'b1;
     end
     */

     // Stall because of load operation
     if ((data_req_ex_i == 1'b1) && (regfile_we_ex_i == 1'b1) &&
         ((reg_d_ex_is_reg_a_id == 1'b1) || (reg_d_ex_is_reg_b_id == 1'b1) || (reg_d_ex_is_reg_c_id == 1'b1)) )
     begin
       deassert_we     = 1'b1;
       load_stall      = 1'b1;
     end

     // TODO: check JALR/JR
     // Stall because of jr path
     // - Load results cannot directly be forwarded to PC
     // - Multiplication results cannot be forwarded to PC
     if (((instr_rdata_i[6:0] == `OPCODE_JALR) || (instr_rdata_i[6:0] == `OPCODE_JAL)) &&
         (((regfile_we_wb_i == 1'b1) && (reg_d_wb_is_reg_b_id == 1'b1) && (data_rvalid_i == 1'b1)) ||
          ((regfile_we_ex_i == 1'b1) && (reg_d_ex_is_reg_b_id == 1'b1))                            ||
          ((regfile_alu_we_fw_i == 1'b1) && (reg_d_alu_is_reg_b_id == 1'b1) && (mult_is_running_ex_i == 1'b1))) )
     begin
       jr_stall        = 1'b1;
       deassert_we     = 1'b1;
     end

     /*
`ifdef BRANCH_PREDICTION
      // Stall because of set_flag path
     if (wrong_branch_taken)
     begin
       deassert_we     = 1'b1;
     end
`endif
      */

   end

`ifdef BRANCH_PREDICTION
   assign drop_instruction_o = wrong_branch_taken;
`else
   assign drop_instruction_o = 1'b0;
`endif

   // Stall because of IF miss
   assign instr_ack_stall = ~instr_ack_i;

   // Stall if TCDM contention has been detected
   assign lsu_stall = ~data_ack_i;

   assign misalign_stall = data_misaligned_i;

   // deassert we signals (in case of stalls)
   assign alu_operator_o    = (deassert_we) ? `ALU_NOP : alu_operator;
   assign mult_is_running_o = (deassert_we) ? 1'b0     : mult_is_running;
   assign regfile_we_o      = (deassert_we) ? 1'b0     : regfile_we;
   assign regfile_alu_we_o  = (deassert_we) ? 1'b0     : regfile_alu_we;
   assign data_we_o         = (deassert_we) ? 1'b0     : data_we;
   assign data_req_o        = (deassert_we) ? 1'b0     : data_req;
   assign set_flag_o        = (deassert_we) ? 1'b0     : set_flag;
   assign set_overflow_o    = (deassert_we) ? 1'b0     : set_overflow;
   assign set_carry_o       = (deassert_we) ? 1'b0     : set_carry;


   ////////////////////////////////////////////////////////////////////////////////////////////
   // Freeze Unit. This unit controls the pipeline stages                                    //
   ////////////////////////////////////////////////////////////////////////////////////////////
   always_comb
   begin
     // we unstall the if_stage if the debug unit wants to set a new
     // pc, so that the new value gets written into current_pc_if and is
     // used by the instr_core_interface
     stall_if_o = (instr_ack_stall | mfspr_stall | mtspr_stall | load_stall | jr_stall | lsu_stall | misalign_stall | dbg_stall_i | (~pc_valid_i));
     stall_id_o =  instr_ack_stall | mfspr_stall | mtspr_stall | load_stall | jr_stall | lsu_stall | misalign_stall | dbg_stall_i;
     stall_ex_o = instr_ack_stall | lsu_stall | dbg_stall_i;
     stall_wb_o = lsu_stall | dbg_stall_i;
   end


   ////////////////////////////////////////////////////////////////////////////////////////////
   // Forwarding control unit. (Forwarding from wb and ex stage to id stage)                 //
   //  RiscV register encoding:  rs1 is [19:15], rs2 is [24:20], rd is [11:7]                //
   //  Or10n register encoding:  ra  is [20:16], rb  is [15:11], rd is [25:21]               //
   ////////////////////////////////////////////////////////////////////////////////////////////
   assign reg_d_ex_is_reg_a_id  = (regfile_waddr_ex_i     == instr_rdata_i[`REG_RS1]) && (rega_used == 1'b1);
   assign reg_d_ex_is_reg_b_id  = (regfile_waddr_ex_i     == instr_rdata_i[`REG_RS2]) && (regb_used == 1'b1);
   assign reg_d_ex_is_reg_c_id  = (regfile_waddr_ex_i     == instr_rdata_i[`REG_RD])  && (regc_used == 1'b1);
   assign reg_d_wb_is_reg_a_id  = (regfile_waddr_wb_i     == instr_rdata_i[`REG_RS1]) && (rega_used == 1'b1);
   assign reg_d_wb_is_reg_b_id  = (regfile_waddr_wb_i     == instr_rdata_i[`REG_RS2]) && (regb_used == 1'b1);
   assign reg_d_wb_is_reg_c_id  = (regfile_waddr_wb_i     == instr_rdata_i[`REG_RD])  && (regc_used == 1'b1);
   assign reg_d_alu_is_reg_a_id = (regfile_alu_waddr_fw_i == instr_rdata_i[`REG_RS1]) && (rega_used == 1'b1);
   assign reg_d_alu_is_reg_b_id = (regfile_alu_waddr_fw_i == instr_rdata_i[`REG_RS2]) && (regb_used == 1'b1);
   //assign reg_d_alu_is_reg_c_id = (regfile_alu_waddr_fw_i == instr_rdata_i[`REG_RD])  && (regc_used == 1'b1);

   always_comb
   begin
     // default assignements
     operand_a_fw_mux_sel_o = `SEL_REGFILE;
     operand_b_fw_mux_sel_o = `SEL_REGFILE;
     operand_c_fw_mux_sel_o = `SEL_REGFILE;

     // Forwarding WB -> ID
     if (regfile_we_wb_i == 1'b1)
     begin
       if (reg_d_wb_is_reg_a_id == 1'b1)
         operand_a_fw_mux_sel_o = `SEL_FW_WB;
       if (reg_d_wb_is_reg_b_id == 1'b1)
         operand_b_fw_mux_sel_o = `SEL_FW_WB;
       if (reg_d_wb_is_reg_c_id == 1'b1)
         operand_c_fw_mux_sel_o = `SEL_FW_WB;
     end

     // Forwarding EX -> ID
     if (regfile_alu_we_fw_i == 1'b1)
     begin
      if (reg_d_alu_is_reg_a_id == 1'b1)
        operand_a_fw_mux_sel_o = `SEL_FW_EX;
      if (reg_d_alu_is_reg_b_id == 1'b1)
        operand_b_fw_mux_sel_o = `SEL_FW_EX;
      if (reg_d_alu_is_reg_c_id == 1'b1)
        operand_c_fw_mux_sel_o = `SEL_FW_EX;
     end

     if (data_misaligned_i == 1'b1)
     begin
       operand_a_fw_mux_sel_o  = `SEL_FW_EX;
       operand_b_fw_mux_sel_o  = `SEL_REGFILE;
     end
   end

   // check if jump or branch in pipeline
  /*
   assign jump_in_id_o = ((instr_rdata_i[31:26] == `OPCODE_BF)  || (instr_rdata_i[31:26] == `OPCODE_BNF)  ||
                          (instr_rdata_i[31:26] == `OPCODE_J)   || (instr_rdata_i[31:26] == `OPCODE_JR)   ||
                          (instr_rdata_i[31:26] == `OPCODE_JAL) || (instr_rdata_i[31:26] == `OPCODE_JALR) ||
                          (instr_rdata_i[31:26] == `OPCODE_RFE) );
   */
  // TODO: FIXME
  assign jump_in_id_o = ((instr_rdata_i[6:0] == `OPCODE_JAL) || (instr_rdata_i[6:0] == `OPCODE_JALR));


  // update registers
  always_ff @(posedge clk , negedge rst_n)
  begin : UPDATE_REGS
    if ( rst_n == 1'b0 )
    begin
      ctrl_fsm_cs <= RESET;
    end
    else
    begin
      ctrl_fsm_cs <= ctrl_fsm_ns;
    end
  end

  // hold NPC until IF stage has taken over this value
  always_ff @(posedge clk , negedge rst_n)
  begin : HOLD_NPC
    if ( rst_n == 1'b0 )
    begin
       set_npc    <= 1'b0;
    end
    else
    begin
       if (dbg_set_npc_i == 1'b1)
         set_npc <= 1'b1;
       else if (stall_if_o == 1'b0)
         set_npc <= 1'b0;
    end
  end

`ifdef BRANCH_PREDICTION
  // Wrong branch was taken!
  always_ff @(posedge clk , negedge rst_n)
  begin : WRONG_BRANCH
    if ( rst_n == 1'b0 )
    begin
       wrong_branch_taken <= 1'b0;
    end
    else
    begin
       if (stall_if_o == 1'b0)
         wrong_branch_taken <= wrong_branch_taken_o;
    end
  end
`endif

endmodule // controller
