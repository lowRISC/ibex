////////////////////////////////////////////////////////////////////////////////
// Company:        IIS @ ETHZ - Federal Institute of Technology               //
//                                                                            //
// Engineer:       Matthias Baer - baermatt@student.ethz.ch                   //
//                                                                            //
// Additional contributions by:                                               //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                                                                            //
//                                                                            //
// Create Date:    19/09/2013                                                 //
// Design Name:    RISC-V processor core                                      //
// Module Name:    controller.sv                                              //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Main CPU controller of the processor                       //
//                                                                            //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - File Created                                               //
// Revision v0.2 - (August 8th 2014) Changed port and signal names, added     //
//                 comments                                                   //
// Revision v0.3 - (December 1th 2014) Merged debug unit                      //
// Revision v0.4 - (January  6th 2015) Added vectorial instructions           //
// Revision v0.5 - (Sept    15th 2015) Separated controller and decoder       //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

`include "defines.sv"

module controller
(
  input  logic        clk,
  input  logic        rst_n,

  input  logic        fetch_enable_i,             // Start the decoding
  output logic        core_busy_o,                // Core is busy processing instructions
  output logic        is_decoding_o,              // Core is in decoding state

  // decoder related signals
  output logic        deassert_we_o,              // deassert write enable for next instruction
  input  logic        illegal_insn_i,             // decoder encountered an invalid instruction
  input  logic        eret_insn_i,                // decoder encountered an eret instruction
  input  logic        pipe_flush_i,               // decoder wants to do a pipe flush

  input  logic        rega_used_i,                // register A is used
  input  logic        regb_used_i,                // register B is used
  input  logic        regc_used_i,                // register C is used

  // from IF/ID pipeline
  input  logic [31:0] instr_rdata_i,              // Instruction read from instr memory/cache: (sampled in the if stage)

  // from prefetcher
  output logic        instr_req_o,                // Start fetching instructions
  input  logic        instr_ack_i,                // Acknow from instr memory or cache (means that data is available)

  // to prefetcher
  output logic        pc_set_o,                   // jump to address set by pc_mux_sel
  output logic [2:0]  pc_mux_sel_o,               // Selector in the Fetch stage to select the rigth PC (normal, jump ...)

  // LSU
  input  logic        data_req_ex_i,              // data memory access is currently performed in EX stage
  input  logic        data_misaligned_i,

  // hwloop signals
  input  logic        hwloop_jump_i,              // modify pc_mux_sel to select the hwloop addr

  // jump/branch signals
  input  logic [1:0]  jump_in_ex_i,               // jump is being calculated in ALU
  input  logic [1:0]  jump_in_id_i,               // jump is being calculated in ALU
  input  logic [1:0]  jump_in_dec_i,              // jump is being calculated in ALU

  input  logic        branch_decision_i,          // branch decision is available in EX stage

  // Interrupt signals
  input  logic        irq_present_i,              // there is an IRQ, so if we are sleeping we should wake up now
  // Exception Controller Signals
  input  logic        exc_pc_sel_i,               // exception execution requested
  input  logic        exc_pipe_flush_i,           // flush pipeline after exception handling
  input  logic        trap_hit_i,                 // a trap was hit, so we have to flush EX and WB
  output logic        illegal_insn_o,             // illegal instruction encountered
  output logic        clear_isr_running_o,        // an l.rfe instruction was encountered, exit ISR

  // Debug Unit Signals
  input  logic        dbg_stall_i,                // Pipeline stall is requested
  input  logic        dbg_set_npc_i,              // Change PC to value from debug unit
  output logic        dbg_trap_o,                 // trap hit, inform debug unit

  // Forwarding signals from regfile
  input  logic [4:0]  regfile_waddr_ex_i,         // FW: write address from EX stage
  input  logic        regfile_we_ex_i,            // FW: write enable from  EX stage
  input  logic [4:0]  regfile_waddr_wb_i,         // FW: write address from WB stage
  input  logic        regfile_we_wb_i,            // FW: write enable from  WB stage
  input  logic [4:0]  regfile_alu_waddr_fw_i,     // FW: ALU/MUL write address from EX stage
  input  logic        regfile_alu_we_fw_i,        // FW: ALU/MUL write enable from  EX stage

  // forwarding signals
  output logic [1:0]  operand_a_fw_mux_sel_o,     // regfile ra data selector form ID stage
  output logic [1:0]  operand_b_fw_mux_sel_o,     // regfile rb data selector form ID stage
  output logic [1:0]  operand_c_fw_mux_sel_o,     // regfile rc data selector form ID stage

  // stall signals
  output logic        halt_if_o,
  output logic        halt_id_o,

  output logic        misaligned_stall_o,
  output logic        jr_stall_o,
  output logic        load_stall_o,

  input  logic        if_valid_i,                 // IF stage is done
  input  logic        id_valid_i,                 // ID stage is done
  input  logic        ex_valid_i,                 // EX stage is done
  input  logic        wb_valid_i,                 // WB stage is done

  // Performance Counters
  output logic        perf_jump_o,                // we are executing a jump instruction   (j, jr, jal, jalr)
  output logic        perf_branch_o,              // we are executing a branch instruction (bf, bnf)
  output logic        perf_jr_stall_o,            // stall due to jump-register-hazard
  output logic        perf_ld_stall_o             // stall due to load-use-hazard
);

  // FSM state encoding
  enum  logic [3:0] { RESET, BOOT_SET, SLEEP, FIRST_FETCH,
                      DECODE, BRANCH,
                      FLUSH_EX, FLUSH_WB,
                      DBG_FLUSH_EX, DBG_FLUSH_WB, DBG_SIGNAL, DBG_WAIT } ctrl_fsm_cs, ctrl_fsm_ns;

  logic reg_d_ex_is_reg_a_id;
  logic reg_d_ex_is_reg_b_id;
  logic reg_d_ex_is_reg_c_id;
  logic reg_d_wb_is_reg_a_id;
  logic reg_d_wb_is_reg_b_id;
  logic reg_d_wb_is_reg_c_id;
  logic reg_d_alu_is_reg_a_id;
  logic reg_d_alu_is_reg_b_id;
  logic reg_d_alu_is_reg_c_id;


`ifndef SYNTHESIS
  // synopsys translate_off
  // make sure we are called later so that we do not generate messages for
  // glitches
  always_ff @(negedge clk)
  begin
    // print warning in case of decoding errors
    if (illegal_insn_o) begin
      $display("%t: Illegal instruction (core %0d) at PC 0x%h:", $time, riscv_core.core_id_i,
               id_stage.current_pc_id_i);
      //prettyPrintInstruction(instr_rdata_i, id_stage.current_pc_id_i);
    end
  end
  // synopsys translate_on
`endif


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
    instr_req_o         = 1'b1;

    pc_mux_sel_o        = `PC_BOOT;
    pc_set_o            = 1'b0;

    ctrl_fsm_ns         = ctrl_fsm_cs;

    core_busy_o         = 1'b1;
    is_decoding_o       = 1'b0;

    halt_if_o           = 1'b0;
    halt_id_o           = 1'b0;
    dbg_trap_o          = 1'b0;
    illegal_insn_o      = 1'b0;
    clear_isr_running_o = 1'b0;

    unique case (ctrl_fsm_cs)
      // We were just reset, wait for fetch_enable
      RESET:
      begin
        core_busy_o   = 1'b0;
        instr_req_o   = 1'b0;

        if (fetch_enable_i == 1'b1)
          ctrl_fsm_ns = BOOT_SET;
      end

      // copy boot address to instr fetch address
      BOOT_SET:
      begin
        instr_req_o   = 1'b1;
        pc_mux_sel_o  = `PC_BOOT;
        pc_set_o      = 1'b1;

        ctrl_fsm_ns = FIRST_FETCH;
      end

      // instruction in if_stage is already valid
      SLEEP:
      begin
        // we begin execution when either fetch_enable is high or an
        // interrupt has arrived
        core_busy_o   = 1'b0;
        instr_req_o   = 1'b0;

        if (fetch_enable_i || irq_present_i)
        begin
          ctrl_fsm_ns  = FIRST_FETCH;
        end
      end // case: SLEEP

      FIRST_FETCH:
      begin
        // Stall because of IF miss
        if ((instr_ack_i == 1'b1) && (dbg_stall_i == 1'b0))
        begin
          ctrl_fsm_ns = DECODE;
        end

        // hwloop detected, jump to start address!
        // Attention: This has to be done in the DECODE and the FIRST_FETCH states
        if (hwloop_jump_i == 1'b1) begin
          pc_mux_sel_o  = `PC_HWLOOP;
          pc_set_o     = 1'b1;
        end
      end

      DECODE:
      begin
        is_decoding_o = 1'b1;

        // handle conditional branches
        if (jump_in_dec_i == `BRANCH_COND) begin
          // handle branch if decision is available in next cycle
          if (id_valid_i)
            ctrl_fsm_ns = BRANCH;
        end

        // handle unconditional jumps
        // we can jump directly since we know the address already
        if (jump_in_dec_i == `BRANCH_JALR || jump_in_dec_i == `BRANCH_JAL) begin
          pc_mux_sel_o = `PC_JUMP;

          // we don't have to change our current state here as the prefetch
          // buffer is automatically invalidated, thus the next instruction
          // that is served to the ID stage is the one of the jump target
        end

        // handle hwloops
        if (hwloop_jump_i) begin
          pc_mux_sel_o = `PC_HWLOOP;
        end

        // handle illegal instructions
        if (illegal_insn_i) begin
          illegal_insn_o = 1'b1;
        end

        if (exc_pc_sel_i) begin
          pc_mux_sel_o   = `PC_EXCEPTION;
          pc_set_o       = 1'b1;

          // we don't have to change our current state here as the prefetch
          // buffer is automatically invalidated, thus the next instruction
          // that is served to the ID stage is the one of the jump to the
          // exception handler
        end

        if (eret_insn_i) begin
          clear_isr_running_o = 1'b1;
          pc_mux_sel_o        = `PC_ERET;
          pc_set_o            = 1'b1;
        end

        // handle WFI instruction, flush pipeline and (potentially) go to
        // sleep
        if (pipe_flush_i || exc_pipe_flush_i)
        begin
          halt_if_o = 1'b1;
          halt_id_o = 1'b1;

          ctrl_fsm_ns = FLUSH_EX;
        end

        // take care of debug
        // branch conditional will be handled in next state
        if(trap_hit_i && jump_in_dec_i != `BRANCH_COND)
        begin
          // halt pipeline immediately
          halt_if_o = 1'b1;
          halt_id_o = 1'b1;

          // TODO: take a second look at this
          // make sure the current instruction has been executed
          // before changing state to non-decode
          //if (~stall_ex_o)
            ctrl_fsm_ns = DBG_SIGNAL;
        end
      end

      // handle branches
      BRANCH:
      begin
        // assume branch instruction is in EX
        if (jump_in_ex_i == `BRANCH_COND && ~branch_decision_i) begin
          // not taken

          // if we want to debug, flush the pipeline
          // the current_pc_if will take the value of the next instruction to
          // be executed (NPC)
          if (trap_hit_i)
          begin
            halt_if_o = 1'b1;
            halt_id_o = 1'b1;

            ctrl_fsm_ns = DBG_SIGNAL;
          end else begin
            if (if_valid_i)
              ctrl_fsm_ns = DECODE;
          end
        end else begin
          // branch taken
          pc_mux_sel_o = `PC_BRANCH;

          // if we want to debug, flush the pipeline
          // the current_pc_if will take the value of the next instruction to
          // be executed (NPC)
          if (trap_hit_i)
          begin
            ctrl_fsm_ns = DBG_SIGNAL;
          end else begin
            if (if_valid_i)
              ctrl_fsm_ns = DECODE;
          end
        end
      end

      // // make sure EX stage is flushed
      // DBG_FLUSH_EX:
      // begin
      //   halt_if_o = 1'b1;
      //   halt_id_o = 1'b1;

      //   if(stall_ex_o == 1'b0)
      //     ctrl_fsm_ns = DBG_FLUSH_WB;
      // end

      // // make sure WB stage is flushed
      // DBG_FLUSH_WB:
      // begin
      //   halt_if_o = 1'b1;
      //   halt_id_o = 1'b1;

      //   if(stall_ex_o == 1'b0)
      //     ctrl_fsm_ns = DBG_SIGNAL;
      // end

      // now we can signal to the debugger that our pipeline is empty and it
      // can examine our current state
      DBG_SIGNAL:
      begin
        dbg_trap_o = 1'b1;
        halt_if_o  = 1'b1;
        halt_id_o  = 1'b1;

        ctrl_fsm_ns = DBG_WAIT;
      end

      // The Debugger is active in this state
      // we wait until it is done and go back to DECODE
      DBG_WAIT:
      begin
        halt_if_o = 1'b1;
        halt_id_o = 1'b1;

        if(dbg_set_npc_i == 1'b1) begin
          halt_id_o    = 1'b0;
          pc_mux_sel_o = `PC_DBG_NPC;
          pc_set_o     = 1'b1;
          ctrl_fsm_ns  = DBG_WAIT;
        end

        if(dbg_stall_i == 1'b0) begin
          halt_if_o   = 1'b0;
          halt_id_o   = 1'b0;
          ctrl_fsm_ns = DECODE;
        end
      end

      // flush the pipeline, insert NOP into EX stage
      FLUSH_EX:
      begin
        halt_if_o = 1'b1;
        halt_id_o = 1'b1;

        if(ex_valid_i)
          ctrl_fsm_ns = FLUSH_WB;
      end

      // flush the pipeline, insert NOP into EX and WB stage
      FLUSH_WB:
      begin
        halt_if_o = 1'b1;
        halt_id_o = 1'b1;

        if (~fetch_enable_i) begin
          // we are requested to go to sleep
          if(wb_valid_i)
            ctrl_fsm_ns = SLEEP;
        end else begin
          // unstall pipeline and continue operation
          halt_if_o = 1'b0;
          halt_id_o = 1'b0;

          if (id_valid_i)
            ctrl_fsm_ns = DECODE;
        end
      end

      default: begin
        instr_req_o = 1'b0;
        ctrl_fsm_ns = RESET;
      end
    endcase
  end

  /////////////////////////////////////////////////////////////
  //  ____  _        _ _    ____            _             _  //
  // / ___|| |_ __ _| | |  / ___|___  _ __ | |_ _ __ ___ | | //
  // \___ \| __/ _` | | | | |   / _ \| '_ \| __| '__/ _ \| | //
  //  ___) | || (_| | | | | |__| (_) | | | | |_| | | (_) | | //
  // |____/ \__\__,_|_|_|  \____\___/|_| |_|\__|_|  \___/|_| //
  //                                                         //
  /////////////////////////////////////////////////////////////
  always_comb
  begin
    load_stall_o  = 1'b0;
    jr_stall_o    = 1'b0;
    deassert_we_o = 1'b0;

    // deassert WE when the core is not decoding instructions
    if (ctrl_fsm_cs != DECODE)
      deassert_we_o = 1'b1;

    // deassert WE in case of illegal instruction
    if (illegal_insn_i)
      deassert_we_o = 1'b1;

    // Stall because of load operation
    if ((data_req_ex_i == 1'b1) && (regfile_we_ex_i == 1'b1) &&
        ((reg_d_ex_is_reg_a_id == 1'b1) || (reg_d_ex_is_reg_b_id == 1'b1) || (reg_d_ex_is_reg_c_id == 1'b1)) )
    begin
      deassert_we_o   = 1'b1;
      load_stall_o    = 1'b1;
    end

    // Stall because of jr path
    // - always stall if a result is to be forwarded to the PC
    // we don't care about in which state the ctrl_fsm is as we deassert_we
    // anyway when we are not in DECODE
    if ((jump_in_dec_i == `BRANCH_JALR) &&
        (((regfile_we_wb_i == 1'b1) && (reg_d_wb_is_reg_a_id == 1'b1)) ||
         ((regfile_we_ex_i == 1'b1) && (reg_d_ex_is_reg_a_id == 1'b1)) ||
         ((regfile_alu_we_fw_i == 1'b1) && (reg_d_alu_is_reg_a_id == 1'b1))) )
    begin
      jr_stall_o      = 1'b1;
      deassert_we_o     = 1'b1;
    end
  end

  // stall because of misaligned data access
  assign misaligned_stall_o = data_misaligned_i;


  ////////////////////////////////////////////////////////////////////////////////////////////
  // Forwarding control unit. (Forwarding from wb and ex stage to id stage)                 //
  //  RiscV register encoding:  rs1 is [19:15], rs2 is [24:20], rd is [11:7]                //
  //  Or10n register encoding:  ra  is [20:16], rb  is [15:11], rd is [25:21]               //
  ////////////////////////////////////////////////////////////////////////////////////////////
  assign reg_d_ex_is_reg_a_id  = (regfile_waddr_ex_i     == instr_rdata_i[`REG_S1]) && (rega_used_i == 1'b1);
  assign reg_d_ex_is_reg_b_id  = (regfile_waddr_ex_i     == instr_rdata_i[`REG_S2]) && (regb_used_i == 1'b1);
  assign reg_d_ex_is_reg_c_id  = (regfile_waddr_ex_i     == instr_rdata_i[`REG_D])  && (regc_used_i == 1'b1);
  assign reg_d_wb_is_reg_a_id  = (regfile_waddr_wb_i     == instr_rdata_i[`REG_S1]) && (rega_used_i == 1'b1);
  assign reg_d_wb_is_reg_b_id  = (regfile_waddr_wb_i     == instr_rdata_i[`REG_S2]) && (regb_used_i == 1'b1);
  assign reg_d_wb_is_reg_c_id  = (regfile_waddr_wb_i     == instr_rdata_i[`REG_D])  && (regc_used_i == 1'b1);
  assign reg_d_alu_is_reg_a_id = (regfile_alu_waddr_fw_i == instr_rdata_i[`REG_S1]) && (rega_used_i == 1'b1);
  assign reg_d_alu_is_reg_b_id = (regfile_alu_waddr_fw_i == instr_rdata_i[`REG_S2]) && (regb_used_i == 1'b1);
  //assign reg_d_alu_is_reg_c_id = (regfile_alu_waddr_fw_i == instr_rdata_i[`REG_RD])  && (regc_used == 1'b1);
  assign reg_d_alu_is_reg_c_id = 1'b0;

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

    // Make sure x0 is never forwarded
    if (instr_rdata_i[`REG_S1] == 5'b0)
      operand_a_fw_mux_sel_o = `SEL_REGFILE;
    if (instr_rdata_i[`REG_S2] == 5'b0)
      operand_b_fw_mux_sel_o = `SEL_REGFILE;

    // for misaligned memory accesses
    if (data_misaligned_i == 1'b1)
    begin
      operand_a_fw_mux_sel_o  = `SEL_FW_EX;
      operand_b_fw_mux_sel_o  = `SEL_REGFILE;
    end
  end

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

  // Performance Counters
  assign perf_jump_o      = (jump_in_id_i == `BRANCH_JAL || jump_in_id_i == `BRANCH_JALR);
  assign perf_branch_o    = (jump_in_id_i == `BRANCH_COND);
  assign perf_jr_stall_o  = jr_stall_o;
  assign perf_ld_stall_o  = load_stall_o;

endmodule // controller
