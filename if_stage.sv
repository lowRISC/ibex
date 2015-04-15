////////////////////////////////////////////////////////////////////////////////
// Company:        IIS @ ETHZ - Federal Institute of Technology               //
//                 DEI @ UNIBO - University of Bologna                        //
//                                                                            //
// Engineer:       Renzo Andri - andrire@student.ethz.ch                      //
//                                                                            //
// Additional contributions by:                                               //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                                                                            //
//                                                                            //
// Create Date:    01/07/2014                                                 //
// Design Name:    Instruction fetch stage                                    //
// Module Name:    if_stage.sv                                                //
// Project Name:   RiscV                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Instruction fetch unit: Selection of the next PC, and      //
//                 buffering (Sampling) of the read instruction               //
// Revision:                                                                  //
// Revision v0.1 - File Created                                               //
// Revision v0.2 - (August 6th 2014) Changed port and signal names, addedd    //
//                 comments                                                   //
// Revision v0.3 - (December 1th 2014) Merged debug unit and added more       //
//                 exceptions                                                 //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////



`include "defines.sv"

module if_stage
(
    input  logic clk,
    input  logic rst_n,

    // the boot address is used to calculate the exception offsets
    input  logic [31:0] boot_addr_i,

    // Output of IF Pipeline stage
    output logic [31:0] instr_rdata_id_o,      // read instruction is sampled and sent to ID stage for decoding
    output logic [31:0] current_pc_if_o,       // "current" pc program counter
    output logic [31:0] current_pc_id_o,       // current pc program counter

    // From to Instr memory
    input  logic [31:0] instr_rdata_i,         // Instruction read from instruction memory /cache
    output logic [31:0] instr_addr_o,          // address for instruction fetch

    // Forwarding ports - control signals
    input  logic        force_nop_i,           // insert a NOP in the pipe
    input  logic [31:0] exception_pc_reg_i,    // address used to restore the program counter when the interrupt/exception is served
    input  logic [31:0] pc_from_regfile_i,     // pc from reg file
    //input  logic [31:0] pc_from_immediate_i,   // pc from immediate
    input  logic [31:0] pc_from_hwloop_i,      // pc from hwloop start addr
    input  logic  [2:0] pc_mux_sel_i,          // sel for pc multiplexer
    input  logic        pc_mux_boot_i,         // load boot address as PC
    input  logic  [1:0] exc_pc_mux_i,          // select which exception to execute

    // jump and branch target and decision
    input  logic [31:0] jump_target_i,      // jump target
    input  logic  [1:0] jump_in_ex_i,       // jump in EX -> get PC from jump target (could also be branch)
    input  logic        branch_decision_i,

    // from debug unit
    input  logic [31:0]  dbg_pc_from_npc,
    input  logic         dbg_set_npc,

    // pipeline stall
    input  logic         stall_if_i,
    input  logic         stall_id_i             // Stall in the id stage: here (if_stage) freeze the registers
);


  ////////////////////////////////////
  // Instruction Fetch (IF) signals //
  ////////////////////////////////////
  logic [31:0] next_pc;            // Next program counter
  logic [31:0] exc_pc;             // Exception PC
  logic [31:0] instr_rdata_int;    // The instruction read from instr memory/cache is forwarded to ID stage, and the controller can force this forwarding to a nop (BUBBLE)


  // Address to fetch the instruction
  assign instr_addr_o = next_pc;

  // Next PC Selection: pc_mux_sel_i comes from id_stage.controller
  /*always_comb
  begin : PC_MUX
    case (pc_mux_sel_i)
      `INCR_PC:         begin  next_pc = current_pc_if_o + 32'd4; end // PC is incremented and points the next instruction
      `NO_INCR:         begin  next_pc = current_pc_if_o;         end // PC is not incremented
      //`PC_FROM_REGFILE: begin  next_pc = pc_from_regfile_i;       end // PC is taken from the regfile
      //`PC_FROM_ALU:     begin  next_pc = pc_from_alu_i;           end // use calculated jump target from ALU
      `PC_EXCEPTION:    begin  next_pc = exc_pc;                  end // PC that points to the exception
      `EXC_PC_REG:      begin  next_pc = exception_pc_reg_i;      end // restore the PC when exiting from interr/ecpetions
      `HWLOOP_ADDR:     begin  next_pc = pc_from_hwloop_i;        end // PC is taken from hwloop start addr
`ifdef BRANCH_PREDICTION
      `PC_BRANCH_PRED:  begin  next_pc = correct_branch;          end // take pc from branch prediction
`endif
       default:         begin  next_pc = current_pc_if_o + 32'd4; end
     endcase //~case (pc_mux_sel_i)
  end */

  // Exception PC selection
  always_comb
  begin : EXC_PC_MUX
    case (exc_pc_mux_i)
      `EXC_PC_IRQ:      begin  exc_pc = {boot_addr_i[31:8], `EXC_IRQ    };     end
      `EXC_PC_IRQ_NM:   begin  exc_pc = {boot_addr_i[31:8], `EXC_IRQ_NM };     end
      `EXC_PC_ILLINSN:  begin  exc_pc = {boot_addr_i[31:8], `EXC_ILLINSN};     end
      `EXC_PC_NO_INCR:  begin  exc_pc = current_pc_if_o;                       end
    endcase //~case (exc_pc_mux_i)
  end


  // PC selection and force NOP logic
  always_comb
  begin
    next_pc = current_pc_if_o;
    instr_rdata_int = instr_rdata_i;

    unique case (pc_mux_sel_i)
      `PC_INCR:         next_pc = current_pc_if_o + 32'd4;  // PC is incremented and points the next instruction
      `PC_NO_INCR:      next_pc = current_pc_if_o;          // PC is not incremented
      `PC_EXCEPTION:    next_pc = exc_pc;                   // PC that points to the exception
      `EXC_PC_REG:      next_pc = exception_pc_reg_i;       // restore the PC when exiting from interr/ecpetions
      `HWLOOP_ADDR:     next_pc = pc_from_hwloop_i;         // PC is taken from hwloop start addr
       default:
       begin
         next_pc = current_pc_if_o;
         // synopsis translate off
         $display("%t: Illegal pc_mux_sel value (%0d)!", $time, pc_mux_sel_i);
         // synopsis translate on
       end
    endcase // unique case (pc_mux_sel_i)

    // if force NOP, do not increase PC
    if (force_nop_i == 1'b1) begin
      instr_rdata_int = { 25'b0, `OPCODE_OPIMM }; // addi x0 = x0 + 0
      next_pc = current_pc_if_o;
    end

    if (jump_in_ex_i == 2'b01) begin
      next_pc = jump_target_i;
    end else if (jump_in_ex_i == 2'b10) begin
      if (branch_decision_i == 1'b1)
        next_pc = jump_target_i;
      else
        next_pc = current_pc_if_o;// + 32'd4; // TODO: Check if merged with previous adder (from PC mux)
    end

  end


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // IF PC register                                                                                           //
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////
  always_ff @(posedge clk, negedge rst_n)
  begin : IF_PIPELINE
    if (rst_n == 1'b0)
    begin : ASSERT_RESET
      current_pc_if_o    <= 32'h0;
    end
    else
    begin : DEASSERT_RESET
      if ( pc_mux_boot_i == 1'b1 )
        begin
          // set PC to boot address if we were just reset
          current_pc_if_o  <= boot_addr_i;
        end
      else if ( dbg_set_npc == 1'b1 )
        begin
          // debug units sets NPC, PC_MUX_SEL holds this value
          current_pc_if_o  <= dbg_pc_from_npc;
        end
      else if ( stall_if_i == 1'b0 )
        begin : ENABLED_PIPE
          current_pc_if_o  <= next_pc;
        end
    end
  end

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // IF-ID PIPE: Pipeline that is frozen when the ID stage is stalled                                         //
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////
  always_ff @(posedge clk, negedge rst_n)
  begin : IF_ID_PIPE_REGISTERS
    if (rst_n == 1'b0)
    begin : ASSERT_RESET
      instr_rdata_id_o   <= '0;
      current_pc_id_o    <= '0;
    end
    else
    begin : DEASSERT_RESET
      if (stall_id_i == 1'b0)
      begin : ENABLED_PIPE
        instr_rdata_id_o <= instr_rdata_int;
        current_pc_id_o  <= current_pc_if_o;
      end
    end
  end

endmodule
