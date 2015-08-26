////////////////////////////////////////////////////////////////////////////////
// Company:        IIS @ ETHZ - Federal Institute of Technology               //
//                 DEI @ UNIBO - University of Bologna                        //
//                                                                            //
// Engineer:       Renzo Andri - andrire@student.ethz.ch                      //
//                                                                            //
// Additional contributions by:                                               //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                                                                            //
//                                                                            //
// Create Date:    01/07/2014                                                 //
// Design Name:    RISC-V processor core                                      //
// Module Name:    if_stage.sv                                                //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Instruction fetch unit: Selection of the next PC, and      //
//                 buffering (sampling) of the read instruction               //
// Revision:                                                                  //
// Revision v0.1 - File Created                                               //
// Revision v0.2 - (August 6th 2014) Changed port and signal names, addedd    //
//                 comments                                                   //
// Revision v0.3 - (December 1th 2014) Merged debug unit and added more       //
//                 exceptions                                                 //
// Revision v0.4 - (July 30th 2015) Moved instr_core_interface into IF,       //
//                 handling compressed instructions with FSM                  //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////


`include "defines.sv"

module if_stage
(
    input  logic        clk,
    input  logic        rst_n,

    // the boot address is used to calculate the exception offsets
    input  logic [31:0] boot_addr_i,

    // instruction request control
    input  logic        req_i,
    output logic        valid_o,
    input  logic        drop_request_i,

    // instruction cache interface
    output logic        instr_req_o,
    output logic [31:0] instr_addr_o,
    input  logic        instr_gnt_i,
    input  logic        instr_rvalid_i,
    input  logic [31:0] instr_rdata_i,

    // Output of IF Pipeline stage
    output logic [31:0] instr_rdata_id_o,      // read instruction is sampled and sent to ID stage for decoding
    output logic [31:0] current_pc_if_o,
    output logic [31:0] current_pc_id_o,

    // Forwarding ports - control signals
    input  logic        force_nop_i,           // insert a NOP in the pipe
    input  logic [31:0] exception_pc_reg_i,    // address used to restore PC when the interrupt/exception is served
    input  logic [31:0] pc_from_hwloop_i,      // pc from hwloop start addr
    input  logic  [2:0] pc_mux_sel_i,          // sel for pc multiplexer
    input  logic  [1:0] exc_pc_mux_i,          // select which exception to execute

    // jump and branch target and decision
    input  logic  [1:0] jump_in_id_i,
    input  logic  [1:0] jump_in_ex_i,       // jump in EX -> get PC from jump target (could also be branch)
    input  logic [31:0] jump_target_i,      // jump target address
    input  logic        branch_decision_i,

    // from debug unit
    input  logic [31:0] dbg_pc_from_npc,
    input  logic        dbg_set_npc,

    // pipeline stall
    input  logic        stall_if_i,
    input  logic        stall_id_i
);


  logic [31:0] exc_pc;

  logic  [1:0] is_compressed;
  logic        unaligned, unaligned_Q;
  logic        unaligned_jump;
  logic        branch_taken;

  logic        force_nop_int;
  logic [31:0] instr_rdata_int;
  logic [31:0] current_pc_id_int;

  // instr_core_interface
  logic        fetch_req;
  logic [31:0] fetch_rdata;
  logic        fetch_valid;
  logic [31:0] fetch_addr, fetch_addr_n;
  logic [31:0] fetch_addr_Q;

  // local cache
  logic [15:0] data_arr;


  // store instr_core_if data in local cache
  always_ff @(posedge clk, negedge rst_n)
  begin
    if (rst_n == 1'b0) begin
      data_arr <= 16'b0;
    end else begin
      if (fetch_valid) begin
        data_arr <= fetch_rdata[31:16];
      end
    end
  end


  always_comb
  begin
    // default values for regular aligned access
    instr_rdata_int   = fetch_rdata;
    current_pc_id_int = {fetch_addr[31:2], 2'b00};

    if (unaligned) begin
      if (unaligned_Q) begin
        // cross-word access
        instr_rdata_int   = {fetch_rdata[15:0], data_arr};
        current_pc_id_int = {fetch_addr_Q[31:2], 2'b10};
      end else begin
        // unaligned compressed instruction
        // don't care about upper half-word, insert good value for
        // optimization
        instr_rdata_int   = {fetch_rdata[31:16], fetch_rdata[31:16]};
        current_pc_id_int = {fetch_addr[31:2], 2'b10};
      end
    end

    // insert NOPs for branches
    if (force_nop_int)
      instr_rdata_int = {25'b0, `OPCODE_OPIMM};
  end

  assign current_pc_if_o = current_pc_id_int;


  // compressed instruction detection
  assign is_compressed[0] = fetch_rdata[1:0]   != 2'b11;
  assign is_compressed[1] = fetch_rdata[17:16] != 2'b11;


  // exception PC selection mux
  always_comb
  begin : EXC_PC_MUX
    unique case (exc_pc_mux_i)
      `EXC_PC_ILLINSN: begin exc_pc = {boot_addr_i[31:5], `EXC_OFF_ILLINSN }; end
      `EXC_PC_IRQ:     begin exc_pc = {boot_addr_i[31:5], `EXC_OFF_IRQ     }; end
      `EXC_PC_IRQ_NM:  begin exc_pc = {boot_addr_i[31:5], `EXC_OFF_IRQ_NM  }; end
    endcase
  end

  // next PC selection
  always_comb
  begin
    unique case (pc_mux_sel_i)
      `PC_BOOT:      fetch_addr_n = {boot_addr_i[31:5], `EXC_OFF_RST};
      `PC_JUMP:      fetch_addr_n = {jump_target_i[31:2], 2'b0};
      `PC_INCR:      fetch_addr_n = fetch_addr + 32'd4; // incremented PC
      `PC_EXCEPTION: fetch_addr_n = exc_pc;             // set PC to exception handler
      `PC_ERET:      fetch_addr_n = exception_pc_reg_i; // PC is restored when returning from IRQ/exception
      `PC_HWLOOP:    fetch_addr_n = pc_from_hwloop_i;   // PC is taken from hwloop start addr
      default:
      begin
        fetch_addr_n = {boot_addr_i[31:5], `EXC_OFF_RST};
        // synopsys translate_off
        $display("%t: Illegal pc_mux_sel value (%0d)!", $time, pc_mux_sel_i);
        // synopsys translate_on
      end
    endcase
  end


  // cache fetch interface
  instr_core_interface instr_core_if_i
  (
    .clk            ( clk            ),
    .rst_n          ( rst_n          ),

    .req_i          ( fetch_req      ),
    .valid_o        ( fetch_valid    ),
    .addr_i         ( fetch_addr_n   ),
    .rdata_o        ( fetch_rdata    ),
    .last_addr_o    ( fetch_addr     ),

    .instr_req_o    ( instr_req_o    ),
    .instr_addr_o   ( instr_addr_o   ),
    .instr_gnt_i    ( instr_gnt_i    ),
    .instr_rvalid_i ( instr_rvalid_i ),
    .instr_rdata_i  ( instr_rdata_i  ),

    .stall_if_i     ( 1'b0           ),
    .drop_request_i ( 1'b0           )  // TODO: Remove?
  );


  // offset FSM
  enum logic[3:0] {IDLE, WAIT_ALIGNED, WAIT_UNALIGNED, VALID_ALIGNED, VALID_UNALIGNED,
                   HANDLE_BRANCH, FETCH_UNALIGNED} offset_fsm_cs, offset_fsm_ns;

  always_ff @(posedge clk, negedge rst_n)
  begin
    if (rst_n == 1'b0) begin
      offset_fsm_cs <= IDLE;
    end else begin
      offset_fsm_cs <= offset_fsm_ns;
    end
  end

  // offset FSM state logic
  always_comb
  begin
    offset_fsm_ns = offset_fsm_cs;

    fetch_req = 1'b0;
    valid_o = 1'b0;

    unaligned = 1'b0;
    force_nop_int = 1'b0;
    branch_taken = 1'b0;

    unique case (offset_fsm_cs)
      // no valid instruction data for ID stage
      // assume aligned
      IDLE: begin
        if (req_i) begin
          fetch_req = 1'b1;
          offset_fsm_ns = WAIT_ALIGNED;
        end
      end

      VALID_ALIGNED,
      WAIT_ALIGNED: begin
        if (fetch_valid || offset_fsm_cs == VALID_ALIGNED) begin
          valid_o = 1'b1;
          offset_fsm_ns = VALID_ALIGNED;

          if (req_i && ~stall_if_i) begin
            if (jump_in_id_i == `BRANCH_NONE) begin
              // ----------------------------------------------------------------------
              // no branch in ID, do regular fetch
              // ----------------------------------------------------------------------
              if (is_compressed[0]) begin
                // compressed instruction
                if (is_compressed[1]) begin
                  // upper half contains compressed instruction and is available
                  // from register
                  offset_fsm_ns = VALID_UNALIGNED;
                end else begin
                  // cross-word access, upper half is regular instruction
                  fetch_req     = 1'b1;
                  offset_fsm_ns = WAIT_UNALIGNED;
                end
              end else begin
                // regular instruction
                fetch_req     = 1'b1;
                offset_fsm_ns = WAIT_ALIGNED;
              end

            end else begin
              // ----------------------------------------------------------------------
              // need to handle branch
              // ----------------------------------------------------------------------
              offset_fsm_ns = HANDLE_BRANCH;
            end
          end
        end
      end

      WAIT_UNALIGNED,
      VALID_UNALIGNED: begin
        unaligned = 1'b1;

        if (fetch_valid || offset_fsm_cs == VALID_UNALIGNED) begin
          valid_o = 1'b1;

          if (req_i && ~stall_if_i) begin
            if (jump_in_id_i == `BRANCH_NONE) begin
              // ----------------------------------------------------------------------
              // no branch in ID, do regular fetch
              // ----------------------------------------------------------------------
              fetch_req = 1'b1;

              if (is_compressed[1]) begin
                // compressed instruction, next instruction will be aligned
                offset_fsm_ns = WAIT_ALIGNED;
              end else begin
                // regular instruction, fetch following instruction
                offset_fsm_ns = WAIT_UNALIGNED;
              end
            end else begin
              // ----------------------------------------------------------------------
              // need to handle branch
              // ----------------------------------------------------------------------
              offset_fsm_ns = HANDLE_BRANCH;
            end
          end
        end
      end

      HANDLE_BRANCH: begin
        // assume jump/branch instruction is in EX stage
        if (jump_in_ex_i == `BRANCH_COND && ~branch_decision_i) begin
          // TODO: Optimize this, already send request & valid
          if (unaligned_Q)
            offset_fsm_ns = VALID_UNALIGNED;
          else
            offset_fsm_ns = VALID_ALIGNED;
        end else begin
          // branch/jump taken
          branch_taken = 1'b1;
          fetch_req    = 1'b1;
          if (unaligned_jump) begin
            unaligned = 1'b1;
            // if the target address is unaligned, we need to fetch the lower
            // word first
            offset_fsm_ns = FETCH_UNALIGNED;
          end else begin
            offset_fsm_ns = WAIT_ALIGNED;
          end
        end
      end

      FETCH_UNALIGNED: begin
        unaligned = 1'b1;

        if (fetch_valid) begin
          if (is_compressed[1]) begin
            // no cross-word access
            valid_o = 1'b1;
            offset_fsm_ns = WAIT_ALIGNED;
          end else begin
            // cross-word access, fetch next word
            fetch_req = 1'b1;
            offset_fsm_ns = WAIT_UNALIGNED;
          end
        end
      end

    endcase
  end


  always_comb
  begin
    unaligned_jump = 1'b0;

    case (pc_mux_sel_i)
      `PC_JUMP:   unaligned_jump = jump_target_i[1];
      `PC_ERET:   unaligned_jump = exception_pc_reg_i[1];
      `PC_HWLOOP: unaligned_jump = pc_from_hwloop_i[1];
    endcase
  end


  // IF PC register
  always_ff @(posedge clk, negedge rst_n)
  begin : IF_PIPELINE
    if (rst_n == 1'b0)
    begin
      unaligned_Q  <= 1'b0;
      fetch_addr_Q <= 32'b0;
    end
    else
    begin
      if (fetch_valid) begin
        unaligned_Q  <= unaligned;
        fetch_addr_Q <= fetch_addr;
      end
    end
  end

  // IF-ID pipeline registers, frozen when the ID stage is stalled
  always_ff @(posedge clk, negedge rst_n)
  begin : IF_ID_PIPE_REGISTERS
    if (rst_n == 1'b0)
    begin
      instr_rdata_id_o   <= '0;
      current_pc_id_o    <= '0;
    end
    else
    begin
      if (stall_id_i == 1'b0)
      begin : ENABLED_PIPE
        instr_rdata_id_o <= instr_rdata_int;
        current_pc_id_o  <= current_pc_id_int;
      end
    end
  end

endmodule
