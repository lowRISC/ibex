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
// Revision v0.4 - (July 30th 2015) Removed instr_core_interface, handling    //
//                 the cache interface in IF now                              //
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
    output logic        ack_o,
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
    input  logic [31:0] exception_pc_reg_i,    // address used to restore the program counter when the interrupt/exception is served
    input  logic [31:0] pc_from_hwloop_i,      // pc from hwloop start addr
    input  logic  [2:0] pc_mux_sel_i,          // sel for pc multiplexer
    input  logic        pc_mux_boot_i,         // load boot address as PC
    input  logic  [1:0] exc_pc_mux_i,          // select which exception to execute

    // jump and branch target and decision
    input  logic [31:0] jump_target_i,      // jump target address
    input  logic  [1:0] jump_in_id_i,
    input  logic  [1:0] jump_in_ex_i,       // jump in EX -> get PC from jump target (could also be branch)
    input  logic        branch_decision_i,

    // from debug unit
    input  logic [31:0] dbg_pc_from_npc,
    input  logic        dbg_set_npc,

    // pipeline stall
    input  logic        stall_if_i,
    input  logic        stall_id_i
);


  logic [31:0] next_pc;

  // next PC mux inputs
  logic [31:0] incr_pc;            // increased PC
  logic [31:0] exc_pc;             // PC from exception


  enum logic [2:0] {IDLE, WAIT_BRANCH, FETCH_STALLED, FETCH_UNSTALLED, WAIT_IF_STALL} CS, NS;


  // PC generation FSM
  enum logic [0:0] {REGULAR, HANDLE_BRANCH} CS_PCGEN, NS_PCGEN;

  // instruction cache interface signals
  //enum logic [1:0] {IDLE, WAIT_GNT, WAIT_RVALID, WAIT_IF_STALL} CS_FETCH, NS_FETCH;
  logic [31:0] fetch_addr, fetch_addr_n;
  logic [31:0] fetch_data, fetch_data_n;

  logic [31:0] instr_addr_o_n;


  logic [31:0] last_fetch_addr;


  // instr_core_interface
  logic        req_int;
  logic        ack_int;
  logic [31:0] addr_int;
  logic [31:0] rdata_int;


  logic        force_nop_int;
  logic [31:0] instr_rdata_int;
  assign instr_rdata_int = (force_nop_int == 1'b0)? rdata_int : {25'b0, `OPCODE_OPIMM};


  // increased PC calculation
  always_comb
  begin
    if (rdata_int[1:0] != 2'b11) begin
      // compressed instruction
      incr_pc = current_pc_if_o + 32'd2;
    end else begin
      incr_pc = current_pc_if_o + 32'd4;
    end
  end


  // exception PC selection mux
  always_comb
  begin : EXC_PC_MUX
    unique case (exc_pc_mux_i)
      `EXC_PC_NO_INCR:  begin  exc_pc = current_pc_if_o;                        end
      `EXC_PC_ILLINSN:  begin  exc_pc = {boot_addr_i[31:5], `EXC_OFF_ILLINSN }; end
      `EXC_PC_IRQ:      begin  exc_pc = {boot_addr_i[31:5], `EXC_OFF_IRQ     }; end
      `EXC_PC_IRQ_NM:   begin  exc_pc = {boot_addr_i[31:5], `EXC_OFF_IRQ_NM  }; end
    endcase
  end

  // next PC selection
  always_comb
  begin
    unique case (pc_mux_sel_i)
      `PC_NO_INCR:   next_pc = current_pc_if_o;    // PC is not incremented
      `PC_INCR:      next_pc = incr_pc;            // incremented PC
      `PC_EXCEPTION: next_pc = exc_pc;             // set PC to exception handler
      `PC_ERET:      next_pc = exception_pc_reg_i; // PC is restored when returning from IRQ/exception
      `PC_HWLOOP:    next_pc = pc_from_hwloop_i;   // PC is taken from hwloop start addr
      default:
      begin
        next_pc = current_pc_if_o;
        // synopsys translate_off
        $display("%t: Illegal pc_mux_sel value (%0d)!", $time, pc_mux_sel_i);
        // synopsys translate_on
      end
    endcase

    if (jump_in_ex_i == 2'b01) begin
      // jump handling
      next_pc = jump_target_i;
    end else if (jump_in_ex_i == 2'b10) begin
      // branch handling
      if (branch_decision_i == 1'b1)
        next_pc = jump_target_i;
      else
        next_pc = incr_pc;
        //next_pc = current_pc_if_o;
    end

    if (pc_mux_boot_i)
      next_pc = {boot_addr_i[31:5], `EXC_OFF_RST};
  end


  always_comb
  begin
    NS = CS;

    req_int = 1'b0;
    addr_int = '0;

    ack_o = 1'b0;

    force_nop_int = 1'b0;

    unique case (CS)
      IDLE:
      begin
        if (req_i) begin
          if (jump_in_id_i == 2'b0) begin
            if (force_nop_i) begin
              force_nop_int = 1'b1;
              ack_o = 1'b1;
            end else begin
              // no branch, do normal fetch
              req_int = 1'b1;
              addr_int = next_pc;
              if (stall_if_i) begin
                NS = FETCH_STALLED;
              end else begin
                NS = FETCH_UNSTALLED;
              end
            end
          end
          else
          begin
            // wait for branch decision / jump target
            force_nop_int = 1'b1;
            ack_o = 1'b1;
            NS = WAIT_BRANCH;
          end
        end
      end

      WAIT_BRANCH:
      begin
        if (jump_in_ex_i != 2'b0) begin
          req_int = 1'b1;
          addr_int = next_pc;
          if (stall_if_i) begin
            NS = FETCH_STALLED;
          end else begin
            NS = FETCH_UNSTALLED;
          end
        end
      end

      FETCH_STALLED,
      FETCH_UNSTALLED:
      begin
        if (ack_int) begin
          NS = IDLE;
          ack_o = 1'b1;
          if (stall_if_i) begin
            if (CS == FETCH_STALLED) begin
              // already fetched instruction for after stall
              NS = WAIT_IF_STALL;
            end
          end
        end
      end

      WAIT_IF_STALL:
      begin
        NS = IDLE;
        ack_o = 1'b1;

        if (stall_if_i)
          NS = WAIT_IF_STALL;
      end

      default:
      begin
        $display("%t: invalid state", $time);
      end
    endcase
  end

  always_ff @(posedge clk, negedge rst_n)
  begin
    if (rst_n == 1'b0)
    begin
      CS <= IDLE;
    end
    else
    begin
      CS <= NS;
    end
  end


  // cache fetch interface
  instr_core_interface instr_core_if_i
  (
    .clk            ( clk            ),
    .rst_n          ( rst_n          ),

    .req_i          ( req_int        ),
    .ack_o          ( ack_int        ),
    .addr_i         ( addr_int       ),
    .rdata_o        ( rdata_int      ),

    .instr_req_o    ( instr_req_o    ),
    .instr_addr_o   ( instr_addr_o   ),
    .instr_gnt_i    ( instr_gnt_i    ),
    .instr_rvalid_i ( instr_rvalid_i ),
    .instr_rdata_i  ( instr_rdata_i  ),

    .last_addr_o    ( last_fetch_addr ),

    .stall_if_i     ( stall_if_i     ),

    .drop_request_i ( drop_request_i )
  );


  // IF PC register
  always_ff @(posedge clk, negedge rst_n)
  begin : IF_PIPELINE
    if (rst_n == 1'b0)
    begin
      current_pc_if_o    <= 32'h0;
    end
    else
    begin
      if (pc_mux_boot_i == 1'b1)
      begin
        // set PC to reset vector
        current_pc_if_o  <= {boot_addr_i[31:5], `EXC_OFF_RST};
      end
      else if (dbg_set_npc == 1'b1)
      begin
        // debug units sets NPC, PC_MUX_SEL holds this value
        current_pc_if_o  <= dbg_pc_from_npc;
      end
      else if (stall_if_i == 1'b0)
      begin
        current_pc_if_o  <= last_fetch_addr;
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
        //current_pc_id_o  <= current_pc_if_o;
        current_pc_id_o  <= last_fetch_addr;
      end
    end
  end

endmodule
