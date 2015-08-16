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
    input  logic [31:0] exception_pc_reg_i,    // address used to restore PC when the interrupt/exception is served
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


  logic sample_addr;
  logic [31:0] fetch_addr, fetch_addr_n;


  logic [31:0] last_fetch_addr;


  logic        force_nop_int;
  logic        handle_branch;
  logic        do_fetch;
  logic [31:0] instr_rdata_int;


  logic fetch_unaligned;
  logic fetch_hit;

  logic  [1:0] is_compressed;


  // instr_core_interface
  logic        req_int;
  logic        ack_int;
  logic [31:0] rdata_int;


  // local cache
  logic [31:0] data_tag;
  logic [1:0][31:0] data_arr;


  logic bypass_data_reg; // use data from instr_core_if, not from data_arr
  logic pc_if_offset, pc_if_offset_n;


  enum logic[3:0] {INVALID, VALID, FETCH, FETCH_NEXT, SERVE_OFFSET, WAIT_ACK, WAIT_REQ, IDLE} fetch_fsm_cs, fetch_fsm_ns;

  always_ff @(posedge clk, negedge rst_n)
  begin
    if (rst_n == 1'b0) begin
      fetch_fsm_cs <= IDLE;
    end else begin
      fetch_fsm_cs <= fetch_fsm_ns;
    end
  end


  assign compressed_instr = instr_rdata_int[1:0] != 2'b11;

  assign do_fetch = req_i;

  always_comb
  begin
    if (pc_if_offset) begin
      incr_pc = fetch_addr + (is_compressed[1] ? 32'd2 : 32'd4);
    end else begin
      incr_pc = fetch_addr + (is_compressed[0] ? 32'd2 : 32'd4);
    end
  end
  //assign incr_pc = current_pc_if_o + (instr_rdata_int[1:0] != 2'b11 ? 32'd2 : 32'd4);


  // store instr_core_if data in local cache
  always_ff @(posedge clk, negedge rst_n)
  begin
    if (rst_n == 1'b0) begin
      data_tag <= '0;
      data_arr <= 32'h0003;
    end else begin
      if (ack_int) begin
        data_tag    <= last_fetch_addr;
        data_arr[1] <= data_arr[0];
        data_arr[0] <= rdata_int;
      end
    end
  end

  // cache data output muxes
  always_comb
  begin
    if (bypass_data_reg) begin
      // bypass cache and get data directly from instr_core_if
      if (pc_if_offset)
        instr_rdata_int = {rdata_int[15:0], data_arr[0][31:16]};
      else
        instr_rdata_int = rdata_int;
    end else begin
      // serve data from cache
      if (pc_if_offset)
        instr_rdata_int = {data_arr[0][15:0], data_arr[1][31:16]};
      else
        instr_rdata_int = data_arr[0];
    end

    if (force_nop_int)
      instr_rdata_int = {25'b0, `OPCODE_OPIMM};
  end

  assign is_compressed[0] = data_arr[0][1:0]   != 2'b11;
  assign is_compressed[1] = data_arr[0][17:16] != 2'b11;
  //assign is_compressed[0] = rdata_int[1:0]   != 2'b11;
  //assign is_compressed[1] = rdata_int[17:16] != 2'b11;

  assign current_pc_if_o = pc_if_offset ? {last_fetch_addr[31:2], 2'b10} : fetch_addr;
  //assign current_pc_if_o = pc_if_offset ? {fetch_addr[31:2], 2'b10} : fetch_addr;


  always_comb
  begin
    fetch_unaligned = next_pc[1:0] != 2'b0;
    fetch_hit       = (next_pc[31:2] == data_tag[31:2]);
  end


  always_comb
  begin
    fetch_fsm_ns    = fetch_fsm_cs;

    force_nop_int   = 1'b0;
    bypass_data_reg = 1'b1;
    sample_addr     = 1'b1;

    //ack_o          = ack_int;
    //req_int        = req_i;
    ack_o          = 1'b0;
    req_int        = 1'b0;
    fetch_addr_n   = {next_pc[31:2], 2'b0};
    pc_if_offset_n = pc_if_offset;

    case (fetch_fsm_cs)
      IDLE:
      begin
        sample_addr = 1'b0;
        if (req_i)
          fetch_fsm_ns = WAIT_REQ;
      end

      WAIT_REQ:
      begin
        if (req_i) begin
          fetch_fsm_ns = WAIT_ACK;
          req_int = 1'b1;

          if (pc_if_offset) begin
            if (is_compressed[1]) begin
              // serve second part of already fetched instruction
              pc_if_offset_n = 1'b0;
              ack_o          = 1'b1;
              req_int        = 1'b1;
              fetch_fsm_ns   = WAIT_REQ;
            end else begin
              // cross line access
              // .. need to fetch next word here and delay everything till then
              sample_addr  = 1'b1;
              fetch_fsm_ns = FETCH_NEXT;
            end
          end else begin
            if (is_compressed[0]) begin
              sample_addr    = 1'b0;
              ack_o          = 1'b1;
              pc_if_offset_n = 1'b1;
            end
          end
        end
      end

      WAIT_ACK:
      begin
        sample_addr = 1'b0;
        if (ack_int) begin
          ack_o = 1'b1;
          fetch_fsm_ns = WAIT_REQ;
          // TODO: Already handle request here
        end
      end

      FETCH_NEXT:
      begin
        sample_addr = 1'b0;
        if (ack_int) begin
          //sample_addr = 1'b1;
          ack_o = 1'b1;
          fetch_fsm_ns = WAIT_REQ;
        end
      end
    endcase
  end


  //always_comb
  //begin
  //  fetch_fsm_ns    = fetch_fsm_cs;

  //  fetch_addr_n    = {next_pc[31:2], 2'b0};
  //  sample_addr     = 1'b0;

  //  pc_if_offset_n  = pc_if_offset; //1'b0;
  //  //sample_offset   = 1'b0;
  //  ack_o           = 1'b0;
  //  req_int         = 1'b0;
  //  force_nop_int   = 1'b0;

  //  bypass_data_reg = 1'b0;


  //  unique case (fetch_fsm_cs)
  //    INVALID:
  //    begin
  //      if (do_fetch) begin
  //        if (force_nop_i) begin
  //          force_nop_int = 1'b1;
  //          ack_o = 1'b1;
  //        end else begin
  //          fetch_fsm_ns = FETCH;
  //        end
  //      end
  //    end

  //    VALID:
  //    begin
  //      if (do_fetch) begin
  //        if (force_nop_i) begin
  //          force_nop_int = 1'b1;
  //          ack_o = 1'b1;
  //        end else begin
  //          if (fetch_hit) begin
  //            if (pc_if_offset) begin
  //              //fetch_addr_n = last_fetch_addr + 4;
  //              sample_addr = 1'b1;
  //              if (is_compressed[1]) begin
  //                pc_if_offset_n = 1'b0;
  //                ack_o = 1'b1;
  //              end else begin
  //                fetch_fsm_ns = FETCH_NEXT;
  //              end
  //            end else begin
  //              ack_o = 1'b1;
  //              if (is_compressed[0]) begin
  //                pc_if_offset_n = 1'b1;
  //              end else begin
  //                //fetch_addr_n = last_fetch_addr + 4;
  //                sample_addr = 1'b1;
  //              end
  //            end
  //          end else begin
  //            // fetch single requested word
  //            sample_addr = 1'b1;
  //            fetch_fsm_ns = FETCH;
  //          end
  //        end
  //      end
  //    end

  //    SERVE_OFFSET:
  //    begin
  //      ack_o = 1'b1;
  //      fetch_fsm_ns = VALID;
  //    end

  //    FETCH:
  //    begin
  //      req_int = 1'b1;
  //      if (ack_int) begin
  //        req_int = 1'b0; // TODO: Maybe only assert req_int before going into FETCH state
  //        bypass_data_reg = 1'b1;
  //        ack_o = 1'b1;
  //        fetch_fsm_ns = VALID;
  //      end
  //    end

  //    FETCH_NEXT:
  //    begin
  //      req_int = 1'b1;
  //      if (ack_int) begin
  //        req_int = 1'b0; // TODO: Maybe only assert req_int before going into FETCH state
  //        bypass_data_reg = 1'b1;
  //        ack_o = 1'b1;
  //        fetch_fsm_ns = VALID;

  //        sample_addr = 1'b1;
  //      end
  //    end
  //  endcase

  //  if (pc_mux_boot_i) begin
  //    sample_addr  = 1'b1;
  //    fetch_fsm_ns = INVALID;
  //  end
  //end


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
        next_pc = {boot_addr_i[31:5], `EXC_OFF_RST};
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
    end

    if (pc_mux_boot_i)
      next_pc = {boot_addr_i[31:5], `EXC_OFF_RST};
  end


  // cache fetch interface
  instr_core_interface instr_core_if_i
  (
    .clk            ( clk            ),
    .rst_n          ( rst_n          ),

    .req_i          ( req_int        ),
    .ack_o          ( ack_int        ),
    .addr_i         ( fetch_addr     ),
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
      fetch_addr   <= '0;
      pc_if_offset <= '0;
    end
    else
    begin
      if (pc_mux_boot_i == 1'b1) begin
        // set PC to reset vector
        fetch_addr   <= {boot_addr_i[31:5], `EXC_OFF_RST};
        pc_if_offset <= 1'b0;
      end else if (dbg_set_npc == 1'b1) begin
        // get PC from debug unit
        fetch_addr   <= {dbg_pc_from_npc[31:2], 2'b0};
        pc_if_offset <= (dbg_pc_from_npc[1:0] != 2'b0);
      //end else if (stall_if_i == 1'b0) begin
      end else begin
        // update PC
        pc_if_offset <= pc_if_offset_n;
        if (sample_addr)
          fetch_addr <= fetch_addr_n;
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
        current_pc_id_o  <= last_fetch_addr + (pc_if_offset? 32'd2 : '0);
        //current_pc_id_o  <= current_pc_if_o;
      end
    end
  end

endmodule
