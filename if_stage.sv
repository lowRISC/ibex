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

module riscv_if_stage
#(
  parameter RDATA_WIDTH = 32
)
(
    input  logic        clk,
    input  logic        rst_n,

    // the boot address is used to calculate the exception offsets
    input  logic [31:0] boot_addr_i,

    // instruction request control
    input  logic        req_i,

    // instruction cache interface
    output logic                   instr_req_o,
    output logic            [31:0] instr_addr_o,
    input  logic                   instr_gnt_i,
    input  logic                   instr_rvalid_i,
    input  logic [RDATA_WIDTH-1:0] instr_rdata_i,

    // Output of IF Pipeline stage
    output logic        instr_valid_id_o,      // instruction in IF/ID pipeline is valid
    output logic [31:0] instr_rdata_id_o,      // read instruction is sampled and sent to ID stage for decoding
    output logic        is_compressed_id_o,    // compressed decoder thinks this is a compressed instruction
    output logic        illegal_c_insn_id_o,   // compressed decoder thinks this is an invalid instruction
    output logic [31:0] current_pc_if_o,
    output logic [31:0] current_pc_id_o,

    // Forwarding ports - control signals
    input  logic        clear_instr_valid_i,   // clear instruction valid bit in IF/ID pipe
    input  logic        pc_set_i,              // set the program counter to a new value
    input  logic [31:0] exception_pc_reg_i,    // address used to restore PC when the interrupt/exception is served
    input  logic  [2:0] pc_mux_i,              // sel for pc multiplexer
    input  logic  [1:0] exc_pc_mux_i,          // selects ISR address
    input  logic  [4:0] exc_vec_pc_mux_i,      // selects ISR address for vectorized interrupt lines

    // jump and branch target and decision
    input  logic [31:0] jump_target_id_i,      // jump target address
    input  logic [31:0] jump_target_ex_i,      // jump target address

    // from hwloop controller
    input  logic        hwloop_jump_i,
    input  logic [31:0] hwloop_target_i,       // pc from hwloop start addr

    // from debug unit
    input  logic [31:0] dbg_npc_i,
    input  logic        dbg_set_npc_i,

    // pipeline stall
    input  logic        halt_if_i,
    output logic        if_ready_o,
    input  logic        id_ready_i,
    output logic        if_valid_o,

    // misc signals
    output logic        if_busy_o,             // is the IF stage busy fetching instructions?
    output logic        perf_imiss_o           // Instruction Fetch Miss
);

  // offset FSM
  enum logic[1:0] {WAIT_ALIGNED, WAIT_UNALIGNED, IDLE } offset_fsm_cs, offset_fsm_ns;

  logic  [1:0] is_compressed;
  logic        unaligned;
  logic        unaligned_jump;

  logic        valid;

  // prefetch buffer related signals
  logic        prefetch_busy;
  logic        branch_req;
  logic [31:0] fetch_addr_n;

  logic        fetch_valid;
  logic        fetch_ready;
  logic [31:0] fetch_rdata;
  logic [31:0] fetch_addr;

  logic        fetch_unaligned_valid;
  logic [31:0] fetch_unaligned_rdata;


  logic [31:0] instr_rdata_int;

  logic [31:0] exc_pc;


  // output data and PC mux
  always_comb
  begin
    // default values for regular aligned access
    current_pc_if_o   = {fetch_addr[31:2], 2'b00};
    instr_rdata_int   = fetch_rdata;

    if (unaligned) begin
      current_pc_if_o   = {fetch_addr[31:2], 2'b10};
      instr_rdata_int   = fetch_unaligned_rdata;
    end
  end


  // compressed instruction detection
  assign is_compressed[0] = (fetch_rdata[1:0]   != 2'b11);
  assign is_compressed[1] = (fetch_rdata[17:16] != 2'b11);


  // exception PC selection mux
  always_comb
  begin : EXC_PC_MUX
    exc_pc = 'x;
    unique case (exc_pc_mux_i)
      `EXC_PC_ILLINSN: exc_pc = { boot_addr_i[31:8], `EXC_OFF_ILLINSN };
      `EXC_PC_ECALL:   exc_pc = { boot_addr_i[31:8], `EXC_OFF_ECALL   };
      `EXC_PC_LOAD:    exc_pc = { boot_addr_i[31:8], `EXC_OFF_LSUERR  };
      `EXC_PC_IRQ:     exc_pc = { boot_addr_i[31:8], 1'b0, exc_vec_pc_mux_i[4:0], 2'b0 };
      // TODO: Add case for EXC_PC_STORE as soon as it differs from load

      default: begin
        // synopsys translate_off
        $display("%t: Illegal exc pc_mux value (%0d)!", $time, exc_pc_mux_i);
        // synopsys translate_on
      end
    endcase
  end

  // fetch address selection
  always_comb
  begin
    fetch_addr_n = 'x;

    unique case (pc_mux_i)
      `PC_BOOT:      fetch_addr_n = {boot_addr_i[31:8], `EXC_OFF_RST};
      `PC_JUMP:      fetch_addr_n = {jump_target_id_i[31:2], 2'b0};
      `PC_BRANCH:    fetch_addr_n = {jump_target_ex_i[31:2], 2'b0};
      `PC_EXCEPTION: fetch_addr_n = exc_pc;             // set PC to exception handler
      `PC_ERET:      fetch_addr_n = exception_pc_reg_i; // PC is restored when returning from IRQ/exception
      `PC_HWLOOP:    fetch_addr_n = hwloop_target_i;    // PC is taken from hwloop start addr
      `PC_DBG_NPC:   fetch_addr_n = dbg_npc_i;          // PC is taken from debug unit

      default: begin
        // synopsys translate_off
        $display("%t: Illegal pc_mux_sel value (%0d)!", $time, pc_mux_i);
        // synopsys translate_on
      end
    endcase
  end

  always_comb
  begin
    unaligned_jump = 1'b0;

    case (pc_mux_i)
      `PC_JUMP:    unaligned_jump = jump_target_id_i[1];
      `PC_BRANCH:  unaligned_jump = jump_target_ex_i[1];
      `PC_ERET:    unaligned_jump = exception_pc_reg_i[1];
      `PC_HWLOOP:  unaligned_jump = hwloop_target_i[1];
      `PC_DBG_NPC: unaligned_jump = dbg_npc_i[1];
    endcase
  end


  generate
    if (RDATA_WIDTH == 32) begin : prefetch_32
      // prefetch buffer, caches a fixed number of instructions
      riscv_prefetch_buffer prefetch_buffer_i
      (
        .clk               ( clk                   ),
        .rst_n             ( rst_n                 ),

        .req_i             ( 1'b1                  ),
        .branch_i          ( branch_req            ),
        .addr_i            ( fetch_addr_n          ),

        .ready_i           ( fetch_ready           ),
        .valid_o           ( fetch_valid           ),
        .rdata_o           ( fetch_rdata           ),
        .addr_o            ( fetch_addr            ),

        .unaligned_valid_o ( fetch_unaligned_valid ),
        .unaligned_rdata_o ( fetch_unaligned_rdata ),

        // goes to instruction memory / instruction cache
        .instr_req_o       ( instr_req_o           ),
        .instr_addr_o      ( instr_addr_o          ),
        .instr_gnt_i       ( instr_gnt_i           ),
        .instr_rvalid_i    ( instr_rvalid_i        ),
        .instr_rdata_i     ( instr_rdata_i         ),

        // Prefetch Buffer Status
        .busy_o            ( prefetch_busy         )
      );
    end else if (RDATA_WIDTH == 128) begin : prefetch_128
      // prefetch buffer, caches a fixed number of instructions
      riscv_prefetch_L0_buffer prefetch_buffer_i
      (
        .clk               ( clk                   ),
        .rst_n             ( rst_n                 ),

        .req_i             ( 1'b1                  ),
        .branch_i          ( branch_req            ),
        .addr_i            ( fetch_addr_n          ),

        .ready_i           ( fetch_ready           ),
        .valid_o           ( fetch_valid           ),
        .rdata_o           ( fetch_rdata           ),
        .addr_o            ( fetch_addr            ),

        .unaligned_valid_o ( fetch_unaligned_valid ),
        .unaligned_rdata_o ( fetch_unaligned_rdata ),

        // goes to instruction memory / instruction cache
        .instr_req_o       ( instr_req_o           ),
        .instr_addr_o      ( instr_addr_o          ),
        .instr_gnt_i       ( instr_gnt_i           ),
        .instr_rvalid_i    ( instr_rvalid_i        ),
        .instr_rdata_i     ( instr_rdata_i         ),

        // Prefetch Buffer Status
        .busy_o            ( prefetch_busy         )
      );
    end
  endgenerate


  // offset FSM state
  always_ff @(posedge clk, negedge rst_n)
  begin
    if (rst_n == 1'b0) begin
      offset_fsm_cs     <= IDLE;
    end else begin
      offset_fsm_cs     <= offset_fsm_ns;
    end
  end

  // offset FSM state transition logic
  always_comb
  begin
    offset_fsm_ns = offset_fsm_cs;

    fetch_ready   = 1'b0;
    branch_req    = 1'b0;
    valid         = 1'b0;

    unaligned     = 1'b0;

    unique case (offset_fsm_cs)
      // no valid instruction data for ID stage
      // assume aligned
      IDLE: begin
        if (req_i) begin
          branch_req    = 1'b1;
          offset_fsm_ns = WAIT_ALIGNED;
        end
      end

      // serving aligned 32 bit or 16 bit instruction, we don't know yet
      WAIT_ALIGNED: begin
        if (fetch_valid) begin
          valid   = 1'b1; // an instruction is ready for ID stage

          if (req_i && if_valid_o) begin

            if (~is_compressed[0]) begin
              // 32 bit aligned instruction found
              fetch_ready   = 1'b1;
              offset_fsm_ns = WAIT_ALIGNED;
            end else begin
              // 16 bit aligned instruction found
              // next instruction will be unaligned
              offset_fsm_ns = WAIT_UNALIGNED;
            end
          end
        end
      end

      // serving unaligned 32 bit instruction
      // next instruction might be 16 bit unaligned (no need to fetch)
      // or 32 bit unaligned (need to fetch another word from cache)
      WAIT_UNALIGNED: begin
        unaligned = 1'b1;

        if (fetch_valid) begin
          if (is_compressed[1]) begin
            valid   = 1'b1; // an instruction is ready for ID stage

            if (req_i && if_valid_o) begin
              // next instruction will be aligned
              fetch_ready   = 1'b1;
              offset_fsm_ns = WAIT_ALIGNED;
            end
          end else begin
            // not compressed, we are looking at a 32 bit instruction

            if (fetch_unaligned_valid) begin
              valid   = 1'b1; // an instruction is ready for ID stage

              if (req_i && if_valid_o) begin
                // next instruction will be unaligned
                fetch_ready   = 1'b1;
                offset_fsm_ns = WAIT_UNALIGNED;
              end
            end
          end
        end
      end

      default: begin
        offset_fsm_ns = IDLE;
      end
    endcase


    // take care of jumps and branches
    if (pc_set_i) begin
      valid = 1'b0;

      // switch to new PC from ID stage
      branch_req = 1'b1;
      if (unaligned_jump)
        offset_fsm_ns = WAIT_UNALIGNED;
      else
        offset_fsm_ns = WAIT_ALIGNED;
    end
  end


  assign if_busy_o = prefetch_busy;

  assign perf_imiss_o = (~fetch_valid) | branch_req;


  // compressed instruction decoding, or more precisely compressed instruction
  // expander
  //
  // since it does not matter where we decompress instructions, we do it here
  // to ease timing closure
  logic [31:0] instr_decompressed;
  logic        illegal_c_insn;
  logic        instr_compressed_int;

  riscv_compressed_decoder compressed_decoder_i
  (
    .instr_i         ( instr_rdata_int      ),
    .instr_o         ( instr_decompressed   ),
    .is_compressed_o ( instr_compressed_int ),
    .illegal_instr_o ( illegal_c_insn       )
  );


  // IF-ID pipeline registers, frozen when the ID stage is stalled
  always_ff @(posedge clk, negedge rst_n)
  begin : IF_ID_PIPE_REGISTERS
    if (rst_n == 1'b0)
    begin
      instr_valid_id_o      <= 1'b0;
      instr_rdata_id_o      <= '0;
      illegal_c_insn_id_o   <= 1'b0;
      is_compressed_id_o    <= 1'b0;
      current_pc_id_o       <= '0;
    end
    else
    begin
      if (clear_instr_valid_i)
        instr_valid_id_o    <= 1'b0;

      if (if_valid_o)
      begin
        instr_valid_id_o    <= 1'b1;
        instr_rdata_id_o    <= instr_decompressed;
        illegal_c_insn_id_o <= illegal_c_insn;
        is_compressed_id_o  <= instr_compressed_int;
        current_pc_id_o     <= current_pc_if_o;
      end
    end
  end

  assign if_ready_o = valid & id_ready_i;
  assign if_valid_o = (~halt_if_i) & if_ready_o;

endmodule
