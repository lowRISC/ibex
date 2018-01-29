// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Renzo Andri - andrire@student.ethz.ch                      //
//                                                                            //
// Additional contributions by:                                               //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                                                                            //
// Design Name:    Instruction Fetch Stage                                    //
// Project Name:   zero-riscy                                                 //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Instruction fetch unit: Selection of the next PC, and      //
//                 buffering (sampling) of the read instruction               //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

`include "zeroriscy_config.sv"

import zeroriscy_defines::*;

module zeroriscy_if_stage
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
      input  logic            [31:0] instr_rdata_i,
      // Output of IF Pipeline stage
      output logic              instr_valid_id_o,      // instruction in IF/ID pipeline is valid
      output logic       [31:0] instr_rdata_id_o,      // read instruction is sampled and sent to ID stage for decoding
      output logic              is_compressed_id_o,    // compressed decoder thinks this is a compressed instruction
      output logic              illegal_c_insn_id_o,   // compressed decoder thinks this is an invalid instruction
      output logic       [31:0] pc_if_o,
      output logic       [31:0] pc_id_o,
      // Forwarding ports - control signals
      input  logic        clear_instr_valid_i,   // clear instruction valid bit in IF/ID pipe
      input  logic        pc_set_i,              // set the program counter to a new value
      input  logic [31:0] exception_pc_reg_i,    // address used to restore PC when the interrupt/exception is served
      input  logic  [2:0] pc_mux_i,              // sel for pc multiplexer
      input  logic  [1:0] exc_pc_mux_i,          // selects ISR address
      input  logic  [4:0] exc_vec_pc_mux_i,      // selects ISR address for vectorized interrupt lines

      // jump and branch target and decision
      input  logic [31:0] jump_target_ex_i,      // jump target address
      // from debug unit
      input  logic [31:0] dbg_jump_addr_i,
      // pipeline stall
      input  logic        halt_if_i,
      input  logic        id_ready_i,
      output logic        if_valid_o,
      // misc signals
      output logic        if_busy_o,             // is the IF stage busy fetching instructions?
      output logic        perf_imiss_o           // Instruction Fetch Miss
    );

      // offset FSM
      enum logic[0:0] {WAIT, IDLE } offset_fsm_cs, offset_fsm_ns;

      logic              valid;
      logic              if_ready;
      // prefetch buffer related signals
      logic              prefetch_busy;
      logic              branch_req;
      logic       [31:0] fetch_addr_n;

      logic              fetch_valid;
      logic              fetch_ready;
      logic       [31:0] fetch_rdata;
      logic       [31:0] fetch_addr;

      logic       [31:0] exc_pc;



      // exception PC selection mux
      always_comb
        begin : EXC_PC_MUX
          exc_pc = '0;

          unique case (exc_pc_mux_i)
            EXC_PC_ILLINSN: exc_pc = { boot_addr_i[31:8], EXC_OFF_ILLINSN };
            EXC_PC_ECALL:   exc_pc = { boot_addr_i[31:8], EXC_OFF_ECALL   };
            EXC_PC_IRQ:     exc_pc = { boot_addr_i[31:8], 1'b0, exc_vec_pc_mux_i[4:0], 2'b0 };
            // TODO: Add case for EXC_PC_STORE and EXC_PC_LOAD as soon as they are supported
            default:;
          endcase
        end

        // fetch address selection
        always_comb
        begin
          fetch_addr_n = '0;

          unique case (pc_mux_i)
            PC_BOOT:      fetch_addr_n = {boot_addr_i[31:8], EXC_OFF_RST};
            PC_JUMP:      fetch_addr_n = jump_target_ex_i;
            PC_EXCEPTION: fetch_addr_n = exc_pc;             // set PC to exception handler
            PC_ERET:      fetch_addr_n = exception_pc_reg_i; // PC is restored when returning from IRQ/exception
            PC_DBG_NPC:   fetch_addr_n = dbg_jump_addr_i;    // PC is taken from debug unit

            default:;
          endcase
        end

        // prefetch buffer, caches a fixed number of instructions
        zeroriscy_prefetch_buffer prefetch_buffer_i
          (
            .clk               ( clk                         ),
            .rst_n             ( rst_n                       ),

            .req_i             ( req_i                       ),

            .branch_i          ( branch_req                  ),
            .addr_i            ( {fetch_addr_n[31:1], 1'b0}  ),

            .ready_i           ( fetch_ready                 ),
            .valid_o           ( fetch_valid                 ),
            .rdata_o           ( fetch_rdata                 ),
            .addr_o            ( fetch_addr                  ),

            // goes to instruction memory / instruction cache
            .instr_req_o       ( instr_req_o                 ),
            .instr_addr_o      ( instr_addr_o                ),
            .instr_gnt_i       ( instr_gnt_i                 ),
            .instr_rvalid_i    ( instr_rvalid_i              ),
            .instr_rdata_i     ( instr_rdata_i               ),

            // Prefetch Buffer Status
            .busy_o            ( prefetch_busy               )
          );


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

          unique case (offset_fsm_cs)
            // no valid instruction data for ID stage
            // assume aligned
            IDLE: begin
              if (req_i) begin
                branch_req    = 1'b1;
                offset_fsm_ns = WAIT;
              end
            end

            // serving aligned 32 bit or 16 bit instruction, we don't know yet
            WAIT: begin
              if (fetch_valid) begin
                valid   = 1'b1; // an instruction is ready for ID stage

                if (req_i && if_valid_o) begin
                  fetch_ready   = 1'b1;
                  offset_fsm_ns = WAIT;
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
            offset_fsm_ns = WAIT;
          end
        end




        assign pc_if_o         = fetch_addr;

        assign if_busy_o       = prefetch_busy;

        assign perf_imiss_o    = (~fetch_valid) | branch_req;


        // compressed instruction decoding, or more precisely compressed instruction
        // expander
        //
        // since it does not matter where we decompress instructions, we do it here
        // to ease timing closure
        logic [31:0] instr_decompressed;
        logic        illegal_c_insn;
        logic        instr_compressed_int;

        zeroriscy_compressed_decoder compressed_decoder_i
          (
            .instr_i         ( fetch_rdata          ),
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
              pc_id_o               <= '0;
            end
          else
            begin

              if (if_valid_o)
              begin
                  instr_valid_id_o    <= 1'b1;
                  instr_rdata_id_o    <= instr_decompressed;
                  illegal_c_insn_id_o <= illegal_c_insn;
                  is_compressed_id_o  <= instr_compressed_int;
                  pc_id_o             <= pc_if_o;
              end else if (clear_instr_valid_i) begin
                instr_valid_id_o    <= 1'b0;
              end

            end
        end


        assign if_ready = valid & id_ready_i;
        assign if_valid_o = (~halt_if_i) & if_ready;

        //----------------------------------------------------------------------------
        // Assertions
        //----------------------------------------------------------------------------
`ifndef VERILATOR
        // there should never be a grant when there is no request
        assert property (
          @(posedge clk) (instr_gnt_i) |-> (instr_req_o) )
        else $warning("There was a grant without a request");
`endif

        endmodule
