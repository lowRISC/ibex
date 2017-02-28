// Copyright 2017 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the “License”); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Matthias Baer - baermatt@student.ethz.ch                   //
//                                                                            //
// Additional contributions by:                                               //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Markus Wegmann - markus.wegmann@technokrat.ch              //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    Top level module                                           //
// Project Name:   zero-riscy                                                 //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Top level module of the RISC-V core.                       //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

`include "zeroriscy_config.sv"

import zeroriscy_defines::*;

module zeroriscy_core
#(
  parameter N_EXT_PERF_COUNTERS = 0,
  parameter INSTR_RDATA_WIDTH   = 32,
  parameter REG_ADDR_WIDTH      = 5
)
(
  // Clock and Reset
  input  logic        clk_i,
  input  logic        rst_ni,

  input  logic        clock_en_i,    // enable clock, otherwise it is gated
  input  logic        test_en_i,     // enable all clock gates for testing

  // Core ID, Cluster ID and boot address are considered more or less static
  input  logic [ 3:0] core_id_i,
  input  logic [ 5:0] cluster_id_i,
  input  logic [31:0] boot_addr_i,

  // Instruction memory interface
  output logic                         instr_req_o,
  input  logic                         instr_gnt_i,
  input  logic                         instr_rvalid_i,
  output logic                  [31:0] instr_addr_o,
  input  logic [INSTR_RDATA_WIDTH-1:0] instr_rdata_i,

  // Data memory interface
  output logic        data_req_o,
  input  logic        data_gnt_i,
  input  logic        data_rvalid_i,
  output logic        data_we_o,
  output logic [3:0]  data_be_o,
  output logic [31:0] data_addr_o,
  output logic [31:0] data_wdata_o,
  input  logic [31:0] data_rdata_i,
  input  logic        data_err_i,

  // Interrupt inputs
  input  logic        irq_i,                 // level sensitive IR lines
  input  logic [4:0]  irq_id_i,
  output logic        irq_ack_o,             // irq ack

  // Debug Interface
  input  logic        debug_req_i,
  output logic        debug_gnt_o,
  output logic        debug_rvalid_o,
  input  logic [14:0] debug_addr_i,
  input  logic        debug_we_i,
  input  logic [31:0] debug_wdata_i,
  output logic [31:0] debug_rdata_o,
  output logic        debug_halted_o,
  input  logic        debug_halt_i,
  input  logic        debug_resume_i,

  // CPU Control Signals
  input  logic        fetch_enable_i,
  output logic        core_busy_o,

  input  logic [N_EXT_PERF_COUNTERS-1:0] ext_perf_counters_i
);

  localparam N_HWLP      = 2;
  localparam N_HWLP_BITS = $clog2(N_HWLP);

  // IF/ID signals
  logic              instr_valid_id;
  logic [31:0]       instr_rdata_id;    // Instruction sampled inside IF stage
  logic              is_compressed_id;
  logic              illegal_c_insn_id; // Illegal compressed instruction sent to ID stage
  logic [31:0]       pc_if;             // Program counter in IF stage
  logic [31:0]       pc_id;             // Program counter in ID stage

  logic              clear_instr_valid;
  logic              pc_set;
  logic [2:0]        pc_mux_id;     // Mux selector for next PC
  logic [1:0]        exc_pc_mux_id;     // Mux selector for exception PC

  logic              lsu_load_err;
  logic              lsu_store_err;

  // ID performance counter signals
  logic        is_decoding;

  
  logic        data_misaligned;
  logic [31:0] misaligned_addr;

  // Jump and branch target and decision (EX->IF)
  logic [31:0] jump_target_ex;
  logic        branch_in_ex;
  logic        branch_decision;

  logic        ctrl_busy;
  logic        if_busy;
  logic        lsu_busy;


  // ALU Control
  logic [ALU_OP_WIDTH-1:0] alu_operator_ex;
  logic [31:0] alu_operand_a_ex;
  logic [31:0] alu_operand_b_ex;
  logic [31:0] alu_operand_c_ex;

  logic [31:0] alu_adder_result_ex; // Used to forward computed address to LSU
  logic [31:0] regfile_wdata_ex;

  // CSR control
  logic        csr_access_ex;
  logic  [1:0] csr_op_ex;

  logic        csr_access;
  logic  [1:0] csr_op;
  logic [11:0] csr_addr;
  logic [11:0] csr_addr_int;
  logic [31:0] csr_rdata;
  logic [31:0] csr_wdata;

  // Data Memory Control:  From ID stage (id-ex pipe) <--> load store unit
  logic        data_we_ex;
  logic [1:0]  data_type_ex;
  logic        data_sign_ext_ex;
  logic [1:0]  data_reg_offset_ex;
  logic        data_req_ex;
  logic [31:0] data_pc_ex;
  logic        data_load_event_ex;
  logic        data_misaligned_ex;
  logic [31:0] regfile_wdata_lsu;


  // stall control
  logic        halt_if;
  logic        if_ready;
  logic        id_ready;
  logic        ex_ready;

  logic        if_valid;
  logic        id_valid;
  logic        wb_valid;

  logic        lsu_ready_ex;
  logic        data_valid_lsu;

  // Signals between instruction core interface and pipe (if and id stages)
  logic        instr_req_int;    // Id stage asserts a req to instruction core interface

  // Interrupts
  logic        irq_enable;
  logic [31:0] mepc;

  logic [5:0]  exc_cause;
  logic        save_exc_cause;
  logic        exc_save_if;
  logic        exc_save_id;
  logic        exc_save_takenbranch_ex;
  logic        exc_restore_id;




  // Debug Unit
  logic [DBG_SETS_W-1:0] dbg_settings;
  logic        dbg_req;
  logic        dbg_ack;
  logic        dbg_stall;
  logic        dbg_trap;

  // Debug GPR Read Access
  logic        dbg_reg_rreq;
  logic [(REG_ADDR_WIDTH-1):0] dbg_reg_raddr;
  logic [31:0] dbg_reg_rdata;

  // Debug GPR Write Access
  logic        dbg_reg_wreq;
  logic [(REG_ADDR_WIDTH-1):0] dbg_reg_waddr;
  logic [31:0] dbg_reg_wdata;

  // Debug CSR Access
  logic        dbg_csr_req;
  logic [11:0] dbg_csr_addr;
  logic        dbg_csr_we;
  logic [31:0] dbg_csr_wdata;

  logic [31:0] dbg_jump_addr;
  logic        dbg_jump_req;

  // Performance Counters
  logic        perf_imiss;
  logic        perf_jump;
  logic        perf_jr_stall;
  logic        perf_ld_stall;


  //////////////////////////////////////////////////////////////////////////////////////////////
  //   ____ _            _      __  __                                                   _    //
  //  / ___| | ___   ___| | __ |  \/  | __ _ _ __   __ _  __ _  ___ _ __ ___   ___ _ __ | |_  //
  // | |   | |/ _ \ / __| |/ / | |\/| |/ _` | '_ \ / _` |/ _` |/ _ \ '_ ` _ \ / _ \ '_ \| __| //
  // | |___| | (_) | (__|   <  | |  | | (_| | | | | (_| | (_| |  __/ | | | | |  __/ | | | |_  //
  //  \____|_|\___/ \___|_|\_\ |_|  |_|\__,_|_| |_|\__,_|\__, |\___|_| |_| |_|\___|_| |_|\__| //
  //                                                     |___/                                //
  //////////////////////////////////////////////////////////////////////////////////////////////

  logic        clk;

  logic        clock_en;
  logic        dbg_busy;

  logic        sleeping;

  // if we are sleeping on a barrier let's just wait on the instruction
  // interface to finish loading instructions
  assign core_busy_o = (data_load_event_ex & data_req_o) ? if_busy : (if_busy | ctrl_busy | lsu_busy);

  assign dbg_busy = dbg_req | dbg_csr_req | dbg_jump_req | dbg_reg_wreq | debug_req_i;

  assign clock_en = clock_en_i | core_busy_o | dbg_busy;

  assign sleeping = (~fetch_enable_i) & (~core_busy_o);


  // main clock gate of the core
  // generates all clocks except the one for the debug unit which is
  // independent
  cluster_clock_gating core_clock_gate_i
  (
    .clk_i     ( clk_i           ),
    .en_i      ( clock_en        ),
    .test_en_i ( test_en_i       ),
    .clk_o     ( clk             )
  );

  //////////////////////////////////////////////////
  //   ___ _____   ____ _____  _    ____ _____    //
  //  |_ _|  ___| / ___|_   _|/ \  / ___| ____|   //
  //   | || |_    \___ \ | | / _ \| |  _|  _|     //
  //   | ||  _|    ___) || |/ ___ \ |_| | |___    //
  //  |___|_|     |____/ |_/_/   \_\____|_____|   //
  //                                              //
  //////////////////////////////////////////////////
  zeroriscy_if_stage
  #(
    .RDATA_WIDTH         ( INSTR_RDATA_WIDTH )
  )
  if_stage_i
  (
    .clk                 ( clk               ),
    .rst_n               ( rst_ni            ),

    // boot address (trap vector location)
    .boot_addr_i         ( boot_addr_i       ),

    // instruction request control
    .req_i               ( instr_req_int     ),

    // instruction cache interface
    .instr_req_o         ( instr_req_o       ),
    .instr_addr_o        ( instr_addr_o      ),
    .instr_gnt_i         ( instr_gnt_i       ),
    .instr_rvalid_i      ( instr_rvalid_i    ),
    .instr_rdata_i       ( instr_rdata_i     ),

    // outputs to ID stage
    .instr_valid_id_o    ( instr_valid_id    ),
    .instr_rdata_id_o    ( instr_rdata_id    ),
    .is_compressed_id_o  ( is_compressed_id  ),
    .illegal_c_insn_id_o ( illegal_c_insn_id ),
    .pc_if_o             ( pc_if             ),
    .pc_id_o             ( pc_id             ),

    // control signals
    .clear_instr_valid_i ( clear_instr_valid ),
    .pc_set_i            ( pc_set            ),
    .exception_pc_reg_i  ( mepc              ), // exception return address
    .pc_mux_i            ( pc_mux_id         ), // sel for pc multiplexer
    .exc_pc_mux_i        ( exc_pc_mux_id     ),
    .exc_vec_pc_mux_i    ( irq_id_i          ),


    // from debug unit
    .dbg_jump_addr_i     ( dbg_jump_addr     ),

    // Jump targets
    .jump_target_ex_i    ( jump_target_ex    ),

    // pipeline stalls
    .halt_if_i           ( halt_if           ),
    .if_ready_o          ( if_ready          ),
    .id_ready_i          ( id_ready          ),
    .if_valid_o          ( if_valid          ),

    .if_busy_o           ( if_busy           ),
    .perf_imiss_o        ( perf_imiss        )
  );


  /////////////////////////////////////////////////
  //   ___ ____    ____ _____  _    ____ _____   //
  //  |_ _|  _ \  / ___|_   _|/ \  / ___| ____|  //
  //   | || | | | \___ \ | | / _ \| |  _|  _|    //
  //   | || |_| |  ___) || |/ ___ \ |_| | |___   //
  //  |___|____/  |____/ |_/_/   \_\____|_____|  //
  //                                             //
  /////////////////////////////////////////////////
  zeroriscy_id_stage
  #(
  )
  id_stage_i
  (
    .clk                          ( clk                  ),
    .rst_n                        ( rst_ni               ),

    .test_en_i                    ( test_en_i            ),

    // Processor Enable
    .fetch_enable_i               ( fetch_enable_i       ),
    .ctrl_busy_o                  ( ctrl_busy            ),
    .is_decoding_o                ( is_decoding          ),

    // Interface to instruction memory
    .instr_valid_i                ( instr_valid_id       ),
    .instr_rdata_i                ( instr_rdata_id       ),
    .instr_req_o                  ( instr_req_int        ),

    // Jumps and branches
    .branch_in_ex_o               ( branch_in_ex         ),
    .branch_decision_i            ( branch_decision      ),

    // IF and ID control signals
    .clear_instr_valid_o          ( clear_instr_valid    ),
    .pc_set_o                     ( pc_set               ),
    .pc_mux_o                     ( pc_mux_id            ),
    .exc_pc_mux_o                 ( exc_pc_mux_id        ),

    .illegal_c_insn_i             ( illegal_c_insn_id    ),
    .is_compressed_i              ( is_compressed_id     ),

    .pc_if_i                      ( pc_if                ),
    .pc_id_i                      ( pc_id                ),

    // Stalls
    .halt_if_o                    ( halt_if              ),

    .if_ready_i                   ( if_ready             ),
    .id_ready_o                   ( id_ready             ),
    .ex_ready_i                   ( ex_ready             ),

    .if_valid_i                   ( if_valid             ),
    .id_valid_o                   ( id_valid             ),

    .alu_operator_ex_o            ( alu_operator_ex      ),
    .alu_operand_a_ex_o           ( alu_operand_a_ex     ),
    .alu_operand_b_ex_o           ( alu_operand_b_ex     ),
     //used in LSU for store instructions
     //TODO: change name
    .alu_operand_c_ex_o           ( alu_operand_c_ex     ),

    // CSR ID/EX
    .csr_access_ex_o              ( csr_access_ex        ),
    .csr_op_ex_o                  ( csr_op_ex            ),

    // LSU
    .data_req_ex_o                ( data_req_ex          ), // to load store unit
    .data_we_ex_o                 ( data_we_ex           ), // to load store unit
    .data_type_ex_o               ( data_type_ex         ), // to load store unit
    .data_sign_ext_ex_o           ( data_sign_ext_ex     ), // to load store unit
    .data_reg_offset_ex_o         ( data_reg_offset_ex   ), // to load store unit
    .data_load_event_ex_o         ( data_load_event_ex   ), // to load store unit

    .data_misaligned_i            ( data_misaligned      ),
    .misaligned_addr_i            ( misaligned_addr      ),

    // Interrupt Signals
    .irq_i                        ( irq_i                ), // incoming interrupts
    .irq_id_i                     ( irq_id_i             ),
    .irq_enable_i                 ( irq_enable           ), // global interrupt enable
    .irq_ack_o                    ( irq_ack_o            ),

    .exc_cause_o                  ( exc_cause            ),
    .save_exc_cause_o             ( save_exc_cause       ),
    .exc_save_if_o                ( exc_save_if          ), // control signal to save pc
    .exc_save_id_o                ( exc_save_id          ), // control signal to save pc
    .exc_restore_id_o             ( exc_restore_id       ), // control signal to restore pc
    .lsu_load_err_i               ( lsu_load_err         ),
    .lsu_store_err_i              ( lsu_store_err        ),

    // Debug Unit Signals
    .dbg_settings_i               ( dbg_settings         ),
    .dbg_req_i                    ( dbg_req              ),
    .dbg_ack_o                    ( dbg_ack              ),
    .dbg_stall_i                  ( dbg_stall            ),
    .dbg_trap_o                   ( dbg_trap             ),

    .dbg_reg_rreq_i               ( dbg_reg_rreq         ),
    .dbg_reg_raddr_i              ( dbg_reg_raddr        ),
    .dbg_reg_rdata_o              ( dbg_reg_rdata        ),

    .dbg_reg_wreq_i               ( dbg_reg_wreq         ),
    .dbg_reg_waddr_i              ( dbg_reg_waddr        ),
    .dbg_reg_wdata_i              ( dbg_reg_wdata        ),

    .dbg_jump_req_i               ( dbg_jump_req         ),

    // write data to commit in the register file
    .regfile_wdata_lsu_i          ( regfile_wdata_lsu    ),
    .regfile_wdata_ex_i           ( regfile_wdata_ex     ),
    .csr_rdata_i                  ( csr_rdata            ),

    // Performance Counters
    .perf_jump_o                  ( perf_jump            ),
    .perf_jr_stall_o              ( perf_jr_stall        ),
    .perf_ld_stall_o              ( perf_ld_stall        )
  );


  zeroriscy_ex_block ex_block_i
  (

    .alu_operator_i             ( alu_operator_ex       ),

    .alu_operand_a_i            ( alu_operand_a_ex      ),
    .alu_operand_b_i            ( alu_operand_b_ex      ),

    .alu_adder_result_ex_o      ( alu_adder_result_ex   ), // from ALU to LSU
    .regfile_wdata_ex_o         ( regfile_wdata_ex      ),

    // To IF: Jump and branch target and decision
    .jump_target_o              ( jump_target_ex        ),
    .branch_decision_o          ( branch_decision       ),

    .lsu_en_i                   ( data_req_ex           ),
    .lsu_ready_ex_i             ( data_valid_lsu        ),
    .ex_ready_o                 ( ex_ready              )

  );

  ////////////////////////////////////////////////////////////////////////////////////////
  //    _     ___    _    ____    ____ _____ ___  ____  _____   _   _ _   _ ___ _____   //
  //   | |   / _ \  / \  |  _ \  / ___|_   _/ _ \|  _ \| ____| | | | | \ | |_ _|_   _|  //
  //   | |  | | | |/ _ \ | | | | \___ \ | || | | | |_) |  _|   | | | |  \| || |  | |    //
  //   | |__| |_| / ___ \| |_| |  ___) || || |_| |  _ <| |___  | |_| | |\  || |  | |    //
  //   |_____\___/_/   \_\____/  |____/ |_| \___/|_| \_\_____|  \___/|_| \_|___| |_|    //
  //                                                                                    //
  ////////////////////////////////////////////////////////////////////////////////////////

  zeroriscy_load_store_unit  load_store_unit_i
  (
    .clk                   ( clk                ),
    .rst_n                 ( rst_ni             ),

    //output to data memory
    .data_req_o            ( data_req_o         ),
    .data_gnt_i            ( data_gnt_i         ),
    .data_rvalid_i         ( data_rvalid_i      ),
    .data_err_i            ( data_err_i         ),

    .data_addr_o           ( data_addr_o        ),
    .data_we_o             ( data_we_o          ),
    .data_be_o             ( data_be_o          ),
    .data_wdata_o          ( data_wdata_o       ),
    .data_rdata_i          ( data_rdata_i       ),

    // signal from ex stage
    .data_we_ex_i          ( data_we_ex         ),
    .data_type_ex_i        ( data_type_ex       ),
    .data_wdata_ex_i       ( alu_operand_c_ex   ),
    .data_reg_offset_ex_i  ( data_reg_offset_ex ),
    .data_sign_ext_ex_i    ( data_sign_ext_ex   ),  // sign extension

    .data_rdata_ex_o       ( regfile_wdata_lsu  ),
    .data_req_ex_i         ( data_req_ex        ),

    .adder_result_ex_i     ( alu_adder_result_ex),

    .data_misaligned_o     ( data_misaligned    ),
    .misaligned_addr_o     ( misaligned_addr    ),

    // exception signals
    .load_err_o            ( lsu_load_err       ),
    .store_err_o           ( lsu_store_err      ),

    // control signals
    .data_valid_o          ( data_valid_lsu     ),
    .lsu_update_addr_o     (                    ),
    .busy_o                ( lsu_busy           )
  );


  //////////////////////////////////////
  //        ____ ____  ____           //
  //       / ___/ ___||  _ \ ___      //
  //      | |   \___ \| |_) / __|     //
  //      | |___ ___) |  _ <\__ \     //
  //       \____|____/|_| \_\___/     //
  //                                  //
  //   Control and Status Registers   //
  //////////////////////////////////////

  zeroriscy_cs_registers
  #(
    .N_EXT_CNT       ( N_EXT_PERF_COUNTERS   )
  )
  cs_registers_i
  (
    .clk                     ( clk                ),
    .rst_n                   ( rst_ni             ),

    // Core and Cluster ID from outside
    .core_id_i               ( core_id_i          ),
    .cluster_id_i            ( cluster_id_i       ),

    // Interface to CSRs (SRAM like)
    .csr_access_i            ( csr_access         ),
    .csr_addr_i              ( csr_addr           ),
    .csr_wdata_i             ( csr_wdata          ),
    .csr_op_i                ( csr_op             ),
    .csr_rdata_o             ( csr_rdata          ),

    // Interrupt related control signals
    .irq_enable_o            ( irq_enable         ),
    .mepc_o                  ( mepc               ),

    .pc_if_i                 ( pc_if              ),
    .pc_id_i                 ( pc_id              ), // from IF stage
    .branch_target_i         ( jump_target_ex     ), // from ID/EX pipeline
    .data_load_event_ex_i    ( data_load_event_ex ), // from ID/EX pipeline
    .exc_save_if_i           ( exc_save_if        ),
    .exc_save_id_i           ( exc_save_id        ),
    .exc_restore_i           ( exc_restore_id     ),

    .exc_cause_i             ( exc_cause          ),
    .save_exc_cause_i        ( save_exc_cause     ),


    // performance counter related signals
    .id_valid_i              ( id_valid           ),
    .is_compressed_i         ( is_compressed_id   ),
    .is_decoding_i           ( is_decoding        ),

    .imiss_i                 ( perf_imiss         ),
    .pc_set_i                ( pc_set             ),
    .jump_i                  ( perf_jump          ),
    .branch_i                ( branch_in_ex       ),
    .branch_taken_i          ( branch_decision    ),
    .ld_stall_i              ( perf_ld_stall      ),
    .jr_stall_i              ( perf_jr_stall      ),

    .mem_load_i              ( data_req_o & data_gnt_i & (~data_we_o) ),
    .mem_store_i             ( data_req_o & data_gnt_i & data_we_o    ),

    .ext_counters_i          ( ext_perf_counters_i                    )
  );

  // Mux for CSR access through Debug Unit
  assign csr_access   = (dbg_csr_req == 1'b0) ? csr_access_ex : 1'b1;
  assign csr_addr     = (dbg_csr_req == 1'b0) ? csr_addr_int     : dbg_csr_addr;
  assign csr_wdata    = (dbg_csr_req == 1'b0) ? alu_operand_a_ex : dbg_csr_wdata;
  assign csr_op       = (dbg_csr_req == 1'b0) ? csr_op_ex
                                              : (dbg_csr_we == 1'b1 ? CSR_OP_WRITE
                                                                    : CSR_OP_NONE );
  assign csr_addr_int = csr_access_ex ? alu_operand_b_ex[11:0] : '0;


  /////////////////////////////////////////////////////////////
  //  ____  _____ ____  _   _  ____   _   _ _   _ ___ _____  //
  // |  _ \| ____| __ )| | | |/ ___| | | | | \ | |_ _|_   _| //
  // | | | |  _| |  _ \| | | | |  _  | | | |  \| || |  | |   //
  // | |_| | |___| |_) | |_| | |_| | | |_| | |\  || |  | |   //
  // |____/|_____|____/ \___/ \____|  \___/|_| \_|___| |_|   //
  //                                                         //
  /////////////////////////////////////////////////////////////

  zeroriscy_debug_unit debug_unit_i
  (
    .clk               ( clk_i              ), // always-running clock for debug
    .rst_n             ( rst_ni             ),

    // Debug Interface
    .debug_req_i       ( debug_req_i        ),
    .debug_gnt_o       ( debug_gnt_o        ),
    .debug_rvalid_o    ( debug_rvalid_o     ),
    .debug_addr_i      ( debug_addr_i       ),
    .debug_we_i        ( debug_we_i         ),
    .debug_wdata_i     ( debug_wdata_i      ),
    .debug_rdata_o     ( debug_rdata_o      ),
    .debug_halt_i      ( debug_halt_i       ),
    .debug_resume_i    ( debug_resume_i     ),
    .debug_halted_o    ( debug_halted_o     ),

    // To/From Core
    .settings_o        ( dbg_settings       ),
    .trap_i            ( dbg_trap           ),
    .exc_cause_i       ( exc_cause          ),
    .stall_o           ( dbg_stall          ),
    .dbg_req_o         ( dbg_req            ),
    .dbg_ack_i         ( dbg_ack            ),

    // register file read port
    .regfile_rreq_o    ( dbg_reg_rreq       ),
    .regfile_raddr_o   ( dbg_reg_raddr      ),
    .regfile_rdata_i   ( dbg_reg_rdata      ),

    // register file write port
    .regfile_wreq_o    ( dbg_reg_wreq       ),
    .regfile_waddr_o   ( dbg_reg_waddr      ),
    .regfile_wdata_o   ( dbg_reg_wdata      ),

    // CSR read/write port
    .csr_req_o         ( dbg_csr_req        ),
    .csr_addr_o        ( dbg_csr_addr       ),
    .csr_we_o          ( dbg_csr_we         ),
    .csr_wdata_o       ( dbg_csr_wdata      ),
    .csr_rdata_i       ( csr_rdata          ),

    // signals for PPC and NPC
    .pc_if_i           ( pc_if              ), // from IF stage
    .pc_id_i           ( pc_id              ), // from ID stage
    .data_load_event_i ( data_load_event_ex ),
    .instr_valid_id_i  ( instr_valid_id     ),

    .sleeping_i        ( sleeping           ),

    .branch_in_ex_i    ( branch_in_ex       ),
    .branch_taken_i    ( branch_decision    ),

    .jump_addr_o       ( dbg_jump_addr      ), // PC from debug unit
    .jump_req_o        ( dbg_jump_req       )  // set PC to new value
  );


`ifdef TRACE_EXECUTION
  zeroriscy_tracer zeroriscy_tracer_i
  (
    .clk            ( clk_i                                ), // always-running clock for tracing
    .rst_n          ( rst_ni                               ),

    .fetch_enable   ( fetch_enable_i                       ),
    .core_id        ( core_id_i                            ),
    .cluster_id     ( cluster_id_i                         ),

    .pc             ( id_stage_i.pc_id_i                   ),
    .instr          ( id_stage_i.instr                     ),
    .compressed     ( id_stage_i.is_compressed_i           ),
    .id_valid       ( id_stage_i.id_valid_o                ),
    .is_decoding    ( id_stage_i.is_decoding_o             ),
    .pipe_flush     ( id_stage_i.controller_i.pipe_flush_i ),

    .rs1_value      ( id_stage_i.operand_a_fw_id           ),
    .rs2_value      ( id_stage_i.operand_b_fw_id           ),
    .rs3_value      ( id_stage_i.alu_operand_c             ),
    .rs2_value_vec  ( id_stage_i.alu_operand_b             ),

    .ex_valid       (                                      ),
    .ex_reg_addr    ( id_stage_i.regfile_waddr_mux         ),
    .ex_reg_we      ( id_stage_i.regfile_we_mux            ),
    .ex_reg_wdata   ( id_stage_i.regfile_wdata_mux         ),
    .data_valid_lsu ( data_valid_lsu                       ),
    .ex_data_addr   ( data_addr_o                          ),
    .ex_data_req    ( data_req_o                           ),
    .ex_data_gnt    ( data_gnt_i                           ),
    .ex_data_we     ( data_we_o                            ),
    // use id_stage_i.regfile_wdata_mux
    .ex_data_wdata  ( data_wdata_o                         ),

    .wb_bypass      ( branch_in_ex_o                       ),

    .wb_valid       (                                      ),
    .wb_reg_addr    (                                      ),
    .wb_reg_we      (                                      ),
    .wb_reg_wdata   ( regfile_wdata_lsu                    ),

    .imm_u_type     ( id_stage_i.imm_u_type                ),
    .imm_uj_type    ( id_stage_i.imm_uj_type               ),
    .imm_i_type     ( id_stage_i.imm_i_type                ),
    .imm_iz_type    ( id_stage_i.imm_iz_type[11:0]         ),
    .imm_z_type     ( id_stage_i.imm_z_type                ),
    .imm_s_type     ( id_stage_i.imm_s_type                ),
    .imm_sb_type    ( id_stage_i.imm_sb_type               ),
    .imm_s2_type    ( id_stage_i.imm_s2_type               ),
    .imm_s3_type    ( id_stage_i.imm_s3_type               ),
    .imm_vs_type    ( id_stage_i.imm_vs_type               ),
    .imm_vu_type    ( id_stage_i.imm_vu_type               ),
    .imm_clip_type  ( id_stage_i.instr_rdata_i[11:7]       )
  );
`endif

endmodule
