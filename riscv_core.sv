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
// Create Date:    24/3/2015                                                  //
// Design Name:    RISCV-V Core                                               //
// Module Name:    riscv_core.sv                                              //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Main module of the core                                    //
//                                                                            //
//                                                                            //
// Revision:                                                                  //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

`include "defines.sv"


module riscv_core
#(
  parameter N_EXT_PERF_COUNTERS = 0,
  parameter INSTR_RDATA_WIDTH   = 32
)
(
  // Clock and Reset
  input  logic        clk,
  input  logic        rst_n,

  input  logic        test_en_i,     // enable all clock gates for testing

  // Core ID, Cluster ID and boot address are considered more or less static
  input  logic [31:0] boot_addr_i,
  input  logic [4:0]  core_id_i,
  input  logic [4:0]  cluster_id_i,

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
  input  logic [31:0] irq_i,                 // level sensitive IR lines

  // Debug Interface
  input  logic        dbginf_stall_i,
  output logic        dbginf_bp_o,
  input  logic        dbginf_strobe_i,
  output logic        dbginf_ack_o,
  input  logic        dbginf_we_i,
  input  logic [15:0] dbginf_addr_i,
  input  logic [31:0] dbginf_data_i,
  output logic [31:0] dbginf_data_o,

  // CPU Control Signals
  input  logic        fetch_enable_i,
  output logic        core_busy_o,

  input  logic [N_EXT_PERF_COUNTERS-1:0] ext_perf_counters_i
);


  // IF/ID signals
  logic        instr_valid_id;
  logic [31:0] instr_rdata_id;    // Instruction sampled inside IF stage
  logic        is_compressed_id;
  logic        illegal_c_insn_id; // Illegal compressed instruction sent to ID stage
  logic [31:0] current_pc_if;     // Current Program counter
  logic [31:0] current_pc_id;     // Current Program counter

  logic        clear_instr_valid;
  logic        pc_set;
  logic [2:0]  pc_mux_id;     // Mux selector for next PC
  logic [1:0]  exc_pc_mux_id;     // Mux selector for exception PC
  logic [4:0]  exc_vec_pc_mux_id; // Mux selector for vectorized IR lines

  logic        lsu_load_err;
  logic        lsu_store_err;

  // ID performance counter signals
  logic        is_decoding;

  logic        useincr_addr_ex;   // Active when post increment
  logic        data_misaligned;

  // Jump and branch target and decision (EX->IF)
  logic [31:0] jump_target_id, jump_target_ex;
  logic        branch_in_ex;
  logic        branch_decision;

  logic        core_busy;
  logic        if_busy;


  logic [31:0] branch_pc_ex; // PC of last executed branch

  // ALU Control
  logic [`ALU_OP_WIDTH-1:0] alu_operator_ex;
  logic [31:0] alu_operand_a_ex;
  logic [31:0] alu_operand_b_ex;
  logic [31:0] alu_operand_c_ex;
  logic        vector_mode_ex;

  // Multiplier Control
  logic        mult_en_ex;
  logic [1:0]  mult_sel_subword_ex;
  logic [1:0]  mult_signed_mode_ex;
  logic        mult_mac_en_ex;

  // Register Write Control
  logic [4:0]  regfile_waddr_ex;
  logic        regfile_we_ex;
  logic [4:0]  regfile_waddr_fw_wb_o;        // From WB to ID
  logic        regfile_we_wb;
  logic [31:0] regfile_wdata;

  logic [4:0]  regfile_alu_waddr_ex;
  logic        regfile_alu_we_ex;

  logic [4:0]  regfile_alu_waddr_fw;
  logic        regfile_alu_we_fw;
  logic [31:0] regfile_alu_wdata_fw;

  // CSR control
  logic        csr_access_ex;
  logic  [1:0] csr_op_ex;

  logic        csr_access;
  logic  [1:0] csr_op;
  logic [11:0] csr_addr;
  logic [31:0] csr_rdata;
  logic [31:0] csr_wdata;

  // Data Memory Control:  From ID stage (id-ex pipe) <--> load store unit
  logic        data_we_ex;
  logic [1:0]  data_type_ex;
  logic        data_sign_ext_ex;
  logic [1:0]  data_reg_offset_ex;
  logic        data_req_ex;
  logic        data_misaligned_ex;

  // stall control
  logic        halt_if;
  logic        if_ready;
  logic        id_ready;
  logic        ex_ready;

  logic        if_valid;
  logic        id_valid;
  logic        ex_valid;
  logic        wb_valid;

  logic        lsu_ready_ex;
  logic        lsu_ready_wb;

  // Signals between instruction core interface and pipe (if and id stages)
  logic        instr_req_int;    // Id stage asserts a req to instruction core interface

  // Interrupts
  logic        irq_enable;
  logic [31:0] epcr;

  logic [5:0]  exc_cause;
  logic        save_exc_cause;
  logic        save_pc_if;
  logic        save_pc_id;


  // Hardware loop controller signals
  logic [31:0] hwloop_target;   // from hwloop controller to if stage


  // Debug Unit
  logic        dbg_stall;
  logic        dbg_stop_req;
  logic        dbg_trap;
  logic        dbg_step_en;     // single-step trace mode enabled
  logic [1:0]  dbg_dsr;         // Debug Stop Register

  logic        dbg_reg_mux;
  logic        dbg_sp_mux;
  logic        dbg_reg_we;
  logic [11:0] dbg_reg_addr;
  logic [31:0] dbg_reg_wdata;
  logic [31:0] dbg_reg_rdata;
  logic [31:0] dbg_rdata;

  logic [31:0] dbg_npc;
  logic        dbg_set_npc;

  // Performance Counters
  logic        perf_imiss;
  logic        perf_jump;
  logic        perf_branch;
  logic        perf_jr_stall;
  logic        perf_ld_stall;


  assign core_busy_o = if_busy || core_busy;


  //////////////////////////////////////////////////
  //   ___ _____   ____ _____  _    ____ _____    //
  //  |_ _|  ___| / ___|_   _|/ \  / ___| ____|   //
  //   | || |_    \___ \ | | / _ \| |  _|  _|     //
  //   | ||  _|    ___) || |/ ___ \ |_| | |___    //
  //  |___|_|     |____/ |_/_/   \_\____|_____|   //
  //                                              //
  //////////////////////////////////////////////////
  riscv_if_stage
  #(
    .RDATA_WIDTH         ( INSTR_RDATA_WIDTH )
  )
  if_stage_i
  (
    .clk                 ( clk             ),
    .rst_n               ( rst_n           ),

    // boot address (trap vector location)
    .boot_addr_i         ( boot_addr_i     ),

    // instruction request control
    .req_i               ( instr_req_int   ),

    // instruction cache interface
    .instr_req_o         ( instr_req_o     ),
    .instr_addr_o        ( instr_addr_o    ),
    .instr_gnt_i         ( instr_gnt_i     ),
    .instr_rvalid_i      ( instr_rvalid_i  ),
    .instr_rdata_i       ( instr_rdata_i   ),

    // outputs to ID stage
    .instr_valid_id_o    ( instr_valid_id    ),
    .instr_rdata_id_o    ( instr_rdata_id    ),
    .is_compressed_id_o  ( is_compressed_id  ),
    .illegal_c_insn_id_o ( illegal_c_insn_id ),
    .current_pc_if_o     ( current_pc_if     ),
    .current_pc_id_o     ( current_pc_id     ),

    // control signals
    .clear_instr_valid_i ( clear_instr_valid ),
    .pc_set_i            ( pc_set            ),
    .exception_pc_reg_i  ( epcr              ), // exception return address
    .pc_mux_i            ( pc_mux_id         ), // sel for pc multiplexer
    .exc_pc_mux_i        ( exc_pc_mux_id     ),
    .exc_vec_pc_mux_i    ( exc_vec_pc_mux_id ),

    // from hwloop controller
    .hwloop_target_i     ( hwloop_target   ),   // pc from hwloop start address

    // from debug unit
    .dbg_npc_i           ( dbg_npc         ),
    .dbg_set_npc_i       ( dbg_set_npc     ),

    // Jump targets
    .jump_target_id_i    ( jump_target_id  ),
    .jump_target_ex_i    ( jump_target_ex  ),

    // pipeline stalls
    .halt_if_i           ( halt_if         ),
    .if_ready_o          ( if_ready        ),
    .id_ready_i          ( id_ready        ),
    .if_valid_o          ( if_valid        ),

    .if_busy_o           ( if_busy         ),
    .perf_imiss_o        ( perf_imiss      )
  );


  /////////////////////////////////////////////////
  //   ___ ____    ____ _____  _    ____ _____   //
  //  |_ _|  _ \  / ___|_   _|/ \  / ___| ____|  //
  //   | || | | | \___ \ | | / _ \| |  _|  _|    //
  //   | || |_| |  ___) || |/ ___ \ |_| | |___   //
  //  |___|____/  |____/ |_/_/   \_\____|_____|  //
  //                                             //
  /////////////////////////////////////////////////
  riscv_id_stage id_stage_i
  (
    .clk                          ( clk                  ),
    .rst_n                        ( rst_n                ),

    .test_en_i                    ( test_en_i            ),

    // Processor Enable
    .fetch_enable_i               ( fetch_enable_i       ),
    .core_busy_o                  ( core_busy            ),
    .is_decoding_o                ( is_decoding          ),

    // Interface to instruction memory
    .instr_valid_i                ( instr_valid_id       ),
    .instr_rdata_i                ( instr_rdata_id       ),
    .instr_req_o                  ( instr_req_int        ),

    // Jumps and branches
    .branch_in_ex_o               ( branch_in_ex         ),
    .branch_decision_i            ( branch_decision      ),
    .jump_target_o                ( jump_target_id       ),

    // IF and ID control signals
    .clear_instr_valid_o          ( clear_instr_valid    ),
    .pc_set_o                     ( pc_set               ),
    .pc_mux_o                     ( pc_mux_id            ),
    .exc_pc_mux_o                 ( exc_pc_mux_id        ),
    .exc_vec_pc_mux_o             ( exc_vec_pc_mux_id    ),

    .illegal_c_insn_i             ( illegal_c_insn_id    ),
    .is_compressed_i              ( is_compressed_id     ),

    .current_pc_if_i              ( current_pc_if        ),
    .current_pc_id_i              ( current_pc_id        ),

    // Stalls
    .halt_if_o                    ( halt_if              ),

    .if_ready_i                   ( if_ready             ),
    .id_ready_o                   ( id_ready             ),
    .ex_ready_i                   ( ex_ready             ),

    .if_valid_i                   ( if_valid             ),
    .id_valid_o                   ( id_valid             ),
    .ex_valid_i                   ( ex_valid             ),
    .wb_valid_i                   ( wb_valid             ),

    // From the Pipeline ID/EX
    .branch_pc_ex_o               ( branch_pc_ex         ),
    .alu_operand_a_ex_o           ( alu_operand_a_ex     ),
    .alu_operand_b_ex_o           ( alu_operand_b_ex     ),
    .alu_operand_c_ex_o           ( alu_operand_c_ex     ),

    .regfile_waddr_ex_o           ( regfile_waddr_ex     ),
    .regfile_we_ex_o              ( regfile_we_ex        ),

    .regfile_alu_we_ex_o          ( regfile_alu_we_ex    ),
    .regfile_alu_waddr_ex_o       ( regfile_alu_waddr_ex ),

    // ALU
    .alu_operator_ex_o            ( alu_operator_ex      ),
    .vector_mode_ex_o             ( vector_mode_ex       ), // from ID to EX stage

    // MUL
    .mult_en_ex_o                 ( mult_en_ex           ), // from ID to EX stage
    .mult_sel_subword_ex_o        ( mult_sel_subword_ex  ), // from ID to EX stage
    .mult_signed_mode_ex_o        ( mult_signed_mode_ex  ), // from ID to EX stage
    .mult_mac_en_ex_o             ( mult_mac_en_ex       ), // from ID to EX stage

    // CSR ID/EX
    .csr_access_ex_o              ( csr_access_ex        ),
    .csr_op_ex_o                  ( csr_op_ex            ),

    // hwloop signals
    .hwloop_targ_addr_o           ( hwloop_target        ),

    // LSU
    .data_req_ex_o                ( data_req_ex          ), // to   load store unit
    .data_we_ex_o                 ( data_we_ex           ), // to   load store unit
    .data_type_ex_o               ( data_type_ex         ), // to   load store unit
    .data_sign_ext_ex_o           ( data_sign_ext_ex     ), // to   load store unit
    .data_reg_offset_ex_o         ( data_reg_offset_ex   ), // to   load store unit
    .data_misaligned_ex_o         ( data_misaligned_ex   ), // to   load store unit

    .prepost_useincr_ex_o         ( useincr_addr_ex      ),
    .data_misaligned_i            ( data_misaligned      ),

    // Interrupt Signals
    .irq_i                        ( irq_i                ), // incoming interrupts
    .irq_enable_i                 ( irq_enable           ), // global interrupt enable
    .exc_cause_o                  ( exc_cause            ),
    .save_exc_cause_o             ( save_exc_cause       ),
    .save_pc_if_o                 ( save_pc_if           ), // control signal to save pc
    .save_pc_id_o                 ( save_pc_id           ), // control signal to save pc
    .lsu_load_err_i               ( lsu_load_err         ),
    .lsu_store_err_i              ( lsu_store_err        ),

    // Debug Unit Signals
    .dbg_stop_req_i               ( dbg_stop_req         ),
    .dbg_step_en_i                ( dbg_step_en          ),
    .dbg_dsr_i                    ( dbg_dsr              ),
    .dbg_stall_i                  ( dbg_stall            ),
    .dbg_trap_o                   ( dbg_trap             ),
    .dbg_reg_mux_i                ( dbg_reg_mux          ),
    .dbg_reg_we_i                 ( dbg_reg_we           ),
    .dbg_reg_addr_i               ( dbg_reg_addr[4:0]    ),
    .dbg_reg_wdata_i              ( dbg_reg_wdata        ),
    .dbg_reg_rdata_o              ( dbg_reg_rdata        ),
    .dbg_set_npc_i                ( dbg_set_npc          ),

    // Forward Signals
    .regfile_waddr_wb_i           ( regfile_waddr_fw_wb_o),  // Write address ex-wb pipeline
    .regfile_we_wb_i              ( regfile_we_wb        ),  // write enable for the register file
    .regfile_wdata_wb_i           ( regfile_wdata        ),  // write data to commit in the register file

    .regfile_alu_waddr_fw_i       ( regfile_alu_waddr_fw ),
    .regfile_alu_we_fw_i          ( regfile_alu_we_fw    ),
    .regfile_alu_wdata_fw_i       ( regfile_alu_wdata_fw ),

    // Performance Counters
    .perf_jump_o                  ( perf_jump            ),
    .perf_branch_o                ( perf_branch          ),
    .perf_jr_stall_o              ( perf_jr_stall        ),
    .perf_ld_stall_o              ( perf_ld_stall        )
  );


  /////////////////////////////////////////////////////
  //   _______  __  ____ _____  _    ____ _____      //
  //  | ____\ \/ / / ___|_   _|/ \  / ___| ____|     //
  //  |  _|  \  /  \___ \ | | / _ \| |  _|  _|       //
  //  | |___ /  \   ___) || |/ ___ \ |_| | |___      //
  //  |_____/_/\_\ |____/ |_/_/   \_\____|_____|     //
  //                                                 //
  /////////////////////////////////////////////////////
  riscv_ex_stage  ex_stage_i
  (
    // Global signals: Clock and active low asynchronous reset
    .clk                        ( clk                          ),
    .rst_n                      ( rst_n                        ),

    // Alu signals from ID stage
    .alu_operator_i             ( alu_operator_ex              ), // from ID/EX pipe registers
    .alu_operand_a_i            ( alu_operand_a_ex             ), // from ID/EX pipe registers
    .alu_operand_b_i            ( alu_operand_b_ex             ), // from ID/EX pipe registers
    .alu_operand_c_i            ( alu_operand_c_ex             ), // from ID/EX pipe registers

    .vector_mode_i              ( vector_mode_ex               ), // from ID/EX pipe registers

    // Multipler
    .mult_en_i                  ( mult_en_ex                   ),
    .mult_sel_subword_i         ( mult_sel_subword_ex          ),
    .mult_signed_mode_i         ( mult_signed_mode_ex          ),
    .mult_mac_en_i              ( mult_mac_en_ex               ),

    // interface with CSRs
    .csr_access_i               ( csr_access_ex                ),
    .csr_rdata_i                ( csr_rdata                    ),

    // From ID Stage: Regfile control signals
    .branch_in_ex_i             ( branch_in_ex                 ),
    .regfile_alu_waddr_i        ( regfile_alu_waddr_ex         ),
    .regfile_alu_we_i           ( regfile_alu_we_ex            ),

    .regfile_waddr_i            ( regfile_waddr_ex             ),
    .regfile_we_i               ( regfile_we_ex                ),

    // Output of ex stage pipeline
    .regfile_waddr_wb_o         ( regfile_waddr_fw_wb_o        ),
    .regfile_we_wb_o            ( regfile_we_wb                ),

    // To IF: Jump and branch target and decision
    .jump_target_o              ( jump_target_ex               ),
    .branch_decision_o          ( branch_decision              ),

    // To ID stage: Forwarding signals
    .regfile_alu_waddr_fw_o     ( regfile_alu_waddr_fw         ),
    .regfile_alu_we_fw_o        ( regfile_alu_we_fw            ),
    .regfile_alu_wdata_fw_o     ( regfile_alu_wdata_fw         ),

    // stall control
    .lsu_ready_ex_i             ( lsu_ready_ex                 ),

    .ex_ready_o                 ( ex_ready                     ),
    .ex_valid_o                 ( ex_valid                     ),
    .wb_ready_i                 ( lsu_ready_wb                 )
  );


  ////////////////////////////////////////////////////////////////////////////////////////
  //    _     ___    _    ____    ____ _____ ___  ____  _____   _   _ _   _ ___ _____   //
  //   | |   / _ \  / \  |  _ \  / ___|_   _/ _ \|  _ \| ____| | | | | \ | |_ _|_   _|  //
  //   | |  | | | |/ _ \ | | | | \___ \ | || | | | |_) |  _|   | | | |  \| || |  | |    //
  //   | |__| |_| / ___ \| |_| |  ___) || || |_| |  _ <| |___  | |_| | |\  || |  | |    //
  //   |_____\___/_/   \_\____/  |____/ |_| \___/|_| \_\_____|  \___/|_| \_|___| |_|    //
  //                                                                                    //
  ////////////////////////////////////////////////////////////////////////////////////////

  riscv_load_store_unit  load_store_unit_i
  (
    .clk                   ( clk                ),
    .rst_n                 ( rst_n              ),

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

    .data_rdata_ex_o       ( regfile_wdata      ),
    .data_req_ex_i         ( data_req_ex        ),
    .operand_a_ex_i        ( alu_operand_a_ex   ),
    .operand_b_ex_i        ( alu_operand_b_ex   ),
    .addr_useincr_ex_i     ( useincr_addr_ex    ),

    .data_misaligned_ex_i  ( data_misaligned_ex ), // from ID/EX pipeline
    .data_misaligned_o     ( data_misaligned    ),

    // exception signals
    .load_err_o            ( lsu_load_err       ),
    .store_err_o           ( lsu_store_err      ),

    // control signals
    .lsu_ready_ex_o        ( lsu_ready_ex       ),
    .lsu_ready_wb_o        ( lsu_ready_wb       ),

    .ex_valid_i            ( ex_valid           )
  );

  assign wb_valid = lsu_ready_wb;


  //////////////////////////////////////
  //        ____ ____  ____           //
  //       / ___/ ___||  _ \ ___      //
  //      | |   \___ \| |_) / __|     //
  //      | |___ ___) |  _ <\__ \     //
  //       \____|____/|_| \_\___/     //
  //                                  //
  //   Control and Status Registers   //
  //////////////////////////////////////

  riscv_cs_registers
  #(
    .N_EXT_PERF_COUNTERS      ( N_EXT_PERF_COUNTERS   )
  )
  cs_registers_i
  (
    .clk                     ( clk            ),
    .rst_n                   ( rst_n          ),

    // Core and Cluster ID from outside
    .core_id_i               ( core_id_i      ),
    .cluster_id_i            ( cluster_id_i   ),

    // Interface to CSRs (SRAM like)
    .csr_access_i            ( csr_access_ex  ),
    .csr_addr_i              ( csr_addr       ),
    .csr_wdata_i             ( csr_wdata      ),
    .csr_op_i                ( csr_op         ),
    .csr_rdata_o             ( csr_rdata      ),

    // Interrupt related control signals
    .irq_enable_o            ( irq_enable     ),
    .epcr_o                  ( epcr           ),

    .curr_pc_if_i            ( current_pc_if  ),    // from IF stage
    .curr_pc_id_i            ( current_pc_id  ),    // from IF stage
    .save_pc_if_i            ( save_pc_if     ),
    .save_pc_id_i            ( save_pc_id     ),

    .exc_cause_i             ( exc_cause      ),
    .save_exc_cause_i        ( save_exc_cause ),

    // performance counter related signals
    .id_valid_i              ( id_valid         ),
    .is_compressed_i         ( is_compressed_id ),
    .is_decoding_i           ( is_decoding      ),

    .imiss_i                 ( perf_imiss     ),
    .jump_i                  ( perf_jump      ),
    .branch_i                ( perf_branch    ),
    .ld_stall_i              ( perf_ld_stall  ),
    .jr_stall_i              ( perf_jr_stall  ),

    .mem_load_i              ( data_req_o & data_gnt_i & (~data_we_o) ),
    .mem_store_i             ( data_req_o & data_gnt_i & data_we_o    ),

    .ext_counters_i          ( ext_perf_counters_i                    )
  );

  // Mux for CSR access through Debug Unit
  assign csr_access = (dbg_sp_mux == 1'b0) ? csr_access_ex : 1'b1;
  assign csr_addr   = (dbg_sp_mux == 1'b0) ? alu_operand_b_ex[11:0] : dbg_reg_addr;
  assign csr_wdata  = (dbg_sp_mux == 1'b0) ? alu_operand_a_ex : dbg_reg_wdata;
  assign csr_op     = (dbg_sp_mux == 1'b0) ? csr_op_ex
                                           : (dbg_reg_we == 1'b1 ? `CSR_OP_WRITE
                                                                 : `CSR_OP_NONE );
  assign dbg_rdata  = (dbg_sp_mux == 1'b0) ? dbg_reg_rdata : csr_rdata;


  /////////////////////////////////////////////////////////////
  //  ____  _____ ____  _   _  ____   _   _ _   _ ___ _____  //
  // |  _ \| ____| __ )| | | |/ ___| | | | | \ | |_ _|_   _| //
  // | | | |  _| |  _ \| | | | |  _  | | | |  \| || |  | |   //
  // | |_| | |___| |_) | |_| | |_| | | |_| | |\  || |  | |   //
  // |____/|_____|____/ \___/ \____|  \___/|_| \_|___| |_|   //
  //                                                         //
  /////////////////////////////////////////////////////////////

  riscv_debug_unit debug_unit_i
  (
    .clk             ( clk             ),
    .rst_n           ( rst_n           ),

    // Debug Interface
    .dbginf_stall_i  ( dbginf_stall_i  ),
    .dbginf_bp_o     ( dbginf_bp_o     ),
    .dbginf_strobe_i ( dbginf_strobe_i ),
    .dbginf_ack_o    ( dbginf_ack_o    ),
    .dbginf_we_i     ( dbginf_we_i     ),
    .dbginf_addr_i   ( dbginf_addr_i   ),
    .dbginf_data_i   ( dbginf_data_i   ),
    .dbginf_data_o   ( dbginf_data_o   ),

    // To/From Core
    .dbg_step_en_o   ( dbg_step_en     ),
    .dbg_dsr_o       ( dbg_dsr         ),

    .stall_core_o    ( dbg_stall       ),
    .stop_req_o      ( dbg_stop_req    ),
    .trap_i          ( dbg_trap        ),

    // register file access
    .sp_mux_o        ( dbg_sp_mux      ),
    .regfile_mux_o   ( dbg_reg_mux     ),
    .regfile_we_o    ( dbg_reg_we      ),
    .regfile_addr_o  ( dbg_reg_addr    ),
    .regfile_wdata_o ( dbg_reg_wdata   ),
    .regfile_rdata_i ( dbg_rdata       ),

    // signals for PPC and NPC
    .curr_pc_if_i    ( current_pc_if   ), // from IF stage
    .curr_pc_id_i    ( current_pc_id   ), // from IF stage
    .branch_pc_i     ( branch_pc_ex    ), // PC of last executed branch (in EX stage)

    .branch_in_ex_i  ( branch_in_ex    ),
    .branch_taken_i  ( branch_decision ),

    .npc_o           ( dbg_npc         ), // PC from debug unit
    .set_npc_o       ( dbg_set_npc     )  // set PC to new value
  );


`ifndef SYNTHESIS
  // Execution trace generation
  // synopsys translate_off
  `ifdef TRACE_EXECUTION
  integer      f;
  string       fn;
  integer      cycles;
  logic [31:0] instr;
  logic        compressed;
  logic [31:0] pc;
  logic  [4:0] rd, rs1, rs2, rs3;
  logic [31:0] rs1_value, rs2_value, rs3_value;
  logic [31:0] imm;
  string       mnemonic;

  // cycle counter
  always_ff @(posedge clk, negedge rst_n)
  begin
    if (rst_n == 1'b0)
      cycles = 0;
    else
      cycles = cycles + 1;
  end

  // open/close output file for writing
  initial
  begin
    #1 // delay needed for valid core_id_i
    $sformat(fn, "trace_core_%h.log", core_id_i);
    $display("[TRACER] Output filename is: %s", fn);
    f = $fopen(fn, "w");
    $fwrite(f, "%20s\t%6s\t%10s\t%10s\t \t%s\n", "Time", "Cycles", "PC", "Instr", "Mnemonic");
  end

  final
  begin
    $fclose(f);
  end

  // log execution
  always @(posedge clk)
  begin
    // get current PC and instruction
    instr      = id_stage_i.instr[31:0];
    compressed = id_stage_i.is_compressed_i;
    pc         = id_stage_i.current_pc_id_i;

    // get register values
    rd         = instr[`REG_D];
    rs1        = instr[`REG_S1];
    rs1_value  = id_stage_i.operand_a_fw_id;
    rs2        = instr[`REG_S2];
    rs2_value  = id_stage_i.operand_b_fw_id;
    rs3        = instr[`REG_S3];
    rs3_value  = id_stage_i.alu_operand_c;

    // special case for WFI because we don't wait for unstalling there
    if ((id_valid && is_decoding) || id_stage_i.controller_i.pipe_flush_i)
    begin
      mnemonic = "";
      imm = 0;

      $fwrite(f, "%t\t%6d\t0x%h\t", $time, cycles, pc);
      if (compressed)
        $fwrite(f, "    0x%4h\tC\t", id_stage_i.instr_rdata_i[15:0]);
      else
        $fwrite(f, "0x%h\tI\t", instr);

      // use casex instead of case inside due to ModelSim bug
      casex (instr)
        // Aliases
        32'h00_00_00_13:   printMnemonic("NOP");
        // Regular opcodes
        // `INSTR_CUSTOM0:    printMnemonic("CUSTOM0");
        // `INSTR_CUSTOM1:    printMnemonic("CUSTOM1");
        `INSTR_LUI:        printUInstr("LUI");
        `INSTR_AUIPC:      printUInstr("AUIPC");
        `INSTR_JAL:        printUJInstr("JAL");
        `INSTR_JALR:       printIInstr("JALR");
        // BRANCH
        `INSTR_BEQ:        printSBInstr("BEQ");
        `INSTR_BNE:        printSBInstr("BNE");
        `INSTR_BLT:        printSBInstr("BLT");
        `INSTR_BGE:        printSBInstr("BGE");
        `INSTR_BLTU:       printSBInstr("BLTU");
        `INSTR_BGEU:       printSBInstr("BGEU");
        // OPIMM
        `INSTR_ADDI:       printIInstr("ADDI");
        `INSTR_SLTI:       printIInstr("SLTI");
        `INSTR_SLTIU:      printIInstr("SLTIU");
        `INSTR_XORI:       printIInstr("XORI");
        `INSTR_ORI:        printIInstr("ORI");
        `INSTR_ANDI:       printIInstr("ANDI");
        `INSTR_SLLI:       printIInstr("SLLI");
        `INSTR_SRLI:       printIInstr("SRLI");
        `INSTR_SRAI:       printIInstr("SRAI");
        // OP
        `INSTR_ADD:        printRInstr("ADD");
        `INSTR_SUB:        printRInstr("SUB");
        `INSTR_SLL:        printRInstr("SLL");
        `INSTR_SLT:        printRInstr("SLT");
        `INSTR_SLTU:       printRInstr("SLTU");
        `INSTR_XOR:        printRInstr("XOR");
        `INSTR_SRL:        printRInstr("SRL");
        `INSTR_SRA:        printRInstr("SRA");
        `INSTR_OR:         printRInstr("OR");
        `INSTR_AND:        printRInstr("AND");
        // FENCE
        `INSTR_FENCE:      printMnemonic("FENCE");
        `INSTR_FENCEI:     printMnemonic("FENCEI");
        // SYSTEM (CSR manipulation)
        `INSTR_CSRRW:      printCSRInstr("CSRRW");
        `INSTR_CSRRS:      printCSRInstr("CSRRS");
        `INSTR_CSRRC:      printCSRInstr("CSRRC");
        `INSTR_CSRRWI:     printCSRInstr("CSRRWI");
        `INSTR_CSRRSI:     printCSRInstr("CSRRSI");
        `INSTR_CSRRCI:     printCSRInstr("CSRRCI");
        // SYSTEM (others)
        `INSTR_ECALL:      printMnemonic("ECALL");
        `INSTR_EBREAK:     printMnemonic("EBREAK");
        `INSTR_ERET:       printMnemonic("ERET");
        `INSTR_WFI:        printMnemonic("WFI");
        // RV32M
        `INSTR_MUL:        printRInstr("MUL");
        `INSTR_MULH:       printRInstr("MULH");
        `INSTR_MULHSU:     printRInstr("MULHSU");
        `INSTR_MULHU:      printRInstr("MULHU");
        `INSTR_DIV:        printRInstr("DIV");
        `INSTR_DIVU:       printRInstr("DIVU");
        `INSTR_REM:        printRInstr("REM");
        `INSTR_REMU:       printRInstr("REMU");
        // PULP specific
        `INSTR_MAC:        printR3Instr("MAC");
        // opcodes with custom decoding
        {25'b?, `OPCODE_LOAD}:       printLoadInstr();
        {25'b?, `OPCODE_LOAD_POST}:  printLoadInstr();
        {25'b?, `OPCODE_STORE}:      printStoreInstr();
        {25'b?, `OPCODE_STORE_POST}: printStoreInstr();
        {25'b?, `OPCODE_HWLOOP}:     printHwloopInstr();
        default:           printMnemonic("INVALID");
      endcase // unique case (instr)

      $fflush(f);
    end
  end // always @ (posedge clk)

  function void printMnemonic(input string mnemonic);
    begin
      riscv_core.mnemonic = mnemonic;
      $fdisplay(f, "%7s", mnemonic);
    end
  endfunction // printMnemonic

  function void printUInstr(input string mnemonic);
    begin
      riscv_core.mnemonic = mnemonic;
      imm = id_stage_i.imm_u_type;
      $fdisplay(f, "%7s\tx%0d, 0x%h (imm)", mnemonic, rd, imm);
    end
  endfunction // printUInstr

  function void printRInstr(input string mnemonic);
    begin
      riscv_core.mnemonic = mnemonic;
      $fdisplay(f, "%7s\tx%0d, x%0d (0x%h), x%0d (0x%h)", mnemonic,
                rd, rs1, rs1_value, rs2, rs2_value);
    end
  endfunction // printRInstr

  function void printR3Instr(input string mnemonic);
    begin
      riscv_core.mnemonic = mnemonic;
      $fdisplay(f, "%7s\tx%0d, x%0d (0x%h), x%0d (0x%h), x%0d (0x%h)", mnemonic,
                rd, rs1, rs1_value, rs2, rs2_value, rs3, rs3_value);
    end
  endfunction // printRInstr

  function void printIInstr(input string mnemonic);
    begin
      riscv_core.mnemonic = mnemonic;
      imm = id_stage_i.imm_i_type;
      $fdisplay(f, "%7s\tx%0d, x%0d (0x%h), 0x%0h (imm)", mnemonic,
                rd, rs1, rs1_value, imm);
    end
  endfunction // printIInstr

  function void printSBInstr(input string mnemonic);
    begin
      riscv_core.mnemonic = mnemonic;
      imm = id_stage_i.imm_sb_type;
      $fdisplay(f, "%7s\tx%0d (0x%h), x%0d (0x%h), 0x%0h (-> 0x%h)", mnemonic,
                rs1, rs1_value, rs2, rs2_value, imm, imm+pc);
    end
  endfunction // printSBInstr

  function void printUJInstr(input string mnemonic);
    begin
      riscv_core.mnemonic = mnemonic;
      imm = id_stage_i.imm_uj_type;
      $fdisplay(f, "%7s\tx%0d, 0x%h (-> 0x%h)", mnemonic, rd, imm, imm+pc);
    end
  endfunction // printUJInstr

  function void printCSRInstr(input string mnemonic);
    logic [11:0] csr;
    begin
      riscv_core.mnemonic = mnemonic;
      imm = id_stage_i.imm_z_type;
      csr = instr[31:20];

      if (instr[14] == 1'b0) begin
        $fdisplay(f, "%7s\tx%0d, 0x%h (csr), x%0d (0x%h)", mnemonic, rd, csr,
          rs1, rs1_value);
      end else begin
        $fdisplay(f, "%7s\tx%0d, 0x%h (csr), 0x%h (imm)", mnemonic, rd, csr, imm);
      end
    end
  endfunction // printCSRInstr

  function void printLoadInstr();
    string mnemonic;
    logic [2:0] size;
    begin
      // detect reg-reg load and find size
      size = instr[14:12];
      if (instr[14:12] == 3'b111)
        size = instr[30:28];
      case (size)
        3'b000: mnemonic = "LB";
        3'b001: mnemonic = "LH";
        3'b010: mnemonic = "LW";
        3'b100: mnemonic = "LBU";
        3'b101: mnemonic = "LHU";
        3'b011,
        3'b110,
        3'b111: begin
          printMnemonic("INVALID");
          return;
        end
      endcase

      // compose mnemonic
      if (instr[14:12] == 3'b111)
        mnemonic = {mnemonic, "RR"};
      if (instr[6:0] == `OPCODE_LOAD_POST)
        mnemonic = {mnemonic, "POST"};
      riscv_core.mnemonic = mnemonic;

      if (instr[14:12] != 3'b111) begin
        // regular load
        imm = id_stage_i.imm_i_type;
        if (instr[6:0] != `OPCODE_LOAD_POST)
          $fdisplay(f, "%7s\tx%0d, x%0d (0x%h), 0x%0h (imm) (-> 0x%h)",
                    mnemonic, rd, rs1, rs1_value, imm, imm+rs1_value);
        else
          $fdisplay(f, "%7s\tx%0d, x%0d! (0x%h), 0x%0h (imm) (-> 0x%h)",
                    mnemonic, rd, rs1, rs1_value, imm, rs1_value);
      end else begin
        // reg-reg load
        if (instr[6:0] != `OPCODE_LOAD_POST)
          $fdisplay(f, "%7s\tx%0d, x%0d (0x%h), x%0d (0x%h) (-> 0x%h)", mnemonic,
                    rd, rs1, rs1_value, rs2, rs2_value, rs1_value+rs2_value);
        else
          $fdisplay(f, "%7s\tx%0d, x%0d! (0x%h), x%0d (0x%h) (-> 0x%h)", mnemonic,
                    rd, rs1, rs1_value, rs2, rs2_value, rs1_value);
      end
    end
  endfunction

  function void printStoreInstr();
    string mnemonic;
    begin
      case (instr[13:12])
        2'b00:  mnemonic = "SB";
        2'b01:  mnemonic = "SH";
        2'b10:  mnemonic = "SW";
        2'b11: begin
          printMnemonic("INVALID");
          return;
        end
      endcase

      // compose mnemonic
      if (instr[14])
        mnemonic = {mnemonic, "RR"};
      if (instr[6:0] == `OPCODE_STORE_POST)
        mnemonic = {mnemonic, "POST"};
      riscv_core.mnemonic = mnemonic;

      if (instr[14] == 1'b0) begin
        // regular store
        imm = id_stage_i.imm_s_type;
        if (instr[6:0] != `OPCODE_STORE_POST)
          $fdisplay(f, "%7s\tx%0d (0x%h), x%0d (0x%h), 0x%0h (imm) (-> 0x%h)",
                    mnemonic, rs1, rs1_value, rs2, rs2_value, imm, imm+rs1_value);
        else
          $fdisplay(f, "%7s\tx%0d! (0x%h), x%0d (0x%h), 0x%0h (imm) (-> 0x%h)",
                    mnemonic, rs1, rs1_value, rs2, rs2_value, imm, rs1_value);
      end else begin
        // reg-reg store
        if (instr[6:0] != `OPCODE_STORE_POST)
          $fdisplay(f, "%7s\tx%0d (0x%h), x%0d (0x%h), x%0d (0x%h) (-> 0x%h)", mnemonic,
                    rs1, rs1_value, rs2, rs2_value, rs3, rs3_value, rs1_value+rs3_value);
        else
          $fdisplay(f, "%7s\tx%0d! (0x%h), x%0d (0x%h), x%0d (0x%h) (-> 0x%h)", mnemonic,
                    rs1, rs1_value, rs2, rs2_value, rs3, rs3_value, rs1_value);
      end
    end
  endfunction // printSInstr

  function void printHwloopInstr();
    string mnemonic;
    begin
      // set mnemonic
      case (instr[14:12])
        3'b000: mnemonic = "LSTARTI";
        3'b001: mnemonic = "LENDI";
        3'b010: mnemonic = "LCOUNT";
        3'b011: mnemonic = "LCOUNTI";
        3'b100: mnemonic = "LSETUP";
        3'b111: begin
          printMnemonic("INVALID");
          return;
        end
      endcase
      riscv_core.mnemonic = mnemonic;

      // decode and print instruction
      imm = id_stage_i.imm_i_type;
      case (instr[14:12])
        // lp.starti and lp.endi
        3'b000,
        3'b001: $fdisplay(f, "%7s\tx%0d, 0x%h (-> 0x%h)", mnemonic, rd, imm, pc+imm);
        // lp.count
        3'b010: $fdisplay(f, "%7s\tx%0d, x%0d (0x%h)", mnemonic, rd, rs1, rs1_value);
        // lp.counti
        3'b011: $fdisplay(f, "%7s\tx%0d, 0x%h", mnemonic, rd, imm);
        // lp.setup
        3'b100: $fdisplay(f, "%7s\tx%0d, x%0d (0x%h), 0x%h (-> 0x%h)", mnemonic,
                          rd, rs1, rs1_value, imm, pc+imm);
      endcase
    end
  endfunction
  `endif // TRACE_EXECUTION
  // synopsys translate_on
`endif

endmodule
