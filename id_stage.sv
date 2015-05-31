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
// Create Date:    19/09/2013                                                 //
// Design Name:    Decode stage                                               //
// Module Name:    id_stage.sv                                                //
// Project Name:   RiscV                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Decode stage of the core. It decodes the instructions      //
//                 and hosts the register file.                               //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - File Created                                               //
// Revision v0.2 - (July   1st 2014) Pipe splitted in several files           //
// Revision v0.3 - (August 7th 2014) Changed port and signal names, added     //
//                 comments                                                   //
// Revision v0.4 - (December 1th 2014) Merged debug unit                      //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////


`include "defines.sv"

module id_stage
(
    input  logic                        clk,
    input  logic                        rst_n,

    input logic                         fetch_enable_i,
    output logic                        core_busy_o,

    // Interface to instruction memory
    input  logic [31:0]                 instr_rdata_i,      // comes from pipeline of IF stage
    output logic                        instr_req_o,
    input  logic                        instr_gnt_i,
    input  logic                        instr_ack_i,

    // Jumps and branches
    output logic [1:0]                  jump_in_id_o,
    output logic [1:0]                  jump_in_ex_o,

    // IF and ID stage signals

    output logic [2:0]                  pc_mux_sel_o,
    output logic                        pc_mux_boot_o,
    output logic [1:0]                  exc_pc_mux_o,
    output logic                        force_nop_o,

    input  logic [31:0]                 current_pc_if_i,
    input  logic [31:0]                 current_pc_id_i,

    // STALLS
    output logic                        stall_if_o,
    output logic                        stall_id_o,
    output logic                        stall_ex_o,
    output logic                        stall_wb_o,

    input logic                         sr_flag_fw_i,
    input logic                         sr_flag_i,

    // To the Pipeline ID/EX
    output logic [31:0]                 regfile_rb_data_ex_o,
    output logic [31:0]                 alu_operand_a_ex_o,
    output logic [31:0]                 alu_operand_b_ex_o,
    output logic [31:0]                 alu_operand_c_ex_o,
    output logic [`ALU_OP_WIDTH-1:0]    alu_operator_ex_o,

    output logic [1:0]                  vector_mode_ex_o,
    output logic [1:0]                  alu_cmp_mode_ex_o,
    output logic [1:0]                  alu_vec_ext_ex_o,

    output logic                        mult_en_ex_o,
    output logic [1:0]                  mult_sel_subword_ex_o,
    output logic [1:0]                  mult_signed_mode_ex_o,
    output logic                        mult_use_carry_ex_o,
    output logic                        mult_mac_en_ex_o,

    output logic [4:0]                  regfile_waddr_ex_o,
    output logic                        regfile_wdata_mux_sel_ex_o,
    output logic                        regfile_we_ex_o,

    output logic [4:0]                  regfile_alu_waddr_ex_o,
    output logic                        regfile_alu_we_ex_o,

    output logic                        prepost_useincr_ex_o,
    input  logic                        data_misaligned_i,

    output logic [2:0]                  hwloop_we_ex_o,
    output logic [1:0]                  hwloop_regid_ex_o,
    output logic                        hwloop_wb_mux_sel_ex_o,
    output logic [31:0]                 hwloop_cnt_o,
    output logic [`HWLOOP_REGS-1:0]     hwloop_dec_cnt_o,
    output logic [31:0]                 hwloop_targ_addr_o,

    output logic                        csr_access_ex_o,
    output logic [1:0]                  csr_op_ex_o,

    // Interface to load store unit
    output logic                        data_we_ex_o,
    output logic [1:0]                  data_type_ex_o,
    output logic                        data_sign_ext_ex_o,
    output logic [1:0]                  data_reg_offset_ex_o,
    output logic                        data_misaligned_ex_o,
    output logic                        data_req_ex_o,
    input  logic                        data_ack_i,      // Grant from data memory
    input  logic                        data_rvalid_i,

    // SPR signals
    output logic                        set_flag_ex_o,
    output logic                        set_carry_ex_o,
    output logic                        set_overflow_ex_o,

    // Interrupt signals
    input  logic                        irq_i,
    input  logic                        irq_nm_i,
    input  logic                        irq_enable_i,
    output logic                        save_pc_if_o,
    output logic                        save_pc_id_o,
    output logic                        save_sr_o,
    output logic                        restore_sr_o,

    // from hwloop regs
    input  logic [`HWLOOP_REGS-1:0] [31:0] hwloop_start_addr_i,
    input  logic [`HWLOOP_REGS-1:0] [31:0] hwloop_end_addr_i,
    input  logic [`HWLOOP_REGS-1:0] [31:0] hwloop_counter_i,

    // Debug Unit Signals
    input  logic                        dbg_flush_pipe_i,
    output logic                        pipe_flushed_o,
    input  logic                        dbg_st_en_i,
    input  logic [1:0]                  dbg_dsr_i,
    input  logic                        dbg_stall_i,
    output logic                        dbg_trap_o,
    input  logic                        dbg_reg_mux_i,
    input  logic                        dbg_reg_we_i,
    input  logic [4:0]                  dbg_reg_addr_i,
    input  logic [31:0]                 dbg_reg_wdata_i,
    output logic [31:0]                 dbg_reg_rdata_o,
    input  logic                        dbg_set_npc_i,

    // Forward Signals
    input  logic [4:0]                  regfile_waddr_wb_i,
    input  logic                        regfile_we_wb_i,
    input  logic [31:0]                 regfile_wdata_wb_i, // From wb_stage: selects data from data memory, ex_stage result and sp rdata

    input  logic [4:0]                  regfile_alu_waddr_fw_i,
    input  logic                        regfile_alu_we_fw_i,
    input  logic [31:0]                 regfile_alu_wdata_fw_i

`ifdef TCDM_ADDR_PRECAL
    ,
    output logic [31:0]                 alu_adder_o
`endif

);


  // Immediate decoding and sign extension
  logic [31:0] imm_i_type;
  logic [31:0] imm_s_type;
  logic [31:0] imm_sb_type;
  logic [31:0] imm_u_type;
  logic [31:0] imm_uj_type;

  logic [31:0] immediate_b;       // contains the immediate for operand b

  logic [31:0] current_pc;        // PC to be used in ALU (either IF or ID)

  logic [31:0] jump_target;       // calculated jump target (-> EX -> IF)

  logic        exc_pc_sel;
  logic [2:0]  pc_mux_sel_int;    // selects next PC in if stage

  logic        force_nop_controller;
  logic        force_nop_exc;

  logic        irq_present;

  // Signals running between controller and exception controller
  logic  [1:0] jump_in_ex;        // registered copy of jump_in_id
  assign jump_in_ex_o = jump_in_ex;

  logic        illegal_insn;
  logic        trap_insn;
  logic        trap_hit;
  logic        pipe_flush;
  logic        pc_valid;
  logic        clear_isr_running;


  logic [4:0]  regfile_addr_ra_id;
  logic [4:0]  regfile_addr_rb_id;
  logic [4:0]  regfile_addr_rc_id;

  logic [4:0]  regfile_waddr_id;
  logic [4:0]  regfile_alu_waddr_id;
  logic        regfile_alu_we_id;

  logic [31:0] regfile_data_ra_id;
  logic [31:0] regfile_data_rb_id;
  logic [31:0] regfile_data_rc_id;

  logic        imm_sign_ext_sel;

  // ALU Control
  logic [`ALU_OP_WIDTH-1:0] alu_operator;
  logic [1:0]  alu_op_a_mux_sel;
  logic [1:0]  alu_op_b_mux_sel;
  logic        alu_op_c_mux_sel;
  logic        scalar_replication;

  logic [1:0]  vector_mode;
  logic [1:0]  alu_cmp_mode;
  logic [1:0]  alu_vec_ext;

  logic        alu_pc_mux_sel;
  logic [3:0]  immediate_mux_sel;

  // Multiplier Control
  logic        mult_en;          // multiplication is used instead of ALU
  logic [1:0]  mult_sel_subword; // Select a subword when doing multiplications
  logic [1:0]  mult_signed_mode; // Signed mode multiplication at the output of the controller, and before the pipe registers
  logic        mult_use_carry;   // Enables carry in for the MAC
  logic        mult_mac_en;      // Enables the use of the accumulator

  // Register Write Control
  logic        regfile_wdata_mux_sel;
  logic        regfile_we_id;
  logic [1:0]  regfile_alu_waddr_mux_sel;  // TODO: FixMe -> 1bit

  // Data Memory Control
  logic        data_we_id;
  logic [1:0]  data_type_id;
  logic        data_sign_ext_id;
  logic [1:0]  data_reg_offset_id;
  logic        data_req_id;

  // hwloop signals
  logic [1:0]  hwloop_regid;
  logic [2:0]  hwloop_we;
  logic        hwloop_wb_mux_sel;
  logic [1:0]  hwloop_cnt_mux_sel;
  logic [31:0] hwloop_cnt;
  logic        hwloop_jump;
  logic        hwloop_enable;

  // CSR control
  logic        csr_access;
  logic [1:0]  csr_op;

  // Supervision Register
  logic        set_flag;
  logic        set_carry;
  logic        set_overflow;

  logic        prepost_useincr;

  // Forwarding
  logic [1:0]  operand_a_fw_mux_sel;
  logic [1:0]  operand_b_fw_mux_sel;
  logic [1:0]  operand_c_fw_mux_sel;
  logic [31:0] operand_a_fw_id;
  logic [31:0] operand_b_fw_id;

  logic [31:0] alu_operand_a;
  logic [31:0] alu_operand_b;
  logic [31:0] alu_operand_c;
  logic [31:0] operand_b;      // before going through the scalar replication mux
  logic [31:0] operand_b_vec;  // scalar replication of operand_b for 8 and 16 bit
  logic [31:0] operand_c;



  assign force_nop_o = force_nop_controller | force_nop_exc;
  assign pc_mux_sel_o = (exc_pc_sel == 1'b1) ? `PC_EXCEPTION : pc_mux_sel_int;

  // immediate extraction and sign extension
  assign imm_i_type  = { {20 {instr_rdata_i[31]}}, instr_rdata_i[31:20] };
  assign imm_s_type  = { {20 {instr_rdata_i[31]}}, instr_rdata_i[31:25], instr_rdata_i[11:7] };
  assign imm_sb_type = { {20 {instr_rdata_i[31]}}, instr_rdata_i[31], instr_rdata_i[7],
                         instr_rdata_i[30:25], instr_rdata_i[11:8], 1'b0 };
  assign imm_u_type  = { instr_rdata_i[31:12], {12 {1'b0}} };
  assign imm_uj_type = { {20 {instr_rdata_i[31]}}, instr_rdata_i[19:12],
                         instr_rdata_i[20], instr_rdata_i[30:21], 1'b0 };

  // immediate for CSR manipulatin (zero extended)
  assign imm_z_type  = { 27'b0, instr_rdata_i[`REG_S1] };

  // source registers
  assign regfile_addr_ra_id = instr_rdata_i[`REG_S1];
  assign regfile_addr_rb_id = instr_rdata_i[`REG_S2];
  //assign regfile_addr_rc_id = instr_rdata_i[25:21];

  // destination registers
  assign regfile_waddr_id = instr_rdata_i[`REG_D];

  //assign alu_vec_ext         = instr_rdata_i[9:8]; TODO
  assign alu_vec_ext = 1'b0;


  // Second Register Write Adress Selection
  // Used for prepost load/store and multiplier
  always_comb
  begin : alu_waddr_mux
    case (regfile_alu_waddr_mux_sel)
      default: regfile_alu_waddr_id = regfile_addr_ra_id;
      2'b00:   regfile_alu_waddr_id = regfile_addr_ra_id;
      2'b01:   regfile_alu_waddr_id = regfile_waddr_id;
    endcase
  end


  ///////////////////////////////////////////////////////////////////////////////////////
  //  ____                                         ____                  _             //
  // |  _ \ _ __ ___   __ _ _ __ __ _ _ __ ___    / ___|___  _   _ _ __ | |_ ___ _ __  //
  // | |_) | '__/ _ \ / _` | '__/ _` | '_ ` _ \  | |   / _ \| | | | '_ \| __/ _ \ '__| //
  // |  __/| | | (_) | (_| | | | (_| | | | | | | | |__| (_) | |_| | | | | ||  __/ |    //
  // |_|   |_|  \___/ \__, |_|  \__,_|_| |_| |_|  \____\___/ \__,_|_| |_|\__\___|_|    //
  //                  |___/                                                            //
  ///////////////////////////////////////////////////////////////////////////////////////

  // PC Mux
  always_comb
  begin : alu_pc_mux
    case (alu_pc_mux_sel)
      1'b0:       current_pc = current_pc_if_i;  // TODO: FIXME 1'b0 is never used
      1'b1:       current_pc = current_pc_id_i;
    endcase; // case (alu_pc_mux_sel)
  end

  // hwloop_cnt_mux
  always_comb
  begin : hwloop_cnt_mux
    case (hwloop_cnt_mux_sel)
      2'b00:      hwloop_cnt = 32'b0;
      //2'b01:      hwloop_cnt = immediate21z_id; // TODO: FIXME use correct immediate when adding hwloops
      //2'b10:      hwloop_cnt = immediate13z_id;
      2'b11:      hwloop_cnt = operand_a_fw_id;
      default:    hwloop_cnt = 32'b0;
    endcase; // case (hwloop_cnt_mux_sel)
  end

  // hwloop register id
  assign hwloop_regid = instr_rdata_i[22:21];     // set hwloop register id

  //////////////////////////////////////////////////////////////////
  //       _                         _____                    _   //
  //     | |_   _ _ __ ___  _ __   |_   _|_ _ _ __ __ _  ___| |_  //
  //  _  | | | | | '_ ` _ \| '_ \    | |/ _` | '__/ _` |/ _ \ __| //
  // | |_| | |_| | | | | | | |_) |   | | (_| | | | (_| |  __/ |_  //
  //  \___/ \__,_|_| |_| |_| .__/    |_|\__,_|_|  \__, |\___|\__| //
  //                       |_|                    |___/           //
  //////////////////////////////////////////////////////////////////

  always_comb
  begin
    unique case (instr_rdata_i[6:0])
      `OPCODE_JAL:    jump_target = current_pc_id_i + imm_uj_type;
      `OPCODE_JALR:   jump_target = operand_a_fw_id + imm_i_type;
      `OPCODE_BRANCH: jump_target = current_pc_id_i + imm_sb_type;
      default:        jump_target = '0;
    endcase // unique case (instr_rdata_i[6:0])
  end


  ////////////////////////////////////////////////////////
  //   ___                                 _      _     //
  //  / _ \ _ __   ___ _ __ __ _ _ __   __| |    / \    //
  // | | | | '_ \ / _ \ '__/ _` | '_ \ / _` |   / _ \   //
  // | |_| | |_) |  __/ | | (_| | | | | (_| |  / ___ \  //
  //  \___/| .__/ \___|_|  \__,_|_| |_|\__,_| /_/   \_\ //
  //       |_|                                          //
  ////////////////////////////////////////////////////////

  // ALU_Op_a Mux
  always_comb
  begin : alu_operand_a_mux
     case (alu_op_a_mux_sel)
       default:            alu_operand_a = operand_a_fw_id;
       `OP_A_REGA_OR_FWD:  alu_operand_a = operand_a_fw_id;
       `OP_A_CURRPC:       alu_operand_a = current_pc;
       `OP_A_ZIMM:         alu_operand_a = imm_z_type;
       `OP_A_ZERO:         alu_operand_a = 32'b0;
     endcase; // case (alu_op_a_mux_sel)
  end

  // Operand a forwarding mux
  always_comb
  begin : operand_a_fw_mux
     case (operand_a_fw_mux_sel)
       `SEL_FW_EX:    operand_a_fw_id = regfile_alu_wdata_fw_i;
       `SEL_FW_WB:    operand_a_fw_id = regfile_wdata_wb_i;
       `SEL_REGFILE:  operand_a_fw_id = regfile_data_ra_id;
       default:       operand_a_fw_id = regfile_data_ra_id;
     endcase; // case (operand_a_fw_mux_sel)
  end

  //////////////////////////////////////////////////////
  //   ___                                 _   ____   //
  //  / _ \ _ __   ___ _ __ __ _ _ __   __| | | __ )  //
  // | | | | '_ \ / _ \ '__/ _` | '_ \ / _` | |  _ \  //
  // | |_| | |_) |  __/ | | (_| | | | | (_| | | |_) | //
  //  \___/| .__/ \___|_|  \__,_|_| |_|\__,_| |____/  //
  //       |_|                                        //
  //////////////////////////////////////////////////////

  // Immediate Mux for operand B
  always_comb
  begin : immediate_mux
     case (immediate_mux_sel)
       //`IMM_VEC:   immediate_b = immediate_vec_id;
       `IMM_I:    immediate_b = imm_i_type;
       `IMM_S:    immediate_b = imm_s_type;
       `IMM_U:    immediate_b = imm_u_type;
       `IMM_HEX4: immediate_b = 32'h4;
       default:   immediate_b = 32'h4;
     endcase; // case (immediate_mux_sel)
  end

  // ALU_Op_b Mux
  always_comb
  begin : alu_operand_b_mux
     case (alu_op_b_mux_sel)
       default:            operand_b = operand_b_fw_id;
       `OP_B_REGB_OR_FWD:  operand_b = operand_b_fw_id;
       // `OP_B_REGC_OR_FWD:  operand_b = alu_operand_c;
       `OP_B_IMM:          operand_b = immediate_b;
     endcase // case (alu_op_b_mux_sel)
  end

  // scalar replication for operand B
  assign operand_b_vec = (vector_mode == `VEC_MODE8) ? {4{operand_b[7:0]}} : {2{operand_b[15:0]}};

  // choose normal or scalar replicated version of operand b
  assign alu_operand_b = (scalar_replication == 1'b1) ? operand_b_vec : operand_b;


  // Operand b forwarding mux
  always_comb
  begin : operand_b_fw_mux
     case (operand_b_fw_mux_sel)
       `SEL_FW_EX:    operand_b_fw_id = regfile_alu_wdata_fw_i;
       `SEL_FW_WB:    operand_b_fw_id = regfile_wdata_wb_i;
       `SEL_REGFILE:  operand_b_fw_id = regfile_data_rb_id;
       default:       operand_b_fw_id = regfile_data_rb_id;
     endcase; // case (operand_b_fw_mux_sel)
  end


  //////////////////////////////////////////////////////
  //   ___                                 _    ____  //
  //  / _ \ _ __   ___ _ __ __ _ _ __   __| |  / ___| //
  // | | | | '_ \ / _ \ '__/ _` | '_ \ / _` | | |     //
  // | |_| | |_) |  __/ | | (_| | | | | (_| | | |___  //
  //  \___/| .__/ \___|_|  \__,_|_| |_|\__,_|  \____| //
  //       |_|                                        //
  //////////////////////////////////////////////////////

  // ALU OP C Mux
  always_comb
  begin : alu_operand_c_mux
    case (alu_op_c_mux_sel)
      `OP_C_JT: operand_c = jump_target;
      default:  operand_c = regfile_data_rc_id;
    endcase // case (alu_op_c_mux_sel)
  end

  // Operand c forwarding mux
  always_comb
  begin : operand_c_fw_mux
     case (operand_c_fw_mux_sel)
       `SEL_FW_EX:    alu_operand_c = regfile_alu_wdata_fw_i;
       `SEL_FW_WB:    alu_operand_c = regfile_wdata_wb_i;
       `SEL_REGFILE:  alu_operand_c = operand_c;
       default:       alu_operand_c = operand_c;
     endcase; // case (operand_b_fw_mux_sel)
  end


  /////////////////////////////////////////////////////////
  //  ____  _____ ____ ___ ____ _____ _____ ____  ____   //
  // |  _ \| ____/ ___|_ _/ ___|_   _| ____|  _ \/ ___|  //
  // | |_) |  _|| |  _ | |\___ \ | | |  _| | |_) \___ \  //
  // |  _ <| |__| |_| || | ___) || | | |___|  _ < ___) | //
  // |_| \_\_____\____|___|____/ |_| |_____|_| \_\____/  //
  //                                                     //
  /////////////////////////////////////////////////////////
  riscv_register_file  registers_i
  (
    .clk          ( clk               ),
    .rst_n        ( rst_n             ),

    // Read port a
    .raddr_a_i    ( (dbg_reg_mux_i == 1'b0) ? regfile_addr_ra_id : dbg_reg_addr_i ),
    .rdata_a_o    ( regfile_data_ra_id ),

    // Read port b
    .raddr_b_i    ( regfile_addr_rb_id ),
    .rdata_b_o    ( regfile_data_rb_id ),

    // Read port c
    .raddr_c_i    ( regfile_addr_rc_id ),
    .rdata_c_o    ( regfile_data_rc_id ),

    // Write port a
    .waddr_a_i    ( regfile_waddr_wb_i ),
    .wdata_a_i    ( regfile_wdata_wb_i ),
    .we_a_i       ( regfile_we_wb_i    ),

    // Write port b
    .waddr_b_i    ( (dbg_reg_mux_i == 1'b0) ? regfile_alu_waddr_fw_i : dbg_reg_addr_i  ),
    .wdata_b_i    ( (dbg_reg_mux_i == 1'b0) ? regfile_alu_wdata_fw_i : dbg_reg_wdata_i ),
    .we_b_i       ( (dbg_reg_mux_i == 1'b0) ? regfile_alu_we_fw_i    : dbg_reg_we_i    )
  );

  assign dbg_reg_rdata_o = regfile_data_ra_id;

  ////////////////////////////////////////////////////////////////////
  //    ____ ___  _   _ _____ ____   ___  _     _     _____ ____    //
  //   / ___/ _ \| \ | |_   _|  _ \ / _ \| |   | |   | ____|  _ \   //
  //  | |  | | | |  \| | | | | |_) | | | | |   | |   |  _| | |_) |  //
  //  | |__| |_| | |\  | | | |  _ <| |_| | |___| |___| |___|  _ <   //
  //   \____\___/|_| \_| |_| |_| \_\\___/|_____|_____|_____|_| \_\  //
  //                                                                //
  ////////////////////////////////////////////////////////////////////
  controller controller_i
  (
      .clk                          ( clk                   ),
      .rst_n                        ( rst_n                 ),
      .fetch_enable_i               ( fetch_enable_i        ),
      .core_busy_o                  ( core_busy_o           ),

      .force_nop_o                  ( force_nop_controller  ),

      // Signal from-to PC pipe (instr rdata) and instr mem system (req and ack)
      .instr_rdata_i                ( instr_rdata_i         ),
      .instr_req_o                  ( instr_req_o           ),
      .instr_gnt_i                  ( instr_gnt_i           ),
      .instr_ack_i                  ( instr_ack_i           ),
      .pc_mux_sel_o                 ( pc_mux_sel_int        ),
      .pc_mux_boot_o                ( pc_mux_boot_o         ),

      // Alu signals
      .alu_operator_o               ( alu_operator          ),
      .extend_immediate_o           ( imm_sign_ext_sel      ),
      .alu_op_a_mux_sel_o           ( alu_op_a_mux_sel      ),
      .alu_op_b_mux_sel_o           ( alu_op_b_mux_sel      ),
      .alu_op_c_mux_sel_o           ( alu_op_c_mux_sel      ),
      .alu_pc_mux_sel_o             ( alu_pc_mux_sel        ),
      .immediate_mux_sel_o          ( immediate_mux_sel     ),

      .scalar_replication_o         ( scalar_replication    ),
      .vector_mode_o                ( vector_mode           ),
      .alu_cmp_mode_o               ( alu_cmp_mode          ),

      // mult signals
      .mult_en_o                    ( mult_en               ),
      .mult_sel_subword_o           ( mult_sel_subword      ),
      .mult_signed_mode_o           ( mult_signed_mode      ),
      .mult_use_carry_o             ( mult_use_carry        ),
      .mult_mac_en_o                ( mult_mac_en           ),

      // Register file control signals
      .regfile_wdata_mux_sel_o      ( regfile_wdata_mux_sel      ),
      .regfile_wdata_mux_sel_ex_i   ( regfile_wdata_mux_sel_ex_o ),
      .regfile_we_o                 ( regfile_we_id              ),

      .regfile_alu_we_o             ( regfile_alu_we_id          ),
      .regfile_alu_waddr_mux_sel_o  ( regfile_alu_waddr_mux_sel  ),

      .prepost_useincr_o            ( prepost_useincr            ),
      .data_misaligned_i            ( data_misaligned_i          ),

      // CSR control signals
      .csr_access_o                 ( csr_access            ),
      .csr_op_o                     ( csr_op                ),

      // Data bus interface
      .data_we_o                    ( data_we_id            ),
      .data_type_o                  ( data_type_id          ),
      .data_sign_extension_o        ( data_sign_ext_id      ),
      .data_reg_offset_o            ( data_reg_offset_id    ),
      .data_req_o                   ( data_req_id           ),
      .data_ack_i                   ( data_ack_i            ),
      .data_req_ex_i                ( data_req_ex_o         ),
      .data_rvalid_i                ( data_rvalid_i         ),

      // hwloop signals
      .hwloop_we_o                  ( hwloop_we             ),
      .hwloop_wb_mux_sel_o          ( hwloop_wb_mux_sel     ),
      .hwloop_cnt_mux_sel_o         ( hwloop_cnt_mux_sel    ),
      .hwloop_jump_i                ( hwloop_jump           ),

      // Interrupt signals
      .irq_present_i                ( irq_present           ),

      // Exception Controller Signals
      .illegal_insn_o               ( illegal_insn          ),
      .trap_insn_o                  ( trap_insn             ),
      .pipe_flush_o                 ( pipe_flush            ),
      .pc_valid_i                   ( pc_valid              ),
      .clear_isr_running_o          ( clear_isr_running     ),
      .pipe_flushed_i               ( pipe_flushed_o        ),
      .trap_hit_i                   ( trap_hit              ),

      // Debug Unit Signals
      .dbg_stall_i                  ( dbg_stall_i           ),
      .dbg_set_npc_i                ( dbg_set_npc_i         ),
      .dbg_trap_o                   ( dbg_trap_o            ),

      // SPR Signals
      .sr_flag_fw_i                 ( sr_flag_fw_i          ), // Forwarded Branch Signal
      .sr_flag_i                    ( sr_flag_i             ),
      .set_flag_ex_i                ( set_flag_ex_o         ),
      .set_flag_o                   ( set_flag              ),
      .set_overflow_o               ( set_overflow          ),
      .set_carry_o                  ( set_carry             ),
      .restore_sr_o                 ( restore_sr_o          ),

      // regfile port 1
      .regfile_waddr_ex_i           ( regfile_waddr_ex_o    ), // Write address for register file from ex-wb- pipeline registers
      .regfile_we_ex_i              ( regfile_we_ex_o       ),
      .regfile_waddr_wb_i           ( regfile_waddr_wb_i    ), // Write address for register file from ex-wb- pipeline registers
      .regfile_we_wb_i              ( regfile_we_wb_i       ),

      // regfile port 2
      .regfile_alu_waddr_fw_i       ( regfile_alu_waddr_fw_i ),
      .regfile_alu_we_fw_i          ( regfile_alu_we_fw_i    ),

      // Forwarding signals
      .operand_a_fw_mux_sel_o       ( operand_a_fw_mux_sel  ),
      .operand_b_fw_mux_sel_o       ( operand_b_fw_mux_sel  ),
      .operand_c_fw_mux_sel_o       ( operand_c_fw_mux_sel  ),

      // To controller (TODO: Remove when control/decode separated and moved)
      .jump_in_ex_i                 ( jump_in_ex_o          ),

      // To exception controller and EX: Jump/Branch indication
      .jump_in_id_o                 ( jump_in_id_o          ),

      // Stall signals
      .stall_if_o                   ( stall_if_o            ),
      .stall_id_o                   ( stall_id_o            ),
      .stall_ex_o                   ( stall_ex_o            ),
      .stall_wb_o                   ( stall_wb_o            )
    );

  ///////////////////////////////////////////////////////////////////////
  //  _____               ____            _             _ _            //
  // | ____|_  _____     / ___|___  _ __ | |_ _ __ ___ | | | ___ _ __  //
  // |  _| \ \/ / __|   | |   / _ \| '_ \| __| '__/ _ \| | |/ _ \ '__| //
  // | |___ >  < (__ _  | |__| (_) | | | | |_| | | (_) | | |  __/ |    //
  // |_____/_/\_\___(_)  \____\___/|_| |_|\__|_|  \___/|_|_|\___|_|    //
  //                                                                   //
  ///////////////////////////////////////////////////////////////////////

  exc_controller exc_controller_i
  (
      .clk                  ( clk               ),
      .rst_n                ( rst_n             ),

      .fetch_enable_i       ( fetch_enable_i    ),

      // to IF stage
      .exc_pc_sel_o         ( exc_pc_sel        ),
      .exc_pc_mux_o         ( exc_pc_mux_o      ),
      .force_nop_o          ( force_nop_exc     ),

      // hwloop signals
      .hwloop_enable_o      ( hwloop_enable     ),

      // Interrupt signals
      .irq_i                ( irq_i             ),
      .irq_nm_i             ( irq_nm_i          ),
      .irq_enable_i         ( irq_enable_i      ),
      .irq_present_o        ( irq_present       ),

      // SPR
      .save_pc_if_o         ( save_pc_if_o      ),
      .save_pc_id_o         ( save_pc_id_o      ),
      .save_sr_o            ( save_sr_o         ),

      // Controller
      .core_busy_i          ( core_busy_o       ),
      .jump_in_id_i         ( jump_in_id_o      ),
      .jump_in_ex_i         ( jump_in_ex        ),
      .stall_id_i           ( stall_id_o        ),
      .illegal_insn_i       ( illegal_insn      ),
      .trap_insn_i          ( trap_insn         ),
      .drop_instruction_i   ( 1'b0              ),
      .pipe_flush_i         ( pipe_flush        ),
      .pc_valid_o           ( pc_valid          ),
      .clear_isr_running_i  ( clear_isr_running ),
      .trap_hit_o           ( trap_hit          ),

      // Debug Unit Signals
      .dbg_flush_pipe_i     ( dbg_flush_pipe_i  ),
      .pipe_flushed_o       ( pipe_flushed_o    ),
      .dbg_st_en_i          ( dbg_st_en_i       ),
      .dbg_dsr_i            ( dbg_dsr_i         )
    );


  //////////////////////////////////////////////////////////////////////////
  //          ____ ___  _   _ _____ ____   ___  _     _     _____ ____    //
  //         / ___/ _ \| \ | |_   _|  _ \ / _ \| |   | |   | ____|  _ \   //
  // HWLOOP-| |  | | | |  \| | | | | |_) | | | | |   | |   |  _| | |_) |  //
  //        | |__| |_| | |\  | | | |  _ <| |_| | |___| |___| |___|  _ <   //
  //         \____\___/|_| \_| |_| |_| \_\\___/|_____|_____|_____|_| \_\  //
  //                                                                      //
  //////////////////////////////////////////////////////////////////////////

  /*
  hwloop_controller hwloop_controller_i
    (
     // from ID stage
     .enable_i                     ( hwloop_enable         ),
     .current_pc_i                 ( current_pc_if_i       ),

     // to ID controller
     .hwloop_jump_o                ( hwloop_jump           ),

     // to if stage
     .hwloop_targ_addr_o           ( hwloop_targ_addr_o    ),

     // from hwloop_regs
     .hwloop_start_addr_i          ( hwloop_start_addr_i   ),
     .hwloop_end_addr_i            ( hwloop_end_addr_i     ),
     .hwloop_counter_i             ( hwloop_counter_i      ),

     // to hwloop_regs
     .hwloop_dec_cnt_o             ( hwloop_dec_cnt_o      )
     );
   */



  /////////////////////////////////////////////////////////////////////////////////
  //   ___ ____        _______  __  ____ ___ ____  _____ _     ___ _   _ _____   //
  //  |_ _|  _ \      | ____\ \/ / |  _ \_ _|  _ \| ____| |   |_ _| \ | | ____|  //
  //   | || | | |_____|  _|  \  /  | |_) | || |_) |  _| | |    | ||  \| |  _|    //
  //   | || |_| |_____| |___ /  \  |  __/| ||  __/| |___| |___ | || |\  | |___   //
  //  |___|____/      |_____/_/\_\ |_|  |___|_|   |_____|_____|___|_| \_|_____|  //
  //                                                                             //
  /////////////////////////////////////////////////////////////////////////////////
  always_ff @(posedge clk, negedge rst_n)
  begin : ID_EX_PIPE_REGISTERS
    if (rst_n == 1'b0)
    begin
      regfile_rb_data_ex_o        <= 32'h0000_0000;

      alu_operator_ex_o           <= `ALU_NOP;
      alu_operand_a_ex_o          <= 32'h0000_0000;
      alu_operand_b_ex_o          <= 32'h0000_0000;
      alu_operand_c_ex_o          <= 32'h0000_0000;

      vector_mode_ex_o            <= `VEC_MODE32;
      alu_cmp_mode_ex_o           <= `ALU_CMP_FULL;
      alu_vec_ext_ex_o            <= 2'h0;

      mult_en_ex_o                <= 1'b0;
      mult_sel_subword_ex_o       <= 2'b0;
      mult_signed_mode_ex_o       <= 2'b0;
      mult_use_carry_ex_o         <= 1'b0;
      mult_mac_en_ex_o            <= 1'b0;

      regfile_waddr_ex_o          <= 5'b0;
      regfile_wdata_mux_sel_ex_o  <= 1'b0;
      regfile_we_ex_o             <= 1'b0;

      regfile_alu_waddr_ex_o      <= 4'b0;
      regfile_alu_we_ex_o         <= 1'b0;
      prepost_useincr_ex_o        <= 1'b0;

      csr_access_ex_o             <= 1'b0;
      csr_op_ex_o                 <= 2'b0;

      data_we_ex_o                <= 1'b0;
      data_type_ex_o              <= 2'b0;
      data_sign_ext_ex_o          <= 1'b0;
      data_reg_offset_ex_o        <= 2'b0;
      data_req_ex_o               <= 1'b0;

      data_misaligned_ex_o        <= 1'b0;

      set_flag_ex_o               <= 1'b0;
      set_overflow_ex_o           <= 1'b0;
      set_carry_ex_o              <= 1'b0;

      hwloop_we_ex_o              <= 3'b0;
      hwloop_regid_ex_o           <= 2'b0;
      hwloop_wb_mux_sel_ex_o      <= 1'b0;
      hwloop_cnt_o                <= 32'b0;

      jump_in_ex                  <= 2'b0;

      `ifdef TCDM_ADDR_PRECAL
      alu_adder_o                 <= '0;
      `endif

    end
    else if ((stall_ex_o == 1'b0) && (data_misaligned_i == 1'b1))
    begin // misaligned access case, only unstall alu operands

      // if we are using post increments, then we have to use the
      // original value of the register for the second memory access
      // => keep it stalled
      if (prepost_useincr_ex_o == 1'b1)
      begin
        alu_operand_a_ex_o        <= alu_operand_a;
      end

      alu_operand_b_ex_o          <= alu_operand_b;
      regfile_alu_we_ex_o         <= regfile_alu_we_id;
      prepost_useincr_ex_o        <= prepost_useincr;

      data_misaligned_ex_o        <= 1'b1;
    end
    else if ((stall_ex_o == 1'b0) && (data_misaligned_i == 1'b0))
    begin // unstall the whole pipeline
      regfile_rb_data_ex_o        <= operand_b_fw_id;

      alu_operator_ex_o           <= alu_operator;
      alu_operand_a_ex_o          <= alu_operand_a;
      alu_operand_b_ex_o          <= alu_operand_b;
      alu_operand_c_ex_o          <= alu_operand_c;

      vector_mode_ex_o            <= vector_mode;
      alu_cmp_mode_ex_o           <= alu_cmp_mode;
      alu_vec_ext_ex_o            <= alu_vec_ext;

      mult_en_ex_o                <= mult_en;
      mult_sel_subword_ex_o       <= mult_sel_subword;
      mult_signed_mode_ex_o       <= mult_signed_mode;
      mult_use_carry_ex_o         <= mult_use_carry;
      mult_mac_en_ex_o            <= mult_mac_en;


      regfile_waddr_ex_o          <= regfile_waddr_id;
      regfile_wdata_mux_sel_ex_o  <= regfile_wdata_mux_sel;
      regfile_we_ex_o             <= regfile_we_id;

      regfile_alu_waddr_ex_o      <= regfile_alu_waddr_id;
      regfile_alu_we_ex_o         <= regfile_alu_we_id;

      prepost_useincr_ex_o        <= prepost_useincr;

      csr_access_ex_o             <= csr_access;
      csr_op_ex_o                 <= csr_op;

      data_we_ex_o                <= data_we_id;
      data_type_ex_o              <= data_type_id;
      data_sign_ext_ex_o          <= data_sign_ext_id;
      data_reg_offset_ex_o        <= data_reg_offset_id;
      data_req_ex_o               <= data_req_id;

      data_misaligned_ex_o        <= 1'b0;

      set_flag_ex_o               <= set_flag;
      set_overflow_ex_o           <= set_overflow;
      set_carry_ex_o              <= set_carry;

      hwloop_we_ex_o              <= hwloop_we;
      hwloop_regid_ex_o           <= hwloop_regid;
      hwloop_wb_mux_sel_ex_o      <= hwloop_wb_mux_sel;
      hwloop_cnt_o                <= hwloop_cnt;

      jump_in_ex                  <= jump_in_id_o;

`ifdef TCDM_ADDR_PRECAL
      alu_adder_o                 <= alu_operand_a + alu_operand_b;
`endif

    end
  end


endmodule
