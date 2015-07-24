////////////////////////////////////////////////////////////////////////////////
// Company:        IIS @ ETHZ - Federal Institute of Technology               //
//                 DEI @ UNIBO - University of Bologna                        //
//                                                                            //
// Engineer:       Renzo Andri - andrire@student.ethz.ch                      //
//                                                                            //
// Additional contributions by:                                               //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                                                                            //
//                                                                            //
// Create Date:    01/07/2014                                                 //
// Design Name:    Excecute stage                                             //
// Module Name:    ex_stage.sv                                                //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Execution stage: Hosts ALU and MAC unit                    //
//                 ALU: computes additions/subtractions/comparisons           //
//                 MAC:                                                       //
//                                                                            //
//                                                                            //
// Revision:                                                                  //
//                                                                            //
// Revision v0.1 - File Created                                               //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////
// int = internal signals
// wb  = writeback
// sp  = special registers

`include "defines.sv"


module ex_stage
(
    input  logic                      clk,
    input  logic                      rst_n,

    // ALU signals from ID stage
    input  logic [`ALU_OP_WIDTH-1:0]  alu_operator_i,
    input  logic [31:0]               alu_operand_a_i,
    input  logic [31:0]               alu_operand_b_i,
    input  logic [31:0]               alu_operand_c_i,

    input  logic [1:0]                vector_mode_i,
    input  logic [1:0]                alu_cmp_mode_i,
    input  logic [1:0]                alu_vec_ext_i,

    // Multiplier signals
    input  logic                      mult_en_i,
    input  logic [1:0]                mult_sel_subword_i,
    input  logic [1:0]                mult_signed_mode_i,
    input  logic                      mult_use_carry_i,
    input  logic                      mult_mac_en_i,

    output logic [31:0]               data_addr_ex_o,

    // input from ID stage
    input  logic                      stall_wb_i,

    input  logic [4:0]                regfile_alu_waddr_i,
    input  logic                      regfile_alu_we_i,

    input  logic                      prepost_useincr_i,

    // directly passed through to WB stage, not used in EX
    input  logic                      regfile_we_i,
    input  logic [4:0]                regfile_waddr_i,
    input  logic                      regfile_wdata_mux_sel_i,

    input  logic [31:0]               regfile_rb_data_i,

    input  logic                      hwloop_wb_mux_sel_i,
    input  logic [31:0]               hwloop_pc_plus4_i,
    input  logic [31:0]               hwloop_cnt_i,

    // CSR access
    input  logic                      csr_access_i,
    input  logic [31:0]               csr_rdata_i,

    // Output of EX stage pipeline
    output logic [4:0]                regfile_waddr_wb_o,
    output logic                      regfile_wdata_mux_sel_wb_o,
    output logic                      regfile_we_wb_o,
    output logic [31:0]               regfile_rb_data_wb_o,

    output logic [31:0]               hwloop_start_data_o,
    output logic [31:0]               hwloop_end_data_o,
    output logic [31:0]               hwloop_cnt_data_o,

    // Forwarding ports : to ID stage
    output logic  [4:0]               regfile_alu_waddr_fw_o,
    output logic                      regfile_alu_we_fw_o,
    output logic [31:0]               regfile_alu_wdata_fw_o,    // forward to RF and ID/EX pipe, ALU & MUL

    // To IF: Jump and branch target and decision
    output logic [31:0]               jump_target_o,
    output logic                      branch_decision_o

`ifdef TCDM_ADDR_PRECAL
    ,
    input logic [31:0]                alu_adder_i
`endif
);


  // Internal output of the LU
  logic [31:0]  alu_result;

  logic [31:0]  alu_adder_lsu_int; // to LS unit

  logic [31:0]  mult_result;


  assign regfile_alu_we_fw_o       = regfile_alu_we_i;
  assign regfile_alu_waddr_fw_o    = regfile_alu_waddr_i;

  always_comb
  begin
    regfile_alu_wdata_fw_o = alu_result;

    if (mult_en_i == 1'b1)
      regfile_alu_wdata_fw_o = mult_result;

    if (csr_access_i == 1'b1)
      regfile_alu_wdata_fw_o = csr_rdata_i;
  end
  // assign regfile_alu_wdata_fw_o    = (mult_en_i == 1'b0) ? alu_result : mult_result;

  //NOTE Igor fix: replaced alu_adder_int with alu_adder_lsu_int --> Now data_addr is calculated with
  //NOTE a dedicated adder, no carry is considered , just op_a + op_b from id stage
  assign data_addr_ex_o        = (prepost_useincr_i == 1'b1) ? alu_adder_lsu_int : alu_operand_a_i;

  // hwloop mux. selects the right data to be sent to the hwloop registers (start/end-address and counter)
  always_comb
  begin : hwloop_start_mux
    case (hwloop_wb_mux_sel_i)
      1'b0: hwloop_start_data_o  = hwloop_pc_plus4_i;
      1'b1: hwloop_start_data_o  = alu_result;
    endcase; // case (hwloop_wb_mux_sel)
  end

  // assign alu result to hwloop end data
  assign hwloop_end_data_o = alu_result;

  // assign hwloop mux. selects the right data to be sent to the hwloop registers (start/end-address and counter)
  assign hwloop_cnt_data_o = hwloop_cnt_i;

  // Branch is taken when result == 1'b1
  assign branch_decision_o = alu_result[0];
  assign jump_target_o     = alu_operand_c_i;


  ////////////////////////////
  //     _    _    _   _    //
  //    / \  | |  | | | |   //
  //   / _ \ | |  | | | |   //
  //  / ___ \| |__| |_| |   //
  // /_/   \_\_____\___/    //
  //                        //
  ////////////////////////////
  alu alu_i
  (
   .operator_i    ( alu_operator_i      ),
   .operand_a_i   ( alu_operand_a_i     ),
   .operand_b_i   ( alu_operand_b_i     ),
   .operand_c_i   ( alu_operand_c_i     ),
   .carry_i       ( 1'b0                ),
   .flag_i        ( 1'b0                ),

   .vector_mode_i ( vector_mode_i       ),
   .cmp_mode_i    ( alu_cmp_mode_i      ),
   .vec_ext_i     ( alu_vec_ext_i       ),

   .adder_lsu_o   ( alu_adder_lsu_int   ),

   .result_o      ( alu_result          ),
   .overflow_o    (                     ),
   .carry_o       (                     ),
   .flag_o        (                     )
  );


  ////////////////////////////////////////////////////////////////
  //  __  __ _   _ _   _____ ___ ____  _     ___ _____ ____     //
  // |  \/  | | | | | |_   _|_ _|  _ \| |   |_ _| ____|  _ \    //
  // | |\/| | | | | |   | |  | || |_) | |    | ||  _| | |_) |   //
  // | |  | | |_| | |___| |  | ||  __/| |___ | || |___|  _ <    //
  // |_|  |_|\___/|_____|_| |___|_|   |_____|___|_____|_| \_\   //
  //                                                            //
  ////////////////////////////////////////////////////////////////
  mult mult_i
  (
   .vector_mode_i   ( vector_mode_i        ),
   .sel_subword_i   ( mult_sel_subword_i   ),
   .signed_mode_i   ( mult_signed_mode_i   ),
   .use_carry_i     ( mult_use_carry_i     ),
   .mac_en_i        ( mult_mac_en_i        ),

   .op_a_i          ( alu_operand_a_i      ),
   .op_b_i          ( alu_operand_b_i      ),
   .mac_i           ( alu_operand_c_i      ),
   .carry_i         ( 1'b0                 ),

   .result_o        ( mult_result          ),

   .carry_o         (                      ),
   .overflow_o      (                      )
  );


  ///////////////////////////////////////
  // EX/WB Pipeline Register           //
  ///////////////////////////////////////
  always_ff @(posedge clk, negedge rst_n)
  begin : EX_WB_Pipeline_Register
    if (rst_n == 1'b0)
    begin
      regfile_waddr_wb_o           <= 5'b0_0000;
      regfile_wdata_mux_sel_wb_o   <= 1'b0;
      regfile_we_wb_o              <= 1'b0;
      regfile_rb_data_wb_o         <= 32'h0000_0000;
    end
    else
    begin
      if (stall_wb_i == 1'b0)
      begin
        regfile_we_wb_o            <= regfile_we_i;
        regfile_waddr_wb_o         <= regfile_waddr_i;
        regfile_wdata_mux_sel_wb_o <= regfile_wdata_mux_sel_i;
        regfile_rb_data_wb_o       <= regfile_rb_data_i;
      end
    end
  end

endmodule
