// Copyright 2015 ETH Zurich and University of Bologna.
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
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                                                                            //
// Design Name:    Subword multiplier and MAC                                 //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Advanced MAC unit for PULP.                                //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

`include "riscv_defines.sv"


module riscv_mult
(
  input  logic [ 2:0] operator_i,

  // integer and short multiplier
  input  logic        short_subword_i,
  input  logic        short_signed_i,

  input  logic [31:0] op_a_i,
  input  logic [31:0] op_b_i,
  input  logic [31:0] op_c_i,

  input  logic [ 4:0] imm_i,


  // dot multiplier
  input  logic [ 1:0] dot_signed_i,
  input  logic [31:0] dot_op_a_i,
  input  logic [31:0] dot_op_b_i,
  input  logic [31:0] dot_op_c_i,

  output logic [31:0] result_o
);

  //////////////////////////////////////////////////////////////
  //  ___ _  _ _____ ___ ___ ___ ___   __  __ _   _ _  _____   //
  // |_ _| \| |_   _| __/ __| __| _ \ |  \/  | | | | ||_   _|  //
  //  | || .` | | | | _| (_ | _||   / | |\/| | |_| | |__| |    //
  // |___|_|\_| |_| |___\___|___|_|_\ |_|  |_|\___/|____|_|    //
  //                                                           //
  ///////////////////////////////////////////////////////////////

  logic [16:0] short_op_a;
  logic [16:0] short_op_b;
  logic [31:0] short_mac;
  logic [31:0] short_round, short_round_tmp;
  logic [31:0] short_result;

  // prepare the rounding value
  assign short_round_tmp = (32'h00000001) << imm_i;
  assign short_round = (operator_i == `MUL_IR) ? {1'b0, short_round_tmp[31:1]} : '0;

  // perform subword selection and sign extensions
  assign short_op_a[15:0] = short_subword_i ? op_a_i[31:16] : op_a_i[15:0];
  assign short_op_b[15:0] = short_subword_i ? op_b_i[31:16] : op_b_i[15:0];

  assign short_op_a[16] = short_signed_i & short_op_a[15];
  assign short_op_b[16] = short_signed_i & short_op_b[15];

  assign short_mac = $signed(op_c_i) + $signed(short_op_a) * $signed(short_op_b) + $signed(short_round);

  assign short_result = $signed({(short_signed_i & short_mac[31]), short_mac[31:0]}) >>> imm_i;


  // 32x32 = 32-bit multiplier
  logic [31:0] int_op_a_msu;
  logic [31:0] int_op_b_msu;
  logic [31:0] int_result;

  logic        int_is_msu;

  assign int_is_msu = (operator_i == `MUL_MSU32); // TODO: think about using a separate signal here, could prevent some switching

  assign int_op_a_msu = op_a_i ^ {32{int_is_msu}};
  assign int_op_b_msu = op_b_i & {32{int_is_msu}};

  assign int_result = $signed(op_c_i) + $signed(int_op_b_msu) + $signed(int_op_a_msu) * $signed(op_b_i);

  ///////////////////////////////////////////////
  //  ___   ___ _____   __  __ _   _ _  _____  //
  // |   \ / _ \_   _| |  \/  | | | | ||_   _| //
  // | |) | (_) || |   | |\/| | |_| | |__| |   //
  // |___/ \___/ |_|   |_|  |_|\___/|____|_|   //
  //                                           //
  ///////////////////////////////////////////////

  logic [3:0][ 8:0] dot_char_op_a;
  logic [3:0][ 8:0] dot_char_op_b;
  logic [3:0][17:0] dot_char_mul;
  logic [31:0]      dot_char_result;

  logic [1:0][16:0] dot_short_op_a;
  logic [1:0][16:0] dot_short_op_b;
  logic [1:0][31:0] dot_short_mul;
  logic [31:0]      dot_short_result;


  assign dot_char_op_a[0] = {dot_signed_i[1] & dot_op_a_i[ 7], dot_op_a_i[ 7: 0]};
  assign dot_char_op_a[1] = {dot_signed_i[1] & dot_op_a_i[15], dot_op_a_i[15: 8]};
  assign dot_char_op_a[2] = {dot_signed_i[1] & dot_op_a_i[23], dot_op_a_i[23:16]};
  assign dot_char_op_a[3] = {dot_signed_i[1] & dot_op_a_i[31], dot_op_a_i[31:24]};

  assign dot_char_op_b[0] = {dot_signed_i[0] & dot_op_b_i[ 7], dot_op_b_i[ 7: 0]};
  assign dot_char_op_b[1] = {dot_signed_i[0] & dot_op_b_i[15], dot_op_b_i[15: 8]};
  assign dot_char_op_b[2] = {dot_signed_i[0] & dot_op_b_i[23], dot_op_b_i[23:16]};
  assign dot_char_op_b[3] = {dot_signed_i[0] & dot_op_b_i[31], dot_op_b_i[31:24]};

  assign dot_char_mul[0]  = $signed(dot_char_op_a[0]) * $signed(dot_char_op_b[0]);
  assign dot_char_mul[1]  = $signed(dot_char_op_a[1]) * $signed(dot_char_op_b[1]);
  assign dot_char_mul[2]  = $signed(dot_char_op_a[2]) * $signed(dot_char_op_b[2]);
  assign dot_char_mul[3]  = $signed(dot_char_op_a[3]) * $signed(dot_char_op_b[3]);

  assign dot_char_result  = $signed(dot_char_mul[0]) + $signed(dot_char_mul[1]) + $signed(dot_char_mul[2]) + $signed(dot_char_mul[3]) + $signed(dot_op_c_i);


  assign dot_short_op_a[0] = {dot_signed_i[1] & dot_op_a_i[15], dot_op_a_i[15: 0]};
  assign dot_short_op_a[1] = {dot_signed_i[1] & dot_op_a_i[31], dot_op_a_i[31:16]};

  assign dot_short_op_b[0] = {dot_signed_i[0] & dot_op_b_i[15], dot_op_b_i[15: 0]};
  assign dot_short_op_b[1] = {dot_signed_i[0] & dot_op_b_i[31], dot_op_b_i[31:16]};

  assign dot_short_mul[0]  = $signed(dot_short_op_a[0]) * $signed(dot_short_op_b[0]);
  assign dot_short_mul[1]  = $signed(dot_short_op_a[1]) * $signed(dot_short_op_b[1]);

  assign dot_short_result  = $signed(dot_short_mul[0]) + $signed(dot_short_mul[1]) + $signed(dot_op_c_i);


  ////////////////////////////////////////////////////////
  //   ____                 _ _     __  __              //
  //  |  _ \ ___  ___ _   _| | |_  |  \/  |_   ___  __  //
  //  | |_) / _ \/ __| | | | | __| | |\/| | | | \ \/ /  //
  //  |  _ <  __/\__ \ |_| | | |_  | |  | | |_| |>  <   //
  //  |_| \_\___||___/\__,_|_|\__| |_|  |_|\__,_/_/\_\  //
  //                                                    //
  ////////////////////////////////////////////////////////

  always_comb
  begin
    result_o   = 'x;

    unique case (operator_i)
      `MUL_MAC32, `MUL_MSU32: result_o = int_result;

      `MUL_I, `MUL_IR: result_o = short_result;

      `MUL_DOT8:  result_o = dot_char_result;
      `MUL_DOT16: result_o = dot_short_result;

      default: ; // default case to suppress unique warning
    endcase
  end
endmodule
