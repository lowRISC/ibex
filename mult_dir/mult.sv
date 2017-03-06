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

import zeroriscy_defines::*;


module zeroriscy_mult
(
//  input  logic        clk,
//  input  logic        rst_n,

//  input  logic        enable_i,
//  input  logic [ 2:0] operator_i,

  // integer and short multiplier
//  input  logic        short_subword_i,
//  input  logic [ 1:0] short_signed_i,

  input  logic [31:0] op_a_i,
  input  logic [31:0] op_b_i,
//  input  logic [31:0] op_c_i,

//  input  logic [ 4:0] imm_i,

  output logic [31:0] result_o

//  output logic        multicycle_o,
//  output logic        ready_o,
//  input  logic        ex_ready_i
);

  logic [31:0] mult_extended;
  assign mult_extended = $signed(op_a_i[7:0])*$signed(op_b_i[7:0]);
  assign result_o      = mult_extended;

endmodule // zeroriscy_mult
