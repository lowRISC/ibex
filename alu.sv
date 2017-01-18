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
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                                                                            //
// Design Name:    ALU                                                        //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Arithmetic logic unit of the pipelined processor           //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

`include "riscv_config.sv"

import riscv_defines::*;

module littleriscv_alu
(
  input  logic                     clk,
  input  logic                     rst_n,

  input  logic [ALU_OP_WIDTH-1:0]  operator_i,
  input  logic [31:0]              operand_a_i,
  input  logic [31:0]              operand_b_i,
  input  logic [31:0]              operand_c_i,


  output logic [31:0]              adder_result_o,

  output logic [31:0]              result_o,
  output logic                     comparison_result_o,

  output logic                     ready_o,
  input  logic                     ex_ready_i
);


  logic [31:0] operand_a_rev;
  logic [31:0] operand_a_neg;
  logic [31:0] operand_a_neg_rev;

  assign operand_a_neg = ~operand_a_i;

  // bit reverse operand_a for left shifts and bit counting
  generate
    genvar k;
    for(k = 0; k < 32; k++)
    begin
      assign operand_a_rev[k] = operand_a_i[31-k];
    end
  endgenerate

  // bit reverse operand_a_neg for left shifts and bit counting
  generate
    genvar m;
    for(m = 0; m < 32; m++)
    begin
      assign operand_a_neg_rev[m] = operand_a_neg[31-m];
    end
  endgenerate

  logic [31:0] operand_b_neg;

  assign operand_b_neg = ~operand_b_i;



  //////////////////////////////////////////////////////////////////////////////////////////
  //   ____            _   _ _   _                      _      _       _     _            //
  //  |  _ \ __ _ _ __| |_(_) |_(_) ___  _ __   ___  __| |    / \   __| | __| | ___ _ __  //
  //  | |_) / _` | '__| __| | __| |/ _ \| '_ \ / _ \/ _` |   / _ \ / _` |/ _` |/ _ \ '__| //
  //  |  __/ (_| | |  | |_| | |_| | (_) | | | |  __/ (_| |  / ___ \ (_| | (_| |  __/ |    //
  //  |_|   \__,_|_|   \__|_|\__|_|\___/|_| |_|\___|\__,_| /_/   \_\__,_|\__,_|\___|_|    //
  //                                                                                      //
  //////////////////////////////////////////////////////////////////////////////////////////

  logic        adder_op_b_negate;
  logic [31:0] adder_op_a, adder_op_b;
  logic [35:0] adder_in_a, adder_in_b;
  logic [31:0] adder_result;
  logic [35:0] adder_result_expanded;

  assign adder_op_b_negate = (operator_i == ALU_SUB) || (operator_i == ALU_SUBR) ||
                             (operator_i == ALU_SUBU) || (operator_i == ALU_SUBUR);

  // prepare operand a
  assign adder_op_a = (operator_i == ALU_ABS) ? operand_a_neg : operand_a_i;

  // prepare operand b
  assign adder_op_b = adder_op_b_negate ? operand_b_neg : operand_b_i;

  // prepare carry
  always_comb
  begin
    adder_in_a[    0] = 1'b1;
    adder_in_a[ 8: 1] = adder_op_a[ 7: 0];
    adder_in_a[    9] = 1'b1;
    adder_in_a[17:10] = adder_op_a[15: 8];
    adder_in_a[   18] = 1'b1;
    adder_in_a[26:19] = adder_op_a[23:16];
    adder_in_a[   27] = 1'b1;
    adder_in_a[35:28] = adder_op_a[31:24];

    adder_in_b[    0] = 1'b0;
    adder_in_b[ 8: 1] = adder_op_b[ 7: 0];
    adder_in_b[    9] = 1'b0;
    adder_in_b[17:10] = adder_op_b[15: 8];
    adder_in_b[   18] = 1'b0;
    adder_in_b[26:19] = adder_op_b[23:16];
    adder_in_b[   27] = 1'b0;
    adder_in_b[35:28] = adder_op_b[31:24];

    if (adder_op_b_negate || (operator_i == ALU_ABS || operator_i == ALU_CLIP)) begin
      // special case for subtractions and absolute number calculations
      adder_in_b[0] = 1'b1;


    end else begin
    end
  end

  // actual adder
  assign adder_result_expanded = adder_in_a + adder_in_b;
  assign adder_result = {adder_result_expanded[35:28],
                         adder_result_expanded[26:19],
                         adder_result_expanded[17:10],
                         adder_result_expanded[8:1]};


  // normalization stage
  logic [31:0] adder_round_value;
  logic [31:0] adder_round_result;

  assign adder_round_value  = '0;
  assign adder_round_result = adder_result;

  assign adder_result_o = adder_result;

  ////////////////////////////////////////
  //  ____  _   _ ___ _____ _____       //
  // / ___|| | | |_ _|  ___|_   _|      //
  // \___ \| |_| || || |_    | |        //
  //  ___) |  _  || ||  _|   | |        //
  // |____/|_| |_|___|_|     |_|        //
  //                                    //
  ////////////////////////////////////////

  logic        shift_left;         // should we shift left
  logic        shift_use_round;
  logic        shift_arithmetic;

  logic [31:0] shift_amt_left;     // amount of shift, if to the left
  logic [31:0] shift_amt;          // amount of shift, to the right
  logic [31:0] shift_amt_int;      // amount of shift, used for the actual shifters
  logic [31:0] shift_amt_norm;     // amount of shift, used for normalization
  logic [31:0] shift_op_a;         // input of the shifter
  logic [31:0] shift_result;
  logic [31:0] shift_right_result;
  logic [31:0] shift_left_result;

  assign shift_amt = operand_b_i;

  // by reversing the bits of the input, we also have to reverse the order of shift amounts
  always_comb
  begin
    begin
      shift_amt_left[31: 0] = shift_amt[31: 0];
    end
  end

  // ALU_FL1 and ALU_CBL are used for the bit counting ops later
  assign shift_left = (operator_i == ALU_SLL) || (operator_i == ALU_BINS) ||
                      (operator_i == ALU_FL1) || (operator_i == ALU_CLB) ||
                      (operator_i == ALU_DIV) || (operator_i == ALU_DIVU) ||
                      (operator_i == ALU_REM) || (operator_i == ALU_REMU);

  assign shift_use_round = (operator_i == ALU_ADD)   || (operator_i == ALU_SUB)   ||
                           (operator_i == ALU_ADDR)  || (operator_i == ALU_SUBR)  ||
                           (operator_i == ALU_ADDU)  || (operator_i == ALU_SUBU)  ||
                           (operator_i == ALU_ADDUR) || (operator_i == ALU_SUBUR);

  assign shift_arithmetic = (operator_i == ALU_SRA)  ||
                            (operator_i == ALU_ADD)  || (operator_i == ALU_SUB)  ||
                            (operator_i == ALU_ADDR) || (operator_i == ALU_SUBR);

  // choose the bit reversed or the normal input for shift operand a
  assign shift_op_a    = shift_left ? operand_a_rev :
                          (shift_use_round ? adder_round_result : operand_a_i);


  assign shift_amt_int = shift_use_round ? shift_amt_norm :
                          (shift_left ? shift_amt_left : shift_amt);

  assign shift_amt_norm = '0;

  // right shifts, we let the synthesizer optimize this
  logic [63:0] shift_op_a_32;

  assign shift_op_a_32 = (operator_i == ALU_ROR) ? {shift_op_a, shift_op_a} : $signed({ {32{shift_arithmetic & shift_op_a[31]}}, shift_op_a});

  always_comb
  begin
    begin
        shift_right_result = shift_op_a_32 >> shift_amt_int[4:0];
    end
  end

  // bit reverse the shift_right_result for left shifts
  genvar       j;
  generate
    for(j = 0; j < 32; j++)
    begin
      assign shift_left_result[j] = shift_right_result[31-j];
    end
  endgenerate

  assign shift_result = shift_left ? shift_left_result : shift_right_result;


  //////////////////////////////////////////////////////////////////
  //   ____ ___  __  __ ____   _    ____  ___ ____   ___  _   _   //
  //  / ___/ _ \|  \/  |  _ \ / \  |  _ \|_ _/ ___| / _ \| \ | |  //
  // | |  | | | | |\/| | |_) / _ \ | |_) || |\___ \| | | |  \| |  //
  // | |__| |_| | |  | |  __/ ___ \|  _ < | | ___) | |_| | |\  |  //
  //  \____\___/|_|  |_|_| /_/   \_\_| \_\___|____/ \___/|_| \_|  //
  //                                                              //
  //////////////////////////////////////////////////////////////////

  logic [3:0] is_equal;
  logic [3:0] is_greater;  // handles both signed and unsigned forms

  // 8-bit vector comparisons, basic building blocks
  logic [3:0] cmp_signed;
  logic [3:0] is_equal_vec;
  logic [3:0] is_greater_vec;

  always_comb
  begin
    cmp_signed = 4'b0;

    unique case (operator_i)
      ALU_GTS,
      ALU_GES,
      ALU_LTS,
      ALU_LES,
      ALU_SLTS,
      ALU_SLETS,
      ALU_MIN,
      ALU_MAX,
      ALU_ABS,
      ALU_CLIP,
      ALU_CLIPU: begin
        cmp_signed[3:0] = 4'b1000;
      end

      default:;
    endcase
  end

  // generate vector equal and greater than signals, cmp_signed decides if the
  // comparison is done signed or unsigned
  genvar i;
  generate
    for(i = 0; i < 4; i++)
    begin
      assign is_equal_vec[i]   = (operand_a_i[8*i+7:8*i] == operand_b_i[8*i+7:i*8]);
      assign is_greater_vec[i] = $signed({operand_a_i[8*i+7] & cmp_signed[i], operand_a_i[8*i+7:8*i]})
                                  >
                                 $signed({operand_b_i[8*i+7] & cmp_signed[i], operand_b_i[8*i+7:i*8]});
    end
  endgenerate

  // generate the real equal and greater than signals that take the vector
  // mode into account
  always_comb
  begin
    // 32-bit mode
    is_equal[3:0]   = {4{is_equal_vec[3] & is_equal_vec[2] & is_equal_vec[1] & is_equal_vec[0]}};
    is_greater[3:0] = {4{is_greater_vec[3] | (is_equal_vec[3] & (is_greater_vec[2]
                                            | (is_equal_vec[2] & (is_greater_vec[1]
                                             | (is_equal_vec[1] & (is_greater_vec[0]))))))}};

  end

  // generate comparison result
  logic [3:0] cmp_result;

  always_comb
  begin
    cmp_result = is_equal;

    unique case (operator_i)
      ALU_EQ:            cmp_result = is_equal;
      ALU_NE:            cmp_result = ~is_equal;
      ALU_GTS, ALU_GTU:  cmp_result = is_greater;
      ALU_GES, ALU_GEU:  cmp_result = is_greater | is_equal;
      ALU_LTS, ALU_SLTS,
      ALU_LTU, ALU_SLTU: cmp_result = ~(is_greater | is_equal);
      ALU_SLETS,
      ALU_SLETU,
      ALU_LES, ALU_LEU:  cmp_result = ~is_greater;

      default: ;
    endcase
  end

  assign comparison_result_o = cmp_result[3];


  // min/max/abs handling
  logic [31:0] result_minmax;
  logic [ 3:0] sel_minmax;
  logic        do_min;
  logic [31:0] minmax_b;

  assign minmax_b = (operator_i == ALU_ABS) ? adder_result : operand_b_i;

  assign do_min   = (operator_i == ALU_MIN)  || (operator_i == ALU_MINU) ||
                    (operator_i == ALU_CLIP) || (operator_i == ALU_CLIPU);

  assign sel_minmax[3:0]      = is_greater ^ {4{do_min}};

  assign result_minmax[31:24] = (sel_minmax[3] == 1'b1) ? operand_a_i[31:24] : minmax_b[31:24];
  assign result_minmax[23:16] = (sel_minmax[2] == 1'b1) ? operand_a_i[23:16] : minmax_b[23:16];
  assign result_minmax[15: 8] = (sel_minmax[1] == 1'b1) ? operand_a_i[15: 8] : minmax_b[15: 8];
  assign result_minmax[ 7: 0] = (sel_minmax[0] == 1'b1) ? operand_a_i[ 7: 0] : minmax_b[ 7: 0];


  // clip
  logic [31:0] clip_result;        // result of clip and clip
  logic        clip_is_lower_neg;  // only signed comparison; used for clip
  logic        clip_is_lower_u;    // only signed comparison; used for clipu, checks for negative number

  assign clip_is_lower_neg = adder_result[31];
  assign clip_is_lower_u   = (operator_i == ALU_CLIPU) && operand_a_i[31];

  assign clip_result       = is_greater ? result_minmax: (clip_is_lower_u ? '0 : (clip_is_lower_neg ? operand_b_neg : result_minmax));








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
      // Standard Operations
      ALU_AND:  result_o = operand_a_i & operand_b_i;
      ALU_OR:   result_o = operand_a_i | operand_b_i;
      ALU_XOR:  result_o = operand_a_i ^ operand_b_i;

      // Shift Operations
      ALU_ADD, ALU_ADDR, ALU_ADDU, ALU_ADDUR,
      ALU_SUB, ALU_SUBR, ALU_SUBU, ALU_SUBUR,
      ALU_SLL,
      ALU_SRL, ALU_SRA,
      ALU_ROR:  result_o = shift_result;



      // Comparison Operations
      ALU_EQ,    ALU_NE,
      ALU_GTU,   ALU_GEU,
      ALU_LTU,   ALU_LEU,
      ALU_GTS,   ALU_GES,
      ALU_LTS,   ALU_LES: begin
          result_o[31:24] = {8{cmp_result[3]}};
          result_o[23:16] = {8{cmp_result[2]}};
          result_o[15: 8] = {8{cmp_result[1]}};
          result_o[ 7: 0] = {8{cmp_result[0]}};
       end
      ALU_SLTS,  ALU_SLTU,
      ALU_SLETS, ALU_SLETU: result_o = {31'b0, comparison_result_o};



      default: ; // default case to suppress unique warning
    endcase
  end

  assign ready_o = 1'b1;

endmodule

module alu_ff
#(
  parameter LEN = 32
)
(
  input  logic [LEN-1:0]         in_i,

  output logic [$clog2(LEN)-1:0] first_one_o,
  output logic                   no_ones_o
);

  localparam NUM_LEVELS = $clog2(LEN);

  logic [LEN-1:0] [NUM_LEVELS-1:0]           index_lut;
  logic [2**NUM_LEVELS-1:0]                  sel_nodes;
  logic [2**NUM_LEVELS-1:0] [NUM_LEVELS-1:0] index_nodes;


  //////////////////////////////////////////////////////////////////////////////
  // generate tree structure
  //////////////////////////////////////////////////////////////////////////////

  generate
    genvar j;
    for (j = 0; j < LEN; j++) begin
      assign index_lut[j] = $unsigned(j);
    end
  endgenerate

  generate
    genvar k;
    genvar l;
    genvar level;
    for (level = 0; level < NUM_LEVELS; level++) begin
    //------------------------------------------------------------
    if (level < NUM_LEVELS-1) begin
      for (l = 0; l < 2**level; l++) begin
        assign sel_nodes[2**level-1+l]   = sel_nodes[2**(level+1)-1+l*2] | sel_nodes[2**(level+1)-1+l*2+1];
        assign index_nodes[2**level-1+l] = (sel_nodes[2**(level+1)-1+l*2] == 1'b1) ?
                                           index_nodes[2**(level+1)-1+l*2] : index_nodes[2**(level+1)-1+l*2+1];
      end
    end
    //------------------------------------------------------------
    if (level == NUM_LEVELS-1) begin
      for (k = 0; k < 2**level; k++) begin
        // if two successive indices are still in the vector...
        if (k * 2 < LEN) begin
          assign sel_nodes[2**level-1+k]   = in_i[k*2] | in_i[k*2+1];
          assign index_nodes[2**level-1+k] = (in_i[k*2] == 1'b1) ? index_lut[k*2] : index_lut[k*2+1];
        end
        // if only the first index is still in the vector...
        if (k * 2 == LEN) begin
          assign sel_nodes[2**level-1+k]   = in_i[k*2];
          assign index_nodes[2**level-1+k] = index_lut[k*2];
        end
        // if index is out of range
        if (k * 2 > LEN) begin
          assign sel_nodes[2**level-1+k]   = 1'b0;
          assign index_nodes[2**level-1+k] = '0;
        end
      end
    end
    //------------------------------------------------------------
    end
  endgenerate

  //////////////////////////////////////////////////////////////////////////////
  // connect output
  //////////////////////////////////////////////////////////////////////////////

  assign first_one_o = index_nodes[0];
  assign no_ones_o   = ~sel_nodes[0];

endmodule

// count the number of '1's in a word
module alu_popcnt
(
  input  logic [31:0]  in_i,
  output logic [5: 0]  result_o
);

  logic [15:0][1:0] cnt_l1;
  logic [ 7:0][2:0] cnt_l2;
  logic [ 3:0][3:0] cnt_l3;
  logic [ 1:0][4:0] cnt_l4;

  genvar      l, m, n, p;
  generate for(l = 0; l < 16; l++)
    begin
      assign cnt_l1[l] = {1'b0, in_i[2*l]} + {1'b0, in_i[2*l + 1]};
    end
  endgenerate

  generate for(m = 0; m < 8; m++)
    begin
      assign cnt_l2[m] = {1'b0, cnt_l1[2*m]} + {1'b0, cnt_l1[2*m + 1]};
    end
  endgenerate

  generate for(n = 0; n < 4; n++)
    begin
      assign cnt_l3[n] = {1'b0, cnt_l2[2*n]} + {1'b0, cnt_l2[2*n + 1]};
    end
  endgenerate

  generate for(p = 0; p < 2; p++)
    begin
      assign cnt_l4[p] = {1'b0, cnt_l3[2*p]} + {1'b0, cnt_l3[2*p + 1]};
    end
  endgenerate

  assign result_o = {1'b0, cnt_l4[0]} + {1'b0, cnt_l4[1]};

endmodule
