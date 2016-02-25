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

`include "riscv_defines.sv"

module riscv_alu
(
  input  logic [`ALU_OP_WIDTH-1:0] operator_i,
  input  logic [31:0]              operand_a_i,
  input  logic [31:0]              operand_b_i,
  input  logic [31:0]              operand_c_i,
  input  logic [ 4:0]              imm_bmask_a_i,
  input  logic [ 4:0]              imm_bmask_b_i,

  output logic [31:0]              result_o,
  output logic                     comparison_result_o
);


  logic [31:0] operand_a_rev;

  // bit reverse operand_a for left shifts and bit counting
  genvar       k;
  generate
    for(k = 0; k < 32; k++)
    begin
      assign operand_a_rev[k] = operand_a_i[31-k];
    end
  endgenerate


  /////////////////////////////////////
  //      _       _     _            //
  //     / \   __| | __| | ___ _ __  //
  //    / _ \ / _` |/ _` |/ _ \ '__| //
  //   / ___ \ (_| | (_| |  __/ |    //
  //  /_/   \_\__,_|\__,_|\___|_|    //
  //                                 //
  /////////////////////////////////////

  logic        carry_in;
  logic [31:0] adder_op_a;
  logic [31:0] adder_op_b;
  logic [31:0] adder_result;

  // prepare operand a
  assign adder_op_a = (operator_i == `ALU_ABS) ? ~operand_a_i : operand_a_i;

  // prepare operand b
  assign adder_op_b = (operator_i == `ALU_SUB) ? ~operand_b_i : operand_b_i;

  // prepare carry
  always_comb
  begin
    case (operator_i)
      `ALU_SUB,
      `ALU_ABS: carry_in = 1'b1;
      default:  carry_in = 1'b0;
    endcase
  end

  // adder
  assign adder_result = adder_op_a + adder_op_b + {31'b0, carry_in};


  // averaging by right shifting of one bit
  logic [31:0] result_avg;

  assign result_avg[30:0] = adder_result[31:1];
  assign result_avg[31]   = (operator_i == `ALU_AVGU) ? 1'b0 : adder_result[31];


  ////////////////////////////////////////
  //  ____  _   _ ___ _____ _____       //
  // / ___|| | | |_ _|  ___|_   _|      //
  // \___ \| |_| || || |_    | |        //
  //  ___) |  _  || ||  _|   | |        //
  // |____/|_| |_|___|_|     |_|        //
  //                                    //
  ////////////////////////////////////////

  logic        shift_left;         // should we shift left
  logic [31:0] shift_amt;          // amount of shift
  logic [31:0] shift_op_a;         // input of the shifter
  logic [31:0] shift_result;
  logic [31:0] shift_right_result;
  logic [31:0] shift_left_result;


  assign shift_left = (operator_i == `ALU_SLL) || (operator_i == `ALU_BINS);

  // choose the bit reversed or the normal input for shift operand a
  assign shift_op_a = (shift_left == 1'b1) ? operand_a_rev : operand_a_i;

  // right shifts
  always_comb
  begin
    if(operator_i == `ALU_SRA)
      shift_right_result = $unsigned( $signed(shift_op_a) >>> shift_amt[4:0] );
    else if(operator_i == `ALU_ROR)
      shift_right_result = {shift_op_a, shift_op_a} >> shift_amt[4:0];
    else
      shift_right_result = shift_op_a               >> shift_amt[4:0];
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

  logic is_equal;
  logic is_greater;

  logic cmp_signed;

  always_comb
  begin
    cmp_signed = 1'b0;

    case (operator_i)
      `ALU_GTS,
      `ALU_GES,
      `ALU_LTS,
      `ALU_LES,
      `ALU_SLTS,
      `ALU_SLETS,
      `ALU_MIN,
      `ALU_MAX,
      `ALU_ABS: cmp_signed = 1'b1;
    endcase
  end

  assign is_equal   = (operand_a_i == operand_b_i);
  assign is_greater = $signed({operand_a_i[31] & cmp_signed, operand_a_i[31:0]})
                      >
                      $signed({operand_b_i[31] & cmp_signed, operand_b_i[31:0]});

  // generate comparison result
  always_comb
  begin
    comparison_result_o = is_equal;

    unique case (operator_i)
      `ALU_EQ:             comparison_result_o = is_equal;
      `ALU_NE:             comparison_result_o = ~is_equal;
      `ALU_GTS, `ALU_GTU:  comparison_result_o = is_greater;
      `ALU_GES, `ALU_GEU:  comparison_result_o = is_greater | is_equal;
      `ALU_LTS, `ALU_SLTS,
      `ALU_LTU, `ALU_SLTU: comparison_result_o = ~(is_greater | is_equal);
      `ALU_SLETS,
      `ALU_SLETU,
      `ALU_LES, `ALU_LEU:  comparison_result_o = ~is_greater;
      `ALU_EQALL:          comparison_result_o = (operand_a_i == 32'hFFFF_FFFF);

      default: ;
    endcase
  end


  logic [31:0] result_minmax;
  logic        sel_minmax;
  logic [31:0] minmax_b;

  assign minmax_b = (operator_i == `ALU_ABS) ? adder_result : operand_b_i;

  assign sel_minmax    = is_greater ^ ((operator_i == `ALU_MIN) || (operator_i == `ALU_MINU));
  assign result_minmax = sel_minmax ? operand_a_i[31:0] : minmax_b[31:0];


  //////////////////////////////////////////////////
  //  _____      _                 _              //
  // | ____|_  _| |_ ___ _ __  ___(_) ___  _ __   //
  // |  _| \ \/ / __/ _ \ '_ \/ __| |/ _ \| '_ \  //
  // | |___ >  <| ||  __/ | | \__ \ | (_) | | | | //
  // |_____/_/\_\\__\___|_| |_|___/_|\___/|_| |_| //
  //                                              //
  //////////////////////////////////////////////////

  logic [31:0] result_ext;

  always_comb
  begin
    // zero extend byte
    result_ext = {24'b0, operand_a_i[7:0]};

    // sign extend byte
    if (operator_i == `ALU_EXTBS)
      result_ext = {{24 {operand_a_i[7]}}, operand_a_i[7:0]};

    // zero extend half word
    if(operator_i == `ALU_EXTHZ)
      result_ext = {16'b0, operand_a_i[15:0]};

    // sign extend half word
    if(operator_i == `ALU_EXTHS)
      result_ext = {{16 {operand_a_i[15]}}, operand_a_i[15:0]};
  end


  /////////////////////////////////////////////////////////////////////
  //   ____  _ _      ____                  _      ___               //
  //  | __ )(_) |_   / ___|___  _   _ _ __ | |_   / _ \ _ __  ___    //
  //  |  _ \| | __| | |   / _ \| | | | '_ \| __| | | | | '_ \/ __|   //
  //  | |_) | | |_  | |__| (_) | |_| | | | | |_  | |_| | |_) \__ \_  //
  //  |____/|_|\__|  \____\___/ \__,_|_| |_|\__|  \___/| .__/|___(_) //
  //                                                   |_|           //
  /////////////////////////////////////////////////////////////////////

  logic [31:0] ff_input;   // either op_a_i or its bit reversed version
  logic [5:0]  clb_result; // count leading bits
  logic [5:0]  ff1_result; // holds the index of the first '1'
  logic [5:0]  fl1_result; // holds the index of the last '1'
  logic        ff_cmp;     // compare value for ff1 and fl1
  integer q;

  assign ff_input  = (operator_i == `ALU_FF1) ? operand_a_i : operand_a_rev;
  assign ff_cmp    = (operator_i == `ALU_CLB) ? ~operand_a_i[31] : 1'b1;

  always_comb
  begin
    ff1_result = 6'd0;

    for(q = 1; q < 33; q++)
    begin
      if(ff_input[q - 1] == ff_cmp)
      begin
        ff1_result = q;
        break;
      end
    end
  end

  // special case if ff1_res is 0 (no 1 found), then we keep the 0
  assign fl1_result = (ff1_result == 6'd0) ? 6'd0 : (6'd33 - ff1_result);
  assign clb_result = (ff1_result == 6'd0) ? 6'd0 : (ff1_result - 6'd2);

  // count the number of '1's in a word
  logic [5:0]  cnt_result;
  logic [1:0]  cnt_l1[16];
  logic [2:0]  cnt_l2[8];
  logic [3:0]  cnt_l3[4];
  logic [4:0]  cnt_l4[2];

  genvar      l, m, n, p;
  generate for(l = 0; l < 16; l++)
    begin
      assign cnt_l1[l] = operand_a_i[2*l] + operand_a_i[2*l + 1];
    end
  endgenerate

  generate for(m = 0; m < 8; m++)
    begin
      assign cnt_l2[m] = cnt_l1[2*m] + cnt_l1[2*m + 1];
    end
  endgenerate

  generate for(n = 0; n < 4; n++)
    begin
      assign cnt_l3[n] = cnt_l2[2*n] + cnt_l2[2*n + 1];
    end
  endgenerate

  generate for(p = 0; p < 2; p++)
    begin
      assign cnt_l4[p] = cnt_l3[2*p] + cnt_l3[2*p + 1];
    end
  endgenerate

  assign cnt_result = cnt_l4[0] + cnt_l4[1];


  ////////////////////////////////////////////////
  //  ____  _ _     __  __             _        //
  // | __ )(_) |_  |  \/  | __ _ _ __ (_)_ __   //
  // |  _ \| | __| | |\/| |/ _` | '_ \| | '_ \  //
  // | |_) | | |_  | |  | | (_| | | | | | |_) | //
  // |____/|_|\__| |_|  |_|\__,_|_| |_|_| .__/  //
  //                                    |_|     //
  ////////////////////////////////////////////////

  logic        extract_is_signed;
  logic        extract_sign;
  logic [31:0] bmask, bmask_first, bmask_inv;
  logic [31:0] bextins_and;
  logic [31:0] bextins_result, bclr_result, bset_result;


  // construct bit mask for insert/extract/bclr/bset
  // bmask looks like this 00..0011..1100..00
  assign bmask_first = {32'hFFFFFFFE} << imm_bmask_a_i;
  assign bmask       = (~bmask_first) << imm_bmask_b_i;
  assign bmask_inv   = ~bmask;

  assign bextins_and = (operator_i == `ALU_BINS) ? operand_c_i : {32{extract_sign}};

  assign extract_is_signed = (operator_i == `ALU_BEXT);
  assign extract_sign = extract_is_signed & shift_result[imm_bmask_a_i];

  assign bextins_result = (bmask & shift_result) | (bextins_and & bmask_inv);

  assign bclr_result = operand_a_i & bmask_inv;
  assign bset_result = operand_a_i | bmask;

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
    shift_amt  = operand_b_i;
    result_o   = 'x;

    unique case (operator_i)
      // Standard Operations
      `ALU_ADD,
      `ALU_SUB:  result_o = adder_result;
      `ALU_AVG,
      `ALU_AVGU: result_o = result_avg;
      `ALU_AND:  result_o = operand_a_i & operand_b_i;
      `ALU_OR:   result_o = operand_a_i | operand_b_i;
      `ALU_XOR:  result_o = operand_a_i ^ operand_b_i;

      // Shift Operations
      `ALU_SLL,
      `ALU_SRL,
      `ALU_SRA,
      `ALU_ROR:  result_o = shift_result;

      // bit manipulation instructions
      `ALU_BINS,
      `ALU_BEXT,
      `ALU_BEXTU: result_o = bextins_result;

      `ALU_BCLR:  result_o = bclr_result;
      `ALU_BSET:  result_o = bset_result;

      // Extension Operations
      `ALU_EXTBZ,
      `ALU_EXTBS,
      `ALU_EXTHZ,
      `ALU_EXTHS: result_o = result_ext;

      // Min/Max/Abs
      `ALU_MIN, `ALU_MINU,
      `ALU_MAX, `ALU_MAXU,
      `ALU_ABS: result_o = result_minmax;

      // Comparison Operations
      `ALU_EQ, `ALU_NE, `ALU_GTU, `ALU_GEU, `ALU_LTU, `ALU_LEU, `ALU_GTS, `ALU_GES, `ALU_LTS, `ALU_LES:
      begin
        // TODO: Check which comparison operations are actually used
        //       Probably it's just slts/stlu/slets/sletu plus what is needed
        //       for branching after the flag is removed
        result_o = {31'b0, comparison_result_o};
      end

      // Set Lower Than Operations (result = 1, if a < b)
      `ALU_SLTS, `ALU_SLTU: result_o = {31'b0, comparison_result_o};

      // Set Lower Equal Than Operations (result = 1, if a <= b)
      `ALU_SLETS, `ALU_SLETU: result_o = {31'b0, comparison_result_o};

      `ALU_FF1: result_o = {26'h0, ff1_result};
      `ALU_FL1: result_o = {26'h0, fl1_result};
      `ALU_CLB: result_o = {26'h0, clb_result};
      `ALU_CNT: result_o = {26'h0, cnt_result};

      default: ; // default case to suppress unique warning
    endcase
  end

endmodule

