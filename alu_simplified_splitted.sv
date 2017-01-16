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
// Engineer:       Markus Wegmann - markus.wegmann@technokrat.ch              //
//                                                                            //
// Design Name:    ALU                                                        //
// Project Name:   littleRISCV                                                //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Arithmetic logic unit of the pipelined processor.          //
//                 Reduced in area and ISA (RV32I) for small area             //
//                 and power consumption. Based on ALU by Matthias Baer.      //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

`include "riscv_config.sv"

import riscv_defines::*;

module riscv_alu_simplified_splitted
(
  input  logic                     clk,
  input  logic                     rst_n,

  input  logic [ALU_OP_WIDTH-1:0]  operator_i,
  input  logic [31:0]              operand_a_i,
  input  logic [31:0]              operand_b_i,
  input  logic                     req_i,

  output logic [31:0]              adder_result_o,

  output logic                     ready_o,
  output logic [31:0]              result_o,
  output logic                     comparison_result_o
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

  assign operand_b_neg = (~operand_b_i) + 32'h0001;


  /////////////////////////////////////
  //      _       _     _            //
  //     / \   __| | __| | ___ _ __  //
  //    / _ \ / _` |/ _` |/ _ \ '__| //
  //   / ___ \ (_| | (_| |  __/ |    //
  //  /_/   \_\__,_|\__,_|\___|_|    //
  //                                 //
  /////////////////////////////////////

  logic        adder_op_b_negate; 
  logic [16:0] adder_in_a, adder_in_b;
  logic [16:0] adder_partial_result_Q, adder_partial_result_n;
  logic [31:0] adder_result;

  always_comb
  begin
    adder_op_b_negate = 1'b0;

    unique case (operator_i)
      // Adder OPs
      ALU_SUB,

      // Comparator OPs
      ALU_EQ,    ALU_NE,
      ALU_GTU,   ALU_GEU,
      ALU_LTU,   ALU_LEU,
      ALU_GTS,   ALU_GES,
      ALU_LTS,   ALU_LES,
      ALU_SLTS,  ALU_SLTU,
      ALU_SLETS, ALU_SLETU: adder_op_b_negate = 1'b1;

      default: ;
    endcase
  end
  
  always_comb
  begin
    if (req_i)
    begin
      // prepare operand a
      adder_in_a = {1'b0, operand_a_i[15:0]};
      // prepare operand b
      adder_in_b = adder_op_b_negate ? {1'b0, operand_b_neg[15:0]} : {1'b0, operand_b_i[15:0]};
    end else begin
      // prepare operand a
      adder_in_a = {1'b1, operand_a_i[31:16]};
      // prepare operand b
      adder_in_b = adder_op_b_negate ? {1'b0, operand_b_neg[31:16]} : {1'b0, operand_b_i[31:16]};
    end
  end

  // actual adder
  assign adder_partial_result_n = adder_in_a + adder_in_b + ( req_i ? 17'b0 : {16'b0, adder_partial_result_Q[16]});

  assign adder_result = {adder_partial_result_n[15:0], adder_partial_result_Q[15:0]};
  
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
  logic        shift_arithmetic;

  logic [31:0] shift_amt;          // amount of shift, to the right
  logic [31:0] shift_op_a;         // input of the shifter
  logic [31:0] shift_result;
  logic [31:0] shift_right_result;
  logic [31:0] shift_left_result;


  assign shift_amt = operand_b_i;


  assign shift_left = (operator_i == ALU_SLL);

  assign shift_arithmetic = (operator_i == ALU_SRA);

  // choose the bit reversed or the normal input for shift operand a
  assign shift_op_a    = shift_left ? operand_a_rev : operand_a_i;

  // right shifts, we let the synthesizer optimize this
  logic [32:0] shift_op_a_32;

  assign shift_op_a_32 = { shift_arithmetic & shift_op_a[31], shift_op_a};

  always_comb
  begin
    shift_right_result = $signed(shift_op_a_32) >>> shift_amt[4:0];
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
  logic is_greater_equal;  // handles both signed and unsigned forms
  logic cmp_signed;

  always_comb
  begin
    cmp_signed = 1'b0;

    unique case (operator_i)
      ALU_GTS,
      ALU_GES,
      ALU_LTS,
      ALU_LES,
      ALU_SLTS,
      ALU_SLETS: begin
        cmp_signed = 1'b1;
      end

      default:;
    endcase
  end

  assign is_equal = (adder_result == 32'b0);
  

  // Is greater equal
  always_comb
  begin
    if ((operand_a_i[31] ^ operand_b_i[31]) == 0)
      is_greater_equal = (adder_result[31] == 0);
    else
      is_greater_equal = operand_a_i[31] ^ (~cmp_signed);
  end

  // GTE unsigned: 
  // (a[31] == 1 && b[31] == 1) => adder_result[31] == 0
  // (a[31] == 0 && b[31] == 0) => adder_result[31] == 0
  // (a[31] == 1 && b[31] == 0) => 1
  // (a[31] == 0 && b[31] == 1) => 0

  // GTE signed:
  // (a[31] == 1 && b[31] == 1) => adder_result[31] == 0
  // (a[31] == 0 && b[31] == 0) => adder_result[31] == 0
  // (a[31] == 1 && b[31] == 0) => 0
  // (a[31] == 0 && b[31] == 1) => 1



  // generate comparison result
  logic cmp_result;

  always_comb
  begin
    cmp_result = is_equal;

    unique case (operator_i)
      ALU_EQ:            cmp_result = is_equal;
      ALU_NE:            cmp_result = (~is_equal);
      ALU_GTS, ALU_GTU:  cmp_result = is_greater_equal && (~is_equal);
      ALU_GES, ALU_GEU:  cmp_result = is_greater_equal;
      ALU_LTS, ALU_SLTS,
      ALU_LTU, ALU_SLTU: cmp_result = (~is_greater_equal);
      ALU_SLETS,
      ALU_SLETU,
      ALU_LES, ALU_LEU:  cmp_result = (~is_greater_equal) || is_equal;

      default: ;
    endcase
  end

  assign comparison_result_o = cmp_result;



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

      // Adder Operations
      ALU_ADD, ALU_ADDR, ALU_ADDU, ALU_ADDUR,
      ALU_SUB: result_o = adder_result;

      // Shift Operations
      ALU_SLL,
      ALU_SRL, ALU_SRA: result_o = shift_result;

      // Comparison Operations
      ALU_EQ,    ALU_NE,
      ALU_GTU,   ALU_GEU,
      ALU_LTU,   ALU_LEU,
      ALU_GTS,   ALU_GES,
      ALU_LTS,   ALU_LES,
      ALU_SLTS,  ALU_SLTU,
      ALU_SLETS, ALU_SLETU: result_o = cmp_result;

      default: ; // default case to suppress unique warning
    endcase
  end


  assign ready_o = ~(req_i); // If there is a new request we execute first step


  always_ff @(posedge clk or negedge rst_n) begin
    if(~rst_n) begin
      adder_partial_result_Q <= 0;
    end else begin
      if (req_i)
        adder_partial_result_Q <= adder_partial_result_n;
    end
  end

  
endmodule
