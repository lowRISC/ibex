// Copyright 2016 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the “License”); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// this module produces both the absolute (positive) value and the negative
// value for any input. Both signed and unsigned numbers are supported
module riscv_alu_abs_neg
(
  input  logic [31:0]  in_i,      // can be either signed or unsigned
  input  logic         signed_i,

  output logic [32:0]  abs_o,     // needs to be 33 bits wide to allow for -(-2**31)
  output logic [32:0]  neg_o      // needs to be 33 bits wide to allow for -(2**32-1)
);

  logic [32:0] in_neg;

  assign in_neg = -{(signed_i & in_i[31]), in_i};

  assign abs_o = (signed_i & in_i[31]) ? in_neg : {1'b0, in_i};
  assign neg_o = (signed_i & in_i[31]) ? {1'b1, in_i} : in_neg;

endmodule


module riscv_alu_div
(
  input  logic         clk,
  input  logic         rst_n,

  input  logic [31:0]  a_i,          // can be either signed or unsigned
  input  logic [31:0]  b_i,          // can be either signed or unsigned
  input  logic         signed_i,
  input  logic         rem_quot_i,   // 1 for rem, 0 for div

  output logic [31:0]  result_o,

  // handshake
  input  logic         div_valid_i,      // valid data available for division
  output logic         div_ready_o,      // set when done or idle

  input  logic         ex_ready_i        // if we have to wait for next stage
);

  enum  logic [1:0] { IDLE, DIV, DIV_DONE } CS, NS;

  logic [31:0] quotient_q, quotient_n;
  logic [63:0] remainder_q, remainder_n, remainder_int;

  logic [31:0] remainder_out;
  logic [31:0] quotient_out;
  logic [31:0] result_int;

  logic [32:0] a_abs;
  logic [32:0] a_neg;

  logic [32:0] b_abs;
  logic [32:0] b_neg;

  logic [32:0] sub_val;

  logic        a_is_neg;
  logic        b_is_neg;
  logic        result_negate;
  logic        quot_negate;
  logic        rem_negate;
  logic        geq_b;
  logic        load_r;
  logic        is_active;
  logic [4:0]  counter_q, counter_n;

  riscv_alu_abs_neg b_abs_neg_i
  (
    .in_i     ( b_i      ),
    .signed_i ( signed_i ),

    .abs_o    ( b_abs    ),
    .neg_o    ( b_neg    )
  );

  riscv_alu_abs_neg a_abs_neg_i
  (
    .in_i     ( a_i      ),
    .signed_i ( signed_i ),

    .abs_o    ( a_abs    ),
    .neg_o    ( a_neg    )
  );

  always_comb
  begin
    NS          = CS;
    div_ready_o = 1'b1;
    load_r      = 1'b0;
    is_active   = 1'b0;
    counter_n   = counter_q - 1;

    case (CS)
      IDLE: begin
        div_ready_o = 1'b1;

        if (div_valid_i) begin
          div_ready_o = 1'b0;
          NS          = DIV;
          load_r      = 1'b1;
          is_active   = 1'b1;
          counter_n   = 31;
        end
      end

      DIV: begin
        div_ready_o = 1'b0;
        is_active   = 1'b1;

        if (counter_q == 0) begin
          div_ready_o = 1'b1;

          if (ex_ready_i)
            NS = IDLE;
          else
            NS = DIV_DONE;
        end
      end

      // if the next stage was stalled when we finished
      DIV_DONE: begin
        div_ready_o = 1'b1;

        if (ex_ready_i)
          NS = IDLE;
      end
    endcase
  end

  assign a_is_neg = a_i[31];
  assign b_is_neg = b_i[31];

  assign quot_negate = ((a_is_neg ^ b_is_neg) && signed_i && (b_i != 0));
  assign rem_negate  =   a_is_neg             && signed_i;

  assign geq_b = (remainder_q[63:31] >= b_abs);

  always_comb
  begin
    quotient_n = {quotient_q[30:0], 1'b0};
    sub_val = '0;

    if (geq_b) begin
      sub_val     = b_neg;
      quotient_n = {quotient_q[30:0], 1'b1};
    end
  end

  always_comb
  begin
    // add (or actually subtract) and shift left by one
    remainder_int[63:32] =  remainder_q[63:31] + sub_val;
    remainder_int[31: 0] = {remainder_q[30:0], 1'b0};
  end

  assign remainder_n = load_r ? {31'b0, a_abs} : remainder_int;


  //----------------------------------------------------------------------------
  // registers
  //----------------------------------------------------------------------------

  always_ff @(posedge clk, negedge rst_n)
  begin
    if (~rst_n) begin
      quotient_q  <= '0;
      remainder_q <= '0;
      counter_q   <= 0;
      CS          <= IDLE;
    end else begin
      // only toggle when there is an active request
      if (is_active) begin
        quotient_q  <= quotient_n;
        remainder_q <= remainder_n;
        counter_q   <= counter_n;
      end
      CS <= NS;
    end
  end


  //----------------------------------------------------------------------------
  // output assignments
  //----------------------------------------------------------------------------

  assign quotient_out  = (CS == DIV) ? quotient_n  : quotient_q;
  assign remainder_out = (CS == DIV) ? remainder_n[63:32] : remainder_q[63:32];
  assign result_int    = rem_quot_i ? remainder_out : quotient_out;
  assign result_negate = rem_quot_i ? rem_negate    : quot_negate;


  assign result_o = result_negate ? -result_int : result_int;

endmodule
