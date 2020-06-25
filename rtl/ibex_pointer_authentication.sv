// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module ibex_pointer_authentication #(
  // This parameter is used in PAC instruction to rewrite MSBs of pointer to an invalid value
  parameter logic [3:0] MSBsInvalidPointer = 4'b1010
) (
    input  logic         clk_i,
    input  logic         rst_ni,

    input  logic [127:0] csr_pa_key_i,

    input  logic         pac_en_i,
    input  logic         aut_en_i,
    input  logic [31:0]  pa_data0_i,
    input  logic [31:0]  pa_data1_i,

    input  logic         pa_ready_id_i,

    output logic [31:0]  pa_result_o,
    output logic         pa_valid_o
);

  logic [3:0]  msbs_pointer_q, msbs_pointer_d;

  // We could theoretically avoid to buffer the pac
  // by changing the decoder to provide the following outputs:
  //   Cycle 1: ptr MSBs (just store ptr MSBs, ignore the pac coming from same register)
  //   Cycle 2: ptr LSBs + context (now we can start the cipher)
  //   Cycle 3 onwards: pac
  // But this is not currently done as it requires a lot of changes.
  logic [27:0] pac_q, pac_d;

  logic [63:0] cipher_in_data;
  logic        cipher_in_ready;
  logic        cipher_in_valid;
  logic [63:0] cipher_out_data;
  logic        cipher_out_ready;
  logic        cipher_out_valid;

  logic [35:0] unused_cipher_out_data;

  // Avoid lint warning
  assign unused_cipher_out_data = cipher_out_data[63:28];

  // Gift cipher module
  gift gift_i (
    .clk_i        ( clk_i            ),
    .rst_ni       ( rst_ni           ),
    .out_ready_i  ( cipher_out_ready ),
    .in_valid_i   ( cipher_in_valid  ),
    .data_i       ( cipher_in_data   ),
    .key_i        ( csr_pa_key_i     ),
    .in_ready_o   ( cipher_in_ready  ),
    .out_valid_o  ( cipher_out_valid ),
    .data_o       ( cipher_out_data  )
  );

  typedef enum logic [1:0] {
    PA_IDLE, PA_START_AUT, PA_WAIT
  } pa_fsm_e;
  pa_fsm_e pa_fsm_q, pa_fsm_d;

  typedef enum logic [1:0] {
    PAC_START, PAC_DONE, AUT_SUCCESS, AUT_FAILURE
  } pa_result_sel_e;
  pa_result_sel_e pa_result_sel;

  typedef enum logic [1:0] {
    CIPHER_IDLE, CIPHER_PAC_START, CIPHER_AUT_START
  } cipher_in_data_sel_e;
  cipher_in_data_sel_e cipher_in_data_sel;

  always_comb begin : pa_result_mux
    unique case (pa_result_sel)
      //                     MSBs of invalid pointer, LSBs of pointer
      PAC_START:   pa_result_o = {MSBsInvalidPointer, pa_data0_i[27:0]};
      //                         MSBs of pointer,     Pointer Authentication Code
      PAC_DONE:    pa_result_o = {msbs_pointer_q,     cipher_out_data[27:0]};
      //                         MSBs of pointer,     LSB of pointer
      AUT_SUCCESS: pa_result_o = {msbs_pointer_q,     pa_data0_i[27:0]};
      // We should make sure that the invalid bits get filled in the pointer
      // no matter the content of msbs_pointer_q
      //                     MSBs of invalid pointer, LSBs of pointer
      AUT_FAILURE: pa_result_o = {MSBsInvalidPointer, pa_data0_i[27:0]};
      // We usually take the first value from above,
      // but AUT_FAILURE seems to be more sensible in this scenario
      default:     pa_result_o = {MSBsInvalidPointer, pa_data0_i[27:0]};
    endcase
  end

  always_comb begin : cipher_in_data_mux
    unique case (cipher_in_data_sel)
      CIPHER_IDLE:      cipher_in_data = '0;
      //                                  context,   MSBs of pointer, LSBs of pointer
      CIPHER_PAC_START: cipher_in_data = {pa_data1_i, msbs_pointer_d, pa_data0_i[27:0]};
      CIPHER_AUT_START: cipher_in_data = {pa_data1_i, msbs_pointer_q, pa_data0_i[27:0]};
      default:          cipher_in_data = '0;
    endcase
  end

  // FSM
  always_comb begin
    pa_result_sel      = AUT_FAILURE;
    pa_valid_o         = '0;

    msbs_pointer_d     = msbs_pointer_q;
    pac_d              = pac_q;

    cipher_in_data_sel = CIPHER_IDLE;
    cipher_in_valid    = '0;
    cipher_out_ready   = '0;

    pa_fsm_d           = pa_fsm_q;

    unique case (pa_fsm_q)

      PA_IDLE: begin
        unique case (1'b1)
          pac_en_i: begin
            pa_result_sel      = PAC_START;
            msbs_pointer_d     = pa_data0_i[31:28];
            cipher_in_data_sel = CIPHER_PAC_START;
            cipher_in_valid    = 1'b1;
            if (cipher_in_ready) begin
              pa_fsm_d         = PA_WAIT;
            end
          end
          aut_en_i: begin
            msbs_pointer_d = pa_data1_i[31:28];
            pac_d          = pa_data1_i[27:0];
            pa_fsm_d       = PA_START_AUT;
          end
          default: begin
            pa_fsm_d = PA_IDLE;
          end
        endcase
      end

      PA_START_AUT: begin
        cipher_in_data_sel = CIPHER_AUT_START;
        cipher_in_valid    = 1'b1;
        if (cipher_in_ready) begin
          pa_fsm_d         = PA_WAIT;
        end
      end

      PA_WAIT: begin
        unique case (1'b1)
          pac_en_i: begin
            if (pa_ready_id_i) begin
              cipher_out_ready = 1'b1;
              if (cipher_out_valid) begin
                pa_result_sel    = PAC_DONE;
                pa_valid_o       = 1'b1;
                pa_fsm_d         = PA_IDLE;
              end
            end
          end
          aut_en_i: begin
            if (pa_ready_id_i) begin
              cipher_out_ready = 1'b1;
              if (cipher_out_valid) begin
                if (pac_q == cipher_out_data[27:0]) begin // Authentication success
                  pa_result_sel  = AUT_SUCCESS;
                end else begin // Authentication failure
                  pa_result_sel  = AUT_FAILURE;
                end
                pa_valid_o       = 1'b1;
                pa_fsm_d         = PA_IDLE;
              end
            end
          end
          default: begin
            pa_fsm_d = PA_IDLE;
          end
        endcase
      end

      default: begin
        pa_fsm_d = PA_IDLE;
      end
    endcase
  end

  // registers for FSM
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if(~rst_ni) begin
      pa_fsm_q       <= PA_IDLE;
      msbs_pointer_q <= '0;
      pac_q          <= '0;
    end else begin
      pa_fsm_q       <= pa_fsm_d;
      msbs_pointer_q <= msbs_pointer_d;
      pac_q          <= pac_d;
    end
  end

endmodule
