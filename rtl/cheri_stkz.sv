// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0


module cheri_stkz import cheri_pkg::*; #(
  parameter int unsigned DataWidth  = 33     // legal values: 32, 33, 65
) (
   // Clock and Reset
  input  logic          clk_i,
  input  logic          rst_ni,

  // CSR register interface
  input  logic          ztop_wr_i,
  input  logic [31:0]   ztop_wdata_i,
  input  full_cap_t     ztop_wfcap_i,
  output logic [31:0]   ztop_rdata_o,
  output reg_cap_t      ztop_rcap_o,
 
  input  logic          unmasked_intr_i,

  output logic          stkz_active_o,
  output logic          stkz_abort_o,
  output logic [31:0]   stkz_ptr_o,
  output logic [31:0]   stkz_base_o,
  output logic          stkz_err_o,

  // LSU req/resp interface (to be multiplixed/qualified)
  input  logic          lsu_stkz_resp_valid_i,
  input  logic          lsu_stkz_resp_err_i,
  input  logic          lsu_stkz_req_done_i,   
  output logic          stkz_lsu_req_o,
  output logic          stkz_lsu_we_o,
  output logic          stkz_lsu_is_cap_o,
  output logic [31:0]   stkz_lsu_addr_o,
  output logic [DataWidth-1:0] stkz_lsu_raw_wdata_o
);

  localparam bit Mem65Bit = (DataWidth == 65);

  typedef enum logic [1:0] {STKZ_IDLE, STKZ_ACTIVE, STKZ_ABORT} stkz_fsm_t;

  stkz_fsm_t  stkz_fsm_d, stkz_fsm_q;

  logic  [29:0] stkz_ptrw, stkz_ptrw_nxt;
  logic  [29:0] stkz_basew;
  logic         stkz_start, stkz_done, stkz_stop, stkz_active;
  reg_cap_t     ztop_rcap, ztop_rcap_nxt;
  logic  [32:0] ztop_wtop33;
  logic  [31:0] ztop_wbase32;
  logic         waddr_eq_base;
  logic         cmd_cap_good;
  reg_cap_t     cmd_wcap; 
  logic         cmd_new_cap, cmd_new_null;
  logic         cmd_is_n2z;

  assign stkz_lsu_raw_wdata_o  = {DataWidth{1'b0}};
  assign stkz_lsu_is_cap_o     = Mem65Bit; 
  assign stkz_lsu_we_o     = 1'b1;
  assign stkz_lsu_req_o    = stkz_active;
  assign stkz_lsu_addr_o   = {stkz_ptrw_nxt, 2'h0};

  assign stkz_active_o     = stkz_active;      
  assign stkz_active       = (stkz_fsm_q != STKZ_IDLE);
  assign stkz_abort_o      = (stkz_fsm_q == STKZ_ABORT);

  assign stkz_ptr_o        = {stkz_ptrw, 2'h0};
  assign stkz_base_o       = {stkz_basew, 2'h0};

  assign ztop_rdata_o = {stkz_ptrw, 2'h0};
  assign ztop_rcap_o  = ztop_rcap;

  assign ztop_wbase32 = ztop_wfcap_i.base32;
  assign ztop_wtop33  = ztop_wfcap_i.top33;

  assign cmd_cap_good  = ztop_wfcap_i.valid && (ztop_wtop33[32:2] >= ztop_wdata_i[31:2]) &&
                         ztop_wfcap_i.perms[PERM_SD];
  assign cmd_is_n2z    = cmd_cap_good && (ztop_wdata_i[31:2] == ztop_wbase32[31:2]);

  assign cmd_new_null  = ztop_wr_i && (ztop_wfcap_i == NULL_FULL_CAP) && (ztop_wdata_i == 32'h0);
  assign cmd_new_cap   = ztop_wr_i && ~cmd_new_null;

  assign stkz_start    = cmd_new_cap && cmd_cap_good && (ztop_wdata_i[31:2] > ztop_wbase32[31:2]);
  assign stkz_done     = (stkz_ptrw_nxt <= stkz_basew);
  assign stkz_stop     = unmasked_intr_i | cmd_new_null;


  always_comb begin
    logic [2:0] tmp3;
    logic [8:0] addrmi9;
 
    if ((stkz_fsm_q == STKZ_IDLE) && stkz_start)
      stkz_fsm_d = STKZ_ACTIVE;
    else if ((stkz_fsm_q == STKZ_ACTIVE) & stkz_done & lsu_stkz_req_done_i)  // "normal" completion
      stkz_fsm_d = STKZ_IDLE;
    else if ((stkz_fsm_q == STKZ_ACTIVE) & stkz_stop & lsu_stkz_req_done_i)  // abort 
      stkz_fsm_d = STKZ_IDLE;
    else if ((stkz_fsm_q == STKZ_ACTIVE) & stkz_stop)  // pending abort, wait till lsu_req_done
      stkz_fsm_d = STKZ_ABORT;
    else if ((stkz_fsm_q == STKZ_ABORT) & lsu_stkz_req_done_i)
      stkz_fsm_d = STKZ_IDLE;    // self clear by any furtherload/store activity
    else
      stkz_fsm_d = stkz_fsm_q;

    // clear tag if writing an ztop value with address == base
    cmd_wcap = full2regcap(ztop_wfcap_i);
    if (cmd_is_n2z) cmd_wcap.valid = 1'b0;

    // we are doing this in lieu of a full set_address.
    //   note we only start an zeroization if addr > base32 so no need for representability check
    ztop_rcap_nxt = ztop_rcap;
    addrmi9 = {stkz_ptrw_nxt, 2'b00} >> ztop_rcap.exp;
    tmp3    = update_temp_fields(ztop_rcap.top, ztop_rcap.base, addrmi9);
    ztop_rcap_nxt.top_cor  = tmp3[2:1];
    ztop_rcap_nxt.base_cor = tmp3[0];
    ztop_rcap_nxt.valid    = ztop_rcap.valid & ~stkz_done;
  end
  
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      stkz_fsm_q    <= STKZ_IDLE;
      stkz_ptrw     <= 30'h0;
      stkz_ptrw_nxt <= 30'h0;
      stkz_basew    <= 30'h0;
      stkz_err_o    <= 1'b0;
      ztop_rcap     <= NULL_REG_CAP;
    end else begin

      stkz_fsm_q <= stkz_fsm_d;

      // zcap is an WARL SCR
      //   - if active
      //     - Readback return current progress 
      //     - allow writing NULL to stop (readback NULL in this case)
      //       
      //   - if not active, i
      //     - only allow writing tagged cap (legalized), which starts zeroization, however
      //     - speical case: write a tagged cap with addr == base will NOT start zeroization but 
      //       will clear tag on read
      //
      if (ztop_wr_i) begin
        stkz_ptrw <= Mem65Bit ? {ztop_wdata_i[31:3], 1'b0} :ztop_wdata_i[31:2];
        ztop_rcap <= cmd_wcap;
      end else if (stkz_active && lsu_stkz_req_done_i) begin
        stkz_ptrw <= stkz_ptrw_nxt; 
        ztop_rcap <= ztop_rcap_nxt;
      end

      // this is the captured hardware zeroization context, only updated for valid zerioation runs
      if (stkz_start) begin
        stkz_ptrw_nxt <= ztop_wdata_i[31:2] - (Mem65Bit ? 2 : 1);
        stkz_basew    <= ztop_wbase32[31:2];
      end else if (stkz_active && lsu_stkz_req_done_i && ~(stkz_done | stkz_stop)) begin
        stkz_ptrw_nxt <= stkz_ptrw_nxt - (Mem65Bit ? 2 : 1);
      end
       
      if (~stkz_active && stkz_start)
        stkz_err_o <= 1'b0;
      else if (lsu_stkz_resp_valid_i && lsu_stkz_resp_err_i)
        stkz_err_o <= 1'b1;

    end
  end

endmodule
