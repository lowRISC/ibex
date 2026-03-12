
// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module cheri_regfile import cheri_pkg::*; #(
  parameter int unsigned NREGS      = 32,
  parameter int unsigned NCAPS      = 32,
  parameter bit          RegFileECC = 1'b0,
  parameter int unsigned DataWidth  = 32,
  parameter bit          CheriPPLBC = 1'b0,
  parameter bit          TRVKBypass = 1'b1
) (
   // Clock and Reset
  input  logic                  clk_i,
  input  logic                  rst_ni,
  input  logic                  par_rst_ni,

  //Read port R1
  input  logic           [4:0]  raddr_a_i,
  output logic [DataWidth-1:0]  rdata_a_o,
  output reg_cap_t              rcap_a_o,

  //Read port R2
  input  logic           [4:0]  raddr_b_i,
  output logic [DataWidth-1:0]  rdata_b_o,
  output reg_cap_t              rcap_b_o,

  // Write port W1
  input  logic          [4:0]   waddr_a_i,
  input  logic [DataWidth-1:0]  wdata_a_i,
  input  reg_cap_t              wcap_a_i,
  input  logic                  we_a_i,         // we always write both cap & data in parallel

  // Tag reservation and revocation port
  output logic          [31:0]  reg_rdy_o,
  input  logic          [4:0]   trvk_addr_i,
  input  logic                  trvk_en_i,
  input  logic                  trvk_clrtag_i,
  input  logic          [6:0]   trvk_par_i,     // make sure this is included in lockstep compare      
  input  logic          [4:0]   trsv_addr_i,
  input  logic                  trsv_en_i,
  input  logic          [6:0]   trsv_par_i,     
  
  output logic                  alert_o
);

  localparam logic [6:0] DefParBits[0:31] = '{7'h27,7'h0d,7'h6b,7'h41,7'h62,7'h48,7'h2e,7'h04,
                                              7'h1f,7'h35,7'h53,7'h79,7'h5a,7'h70,7'h16,7'h3c,
                                              7'h6e,7'h44,7'h22,7'h08,7'h2b,7'h01,7'h67,7'h4d,
                                              7'h56,7'h7c,7'h1a,7'h30,7'h13,7'h39,7'h5f,7'h75};

  localparam logic [6:0] TrvkParIncr = 7'h15;
  localparam logic [6:0] NullParBits = 7'h2a;           // 7-bit parity for 32'h0

  logic [31:0] rf_reg   [31:0];
  logic [31:0] rf_reg_q [NREGS-1:1];
  
  logic [6:0]  rf_reg_par   [31:0];
  logic [6:0]  rf_reg_par_q [NREGS-1:0];
  
  reg_cap_t         rf_cap   [31:0];
  reg_cap_t         rf_cap_q [NCAPS-1:1];

  reg_cap_t         rcap_a, rcap_b;

  logic [NREGS-1:1] we_a_dec;
  logic [NREGS-1:1] trvk_dec, trsv_dec;
  logic [31:0]      reg_rdy_vec;
  
  logic             pplbc_alert;
  
  always_comb begin : we_a_decoder
    for (int unsigned i = 1; i < NREGS; i++) begin
      we_a_dec[i] = (waddr_a_i == 5'(i)) ? we_a_i : 1'b0;
      trvk_dec[i] = CheriPPLBC ? (trvk_addr_i == 5'(i)) : 1'b0;
      trsv_dec[i] = CheriPPLBC ? (trsv_addr_i == 5'(i)) : 1'b0;
    end
  end

  // No flops for R0 as it's hard-wired to 0
  for (genvar i = 1; i < NREGS; i++) begin : g_rf_flops
    
    
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        rf_reg_q[i] <= 32'h0;
      end else if (we_a_dec[i]) begin
        rf_reg_q[i] <= wdata_a_i[31:0];
      end 
    end
    
    if (RegFileECC) begin : g_reg_par
      logic [6:0] wdata_par;
      logic       trvk_clr_we;
      
      assign trvk_clr_we = CheriPPLBC & trvk_dec[i] & trvk_en_i & trvk_clrtag_i;      
      assign wdata_par   = wdata_a_i[DataWidth-1:DataWidth-7];
      
      // split reset of data and parity to detect spurious reset (fault protection)
      always_ff @(posedge clk_i or negedge par_rst_ni) begin
        if (!par_rst_ni) begin
          rf_reg_par_q[i] <= DefParBits[i];
        end else if (trvk_clr_we && we_a_dec[i]) begin
          rf_reg_par_q[i] <= wdata_par ^ TrvkParIncr;
        end else if (trvk_clr_we) begin
          // update parity bits
          rf_reg_par_q[i] <= rf_reg_par_q[i] ^ TrvkParIncr;
        end else if (we_a_dec[i]) begin
          rf_reg_par_q[i] <= wdata_par;
        end 
      end
    end else begin : g_no_reg_par
      assign rf_reg_par_q[i] = 7'h0;
    end  // gen reg_par

  end // g_rf_flops


  assign rf_reg[0]     = 32'h0;
  assign rf_reg_par[0] = DefParBits[0];
  for (genvar i=1; i<32 ; i++) begin
    if (i < NREGS) begin
      assign rf_reg[i]     = rf_reg_q[i];         
      assign rf_reg_par[i] = rf_reg_par_q[i];     
    end else begin
      assign rf_reg[i]     = 0;
      assign rf_reg_par[i] = DefParBits[i];
    end
  end

  assign rdata_a_o = DataWidth'({rf_reg_par[raddr_a_i], rf_reg[raddr_a_i]});
  assign rdata_b_o = DataWidth'({rf_reg_par[raddr_b_i], rf_reg[raddr_b_i]});

  // capability meta data (MSW)
  for (genvar i = 1; i < NCAPS; i++) begin : g_cap_flops
    logic trvk_clr_we;
      
    assign trvk_clr_we = CheriPPLBC & trvk_dec[i] & trvk_en_i & trvk_clrtag_i;      
 
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        rf_cap_q[i] <= NULL_REG_CAP;
      end else if (trvk_clr_we && we_a_dec[i]) begin
        rf_cap_q[i] <= and_regcap_tag(wcap_a_i, 1'b0);
      end else if (trvk_clr_we) begin
        // prioritize revocation (later in pipeline)
        rf_cap_q[i] <= and_regcap_tag(rf_cap_q[i], 1'b0);
      end else if (we_a_dec[i]) begin
        rf_cap_q[i] <= wcap_a_i;
      end
    end
  end

  assign rf_cap[0] = NULL_REG_CAP;
  for (genvar i=1; i<32 ; i++) begin
    if (i < NCAPS) begin 
      assign rf_cap[i] = rf_cap_q[i];
    end else begin
      assign rf_cap[i] = NULL_REG_CAP;
    end
  end

  assign rcap_a = rf_cap[raddr_a_i];
  assign rcap_b = rf_cap[raddr_b_i];

  if (CheriPPLBC) begin : g_regrdy

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni)
        reg_rdy_vec[0] <= 1'b1;
    end

    for (genvar i=1; i<NCAPS; i++) begin
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni)
          reg_rdy_vec[i] <= 1'b1;
        else if (trsv_dec[i] & trsv_en_i)   // prioritize trsv t
          reg_rdy_vec[i] <= 1'b0;
        else if (trvk_dec[i] & trvk_en_i)
          reg_rdy_vec[i] <= 1'b1;
      end  // always_ff
    end

    // unused bits
    for (genvar i=NCAPS; i<32; i++) begin
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni)
          reg_rdy_vec[i] <= 1'b1;
      end
    end
    
    // build the shadow copy of reg_rdy_vec for fault protection
    if (RegFileECC) begin : gen_shdw
      logic  [4:0] trvk_addr_q;
      logic        trvk_en_q;
      logic        trvk_clrtag_q;
      logic  [6:0] trvk_par_q;
      logic  [4:0] trsv_addr_q;
      logic        trsv_en_q;
      logic  [6:0] trsv_par_q;

      logic      [31:0] reg_rdy_vec_shdw, reg_rdy_vec_q;  
      logic [NREGS-1:1] trvk_dec_shdw, trsv_dec_shdw;
      logic             shdw_mismatch_err, cap_rvk_err;            


      always_comb begin  
        for (int unsigned i = 1; i < NREGS; i++) begin
          trvk_dec_shdw[i] = (trvk_addr_q == 5'(i));
          trsv_dec_shdw[i] = (trsv_addr_q == 5'(i));
        end
      end
      
      always_ff @(posedge clk_i or negedge par_rst_ni) begin
        if (!par_rst_ni) begin
           trvk_addr_q   <= 5'h0;
           trvk_en_q     <= 1'b0;        
           trvk_clrtag_q <= 1'b0;
           trvk_par_q    <= NullParBits;   
           trsv_addr_q   <= 5'h0;
           trsv_en_q     <= 1'b0;
           trsv_par_q    <= NullParBits;
           reg_rdy_vec_q <= {32{1'b1}};
        end else begin
           trvk_addr_q   <= trvk_addr_i;
           trvk_en_q     <= trvk_en_i;
           trvk_clrtag_q <= trvk_clrtag_i;
           trvk_par_q    <= trvk_par_i;   
           trsv_addr_q   <= trsv_addr_i;
           trsv_en_q     <= trsv_en_i;
           trsv_par_q    <= trsv_par_i;
           reg_rdy_vec_q <= reg_rdy_vec;
        end
      end
      
      for (genvar i = 0; i < 32; i++) begin
        if ((i == 0) || (i >= NCAPS)) begin
          assign reg_rdy_vec_shdw[i] = 1'b1;
        end else begin
          always_ff @(posedge clk_i or negedge par_rst_ni) begin
            if (!par_rst_ni)
              reg_rdy_vec_shdw[i] <= 1'b1;
            else if (trsv_dec_shdw[i] & trsv_en_q)
            reg_rdy_vec_shdw[i] <= 1'b0;
            else if (trvk_dec_shdw[i] & trvk_en_q)
              reg_rdy_vec_shdw[i] <= 1'b1;
          end  // always_ff
        end
      end

      // generate alert 
      assign shdw_mismatch_err = (reg_rdy_vec_shdw != reg_rdy_vec_q);

      // readback revoked cap to make sure the valid bit is actually cleared
      always_comb begin
        cap_rvk_err = 0;        
        for (int unsigned i = 1; i < NCAPS; i++) begin
          cap_rvk_err = cap_rvk_err | (trvk_en_q & trvk_clrtag_q & trvk_dec_shdw[i] & rf_cap_q[i].valid);
        end
      end
 
       
      // check parity of trsv and trvk requests
      logic [1:0] trsv_ecc_err, trvk_ecc_err;

      prim_secded_inv_39_32_dec trsv_ecc_i (
        .data_i    ({trsv_par_q, 26'h0, trsv_en_q, trsv_addr_q}),
        .data_o    (),
        .syndrome_o(),
        .err_o     (trsv_ecc_err)
      );

      prim_secded_inv_39_32_dec trsk_ecc_i (
        .data_i    ({trvk_par_q, 25'h0, trvk_en_q, trvk_clrtag_q, trvk_addr_q}),
        .data_o    (),
        .syndrome_o(),
        .err_o     (trvk_ecc_err)
      );

      assign pplbc_alert = shdw_mismatch_err | cap_rvk_err | (|trsv_ecc_err) | (|trvk_ecc_err);
      
    end else begin : gen_no_shdw // no ECC or shdw checking
      assign pplbc_alert = 1'b0;      
    end
    
  end else begin : g_no_regrdy
    assign reg_rdy_vec = {32{1'b1}};
    assign pplbc_alert = 1'b0;
  end  // not pplbc
  
  //
  //  read back last-writen register for fault protection
  //
  logic reg_rdbk_err;
  
  if (RegFileECC) begin : gen_fault_rdbk
    logic [NREGS-1:1] we_a_dec_shdw;
    logic       [4:0] waddr_a_q;
    logic      [31:0] wdata_a_q;
    logic       [6:0] wpar_a_q;
    logic      [37:0] wcap_vec_q;
    logic             we_a_q;
    logic      [31:0] wdata_tmp;
    logic       [6:0] rpar_tmp;
    logic       [1:0] wreq_ecc_err;
    logic             rdbk_cmp_err;
    
    // flop the write request and check parity 
    //   need all fields to compute parity bits
    always_ff @(posedge clk_i or negedge par_rst_ni) begin
      if (!par_rst_ni) begin
        waddr_a_q   <= 5'h0;
        wdata_a_q   <= 32'h0;
        wpar_a_q    <= NullParBits;
        wcap_vec_q  <= 38'h0;
        we_a_q      <= 1'b0;
      end else begin
        waddr_a_q   <= waddr_a_i;
        wdata_a_q   <= wdata_a_i[31:0];
        wpar_a_q    <= wdata_a_i[DataWidth-1:DataWidth-7];
        wcap_vec_q  <= reg2vec(wcap_a_i);
        we_a_q      <= we_a_i;
      end
    end      

    assign wdata_tmp    = wdata_a_q ^ wcap_vec_q[31:0] ^ {20'h0, we_a_q, waddr_a_q, wcap_vec_q[37:32]};

    prim_secded_inv_39_32_dec wdata_ecc_i (
      .data_i    ({wpar_a_q, wdata_tmp}),
      .data_o    (),
      .syndrome_o(),
      .err_o     (wreq_ecc_err)
    );
   
    // decode and read back to verify (only parity bits)
    always_comb begin 
      for (int unsigned i = 1; i < NREGS; i++) begin
        we_a_dec_shdw[i] = (waddr_a_q == 5'(i)) ? we_a_q : 1'b0;
      end
    end

    assign rpar_tmp     = rf_reg_par[waddr_a_q]; 
   
    assign rdbk_cmp_err = (rpar_tmp != wpar_a_q) && (waddr_a_q != 0) && we_a_q;

    assign reg_rdbk_err = (|wreq_ecc_err) | rdbk_cmp_err;

  end else begin : gen_no_fault_rdbk
    assign reg_rdbk_err = 1'b0;
  end 
  
  assign alert_o   = pplbc_alert | reg_rdbk_err;

  reg_cap_t rcap_a_rvkd, rcap_b_rvkd;

  if (TRVKBypass) begin
    // Bypass the registier update cycle and directly update the read ports
    always_comb begin
      reg_rdy_o = reg_rdy_vec | ({NREGS{trvk_en_i}} & {trvk_dec, 1'b0});
      
      rcap_a_rvkd = rcap_a;
      if (trvk_en_i && trvk_clrtag_i && (trvk_addr_i == raddr_a_i))
        rcap_a_rvkd.valid = 1'b0;
      rcap_a_o = rcap_a_rvkd;

      rcap_b_rvkd = rcap_b;
      if (trvk_en_i && trvk_clrtag_i && (trvk_addr_i == raddr_b_i))
        rcap_b_rvkd.valid = 1'b0;
      rcap_b_o = rcap_b_rvkd;
    
    end
  end else begin
    assign reg_rdy_o = reg_rdy_vec;

    assign rcap_a_rvkd = rcap_a;
    assign rcap_a_o    = rcap_a_rvkd;
    assign rcap_b_rvkd = rcap_b;
    assign rcap_b_o  = rcap_b_rvkd;
  end
   


endmodule
