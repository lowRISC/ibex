// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module cheri_ex import cheri_pkg::*; #(
  parameter bit          WritebackStage = 1'b0,
  parameter bit          MemCapFmt      = 1'b0,
  parameter int unsigned HeapBase       = 32'h2001_0000,
  parameter int unsigned TSMapBase      = 32'h2002_f000,
  parameter bit          CheriPPLBC     = 1'b1,
  parameter bit          CheriSBND2     = 1'b0,
  parameter bit          CheriStkZ      = 1'b1,
  parameter bit          CheriCapIT8    = 1'b0
)(
   // Clock and Reset
  input  logic          clk_i,
  input  logic          rst_ni,

  // configuration & control
  input  logic          cheri_pmode_i,
  input  logic          cheri_tsafe_en_i,
  input  logic          debug_mode_i,

  // data forwarded from WB stage
  input  logic          fwd_we_i,
  input  logic  [4:0]   fwd_waddr_i,
  input  logic [31:0]   fwd_wdata_i,
  input  reg_cap_t      fwd_wcap_i,

  // regfile interface
  input  logic  [4:0]   rf_raddr_a_i,
  input  logic [31:0]   rf_rdata_a_i,
  input  reg_cap_t      rf_rcap_a_i,
  input  logic  [4:0]   rf_raddr_b_i,
  input  logic [31:0]   rf_rdata_b_i,
  input  reg_cap_t      rf_rcap_b_i,
  output logic          rf_trsv_en_o,
  input  logic  [4:0]   rf_waddr_i,

  // pcc interface
  input  pcc_cap_t      pcc_cap_i,
  output pcc_cap_t      pcc_cap_o,
  input  logic [31:0]   pc_id_i,

  // use branch_req_o also to update pcc cap
  output logic          branch_req_o,          // update PCC (goes to cs_registers)
  output logic          branch_req_spec_o,     // speculative branch request (go to IF)
  output logic [31:0]   branch_target_o,

  // Interface to ID stage control logic
  input  logic          cheri_exec_id_i,
  input  logic          instr_first_cycle_i,   // 1st exec cycle allowing lsu_req

  // inputs from decoder
  input  logic          instr_valid_i,
  input  logic          instr_is_cheri_i,
  input  logic          instr_is_rv32lsu_i,
  input  logic          instr_is_compressed_i,
  input  logic [11:0]   cheri_imm12_i,
  input  logic [19:0]   cheri_imm20_i,
  input  logic [20:0]   cheri_imm21_i,
  input  logic  [4:0]   cheri_cs2_dec_i,       // cs2 used for CSR address
  input  logic [OPDW-1:0] cheri_operator_i,

  // output to wb stage
  output logic          cheri_rf_we_o,
  output logic [31:0]   result_data_o,
  output reg_cap_t      result_cap_o,

  output logic          cheri_ex_valid_o,
  output logic          cheri_ex_err_o,
  output logic [11:0]   cheri_ex_err_info_o,
  output logic          cheri_wb_err_o,
  output logic [15:0]   cheri_wb_err_info_o,

  // lsu interface
  output logic          lsu_req_o,
  output logic          lsu_cheri_err_o,
  output logic          lsu_is_cap_o,
  output logic  [3:0]   lsu_lc_clrperm_o,
  output logic          lsu_we_o,
  output logic [31:0]   lsu_addr_o,
  output logic [1:0]    lsu_type_o,
  output logic [31:0]   lsu_wdata_o,
  output reg_cap_t      lsu_wcap_o,
  output logic          lsu_sign_ext_o,
  output logic          cpu_stall_by_stkz_o,
  output logic          cpu_grant_to_stkz_o,

  input  logic          addr_incr_req_i,
  input  logic [31:0]   addr_last_i,
  input  logic          lsu_req_done_i,

  // LSU interface to the existing core (muxed)
  input  logic          rv32_lsu_req_i,
  input  logic          rv32_lsu_we_i,
  input  logic [1:0]    rv32_lsu_type_i,
  input  logic [31:0]   rv32_lsu_wdata_i,
  input  logic          rv32_lsu_sign_ext_i,
  input  logic [31:0]   rv32_lsu_addr_i,
  output logic          rv32_addr_incr_req_o,
  output logic [31:0]   rv32_addr_last_o,

  output logic          cpu_lsu_dec_o,

  input  logic [31:0]   csr_rdata_i,
  input  reg_cap_t      csr_rcap_i,
  input  logic          csr_mstatus_mie_i,
  output logic          csr_access_o,
  output logic  [4:0]   csr_addr_o,
  output logic [31:0]   csr_wdata_o,
  output reg_cap_t      csr_wcap_o,
  output cheri_csr_op_e csr_op_o,
  output logic          csr_op_en_o,
  output logic          csr_set_mie_o,
  output logic          csr_clr_mie_o,

  // stack highwater mark updates
  input  logic [31:0]   csr_mshwm_i,
  input  logic [31:0]   csr_mshwmb_i,
  output logic          csr_mshwm_set_o,
  output logic [31:0]   csr_mshwm_new_o,

  // stack fast clearing control signals
  input  logic          stkz_active_i,
  input  logic          stkz_abort_i,
  input  logic [31:0]   stkz_ptr_i,
  input  logic [31:0]   stkz_base_i,

  output logic          ztop_wr_o,
  output logic [31:0]   ztop_wdata_o,
  output full_cap_t     ztop_wfcap_o,
  input  logic [31:0]   ztop_rdata_i,
  input  reg_cap_t      ztop_rcap_i,

  // debug feature
  input  logic          csr_dbg_tclr_fault_i
);

  logic          cheri_lsu_req;
  logic          cheri_lsu_we;
  logic [31:0]   cheri_lsu_addr;
  logic [31:0]   cheri_lsu_wdata;
  reg_cap_t      cheri_lsu_wcap;
  logic          cheri_lsu_err;
  logic          cheri_lsu_is_cap;

  logic [31:0]   rf_rdata_a, rf_rdata_ng_a;
  logic [31:0]   rf_rdata_b, rf_rdata_ng_b;

  reg_cap_t      rf_rcap_a, rf_rcap_ng_a;
  reg_cap_t      rf_rcap_b, rf_rcap_ng_b;

  full_cap_t     rf_fullcap_a, rf_fullcap_b;

  reg_cap_t      csc_wcap;

  logic          is_load_cap, is_store_cap, is_cap;

  logic          addr_bound_vio;
  logic          perm_vio, perm_vio_slc;
  logic          rv32_lsu_err;
  logic          addr_bound_vio_rv32;
  logic          perm_vio_rv32;

  logic [W_PVIO-1:0]  perm_vio_vec, perm_vio_vec_rv32;

  logic  [31:0]  cs1_addr_plusimm;
  logic  [31:0]  cs1_imm;
  logic  [31:0]  addr_result;


  logic          cheri_rf_we_raw, branch_req_raw, branch_req_spec_raw;
  logic          csr_set_mie_raw, csr_clr_mie_raw;
  logic          cheri_ex_valid_raw, cheri_ex_err_raw;
  logic          csr_op_en_raw;
  logic          cheri_wb_err_raw;
  logic          cheri_wb_err_q, cheri_wb_err_d;
  logic          ztop_wr_raw;

  logic   [3:0]  cheri_lsu_lc_clrperm;
  logic          lc_cglg, lc_csdlm, lc_ctag;
  logic  [31:0]  pc_id_nxt;

  full_cap_t     setaddr1_outcap, setbounds_outcap, setbounds_rndn_outcap;
  logic  [15:0]  cheri_wb_err_info_q, cheri_wb_err_info_d;
  logic          set_bounds_done;

  logic   [4:0]  cheri_err_cause, rv32_err_cause;
  logic   [31:0] cpu_lsu_addr;
  logic   [31:0] cpu_lsu_wdata;
  logic          cpu_lsu_we;
  logic          cpu_lsu_cheri_err, cpu_lsu_is_cap;

  logic          illegal_scr_addr;
  logic          scr_legalization;

  // data forwarding for CHERI instructions
  //  - note address 0 is a read-only location per RISC-V
  always_comb begin : fwd_data_merger
    if ((rf_raddr_a_i == fwd_waddr_i) && fwd_we_i && (|rf_raddr_a_i)) begin
      rf_rdata_ng_a = fwd_wdata_i;
      rf_rcap_ng_a  = fwd_wcap_i;
    end else begin
      rf_rdata_ng_a = rf_rdata_a_i;
      rf_rcap_ng_a  = rf_rcap_a_i;
    end

    if ((rf_raddr_b_i == fwd_waddr_i) && fwd_we_i && (|rf_raddr_b_i)) begin
      rf_rdata_ng_b = fwd_wdata_i;
      rf_rcap_ng_b  = fwd_wcap_i;
    end else begin
      rf_rdata_ng_b = rf_rdata_b_i;
      rf_rcap_ng_b  = rf_rcap_b_i;
    end
  end

  // 1st level of operand gating (power-saving)
  //  - gate off the input to reg2full conversion logic
  //  - note rv32 lsu req only use cs1
  //  - may need to use dont_tounch gates
  assign rf_rcap_a   = (instr_is_cheri_i | instr_is_rv32lsu_i) ? rf_rcap_ng_a : NULL_REG_CAP;
  assign rf_rdata_a  = (instr_is_cheri_i | instr_is_rv32lsu_i) ? rf_rdata_ng_a : 32'h0;

  assign rf_rcap_b   = instr_is_cheri_i ? rf_rcap_ng_b : NULL_REG_CAP;
  assign rf_rdata_b  = instr_is_cheri_i ? rf_rdata_ng_b : 32'h0;

  // expand the capabilities
  assign rf_fullcap_a = reg2fullcap(rf_rcap_a, rf_rdata_a);
  assign rf_fullcap_b = reg2fullcap(rf_rcap_b, rf_rdata_b);

  // gate these signals with cheri_exec_id to make sure they are only active when needed
  // (only 1 cycle in all cases other than cheri_rf_we)
  // -- safest approach and probably the right thing to do in case there is a wb_exception
  assign cheri_rf_we_o     = cheri_rf_we_raw & cheri_exec_id_i;
  assign branch_req_o      = branch_req_raw & cheri_exec_id_i;
  assign branch_req_spec_o = branch_req_spec_raw & cheri_exec_id_i;
  assign csr_set_mie_o     = csr_set_mie_raw & cheri_exec_id_i;
  assign csr_clr_mie_o     = csr_clr_mie_raw & cheri_exec_id_i;
  assign csr_op_en_o       = csr_op_en_raw & cheri_exec_id_i;
  assign ztop_wr_o         = ztop_wr_raw & cheri_exec_id_i;

  // ex_valid only used in multicycle case
  // ex_err is used for id exceptions
  assign cheri_ex_valid_o = cheri_ex_valid_raw & cheri_exec_id_i;
  assign cheri_ex_err_o   = cheri_ex_err_raw & cheri_exec_id_i & ~debug_mode_i;

  if (WritebackStage) begin
    assign cheri_wb_err_o   = cheri_wb_err_q;
  end else begin
    assign cheri_wb_err_o   = cheri_wb_err_d;
  end

  assign cheri_lsu_lc_clrperm = debug_mode_i ? 4'h0 : {lc_ctag, 1'b0, lc_csdlm, lc_cglg};

  always_comb begin : main_ex
    logic [PERMS_W-1:0] perms_temp;
    full_cap_t          tfcap;

    //default
    cheri_rf_we_raw      = 1'b0;
    result_data_o        = 32'h0;
    result_cap_o         = NULL_REG_CAP;
    csc_wcap             = NULL_REG_CAP;
    cheri_ex_valid_raw   = 1'b0;
    cheri_ex_err_raw     = 1'b0;
    cheri_wb_err_raw     = 1'b0;
    perms_temp           = 0;

    csr_access_o         = 1'b0;
    csr_addr_o           = 5'h0;
    csr_wdata_o          = 32'h0;
    csr_wcap_o           = NULL_REG_CAP;
    csr_op_o             = CHERI_CSR_NULL;
    csr_op_en_raw        = 1'b0;
    scr_legalization     = 1'b0;

    branch_req_raw       = 1'b0;
    branch_req_spec_raw  = 1'b0;
    csr_set_mie_raw      = 1'b0;
    csr_clr_mie_raw      = 1'b0;
    branch_target_o      = 32'h0;
    pcc_cap_o            = NULL_PCC_CAP;
    tfcap                = NULL_FULL_CAP;
    lc_cglg              = 1'b0;
    lc_csdlm             = 1'b0;
    lc_ctag              = 1'b0;
    rf_trsv_en_o         = 1'b0;
    ztop_wr_raw          = 1'b0;
    ztop_wdata_o         = 32'h0;
    ztop_wfcap_o         = NULL_FULL_CAP;

    unique case (1'b1)
      cheri_operator_i[CGET_PERM]:
        begin
          result_data_o       = {20'h0, rf_fullcap_a.perms};
          result_cap_o        = NULL_REG_CAP;   // zerout the cap msw
          cheri_rf_we_raw     = 1'b1;
          cheri_ex_valid_raw  = 1'b1;
        end
      cheri_operator_i[CGET_TYPE]:
        begin
          result_data_o       = {28'h0, decode_otype(rf_fullcap_a.otype, rf_fullcap_a.perms[PERM_EX])};
          result_cap_o        = NULL_REG_CAP;
          cheri_rf_we_raw     = 1'b1;
          cheri_ex_valid_raw  = 1'b1;
        end
      cheri_operator_i[CGET_BASE]:
        begin
          result_data_o       = rf_fullcap_a.base32;
          result_cap_o        = NULL_REG_CAP;
          cheri_rf_we_raw     = 1'b1;
          cheri_ex_valid_raw  = 1'b1;
        end
      cheri_operator_i[CGET_TOP]:
        begin
          result_data_o       = rf_fullcap_a.top33[32] ? 32'hffff_ffff : rf_fullcap_a.top33[31:0];
          result_cap_o        = NULL_REG_CAP;
          cheri_rf_we_raw     = 1'b1;
          cheri_ex_valid_raw  = 1'b1;
        end
      cheri_operator_i[CGET_LEN]:
        begin
          result_data_o       = get_cap_len(rf_fullcap_a);
          result_cap_o        = NULL_REG_CAP;
          cheri_rf_we_raw     = 1'b1;
          cheri_ex_valid_raw  = 1'b1;
        end
      cheri_operator_i[CGET_TAG]:
        begin
          result_data_o       = {31'h0, rf_fullcap_a.valid};
          result_cap_o        = NULL_REG_CAP;
          cheri_rf_we_raw     = 1'b1;
          cheri_ex_valid_raw  = 1'b1;
        end
      cheri_operator_i[CGET_ADDR]:
        begin
          result_data_o       = rf_rdata_a;
          result_cap_o        = NULL_REG_CAP;
          cheri_rf_we_raw     = 1'b1;
          cheri_ex_valid_raw  = 1'b1;
        end
      cheri_operator_i[CGET_HIGH]:
        begin
          logic [65:0] tmp66;
          tmp66 = MemCapFmt ? (CheriCapIT8 ? reg2mem_it8_fmt1(rf_rcap_a, rf_rdata_a) :
                                             reg2mem_fmt1(rf_rcap_a, rf_rdata_a)) :
                              (CheriCapIT8 ? {reg2memcap_it8_fmt0(rf_rcap_a), 1'b0, rf_rdata_a[31:0]} :
                                             {reg2memcap_fmt0(rf_rcap_a), 1'b0, rf_rdata_a[31:0]});
          result_data_o       = tmp66[64:33];
          result_cap_o        = NULL_REG_CAP;
          cheri_rf_we_raw     = 1'b1;
          cheri_ex_valid_raw  = 1'b1;
        end
      (cheri_operator_i[CSEAL] | cheri_operator_i[CUNSEAL]):
        begin                   // cd <-- cs1; cd.otyp <-- cs2.otype; cd.sealed <-- val
          result_data_o        = rf_rdata_a;

          if (cheri_operator_i[CSEAL])
            result_cap_o       = full2regcap(seal_cap(rf_fullcap_a, rf_rdata_b[OTYPE_W-1:0]));
          else begin
            tfcap                = unseal_cap(rf_fullcap_a);
            tfcap.perms[PERM_GL] = rf_fullcap_a.perms[PERM_GL] & rf_fullcap_b.perms[PERM_GL];
            tfcap.cperms         = compress_perms(tfcap.perms, tfcap.cperms[5:4]);
            result_cap_o         = full2regcap(tfcap);
          end

          result_cap_o.valid   = result_cap_o.valid & (~addr_bound_vio) & (~perm_vio);
          cheri_rf_we_raw      = 1'b1;
          cheri_ex_valid_raw   = 1'b1;
        end
      cheri_operator_i[CAND_PERM]:         // cd <-- cs1; cd.perm <-- cd.perm & rs2
        begin
          logic [PERMS_W-1:0] pmask;
          result_data_o      = rf_rdata_a;
          tfcap              = rf_fullcap_a;
          tfcap.perms        = tfcap.perms & rf_rdata_b[PERMS_W-1:0];
          tfcap.cperms       = compress_perms(tfcap.perms, tfcap.cperms[5:4]);
          // for sealed caps, clear tag unless perm mask (excluding GL) == all '1'
          pmask              = rf_rdata_b[PERMS_W-1:0];
          pmask[PERM_GL]     = 1'b1;
          tfcap.valid        = tfcap.valid & (~is_cap_sealed(rf_fullcap_a) | (&pmask));
          result_cap_o       = full2regcap(tfcap);
          cheri_rf_we_raw    = 1'b1;
          cheri_ex_valid_raw = 1'b1;
        end
      cheri_operator_i[CSET_HIGH]:         // cd <-- cs1; cd.high <-- convert(rs2)
        begin
          // this only works for memcap_fmt0 for now QQQ
          result_data_o      = rf_rdata_a;
          result_cap_o       = CheriCapIT8 ? mem2regcap_it8_fmt0({1'b0, rf_rdata_b}, {1'b0, rf_rdata_a}, 4'h0) :
                                             mem2regcap_fmt0({1'b0, rf_rdata_b}, {1'b0, rf_rdata_a}, 4'h0);
          cheri_rf_we_raw    = 1'b1;
          cheri_ex_valid_raw = 1'b1;
        end

      // setaddr/incoffset: cd <-- cs1; cd.offset <-- rs2, or cs1.addr + rs2, or cs1.addr + imm12
      // auipcc: cd <-- pcc, cd.address <-- pcc.address + (imm20 << 12)
      (cheri_operator_i[CSET_ADDR] | cheri_operator_i[CINC_ADDR] |
       cheri_operator_i[CINC_ADDR_IMM] | cheri_operator_i[CAUIPCC] | cheri_operator_i[CAUICGP]):
        begin
          logic clr_sealed;
          logic instr_fault;

          result_data_o        = addr_result;

          // for pointer operations, follow C convention and allow newptr == top
          clr_sealed           = cheri_operator_i[CAUIPCC] ? 1'b0 : is_cap_sealed(rf_fullcap_a);
          tfcap                = setaddr1_outcap;
          tfcap.valid          = tfcap.valid & ~clr_sealed;
          result_cap_o         = full2regcap(tfcap);
          instr_fault          = csr_dbg_tclr_fault_i & (rf_fullcap_a.valid | cheri_operator_i[CAUIPCC]) &
                                 ~result_cap_o.valid;
          cheri_wb_err_raw     = instr_fault;
          cheri_rf_we_raw      = ~instr_fault;
          cheri_ex_valid_raw   = 1'b1;
        end
      (cheri_operator_i[CSET_BOUNDS] | cheri_operator_i[CSET_BOUNDS_IMM] | cheri_operator_i[CSET_BOUNDS_EX] |
       cheri_operator_i[CRRL] | cheri_operator_i[CRAM] | cheri_operator_i[CSET_BOUNDS_RNDN]):
        begin                  // cd <-- cs1; cd.base <-- cs1.address, cd.len <-- rs2 or imm12
          logic instr_fault;

          tfcap            = cheri_operator_i[CSET_BOUNDS_RNDN] ? setbounds_rndn_outcap : setbounds_outcap;
          tfcap.valid      = tfcap.valid & ~is_cap_sealed(rf_fullcap_a);

          if (cheri_operator_i[CRRL]) begin
            result_data_o = tfcap.rlen;
            result_cap_o  = NULL_REG_CAP;
          end else if (cheri_operator_i[CRAM]) begin
            result_data_o = tfcap.maska;
            result_cap_o  = NULL_REG_CAP;
          end else begin
            result_data_o = rf_rdata_a;
            result_cap_o  = full2regcap(tfcap);
          end

          cheri_ex_valid_raw = set_bounds_done;
          instr_fault        = csr_dbg_tclr_fault_i & rf_fullcap_a.valid & ~result_cap_o.valid &
                             (cheri_operator_i[CSET_BOUNDS] | cheri_operator_i[CSET_BOUNDS_IMM] |
                              cheri_operator_i[CSET_BOUNDS_EX] | cheri_operator_i[CSET_BOUNDS_RNDN]);
          cheri_rf_we_raw    = ~instr_fault;
          cheri_wb_err_raw   = instr_fault;
        end
      cheri_operator_i[CCLEAR_TAG]:         // cd <-- cs1; cd.tag <-- '0'
        begin
          result_data_o        = rf_rdata_a;
          result_cap_o         = rf_rcap_a;
          result_cap_o.valid   = 1'b0;
          cheri_rf_we_raw      = 1'b1;
          cheri_ex_valid_raw   = 1'b1;
        end
      cheri_operator_i[CIS_SUBSET]:      // rd <-- (cs1.tag == cs2.tag) && (cs2 is_subset_of cs1)
        begin
          result_data_o       = 32'((rf_fullcap_a.valid  == rf_fullcap_b.valid) &&
                                 ~addr_bound_vio && (&(rf_fullcap_a.perms | ~rf_fullcap_b.perms)));
          result_cap_o        = NULL_REG_CAP;
          cheri_rf_we_raw     = 1'b1;
          cheri_ex_valid_raw  = 1'b1;
        end
      cheri_operator_i[CIS_EQUAL]:       // rd <-- (cs1 == cs2)
        begin
          result_data_o       = 32'(is_equal(rf_fullcap_a, rf_fullcap_b, rf_rdata_a, rf_rdata_b));
          result_cap_o        = NULL_REG_CAP;
          cheri_rf_we_raw     = 1'b1;
          cheri_ex_valid_raw  = 1'b1;
        end
      cheri_operator_i[CSUB_CAP]:          // rd <-- cs1.addr - cs2.addr
        begin
          result_data_o       = rf_rdata_a - rf_rdata_b;
          result_cap_o        = NULL_REG_CAP;
          cheri_rf_we_raw     = 1'b1;
          cheri_ex_valid_raw  = 1'b1;
        end
      cheri_operator_i[CMOVE_CAP]:         // cd <-- cs1
        begin
          result_data_o       = rf_rdata_a;
          result_cap_o        = rf_rcap_a;
          cheri_rf_we_raw     = 1'b1;
          cheri_ex_valid_raw  = 1'b1;
        end
      cheri_operator_i[CLOAD_CAP]:
        begin
          lc_cglg              = ~rf_fullcap_a.perms[PERM_LG];
          lc_csdlm             = ~rf_fullcap_a.perms[PERM_LM];
          lc_ctag              = ~rf_fullcap_a.perms[PERM_MC];

          result_data_o        = 32'h0;
          result_cap_o         = NULL_REG_CAP;
          cheri_rf_we_raw      = 1'b0;
          cheri_ex_valid_raw   = 1'b1;             // lsu_req_done is factored in by id_stage
          cheri_ex_err_raw     = 1'b0;             // acc err passed to LSU and processed later in WB
          rf_trsv_en_o         = CheriPPLBC & cheri_tsafe_en_i & lsu_req_done_i;
        end
      cheri_operator_i[CSTORE_CAP]:
        begin
          result_data_o        = 32'h0;
          result_cap_o         = NULL_REG_CAP;
          cheri_rf_we_raw      = 1'b0;
          cheri_ex_valid_raw   = 1'b1;
          cheri_ex_err_raw     = 1'b0;       // acc err passed to LSU and processed later in WB
          csc_wcap             = rf_rcap_b;
          csc_wcap.valid       = rf_rcap_b.valid & ~perm_vio_slc;
        end
      cheri_operator_i[CCSR_RW]:           // cd <-- scr; scr <-- cs1 if cs1 != C0
        begin
          logic [31:0] tmp32;
          logic        is_ztop, is_write;
          reg_cap_t    trcap;
          logic        instr_fault;

          is_ztop            = (cheri_cs2_dec_i==CHERI_SCR_ZTOPC);
          is_write           = (rf_raddr_a_i != 0);
          instr_fault        = perm_vio | illegal_scr_addr;

          csr_access_o       = ~instr_fault;
          csr_op_o           = CHERI_CSR_RW;
          csr_op_en_raw      = ~instr_fault && is_write && ~is_ztop;
          ztop_wr_raw        = ~instr_fault && is_write && is_ztop;
          csr_addr_o         = cheri_cs2_dec_i;

          if (cheri_cs2_dec_i == CHERI_SCR_MTCC) begin
            // MTVEC/MTCC legalization (clear tag if checking fails)
            // note we don't reall need set_address checks here - it's only used to update temp fields
            //   so that RTL behavior would match sail
            scr_legalization = 1'b1;
            csr_wdata_o      = {rf_rdata_a[31:2], 2'b00};
            trcap            = full2regcap(setaddr1_outcap);
            if ((rf_rdata_a[1:0] != 2'b00) || ~rf_fullcap_a.perms[PERM_EX] || (rf_fullcap_a.otype != 0))
              trcap.valid = 1'b0;
            else
              trcap.valid = rf_fullcap_a.valid;
            csr_wcap_o       = trcap;
          end else if (cheri_cs2_dec_i == CHERI_SCR_MEPCC) begin
            // MEPCC legalization (clear tag if checking fails)
            scr_legalization = 1'b1;
            csr_wdata_o      = {rf_rdata_a[31:1], 1'b0};
            trcap            = full2regcap(setaddr1_outcap);
            if ((rf_rdata_a[0] != 1'b0) || ~rf_fullcap_a.perms[PERM_EX] || (rf_fullcap_a.otype != 0))
              trcap.valid = 1'b0;
            else
              trcap.valid = rf_fullcap_a.valid;
            csr_wcap_o       = trcap;
          end else begin
            scr_legalization = 1'b0;
            csr_wdata_o      = rf_rdata_a;
            csr_wcap_o       = rf_rcap_a;
          end

          if (is_ztop) begin
            result_data_o    = ztop_rdata_i;
            result_cap_o     = ztop_rcap_i;
            ztop_wfcap_o     = rf_fullcap_a;
            ztop_wdata_o     = rf_rdata_a;
          end else begin
            result_data_o    = csr_rdata_i;
            result_cap_o     = csr_rcap_i;
            ztop_wfcap_o     = NULL_FULL_CAP;
            ztop_wdata_o     = 32'h0;
          end
          cheri_rf_we_raw    = ~instr_fault;
          cheri_ex_valid_raw = 1'b1;
          cheri_wb_err_raw   = instr_fault;
        end
      (cheri_operator_i[CJALR] | cheri_operator_i[CJAL]):
        begin                  // cd <-- pcc; pcc <-- cs1/pc+offset; pcc.address[0] <--'0'; pcc.sealed <--'0'
          logic [2:0] seal_type;
          logic       instr_fault;

          // note this is the RV32 definition of JALR arithmetic (add first then mask of lsb)
          branch_target_o      = {addr_result[31:1], 1'b0};
          pcc_cap_o            = full2pcap(unseal_cap(rf_fullcap_a));
          // Note we can't directly use pc_if here
          // (link address == pc_id + delta, but pc_if should be the next executed PC (the jump target)
          //  if branch prediction works)
          result_data_o        = pc_id_nxt;
          seal_type            = csr_mstatus_mie_i ? OTYPE_SENTRY_IE_BKWD : OTYPE_SENTRY_ID_BKWD;
          //tfcap                = seal_cap(setaddr1_outcap, seal_type);
          tfcap                = (rf_waddr_i == 5'h1) ? seal_cap(setaddr1_outcap, seal_type) :
                                                        setaddr1_outcap;
          result_cap_o         = full2regcap(tfcap);

          // problem with instr_fault: the pcc_cap.valid check causing timing issue on instr_addr_o
          // -- use the speculative version for instruction fetch
          // -- the ID exception (cheri_ex_err) flushes the pipeline and re-set PC so
          //    the speculatively fetched instruction will be flushed
          // -- this is now mitigated since we no longer do address bound checking here
          //    but let's keep the solution for now

          instr_fault           = perm_vio;

          cheri_rf_we_raw      = ~instr_fault;    // err -> wb exception
          branch_req_raw       = ~instr_fault & cheri_operator_i[CJALR];    // update PCC in CSR
          // branch_req_spec_raw  = 1'b1;
          branch_req_spec_raw  = ~instr_fault;    // set fetch PC

          cheri_wb_err_raw     = instr_fault;
          cheri_ex_err_raw     = 1'b0;
          csr_set_mie_raw      = ~instr_fault && cheri_operator_i[CJALR] &&
                                 ((rf_fullcap_a.otype == OTYPE_SENTRY_IE_FWD) ||
                                  (rf_fullcap_a.otype == OTYPE_SENTRY_IE_BKWD)) ;
          csr_clr_mie_raw      = ~instr_fault && cheri_operator_i[CJALR] &&
                                 ((rf_fullcap_a.otype == OTYPE_SENTRY_ID_FWD) ||
                                  (rf_fullcap_a.otype == OTYPE_SENTRY_ID_BKWD)) ;
          cheri_ex_valid_raw   = 1'b1;
        end
      default:;
    endcase
  end   // always_combi

  assign is_load_cap  = cheri_operator_i[CLOAD_CAP];
  assign is_store_cap = cheri_operator_i[CSTORE_CAP];

  assign is_cap   = cheri_operator_i[CLOAD_CAP] | cheri_operator_i[CSTORE_CAP];

  // muxing between "normal cheri LSU requests (clc/csc) and CLBC

  if (WritebackStage) begin
    // assert LSU req until instruction is retired (req_done from LSU)
    // note if the previous instr is also a load/store, cheri_exec_id won't be asserted
    // till WB is ready (lsu_resp for the previous isntr)
    assign cheri_lsu_req      = is_cap & cheri_exec_id_i;
  end else begin
    // no WB stage, only assert req in the first_cycle phase of the instruction
    // (consistent with the RV32 load/store instructions)
    // Here instruction won't complete till lsu_resp_valid in this case,
    // keeping lsu_req asserted causes problem as LSU sees it as a new request
    assign cheri_lsu_req      = is_cap & cheri_exec_id_i & instr_first_cycle_i;
  end

  assign cheri_lsu_we       = is_store_cap;
  assign cheri_lsu_addr     = cs1_addr_plusimm + {29'h0, addr_incr_req_i, 2'b00};
  assign cheri_lsu_is_cap   = is_cap;

  assign cheri_lsu_wdata    = is_store_cap ? rf_rdata_b : 33'h0;
  assign cheri_lsu_wcap     = is_store_cap  ? csc_wcap : NULL_REG_CAP;

  // RS1/CS1+offset is
  //  keep this separate to help timing on the memory interface
  //   - the starting address for cheri L*/S*.CAP instructions
  assign cs1_imm = (is_cap|cheri_operator_i[CJALR]) ? {{20{cheri_imm12_i[11]}}, cheri_imm12_i} : 0;

  assign cs1_addr_plusimm   = rf_rdata_a + cs1_imm;

  assign pc_id_nxt = pc_id_i + (instr_is_compressed_i ? 2 : 4);

  //
  // shared adder for address calculation
  //
  always_comb begin : shared_adder
    logic        [31:0] tmp32a, tmp32b;

    if      (cheri_operator_i[CJALR])           tmp32a = {{20{cheri_imm12_i[11]}}, cheri_imm12_i};
    else if (cheri_operator_i[CJAL])            tmp32a = {{11{cheri_imm21_i[20]}}, cheri_imm21_i};
    else if (cheri_operator_i[CAUIPCC])         tmp32a = {cheri_imm20_i[19], cheri_imm20_i, 11'h0};
    else if (cheri_operator_i[CAUICGP])         tmp32a = {cheri_imm20_i[19], cheri_imm20_i, 11'h0};
    else if (cheri_operator_i[CSET_ADDR])       tmp32a = rf_rdata_b;
    else if (cheri_operator_i[CINC_ADDR])       tmp32a = rf_rdata_b;
    else if (cheri_operator_i[CINC_ADDR_IMM])   tmp32a = {{20{cheri_imm12_i[11]}}, cheri_imm12_i};
    else                                        tmp32a = 0;

    if      (cheri_operator_i[CJALR])           tmp32b = rf_rdata_a;
    else if (cheri_operator_i[CJAL])            tmp32b = pc_id_i;
    else if (cheri_operator_i[CAUIPCC])         tmp32b = pc_id_i;
    else if (cheri_operator_i[CAUICGP])         tmp32b = rf_rdata_a;
    else if (cheri_operator_i[CSET_ADDR])       tmp32b = 32'h0;
    else if (cheri_operator_i[CINC_ADDR])       tmp32b = rf_rdata_a;
    else if (cheri_operator_i[CINC_ADDR_IMM])   tmp32b = rf_rdata_a;
    else                                        tmp32b = 0;

    addr_result  = tmp32a + tmp32b;
  end

  //
  // Big combinational functions
  //  - break out to make sure we can properly gate off operands to save power
  //
  always_comb begin: set_address_comb
    full_cap_t   tfcap1;
    logic [31:0] taddr1;

    // set_addr operation 1
    if (cheri_operator_i[CJAL] | cheri_operator_i[CJALR]) begin
      // we don't really need the representability check here, but update_temp_fields is necessary
      tfcap1  = pcc2fullcap(pcc_cap_i);        // pcc to link register
      taddr1  = pc_id_nxt;
    end else if (cheri_operator_i[CAUIPCC]) begin
      tfcap1  = pcc2fullcap(pcc_cap_i);
      taddr1  = addr_result;
    end else if (cheri_operator_i[CSET_ADDR] | cheri_operator_i[CINC_ADDR] |
                 cheri_operator_i[CINC_ADDR_IMM] | cheri_operator_i[CAUICGP]) begin
      tfcap1  = rf_fullcap_a;
      taddr1  = addr_result;
    end else if (scr_legalization) begin
      tfcap1  = rf_fullcap_a;
      taddr1  = csr_wdata_o;
    end else begin
      tfcap1  = NULL_FULL_CAP;
      taddr1  = 32'h0;
    end

    // representability check only
    setaddr1_outcap = set_address(tfcap1, taddr1, 0, 0);
  end

  bound_req_t bound_req1, bound_req2;

  always_comb begin: set_bounds_comb
    logic [31:0] newlen;
    logic        req_exact;
    logic [31:0] tmp_addr;
    full_cap_t   tfcap3;

    // set_bounds
    if (cheri_operator_i[CSET_BOUNDS] | cheri_operator_i[CSET_BOUNDS_RNDN]) begin
      newlen    = rf_rdata_b;
      req_exact = 1'b0;
      tfcap3 = rf_fullcap_a;
      tmp_addr  = rf_rdata_a;
    end else if (cheri_operator_i[CSET_BOUNDS_EX]) begin
      newlen    = rf_rdata_b;
      req_exact = 1'b1;
      tfcap3 = rf_fullcap_a;
      tmp_addr  = rf_rdata_a;
    end else if (cheri_operator_i[CSET_BOUNDS_IMM]) begin
      newlen    = 32'(cheri_imm12_i);  // unsigned imm
      req_exact = 1'b0;
      tfcap3 = rf_fullcap_a;
      tmp_addr  = rf_rdata_a;
    end else if (cheri_operator_i[CRRL] | cheri_operator_i[CRAM]) begin
      newlen    = rf_rdata_a;
      req_exact = 1'b0;
      tfcap3 = NULL_FULL_CAP;
      tmp_addr  = 0;
    end else begin
      newlen    = 32'h0;
      req_exact = 1'b0;
      tfcap3 = NULL_FULL_CAP;
      tmp_addr  = 0;
    end

    bound_req1 = CheriCapIT8 ? prep_bound_req_it8 (tfcap3, tmp_addr, newlen) :
                               prep_bound_req (tfcap3, tmp_addr, newlen);

    setbounds_outcap = set_bounds(tfcap3, tmp_addr, bound_req2, req_exact);

    setbounds_rndn_outcap = CheriCapIT8 ? set_bounds_rndn_it8(tfcap3, tmp_addr, bound_req2) :
                                          set_bounds_rndn(tfcap3, tmp_addr, bound_req2);
  end

  if (CheriSBND2) begin
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        bound_req2      <= '{0, 0, 0, 0, 0, 0};
        set_bounds_done <= 1'b0;
      end else begin
        bound_req2      <= bound_req1;
        // set_bounds_done is asserted in the 2nd cycle of execution when SBD2 == 1
        // note in ibex it actaully is ok to hold set_bounds_done high for both cycles
        // since the multicycle control logic won't look at ex_valid till the 2nd cycle
        // however this is the cleaner solution.
        set_bounds_done <= (cheri_operator_i[CSET_BOUNDS] | cheri_operator_i[CSET_BOUNDS_IMM] |
                            cheri_operator_i[CSET_BOUNDS_EX] | cheri_operator_i[CRRL] |
                            cheri_operator_i[CRAM]) & cheri_exec_id_i & ~set_bounds_done ;
      end
    end
  end else begin
    assign bound_req2      = bound_req1;
    assign set_bounds_done = 1'b1;
  end



  // address bound and permission checks for
  //    - cheri no-LSU instructions
  //    - cheri LSU (cap) instructions (including internal instr like LBC)
  //    - RV32  LSU (data) instructions
  // this is a architectural access check (apply to the whole duration of an instruction)
  //    - based on architectural capability registers and addresses

  // - orginally we combine checking for CHERI and RV32 but it caused a combi loop
  //   that goes from instr_executing -> rv32_lsu_req -> lsu_error -> cheri_ex_err -> instr_executing
  //   it's not a real runtime issue but it does confuses timing tools so let's split for now.
  //   Besides - note checking/lsu_cheri_err_o is one timing critical path
  logic [31:0] rv32_ls_chkaddr;
  assign rv32_ls_chkaddr = rv32_lsu_addr_i;

  always_comb begin : check_rv32
    logic [31:0] top_offset;
    logic [32:0] top_bound;
    logic [31:0] base_bound, base_chkaddr;
    logic        top_vio, base_vio;
    logic [32:0] top_chkaddr;
    logic        top_size_ok;

    // generate the address used to check top bound violation
    base_chkaddr = rv32_ls_chkaddr;

    if (rv32_lsu_type_i == 2'b00) begin
      top_offset  = 32'h4;
      top_size_ok = |rf_fullcap_a.top33[32:2];     // at least 4 bytes
    end else if (rv32_lsu_type_i == 2'b01) begin
      top_offset  = 32'h2;
      top_size_ok = |rf_fullcap_a.top33[32:1];
    end else begin
      top_offset = 32'h1;
      top_size_ok = |rf_fullcap_a.top33[32:0];
    end

    //top_chkaddr = base_chkaddr + top_offset;
    top_chkaddr = {1'b0, base_chkaddr};

    // top_bound  = rf_fullcap_a.top33;
    top_bound  = rf_fullcap_a.top33 - top_offset;
    base_bound = rf_fullcap_a.base32;

    top_vio  = (top_chkaddr  > top_bound) || ~top_size_ok;
    base_vio = (base_chkaddr < base_bound);

    // timing critical (data_req_o) path - don't add any unnecssary terms.
    // we will chose with is_cheri on the LSU interface later.
    //   for unaligned access, only check the starting (1st) address
    //   (if there is an error, addr_incr_req won't be thre anyway
    addr_bound_vio_rv32 =  (top_vio | base_vio) & ~addr_incr_req_i ;

    // main permission logic
    perm_vio_vec_rv32 = 0;

    perm_vio_vec_rv32[PVIO_TAG]  = ~rf_fullcap_a.valid;
    perm_vio_vec_rv32[PVIO_SEAL] = is_cap_sealed(rf_fullcap_a);
    perm_vio_vec_rv32[PVIO_LD]   = ((~rv32_lsu_we_i) && (~rf_fullcap_a.perms[PERM_LD]));
    perm_vio_vec_rv32[PVIO_SD]   = (rv32_lsu_we_i && (~rf_fullcap_a.perms[PERM_SD]));

    perm_vio_rv32 =  |perm_vio_vec_rv32;
  end

  assign rv32_lsu_err = cheri_pmode_i & ~debug_mode_i & (addr_bound_vio_rv32 | perm_vio_rv32);

  // Cheri instr address bound checking
  //   -- we choose to centralize the address bound checking here
  //      so that we can mux the inputs and save some area


  logic [31:0] cheri_ls_chkaddr;
  assign cheri_ls_chkaddr = cs1_addr_plusimm;

  always_comb begin : check_cheri
    logic [31:0] top_offset;
    logic [32:0] top_bound;
    logic [31:0] base_bound, base_chkaddr;
    logic [32:0] top_chkaddr;
    logic        top_vio, base_vio, top_equal;
    logic        cs2_bad_type;
    logic        cs1_otype_0, cs1_otype_1, cs1_otype_45, cs1_otype_23;
    logic        cs2_otype_45;

    // generate the address used to check top bound violation
    if (cheri_operator_i[CSEAL])
      base_chkaddr = rf_rdata_b;           // cs2.address
    else if (cheri_operator_i[CUNSEAL])
      // inCapBounds(cs2_val, zero_extend(cs1_val.otype), 1)
      base_chkaddr =  {28'h0, decode_otype(rf_fullcap_a.otype, rf_fullcap_a.perms[PERM_EX])};
    else if (cheri_operator_i[CIS_SUBSET])
      base_chkaddr = rf_fullcap_b.base32;  // cs2.base32
    else   // CLC/CSC
      base_chkaddr = cheri_ls_chkaddr;     // cs1.address + offset

    if (cheri_operator_i[CIS_SUBSET])
      top_chkaddr = rf_fullcap_b.top33;
    else if (is_cap)  // CLC/CSC
      top_chkaddr = {1'b0, base_chkaddr[31:3], 3'b000};
    else
      top_chkaddr = {1'b0, base_chkaddr};

    if (cheri_operator_i[CSEAL] | cheri_operator_i[CUNSEAL]) begin
      top_bound  = rf_fullcap_b.top33;
      base_bound = rf_fullcap_b.base32;
    end else if (is_cap) begin // CLC/CSC
      top_bound  = {rf_fullcap_a.top33[32:3], 3'b000};       // 8-byte aligned access only
      base_bound = rf_fullcap_a.base32;
    end else begin
      top_bound  = rf_fullcap_a.top33;
      base_bound = rf_fullcap_a.base32;
    end

    top_vio   = (top_chkaddr  > top_bound);
    base_vio  = (base_chkaddr < base_bound);
    top_equal = (top_chkaddr == top_bound);

    if (debug_mode_i)
      addr_bound_vio = 1'b0;
    else if (is_cap)
      addr_bound_vio = top_vio | base_vio | top_equal;
    else if (cheri_operator_i[CIS_SUBSET])
      addr_bound_vio = top_vio | base_vio;
    else if (cheri_operator_i[CSEAL] | cheri_operator_i[CUNSEAL])
      addr_bound_vio = top_vio | base_vio | top_equal;
    else
      addr_bound_vio = 1'b0;

    // main permission logic
    perm_vio_vec = 0;
    perm_vio     = 0;
    perm_vio_slc = 0;
    cs2_bad_type = 1'b0;
    illegal_scr_addr = 1'b0;

    // otype_1: forward sentry; otype_23: forward inherit sentry; otype_45: backward sentry;
    cs1_otype_0  = (rf_fullcap_a.otype == 3'h0);
    cs1_otype_1  = rf_fullcap_a.perms[PERM_EX] & (rf_fullcap_a.otype == 3'h1);  // fwd sentry
    cs1_otype_45 = rf_fullcap_a.perms[PERM_EX] & ((rf_fullcap_a.otype == 3'h4) || (rf_fullcap_a.otype == 3'h5));
    cs1_otype_23 = rf_fullcap_a.perms[PERM_EX] & ((rf_fullcap_a.otype == 3'h2) || (rf_fullcap_a.otype == 3'h3));

    cs2_otype_45 = rf_fullcap_b.perms[PERM_EX] & ((rf_fullcap_b.otype == 3'h4) || (rf_fullcap_b.otype == 3'h5));

    // note cseal/unseal/cis_subject doesn't generate exceptions,
    // so for all exceptions, violations can always be attributed to cs1, thus no need to further split
    // exceptions based on source operands.
    if (is_load_cap) begin
      perm_vio_vec[PVIO_TAG]   = ~rf_fullcap_a.valid;
      perm_vio_vec[PVIO_SEAL]  = is_cap_sealed(rf_fullcap_a);
      perm_vio_vec[PVIO_LD]    = ~(rf_fullcap_a.perms[PERM_LD]);
      perm_vio_vec[PVIO_ALIGN] = (cheri_ls_chkaddr[2:0] != 0);
    end else if (is_store_cap) begin
      perm_vio_vec[PVIO_TAG]   = (~rf_fullcap_a.valid);
      perm_vio_vec[PVIO_SEAL]  = is_cap_sealed(rf_fullcap_a);
      perm_vio_vec[PVIO_SD]    = ~rf_fullcap_a.perms[PERM_SD];
      perm_vio_vec[PVIO_SC]    = (~rf_fullcap_a.perms[PERM_MC] && rf_fullcap_b.valid);
      perm_vio_vec[PVIO_ALIGN] = (cheri_ls_chkaddr[2:0] != 0);
      perm_vio_slc             = ~rf_fullcap_a.perms[PERM_SL] && rf_fullcap_b.valid &&
                                (~rf_fullcap_b.perms[PERM_GL]) ;
    end else if (cheri_operator_i[CSEAL]) begin
      cs2_bad_type = rf_fullcap_a.perms[PERM_EX] ?
                     ((rf_rdata_b[31:3]!=0)||(rf_rdata_b[2:0]==0)) :
                     ((|rf_rdata_b[31:4]) || (rf_rdata_b[3:0] <= 8));
      // cs2.addr check : ex: 0-7, non-ex: 9-15
      perm_vio_vec[PVIO_TAG]   = ~rf_fullcap_b.valid;
      perm_vio_vec[PVIO_SEAL]  = is_cap_sealed(rf_fullcap_a) || is_cap_sealed(rf_fullcap_b) ||
                                  (~rf_fullcap_b.perms[PERM_SE]) || cs2_bad_type;
    end else if (cheri_operator_i[CUNSEAL]) begin
      perm_vio_vec[PVIO_TAG]   = ~rf_fullcap_b.valid;
      perm_vio_vec[PVIO_SEAL]  = (~is_cap_sealed(rf_fullcap_a)) || is_cap_sealed(rf_fullcap_b) ||
                                 (~rf_fullcap_b.perms[PERM_US]);
    end else if (cheri_operator_i[CJALR]) begin
      perm_vio_vec[PVIO_TAG]   = ~rf_fullcap_a.valid;
      perm_vio_vec[PVIO_SEAL]  = (is_cap_sealed(rf_fullcap_a) && (cheri_imm12_i != 0)) ||
                                 ~(((rf_waddr_i == 0) && (rf_raddr_a_i == 5'h1) && cs1_otype_45) ||
                                   ((rf_waddr_i == 0) && (rf_raddr_a_i != 5'h1) && (cs1_otype_0 || cs1_otype_1)) ||
                                   ((rf_waddr_i == 5'h1) && (cs1_otype_0 | cs1_otype_23)) ||
                                   ((rf_waddr_i != 0) && (cs1_otype_0 | cs1_otype_1)));

      perm_vio_vec[PVIO_EX]    = ~rf_fullcap_a.perms[PERM_EX];
    end else if (cheri_operator_i[CCSR_RW]) begin
      perm_vio_vec[PVIO_ASR]   = ~pcc_cap_i.perms[PERM_SR];
      illegal_scr_addr         = ~debug_mode_i & (csr_addr_o < 27);
    end else begin
      perm_vio_vec = 0;
    end

    perm_vio = | perm_vio_vec;

  end

  // qualified by lsu_req later
  // store_local error only causes tag clearing unless escalated to fault for debugging
  assign cheri_lsu_err = cheri_pmode_i & ~debug_mode_i &
                         (addr_bound_vio | perm_vio | (csr_dbg_tclr_fault_i & perm_vio_slc));

  //
  // fault case mtval generation
  // report to csr as mtval
  logic ls_addr_misaligned_only;

  assign cheri_ex_err_info_o = 12'h0;           // no ex stage cheri error currently
  assign cheri_wb_err_info_o = cheri_wb_err_info_q;

  assign cheri_wb_err_d      = cheri_wb_err_raw & cheri_exec_id_i & cheri_ex_valid_raw & ~debug_mode_i;

  // addr_bound_vio is the timing optimized version (gating data_req)
  // However we need to generate full version of addr_bound_vio to match the sail exception
  // priority definition (bound_vio has higher priority over alignment_error).
  // this has less timing impact since it goes to a flop stage
  logic addr_bound_vio_ext;
  logic [32:0] cheri_top_chkaddr_ext;

  assign cheri_top_chkaddr_ext = cheri_ls_chkaddr + 8;   // extend to 33 bit for compare
  assign addr_bound_vio_ext = is_cap ?  addr_bound_vio | (cheri_top_chkaddr_ext > rf_fullcap_a.top33) :
                              addr_bound_vio;

  always_comb begin : err_cause_comb
    cheri_err_cause  = vio_cause_enc(addr_bound_vio_ext, perm_vio_vec);
    rv32_err_cause   = vio_cause_enc(addr_bound_vio_rv32, perm_vio_vec_rv32);


    ls_addr_misaligned_only = perm_vio_vec[PVIO_ALIGN] && (perm_vio_vec[PVIO_ALIGN-1:0] == 0) && ~addr_bound_vio_ext;

    // cheri_wb_err_raw is already qualified by instr
    // bit 15:13: reserved
    // bit 12: illegal_scr_addr
    // bit 11: alignment error (load/store)
    // bit 10:0 mtval as defined by CHERIoT arch spec
    if (cheri_operator_i[CCSR_RW] & cheri_wb_err_raw & illegal_scr_addr & cheri_exec_id_i)
      // cspecialrw trap, illegal addr, treated as illegal_insn
      cheri_wb_err_info_d = {3'h0, 1'b1, 12'h0};
    else if (cheri_operator_i[CCSR_RW] & cheri_wb_err_raw & cheri_exec_id_i)
      // cspecialrw traps, PERM_SR
      cheri_wb_err_info_d = {5'h0, 1'b1, cheri_cs2_dec_i, cheri_err_cause};
    else if (cheri_wb_err_raw  & cheri_exec_id_i)
      cheri_wb_err_info_d = {5'h0, 1'b0, rf_raddr_a_i, cheri_err_cause};
    else if ((is_load_cap | is_store_cap) & cheri_lsu_err & cheri_exec_id_i)
      cheri_wb_err_info_d = {4'h0, ls_addr_misaligned_only, 1'b0, rf_raddr_a_i, cheri_err_cause};
    else if (rv32_lsu_req_i & rv32_lsu_err)
      cheri_wb_err_info_d = {5'h0, 1'b0, rf_raddr_a_i, rv32_err_cause};
    else
      cheri_wb_err_info_d = cheri_wb_err_info_q;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cheri_wb_err_q      <= 1'b0;
      cheri_wb_err_info_q <= 'h0;
    end else begin
      // Simple flop here works since
      //  -- cheri_wb_err is gated by cheri_exec_id/ex_valid
      //  --  all non-load/store cheriot instructions that can generate exceptions
      //      only takes 1 cycle in ID/EX stage
      //  -- faulted non-load/store instruction can only stay 1 cycle in wb_stage
      cheri_wb_err_q      <= cheri_wb_err_d;
      cheri_wb_err_info_q <= cheri_wb_err_info_d;
    end
  end

  //
  // muxing in cheri LSU signals with the rv32 signals
  //
  assign lsu_req_o         = (instr_is_cheri_i ? cheri_lsu_req : rv32_lsu_req_i);
  assign cpu_lsu_dec_o     = ((instr_is_cheri_i && is_cap) | instr_is_rv32lsu_i);


  assign cpu_lsu_cheri_err = instr_is_cheri_i ? cheri_lsu_err : rv32_lsu_err;
  assign cpu_lsu_addr      = instr_is_cheri_i ? cheri_lsu_addr : rv32_lsu_addr_i;
  assign cpu_lsu_we        = instr_is_cheri_i ? cheri_lsu_we : rv32_lsu_we_i;
  assign cpu_lsu_wdata     = instr_is_cheri_i ? cheri_lsu_wdata : rv32_lsu_wdata_i;
  assign cpu_lsu_is_cap    = instr_is_cheri_i & cheri_lsu_is_cap;

  // muxing tbre ctrl inputs and CPU ctrl inputs

  assign lsu_cheri_err_o   = cpu_lsu_cheri_err;
  assign lsu_we_o          = cpu_lsu_we;
  assign lsu_addr_o        = cpu_lsu_addr;
  assign lsu_wdata_o       = cpu_lsu_wdata;
  assign lsu_is_cap_o      = cpu_lsu_is_cap;

  assign lsu_lc_clrperm_o  = (instr_is_cheri_i) ? cheri_lsu_lc_clrperm : 0;
  assign lsu_type_o        = (~instr_is_cheri_i) ? rv32_lsu_type_i : 2'b00;
  assign lsu_wcap_o        = (instr_is_cheri_i) ? cheri_lsu_wcap    : NULL_REG_CAP;
  assign lsu_sign_ext_o    = (~instr_is_cheri_i) ? rv32_lsu_sign_ext_i : 1'b0;

  // rv32 core side signals
  // request phase: be nice and mux using the current EX instruction to select

  // addr_incr:
  //  -- must qualify addr_incr otherwise it goes to ALU and mess up non-LSU instructions
  //  -- however for LEC to gate this with cheri_pmode, otherwise illegal_insn will feed into addr logic
  //     since illegal_insn goes into instr_is_rv32lsu
  // assign rv32_addr_incr_req_o   = instr_is_rv32lsu_i  ?  addr_incr_req_i : 1'b0;   // original
  assign rv32_addr_incr_req_o   = (~cheri_pmode_i | instr_is_rv32lsu_i)  ?  addr_incr_req_i : 1'b0;

  assign rv32_addr_last_o       = addr_last_i;

  // req_done, resp_valid, load/store_err will be directly from LSU

  //
  // Stack high watermark CSR update
  //

  // Notes,
  //  - this should also take care of unaligned access (which increases addr only)
  //    (although stack access should not have any)
  //  - it's also ok if the prev instr gets faulted in WB, since stall_mem/data_req_allowed logic  ensures
  //    that lsu_req won't be issued till memory response/error comes back
  //  - what if the instruction gets faulted later in WB stage? Also fine since worst case even if HM is
  //    too aggressive we will just have to spend more time zeroing out more stack area.

  assign csr_mshwm_set_o = lsu_req_o & ~lsu_cheri_err_o & lsu_we_o &
                           (lsu_addr_o[31:4] >= csr_mshwmb_i[31:4]) & (lsu_addr_o[31:4] < csr_mshwm_i[31:4]);
  assign csr_mshwm_new_o = {lsu_addr_o[31:4], 4'h0};


  //
  // Stack fast clearing support
  //

  if (CheriStkZ) begin
    logic lsu_addr_in_stkz_range, stkz_stall_q;

    assign lsu_addr_in_stkz_range = cpu_lsu_dec_o && (cpu_lsu_addr[31:4] >= stkz_base_i[31:4]) &&
                                    (cpu_lsu_addr[31:2] < stkz_ptr_i[31:2]);

    // cpu_lsu_dec_o is meant to be an early hint to help LSU to generate mux selects for
    // address/ctrl/wdata (eventually to help timing on those output ports)
    // - we always suppress lsu_req if stkclr active and address-in-range (to be cleared)
    // - however in the first cycle we speculatively still assert cpu_lsu_dec_o to let LSU choose
    //   the address from cpu core (and hold back stkz/tbre_req). In the next cycle we can deassert
    //   cpu_lsu_dec_o to let stkz/tbre_req go through
    // - we also require that lsu_req (after gated by cpu_stkz_stall0) can only go from 0 to 1
    //   once in an instruction cycle. It's satisfied b/c,
    //   -- Note stkz_active_i is asserted synchronously by writing to the new stkz_ptr CSR.
    //      As such it is not possible for active to go from '0' to '1' in the middle of an
    //      load/store instruction when we want to keep lsu_req high while waiting for lsu_req_done
    //   -- Also, since the cpu_lsu_addr only increments (clc/csc/unaligned) and stkz address
    //      only decrements, if lsu_addr_in_range = 0 for the 1st word, it will stay 0 for 2nd
    //   -- Need to ensure stkz design meet those requirements
    assign cpu_stall_by_stkz_o = stkz_active_i & lsu_addr_in_stkz_range;
    assign cpu_grant_to_stkz_o  = ~instr_first_cycle_i & stkz_stall_q;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        stkz_stall_q <= 1'b0;
      end else begin
        stkz_stall_q <= stkz_active_i & lsu_addr_in_stkz_range;
      end
    end

  end else begin
    assign cpu_stall_by_stkz_o = 1'b0;
    assign cpu_grant_to_stkz_o = 1'b0;
  end

  //
  // debug signal for FPGA only
  //
  logic [15:0] dbg_status;
  logic [66:0] dbg_cs1_vec, dbg_cs2_vec, dbg_cd_vec;

  assign dbg_status = {4'h0,
                       instr_is_rv32lsu_i, rv32_lsu_req_i, rv32_lsu_we_i,  rv32_lsu_err,
                       cheri_exec_id_i, cheri_lsu_err, rf_fullcap_a.valid, result_cap_o.valid,
                       addr_bound_vio, perm_vio, addr_bound_vio_rv32, perm_vio_rv32};

  assign dbg_cs1_vec = {rf_fullcap_a.top_cor, rf_fullcap_a.base_cor, // 66:64
                        rf_fullcap_a.exp,                            // 63:59
                        rf_fullcap_a.top, rf_fullcap_a.base,         // 58:41
                        rf_fullcap_a.otype, rf_fullcap_a.cperms,     // 40:32
                        rf_rdata_a};                                 // 31:0

  assign dbg_cs2_vec = {rf_fullcap_b.top_cor, rf_fullcap_b.base_cor, // 66:64
                        rf_fullcap_b.exp,                            // 63:59
                        rf_fullcap_b.top, rf_fullcap_b.base,         // 58:41
                        rf_fullcap_b.otype, rf_fullcap_b.cperms,     // 40:32
                        rf_rdata_b};                                 // 31:0

  assign dbg_cd_vec = {result_cap_o.top_cor, result_cap_o.base_cor,  // 66:64
                        result_cap_o.exp,                            // 63:59
                        result_cap_o.top, result_cap_o.base,         // 58:41
                        result_cap_o.otype, result_cap_o.cperms,     // 40:32
                        result_data_o};                              // 31:0


endmodule
