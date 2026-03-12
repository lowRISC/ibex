// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package cheri_pkg;

  // bit field widths
  parameter int unsigned ADDR_W    = 32;
  parameter int unsigned TOP_W     = 9;
  parameter int unsigned TOP8_W    = 8;   // IT8 encoding only
  parameter int unsigned BOT_W     = 9;
  parameter int unsigned CEXP_W    = 4;
  parameter int unsigned CEXP5_W   = 5;   // IT8 encoding only
  parameter int unsigned EXP_W     = 5;
  parameter int unsigned OTYPE_W   = 3;
  parameter int unsigned CPERMS_W  = 6;
  parameter int unsigned PERMS_W   = 12;

  parameter int unsigned REGCAP_W  = 37;

  parameter bit    [4:0] RESETEXP  = 24;
  parameter int unsigned UPPER_W   = 24;
  parameter bit    [4:0] RESETCEXP = 15;   // only used in non-IT8 encoding

  // bit index of PERMS field
  // U0 SE US EX SR MC LD SL LM SD LG GL
  parameter int unsigned PERM_GL =  0;     // global flag
  parameter int unsigned PERM_LG =  1;     // load global
  parameter int unsigned PERM_SD =  2;     // store
  parameter int unsigned PERM_LM =  3;     // load mutable
  parameter int unsigned PERM_SL =  4;     // store local
  parameter int unsigned PERM_LD =  5;     // load
  parameter int unsigned PERM_MC =  6;     // capability load/store
  parameter int unsigned PERM_SR =  7;     // access system registes
  parameter int unsigned PERM_EX =  8;     // execution
  parameter int unsigned PERM_US =  9;     // unseal
  parameter int unsigned PERM_SE = 10;     // seal
  parameter int unsigned PERM_U0 = 11;     //

  parameter logic [2:0] OTYPE_SENTRY_IE_BKWD = 3'd5;
  parameter logic [2:0] OTYPE_SENTRY_ID_BKWD = 3'd4;
  parameter logic [2:0] OTYPE_SENTRY_IE_FWD  = 3'd3;
  parameter logic [2:0] OTYPE_SENTRY_ID_FWD  = 3'd2;
  parameter logic [2:0] OTYPE_SENTRY     = 3'd1;
  parameter logic [2:0] OTYPE_UNSEALED   = 3'd0;

  // Compressed (regFile) capability type
  typedef struct packed {
    logic                valid;
    logic [1:0]          top_cor;
    logic                base_cor;
    logic [EXP_W-1   :0] exp;    // expanded
    logic [TOP_W-1   :0] top;
    logic [BOT_W-1   :0] base;
    logic [OTYPE_W-1 :0] otype;
    logic [CPERMS_W-1:0] cperms;
    logic                rsvd;
  } reg_cap_t;

  typedef struct packed {
    logic                valid;
    logic [EXP_W-1   :0] exp;    // expanded
    logic [ADDR_W    :0] top33;
    logic [ADDR_W-1  :0] base32;
    logic [OTYPE_W-1 :0] otype;
    logic [PERMS_W-1: 0] perms;
    logic [1:0]          top_cor;
    logic                base_cor;
    logic [TOP_W-1   :0] top;
    logic [BOT_W-1   :0] base;
    logic [CPERMS_W-1:0] cperms;
    logic [31:0]         maska;
    logic                rsvd;
    logic [31:0]         rlen;
  } full_cap_t;

  typedef struct packed {
    logic                valid;
    logic [EXP_W-1   :0] exp;    // expanded
    logic [ADDR_W    :0] top33;
    logic [ADDR_W-1  :0] base32;
    logic [OTYPE_W-1 :0] otype;
    logic [PERMS_W-1: 0] perms;
    logic [CPERMS_W-1:0] cperms;
    logic                rsvd;
  } pcc_cap_t;

  typedef struct packed {
    logic [32:0]      top33req;
    logic [EXP_W-1:0] exp1;
    logic [EXP_W-1:0] exp2;
    logic [EXP_W:0]   explen;
    logic [EXP_W:0]   expb;   // this can be 32 so must be 6-bit
    logic             in_bound;
  } bound_req_t;

  parameter reg_cap_t  NULL_REG_CAP  = '{0, 0, 0, 0, 0, 0, 0, 0, 0};
  parameter full_cap_t NULL_FULL_CAP = '{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
  parameter pcc_cap_t  NULL_PCC_CAP  = '{0, 0, 0, 0, 0, 0, 0, 0};

  parameter logic [5:0] CPERMS_TX = 6'b101111;  // Tx (execution root)
  parameter logic [5:0] CPERMS_TM = 6'b111111;  // Tm (memory data root)
  parameter logic [5:0] CPERMS_TS = 6'b100111;  // Tx (seal root)

  parameter pcc_cap_t PCC_RESET_CAP   = '{1'b1, RESETEXP, 33'h10000_0000, 0, OTYPE_UNSEALED, 13'h1eb, CPERMS_TX, 1'b0};   // Tx (execution root)

  parameter reg_cap_t  MTVEC_RESET_CAP     = '{1'b1, 0, 0, RESETEXP, 9'h100, 0, OTYPE_UNSEALED, CPERMS_TX, 1'b0};   // Tx (execution root)
  parameter reg_cap_t  MTDC_RESET_CAP      = '{1'b1, 0, 0, RESETEXP, 9'h100, 0, OTYPE_UNSEALED, CPERMS_TM, 1'b0};   // Tm
  parameter reg_cap_t MEPC_RESET_CAP       = '{1'b1, 0, 0, RESETEXP, 9'h100, 0, OTYPE_UNSEALED, CPERMS_TX, 1'b0};   // Tx
  parameter reg_cap_t  MSCRATCHC_RESET_CAP = '{1'b1, 0, 0, RESETEXP, 9'h100, 0, OTYPE_UNSEALED, CPERMS_TS, 1'b0};   // Ts


  parameter logic [PERMS_W-1: 0] PERM_MC_IMSK = (1<<PERM_LD) | (1<<PERM_MC) | (1<<PERM_SD);
  parameter logic [PERMS_W-1: 0] PERM_LC_IMSK = (1<<PERM_LD) | (1<<PERM_MC);
  parameter logic [PERMS_W-1: 0] PERM_SC_IMSK = (1<<PERM_SD) | (1<<PERM_MC);
  parameter logic [PERMS_W-1: 0] PERM_DD_IMSK = 0;
  parameter logic [PERMS_W-1: 0] PERM_EX_IMSK = (1<<PERM_EX) | (1<<PERM_MC) | (1<<PERM_LD);
  parameter logic [PERMS_W-1: 0] PERM_SE_IMSK = 0;

  // expand the perms from memory representation
  function automatic logic [PERMS_W-1:0] expand_perms(logic [CPERMS_W-1:0] cperms);
    logic [PERMS_W-1:0] perms;

    perms = 0;
    perms[PERM_GL] = cperms[5];

    if (cperms[4:3] == 2'b11) begin
      perms[PERM_LG] = cperms[0];
      perms[PERM_LM] = cperms[1];
      perms[PERM_SL] = cperms[2];
      perms          = perms | PERM_MC_IMSK;
    end else if (cperms[4:2] == 3'b101) begin
      perms[PERM_LG] = cperms[0];
      perms[PERM_LM] = cperms[1];
      perms          = perms | PERM_LC_IMSK;
    end else if (cperms[4:0] == 5'b10000) begin
      perms = perms | PERM_SC_IMSK;
    end else if (cperms[4:2] == 3'b100) begin
      perms[PERM_SD] = cperms[0];
      perms[PERM_LD] = cperms[1];
      perms          = perms | PERM_DD_IMSK;
    end else if (cperms[4:3] == 2'b01) begin
      perms[PERM_LG] = cperms[0];
      perms[PERM_LM] = cperms[1];
      perms[PERM_SR] = cperms[2];
      perms          = perms | PERM_EX_IMSK;
    end else if (cperms[4:3] == 2'b00) begin
      perms[PERM_US] = cperms[0];
      perms[PERM_SE] = cperms[1];
      perms[PERM_U0] = cperms[2];
      perms          = perms | PERM_SE_IMSK;
    end

    return perms;
  endfunction

  // test the implict permission mask (any bits not 1?)
  `define TEST_IMSK(P, M) (&((P) | ~(M)))

  // compress perms field to memory representation
  function automatic logic [CPERMS_W-1:0] compress_perms (logic [PERMS_W-1:0] perms, logic [1:0] unused_qqq);   // unused_qqq is a place holder, just to compatible with the old encoding for now.
    logic [CPERMS_W-1:0] cperms;

    // test all types encoding and determine encoding (Robert's priority order)
    // Encoding explicit bits based on type
    cperms    = 0;
    cperms[5] = perms[PERM_GL];

    if (`TEST_IMSK(perms, PERM_EX_IMSK)) begin
      cperms[0]   = perms[PERM_LG];
      cperms[1]   = perms[PERM_LM];
      cperms[2]   = perms[PERM_SR];
      cperms[4:3] = 2'b01;
    end else if (`TEST_IMSK(perms, PERM_MC_IMSK)) begin
      cperms[0]   = perms[PERM_LG];
      cperms[1]   = perms[PERM_LM];
      cperms[2]   = perms[PERM_SL];
      cperms[4:3] = 2'b11;
    end else if (`TEST_IMSK(perms, PERM_LC_IMSK)) begin
      cperms[0]   = perms[PERM_LG];
      cperms[1]   = perms[PERM_LM];
      cperms[4:2] = 3'b101;
    end else if (`TEST_IMSK(perms, PERM_SC_IMSK)) begin
      cperms[4:0] = 5'b10000;
    end else if (perms[PERM_SD] | perms[PERM_LD]) begin
      cperms[0]   = perms[PERM_SD];
      cperms[1]   = perms[PERM_LD];
      cperms[4:2] = 3'b100;
    end else begin
      cperms[0]   = perms[PERM_US];
      cperms[1]   = perms[PERM_SE];
      cperms[2]   = perms[PERM_U0];
      cperms[4:3] = 2'b00;
    end

    //$display("-------compress_perms:%t: %x - %x", $time, perms, cperms);
    return cperms;
  endfunction

  // handling cperms in loaded cap based on the loading cap requirment
  function automatic logic [CPERMS_W-1:0] mask_clcperms (logic [CPERMS_W-1:0] cperms_in, logic [3:0] clrperm,
                                                   logic valid_in, logic sealed);
    logic [CPERMS_W-1:0] cperms_out;
    logic                clr_gl, clr_lg, clr_sdlm;

    clr_gl    = clrperm[0] & valid_in;
    clr_lg    = clrperm[0] & valid_in & ~sealed;
    clr_sdlm  = clrperm[1] & valid_in & ~sealed;  // only clear SD/LM if not sealed

    cperms_out    = cperms_in;
    cperms_out[5] = cperms_in[5] & ~clr_gl;         // GL

    if (cperms_in[4:3] == 2'b11) begin
      cperms_out[0] = cperms_in[0] & ~clr_lg;       // LG
      cperms_out[1] = cperms_in[1] & ~clr_sdlm;      // LM
      cperms_out[4:2] = clr_sdlm ? 3'b101 : cperms_in[4:2];
    end else if (cperms_in[4:2] == 3'b101) begin
      cperms_out[0] = cperms_in[0] & ~clr_lg;       // LG
      cperms_out[1] = cperms_in[1] & ~clr_sdlm;      // LM
    end else if (cperms_in[4:0] == 5'b10000) begin
      cperms_out[4:0] = clr_sdlm? 5'h0 : cperms_in[4:0];   // clear SD will results in NULL permission
    end else if (cperms_in[4:2] == 3'b100) begin
      cperms_out[4] = ~(clr_sdlm & ~cperms_in[1]);    // must decode to 5'h0 if both ld/sd are 0.
      cperms_out[0] = cperms_in[0] & ~clr_sdlm;
    end else if (cperms_in[4:3] == 2'b01) begin
      cperms_out[0] = cperms_in[0] & ~clr_lg;       // LG
      cperms_out[1] = cperms_in[1] & ~clr_sdlm;      // LM
    end

    return cperms_out;
  endfunction

  // caculate length (mem size) in bytes of a capability
  function automatic logic[31:0] get_cap_len (full_cap_t full_cap);
    logic [32:0] tmp33;
    logic [31:0] result;

    tmp33  = full_cap.top33 - full_cap.base32;
    result = tmp33[32]? 32'hffff_ffff: tmp33[31:0];

    return result;
  endfunction

  // obtain 32-bit representation of top
  function automatic logic[32:0] get_bound33(logic [TOP_W-1:0] top, logic [1:0]  cor,
                                           logic [EXP_W-1:0] exp, logic [31:0] addr);
    logic [32:0] t1, t2, mask, cor_val;

    if (cor[1])
      cor_val = {33{cor[1]}};         // negative sign extension
    else
      cor_val = {32'h0, (~cor[1]) & cor[0]};

    cor_val = (cor_val << exp) << TOP_W;
    mask    = (33'h1_ffff_ffff << exp) << TOP_W;

    t1 = ({1'b0, addr} & mask) + cor_val;     // apply correction and truncate
//$display("gb33: corval=%09x, mask=%09x, t1=%09x", cor_val, mask, t1);
    t2 = {24'h0, top};                         // extend to 32 bit
    t1 = t1 | (t2 << exp);

    return t1;

  endfunction

  // this implementation give slightly better timing/area results
  function automatic logic[32:0] get_bound33_trial(logic [TOP_W-1:0] top, logic [1:0]  cor,
                                             logic [EXP_W-1:0] exp, logic [31:0] addr);
    logic [32:0] t33a, t33b, result;
    logic [23:0] t24a, t24b, mask24, cor24;

    if (cor[1])
      cor24 = {24{cor[1]}};         // negative sign extension
    else
      cor24 = {23'h0, (~cor[1]) & cor[0]};

    cor24  = (cor24 << exp);
    mask24 = {24{1'b1}} << exp;

    t24a = ({1'b0, addr[31:9]} & mask24) + cor24;     // apply correction and truncate
//$display("gb33: corval=%09x, mask=%09x, t1=%09x", cor_val, mask, t1);
    t33a = {24'h0, top};
    result = {t24a, 9'h0} | (t33a << exp);

    return result;

  endfunction

  // update the top/base correction for a cap
  function automatic logic [2:0] update_temp_fields(logic [TOP_W-1:0] top, logic [BOT_W-1:0] base,
                                                    logic [BOT_W-1:0] addrmi);
    logic top_hi, addr_hi;
    logic [2:0] res3;

    top_hi   = (top < base);
    addr_hi  = (addrmi < base);

    // top_cor
    res3[2:1] = (top_hi == addr_hi)? 2'b00 : ((top_hi && (!addr_hi))? 2'b01 : 2'b11);

    // base_cor
    res3[0] = (addr_hi) ? 1 : 0;

    return res3;
  endfunction

  // set address of a capability
  //   by default we check for representability only.
  //   use checktop/checkbase to check explicitly against top33/base32 bounds (pcc updates)
  //   * note, representability check in most cases (other than exp=24) covers the base32 check

  function automatic full_cap_t set_address (full_cap_t in_cap, logic [31:0] newptr, logic chktop, logic chkbase);
    full_cap_t        out_cap;
    logic [32:0]      tmp33;
    logic [32-TOP_W:0] tmp24, mask24;
    logic  [2:0]      tmp3;
    logic [BOT_W-1:0] ptrmi9;
    logic             top_lt;

    out_cap = in_cap;
    mask24  = {(33-TOP_W){1'b1}} << in_cap.exp;          // mask24 = 0 if exp == 24

    tmp33   = {1'b0, newptr} - {1'b0, in_cap.base32};  // extend to make sure we can see carry from MSB
    tmp24   = tmp33[32:TOP_W] & mask24;
    top_lt  =  ({1'b0, newptr} < {in_cap.top33[32:1], 1'b0});

    if ((tmp24 != 0) || (chktop & ~top_lt) || (chkbase & tmp33[32]))
      out_cap.valid = 1'b0;

    ptrmi9           = BOT_W'(newptr >> in_cap.exp);
    tmp3             = update_temp_fields(out_cap.top, out_cap.base, ptrmi9);
    out_cap.top_cor  = tmp3[2:1];
    out_cap.base_cor = tmp3[0];

    return out_cap;
  endfunction

  //
  // utility functions
  //

  // return the size (bit length) of input number without leading zeros
  function automatic logic [5:0] get_size(logic [31:0] din);
    logic  [5:0] count;
    logic [31:0] a32;
    int i;

    a32 = {din[31], 31'h0};
    for (i = 30; i >=  0; i--) a32[i] = a32[i+1] | din[i];
    count = thermo_dec32(a32);

    return count;
  endfunction

  // return the exp of a 32-bit input (by count trailing zeros)
  function automatic logic [5:0] count_tz (logic [31:0] din);
    logic  [5:0] count;
    logic [31:0] a32, b32;
    int i;

    a32 = {31'h0, din[0]};
    for (i = 1; i < 32; i++) a32[i] = a32[i-1] | din[i];
    // count = a32[31] ? thermo_dec32(~a32) : 0;       // if input all zero, return 0
    count = thermo_dec32(~a32);       // if input all zero, return 32

    return count;
  endfunction

  // this simply count the number of 1's in a thermoeter-encoded input vector
  //    (32-N zeros followed by N ones)
  //
  function automatic logic [5:0] thermo_dec32(logic [31:0] a32);
    logic  [5:0] count;
    logic [31:0] b32;

    if (a32[31]) count = 32;
    else begin
      count[5] = 1'b0;
      count[4] = a32[15];
      b32[15:0] = count[4] ? a32[31:16] : a32[15:0];
      count[3] = b32[7];
      b32[ 7:0] = count[3] ? b32[15:8] : b32[7:0];
      count[2] = b32[3];
      b32[ 3:0] = count[2] ?  b32[7:4] : b32[3:0];
      count[1] = b32[1];
      b32[ 1:0] = count[1] ?  b32[3:2] : b32[1:0];
      count[0] = b32[0];
    end

    return count;
  endfunction

  // set bounds (top/base/exp/addr) of a capability

  // break up into 2 parts to enable 2-cycle option
  function automatic bound_req_t prep_bound_req (full_cap_t in_cap, logic [31:0] addr, logic [31:0] length);
    bound_req_t result;
    logic [5:0] size_result;

    result.top33req = {1'b0, addr} + {1'b0, length};    // "requested" 33-bit top
    result.expb     = count_tz(addr);
    result.explen   = get_size({9'h0, length[31:9]});        // length exp without saturation

    size_result     = result.explen;
    result.exp1     = (size_result >= 6'(RESETCEXP)) ? EXP_W'(RESETEXP) : EXP_W'(size_result);

    size_result     += 1;
    result.exp2     = (size_result >= 6'(RESETCEXP)) ? EXP_W'(RESETEXP) : EXP_W'(size_result);

    // move this to prep_bound_req to share with set_bounds_rndown
    //   should be ok to fit this in cycle 1 since it is a straight compare
    result.in_bound = ~((result.top33req > in_cap.top33) || (addr < in_cap.base32));

    return result;
  endfunction

  function automatic bound_req_t prep_bound_req_it8 (full_cap_t in_cap, logic [31:0] addr, logic [31:0] length);   // IT8 encoding
    bound_req_t result;
    logic [4:0] size_result;
    logic       gt24;
    logic [4:0] limit24_mask;

    result.top33req = {1'b0, addr} + {1'b0, length};    // "requested" 33-bit top
    result.expb     = count_tz(addr);
    result.explen   = get_size({9'h0, length[31:9]});   // length exp without saturation, max 23

    // since explen <= 23, exp1 and exp must be <= 24. No need for saturation logic
    result.exp1     = result.explen;
    result.exp2     = result.explen + 1;

    // move this to prep_bound_req to share with set_bounds_rndown
    //   should be ok to fit this in cycle 1 since it is a straight compare
    result.in_bound = ~((result.top33req > in_cap.top33) || (addr < in_cap.base32));

    return result;
  endfunction

  function automatic full_cap_t set_bounds (full_cap_t in_cap, logic[31:0] addr,
                                            bound_req_t bound_req, logic req_exact);
    full_cap_t       out_cap;

    logic [EXP_W-1:0] exp1, exp2;
    logic [32:0]      top33req;
    logic [BOT_W:0]   base1, base2, top1, top2, len1, len2;
    logic [32:0]      mask1, mask2;
    logic             ovrflw, topoff1, topoff2, topoff;
    logic             baseoff1, baseoff2, baseoff;
    logic             tophi1, tophi2, tophi;
    logic             in_bound;

    out_cap  = in_cap;

    top33req = bound_req.top33req;
    exp1     = bound_req.exp1;
    exp2     = bound_req.exp2;
    in_bound = bound_req.in_bound;

    // 1st path
    mask1    = {33{1'b1}} << exp1;
    base1    = (BOT_W+1)'(addr >> exp1);
    topoff1  = |(top33req & ~mask1);
    baseoff1 = |({1'b0, addr} & ~mask1);
    top1     = (BOT_W+1)'(top33req >> exp1) + (BOT_W+1)'(topoff1);
    len1     = top1 - base1;
    tophi1   = (top1[8:0] >= base1[8:0]);

    // overflow detection based on 1st path
    ovrflw = len1[9];

    // 2nd path in parallel
    mask2    = {33{1'b1}} << exp2;
    base2    = (BOT_W+1)'(addr >> exp2);
    topoff2  = |(top33req & ~mask2);
    baseoff2 = |({1'b0, addr} & ~mask2);
    top2     = (BOT_W+1)'(top33req >> exp2) + (BOT_W+1)'(topoff2);
    len2     = top2 - base2;
    tophi2   = (top2[8:0] >= base2[8:0]);

    // select results
    if (~ovrflw) begin
      out_cap.exp   = exp1;
      out_cap.top   = top1[TOP_W-1:0];
      out_cap.base  = base1[BOT_W-1:0];
      out_cap.maska = mask1[31:0];
      out_cap.rlen  = {22'h0, len1} << exp1;
      topoff        = topoff1;
      baseoff       = baseoff1;
      tophi         = tophi1;
    end else begin
      out_cap.exp   = exp2;
      out_cap.top   = top2[TOP_W-1:0];
      out_cap.base  = base2[BOT_W-1:0];
      out_cap.maska = mask2[31:0];
      out_cap.rlen  = {22'h0, len2} << exp2;
      topoff        = topoff2;
      baseoff       = baseoff2;
      tophi         = tophi2;
    end

`ifdef CHERI_PKG_DEBUG

$display("--- set_bounds: exact = %x, ovrflw = %x, exp1 = %x, exp2 = %x, exp = %x, len = %x", ~(topoff|baseoff), ovrflw, exp1, exp2, out_cap.exp, out_cap.rlen);
$display("--- set_bounds:  b1 = %x, t1 = %x, b2 = %x, t2 = %x", base1, top1, base2, top2);
`endif

    // top/base correction values
    //   Note the new base == addr >> exp, so addr_hi == FALSE, thus base_cor == 0
    //   as such, top_cor can only be either either 0 or +1;
    out_cap.top_cor  = tophi ? 2'b00 : 2'b01;
    out_cap.base_cor = 1'b0;

    if (req_exact & (topoff | baseoff)) out_cap.valid = 1'b0;

    // we used the "requested top" to verify the results against original bounds
    // also compare address >= old base 32 to handle exp=24 case
    //   exp = 24 case: can have addr < base (not covered by representibility checking);
    //   other exp cases: always addr >= base when out_cap.tag == 1
    if (~in_bound)
      out_cap.valid = 1'b0;

    return out_cap;
  endfunction

  function automatic full_cap_t set_bounds_rndn (full_cap_t in_cap, logic[31:0] addr,
                                                 bound_req_t bound_req);
    full_cap_t       out_cap;

    logic [EXP_W:0]  explen, expb, exp_final;
    logic [32:0]     top33req;
    logic            in_bound;
    logic            el_gt_eb, el_gt_14, eb_gt_14;
    logic            tophi;

    out_cap  = in_cap;

    top33req = bound_req.top33req;
    explen   = bound_req.explen;
    expb     = bound_req.expb;
    in_bound = bound_req.in_bound;

    el_gt_eb = (explen > expb);
    el_gt_14 = (explen > 14);
    eb_gt_14 = (expb   > 14);

    // final exp =  min(14, e_l, e_b)
    exp_final = (el_gt_eb & !eb_gt_14) ? expb : (el_gt_14 ? 14 : explen);

    // if (el_gt_eb & eb_gt_14) exp_final = 14;       //  min(14, min(e_l, e_b)), el > eb, eb > 14
    // else if (el_gt_eb)       exp_final = expb;     //  min(14, min(e_l, e_b)), el > eb, eb <= 14
    // else if (el_gt_14)       exp_final = 14;       //  min(14, min(e_l, e_b)), el <= eb, el > 14
    // else                     exp_final = explen;   //  e_l,                    el <= eb, el <= 14

    out_cap.exp  = exp_final;
    out_cap.base = (BOT_W)'(addr >> exp_final);

    out_cap.top = (el_gt_eb | el_gt_14) ? ((BOT_W)'(out_cap.base-1)) :
                                          ((BOT_W)'(top33req >> exp_final));

    if (~in_bound) out_cap.valid = 1'b0;

    // top/base correction values
    //   Note the new base == addr >> exp, so addr_hi == FALSE, thus base_cor == 0
    //   as such, top_cor can only be either either 0 or +1;
    tophi = (out_cap.top >= out_cap.base);
    out_cap.top_cor  = tophi ? 2'b00 : 2'b01;
    out_cap.base_cor = 2'b00;

    return out_cap;
  endfunction


  function automatic full_cap_t set_bounds_rndn_it8 (full_cap_t in_cap, logic[31:0] addr,         // IT8 encoding
                                                     bound_req_t bound_req);
    full_cap_t       out_cap;

    logic [EXP_W:0]  explen, expb, exp_final;
    logic [32:0]     top33req;
    logic            in_bound;
    logic            el_gt_eb;
    logic            tophi;

    out_cap  = in_cap;

    top33req = bound_req.top33req;
    explen   = bound_req.explen;
    expb     = bound_req.expb;
    in_bound = bound_req.in_bound;

    el_gt_eb = (explen > expb);

    exp_final = (el_gt_eb) ? expb :  explen;

    out_cap.exp  = exp_final;
    out_cap.base = (BOT_W)'(addr >> exp_final);

    out_cap.top = (el_gt_eb) ? ((BOT_W)'(out_cap.base-1)) : ((BOT_W)'(top33req >> exp_final));

    if (~in_bound) out_cap.valid = 1'b0;

    // top/base correction values
    //   Note the new base == addr >> exp, so addr_hi == FALSE, thus base_cor == 0
    //   as such, top_cor can only be either either 0 or +1;
    tophi = (out_cap.top >= out_cap.base);
    out_cap.top_cor  = tophi ? 2'b00 : 2'b01;
    out_cap.base_cor = 2'b00;

    return out_cap;
  endfunction



  // seal/unseal related functions
  function automatic full_cap_t seal_cap (full_cap_t in_cap, logic [OTYPE_W-1:0] new_otype);
    full_cap_t out_cap;

    out_cap = in_cap;
    out_cap.otype = new_otype;
    return out_cap;
  endfunction

  function automatic full_cap_t unseal_cap (full_cap_t in_cap);
    full_cap_t out_cap;
    out_cap = in_cap;
    out_cap.otype = OTYPE_UNSEALED;
    return out_cap;
  endfunction

  function automatic logic is_cap_sealed (full_cap_t in_cap);
    logic result;

    result = (in_cap.otype != OTYPE_UNSEALED);
    return result;
  endfunction

  //function automatic logic is_cap_sentry (full_cap_t in_cap);
  //  logic result;

  //  result = (in_cap.perms[PERM_EX]) && ((in_cap.otype == OTYPE_SENTRY) || (in_cap.otype == OTYPE_SENTRY_ID) ||
  //            (in_cap.otype == OTYPE_SENTRY_IE));
  //  return result;
  //endfunction


  function automatic logic [3:0] decode_otype (logic [2:0] otype3, logic perm_ex);
    logic [3:0] otype4;

    otype4 = {~perm_ex & (otype3 != 0), otype3};
    return otype4;
  endfunction

  // reg_cap decompression (to full_cap)
  function automatic full_cap_t reg2fullcap (reg_cap_t reg_cap, logic [31:0] addr);
    full_cap_t full_cap;

    full_cap.perms    = expand_perms(reg_cap.cperms);
    full_cap.valid    = reg_cap.valid;
    full_cap.exp      = reg_cap.exp;
    full_cap.otype    = reg_cap.otype;
    full_cap.top_cor  = reg_cap.top_cor;
    full_cap.base_cor = reg_cap.base_cor;
    full_cap.top      = reg_cap.top;
    full_cap.base     = reg_cap.base;
    full_cap.cperms   = reg_cap.cperms;
    full_cap.rsvd     = reg_cap.rsvd;

    full_cap.top33  = get_bound33(reg_cap.top, reg_cap.top_cor, reg_cap.exp, addr);
    full_cap.base32 = get_bound33(reg_cap.base, {2{reg_cap.base_cor}}, reg_cap.exp, addr);
    // full_cap  = update_bounds(full_cap, addr);   // for some reason this increases area

    full_cap.maska    = 0;
    full_cap.rlen     = 0;

    return full_cap;
  endfunction

  // full_cap compression (to reg_cap).
  //   note we don't recalculate top/base_cor here since the address/bounds of a capability
  //   won't change without an explicit instruction (only exception is PCC)
  function automatic reg_cap_t full2regcap (full_cap_t full_cap);
    reg_cap_t reg_cap;

    reg_cap          = NULL_REG_CAP;
    reg_cap.valid    = full_cap.valid;
    reg_cap.top_cor  = full_cap.top_cor;
    reg_cap.base_cor = full_cap.base_cor;
    reg_cap.exp      = full_cap.exp;
    reg_cap.top      = full_cap.top;
    reg_cap.base     = full_cap.base;
    reg_cap.cperms   = full_cap.cperms;
    reg_cap.rsvd     = full_cap.rsvd;
    reg_cap.otype    = full_cap.otype;

    return reg_cap;
  endfunction

  // pcc_cap expansion (to full_cap).
  //  -- pcc is a special case since the address (PC) moves around..
  //     so have to adjust correction factors and validate bounds here
  // function automatic full_cap_t pcc2fullcap (pcc_cap_t pcc_cap, logic [31:0] pc_addr);
  function automatic full_cap_t pcc2fullcap (pcc_cap_t in_pcap);
    full_cap_t pcc_fullcap;

    pcc_fullcap.valid    = in_pcap.valid;
    pcc_fullcap.exp      = in_pcap.exp;
    pcc_fullcap.top33    = in_pcap.top33;
    pcc_fullcap.base32   = in_pcap.base32;
    pcc_fullcap.otype    = in_pcap.otype;
    pcc_fullcap.perms    = in_pcap.perms;
    pcc_fullcap.top_cor  = 2'b0;          // will be updated by set_address()
    pcc_fullcap.base_cor = 1'b0;
    pcc_fullcap.top      = TOP_W'(in_pcap.top33  >> (in_pcap.exp));
    pcc_fullcap.base     = BOT_W'(in_pcap.base32 >> (in_pcap.exp));
    pcc_fullcap.cperms   = in_pcap.cperms;
    pcc_fullcap.maska    = 0;             // not used in pcc_cap
    pcc_fullcap.rsvd     = in_pcap.rsvd;
    pcc_fullcap.rlen     = 0;             // not used in pcc_cap

    return pcc_fullcap;
  endfunction

  // compress full_cap to pcc_cap
  function automatic pcc_cap_t full2pcap (full_cap_t full_cap);
    pcc_cap_t pcc_cap;

    pcc_cap.valid    = full_cap.valid;
    pcc_cap.exp      = full_cap.exp;
    pcc_cap.top33    = full_cap.top33;
    pcc_cap.base32   = full_cap.base32;
    pcc_cap.otype    = full_cap.otype;
    pcc_cap.perms    = full_cap.perms;
    pcc_cap.cperms   = full_cap.cperms;
    pcc_cap.rsvd     = full_cap.rsvd;

    return pcc_cap;
  endfunction

  function automatic reg_cap_t pcc2mepcc (pcc_cap_t pcc_cap, logic [31:0] address, logic clrtag);
    reg_cap_t  reg_cap;
    full_cap_t tfcap0, tfcap1;

    tfcap0  = pcc2fullcap(pcc_cap);
    // Still need representability check to cover save_pc_if and save_pc_wb cases
    tfcap1  = set_address(tfcap0, address, 0, 0);

    reg_cap = full2regcap(tfcap1);
    if (clrtag) reg_cap.valid = 1'b0;

    return reg_cap;
  endfunction

  //
  // pack/unpack the cap+addr between reg and memory
  // format 0: lsw32 = addr, msw33 = cap fields
  //
  // p’7 otype’3 E’4 B’9 T’9
  localparam integer RSVD_LO   = 31;
  localparam integer CPERMS_LO = 25;
  localparam integer OTYPE_LO  = 22;
  localparam integer CEXP_LO   = 18;
  localparam integer CEXP5_LO  = 17;   // IT8 encoding only
  localparam integer TOP_LO    = 9;
  localparam integer BASE_LO   = 0;

  // mem2reg, cap meta data, original cap bound encoding, memfmt0
  function automatic reg_cap_t mem2regcap_fmt0 (logic [32:0] msw, logic [32:0] addr33, logic [3:0] clrperm);
    reg_cap_t regcap;
    logic [EXP_W-1:0] tmp5;
    logic [2:0]  tmp3;
    logic [CPERMS_W-1:0] cperms_mem;
    logic [BOT_W-1:0]    addrmi9;
    logic                sealed;
    logic                valid_in;

    valid_in      = msw[32] & addr33[32];
    regcap.valid  = valid_in & ~clrperm[3];

    tmp5 = {1'b0, msw[CEXP_LO+:CEXP_W]};
    if (tmp5 == EXP_W'(RESETCEXP)) tmp5 = RESETEXP;
    regcap.exp = tmp5;

    regcap.top    = msw[TOP_LO+:TOP_W];
    regcap.base   = msw[BASE_LO+:BOT_W];
    regcap.otype  = msw[OTYPE_LO+:OTYPE_W];

    sealed = (regcap.otype != OTYPE_UNSEALED);
    cperms_mem      = msw[CPERMS_LO+:CPERMS_W];
    regcap.cperms   = mask_clcperms(cperms_mem, clrperm, regcap.valid, sealed);
    addrmi9         = BOT_W'({1'b0, addr33[31:0]} >> regcap.exp); // ignore the tag valid bit
    tmp3            = update_temp_fields(regcap.top, regcap.base, addrmi9);
    regcap.top_cor  = tmp3[2:1];
    regcap.base_cor = tmp3[0];

    regcap.rsvd     = msw[RSVD_LO];

    return regcap;

  endfunction

  // mem2reg, cap meta data, IT8 encoding, memfmt0
  function automatic reg_cap_t mem2regcap_it8_fmt0 (logic [32:0] msw, logic [32:0] addr33, logic [3:0] clrperm);   // IT8
    reg_cap_t regcap;
    logic [EXP_W-1:0] cexp;
    logic [TOP_W-2:0] top8, base8;
    logic [TOP_W-1:0] top9, base9;
    logic             denorm, ltop, btop, ttop, tcin;
    logic             top_hi, addr_hi;
    logic [2:0]       res3;

    logic [CPERMS_W-1:0] cperms_mem;
    logic [BOT_W-1:0]    addrmi9;
    logic                sealed;
    logic                valid_in;

    valid_in      = msw[32] & addr33[32];
    regcap.valid  = valid_in & ~clrperm[3];

    cexp          = msw[CEXP5_LO+:CEXP5_W];
    denorm        = (cexp == 0);

    btop          = msw[BASE_LO+BOT_W-1];
    base8         = msw[BASE_LO+:(BOT_W-1)];
    top8          = msw[TOP_LO+:(TOP_W-1)];

    tcin          = (top8 < base8);           // can actually merge it with t_hi in update_temp_fields QQQ
    ltop          = ~denorm;
    ttop          = ltop ^ tcin ^ btop;

    regcap.exp    = cexp ^ {5{~denorm}};      // this is the ^0b11111 part
    top9          = {ttop, top8};
    base9         = {btop, base8};
    regcap.top    = top9;
    regcap.base   = base9;

    regcap.otype  = msw[OTYPE_LO+:OTYPE_W];

    sealed = (regcap.otype != OTYPE_UNSEALED);
    cperms_mem      = msw[CPERMS_LO+:CPERMS_W];
    regcap.cperms   = mask_clcperms(cperms_mem, clrperm, regcap.valid, sealed);
    addrmi9         = BOT_W'({1'b0, addr33[31:0]} >> regcap.exp); // ignore the tag valid bit

    // update temp fields
    // tmp3            = update_temp_fields(regcap.top, regcap.base, addrmi9);
    // top_hi   = (top < base);
    top_hi   = (btop ^ ttop) ? ~ttop : tcin;
    addr_hi  = (addrmi9 < base9);

    regcap.top_cor  = (top_hi == addr_hi)? 2'b00 : ((top_hi && (!addr_hi))? 2'b01 : 2'b11);
    regcap.base_cor = (addr_hi) ? 1'b1 : 1'b0;

    regcap.rsvd     = msw[RSVD_LO];

    return regcap;

  endfunction

  // reg to mem, meta data, original cap bound encoding, memfmt0
  function automatic logic[32:0] reg2memcap_fmt0 (reg_cap_t regcap);

    logic [32:0] msw;

    msw[32] = regcap.valid ;

    msw[CEXP_LO+:CEXP_W]     = (regcap.exp == RESETEXP) ? RESETCEXP : regcap.exp[CEXP_W-1:0];
    msw[TOP_LO+:TOP_W]       = regcap.top   ;
    msw[BASE_LO+:BOT_W]      = regcap.base  ;
    msw[OTYPE_LO+:OTYPE_W]   = regcap.otype ;
    msw[CPERMS_LO+:CPERMS_W] = regcap.cperms;
    msw[RSVD_LO]             = regcap.rsvd;

    return msw;

  endfunction

  // reg to mem, meta data, IT8 encoding, memfmt0
  function automatic logic[32:0] reg2memcap_it8_fmt0 (reg_cap_t regcap);         // IT8

    logic [32:0] msw;
    logic        denorm, ltop, cor;
    logic  [9:0] top10, base10, len10;

    cor    = (regcap.top_cor == {2{regcap.base_cor}});
    top10  = {~cor, regcap.top};
    base10 = {1'b0, regcap.base};
    len10  = top10 - base10;
    ltop   = len10[9] | len10[8];

    denorm = (regcap.exp == 0) && ~ltop;

    msw[32] = regcap.valid;

    msw[CEXP5_LO+:CEXP5_W]   = regcap.exp ^ {5{~denorm}};
    msw[TOP_LO+:(TOP_W-1)]   = regcap.top[7:0];
    msw[BASE_LO+:BOT_W]      = regcap.base  ;
    msw[OTYPE_LO+:OTYPE_W]   = regcap.otype ;
    msw[CPERMS_LO+:CPERMS_W] = regcap.cperms;
    msw[RSVD_LO]             = regcap.rsvd;

    return msw;

  endfunction

  //
  // pack/unpack the cap+addr between reg and memory
  // format 1: lsw32 = RSVD+EXP+T+B+A9, msw32 = CPERMS+OTYPE+A23
  //

  // mem to reg, meta data, original cap bound encoding, memfmt1
  function automatic reg_cap_t mem2regcap_fmt1 (logic [32:0] msw, logic [32:0] lsw, logic [3:0] clrperm);
    reg_cap_t regcap;
    logic [2:0]  tmp3;
    logic        sealed;
    logic [8:0]  addrmi9;
    logic [CPERMS_W-1:0] cperms_mem;
    logic        valid_in;

    // lsw is now EXP+B+T+A
    valid_in      = msw[32] & lsw[32];
    regcap.valid  = valid_in & ~clrperm[3];
    regcap.exp    = (lsw[30:27] == RESETCEXP) ?  RESETEXP : {1'b0, lsw[30:27]};
    regcap.base   = lsw[26:18];
    regcap.top    = lsw[17:9];
    addrmi9       = (lsw[30:27] == RESETCEXP) ? {1'b0, lsw[8:1]} : lsw[8:0];

    regcap.otype  = msw[25:23];
    sealed        = (regcap.otype != OTYPE_UNSEALED);

    // cperms_mem = {lsw[31], msw[31:26]};
    cperms_mem    = msw[31:26];
    regcap.cperms = mask_clcperms(cperms_mem, clrperm, regcap.valid, sealed);
    regcap.rsvd   = lsw[31];

    tmp3 = update_temp_fields(regcap.top, regcap.base, addrmi9);
    regcap.top_cor  = tmp3[2:1];
    regcap.base_cor = tmp3[0];

    return regcap;

  endfunction


  // mem to reg, meta data, IT8 encoding, memfmt1
  function automatic reg_cap_t mem2regcap_it8_fmt1 (logic [32:0] msw, logic [32:0] lsw, logic [3:0] clrperm);   // xyz
    reg_cap_t regcap;
    logic [EXP_W-1:0] cexp;
    logic [TOP_W-2:0] top8, base8;
    logic [TOP_W-1:0] top9, base9;
    logic             denorm, ltop, btop, ttop, tcin;
    logic             top_hi, addr_hi;
    logic [2:0]       res3;

    logic        sealed;
    logic [8:0]  addrmi9;
    logic [CPERMS_W-1:0] cperms_mem;
    logic        valid_in;


    // lsw is now EXP+T+B+A
    valid_in      = msw[32] & lsw[32];
    regcap.valid  = valid_in & ~clrperm[3];

    cexp          = lsw[30:26];
    denorm        = (cexp == 0);

    btop          = lsw[17];
    base8         = lsw[16:9];
    top8          = lsw[25:18];

    tcin          = (top8 < base8);           // can actually merge it with t_hi in update_temp_fields QQQ
    ltop          = ~denorm;
    ttop          = ltop ^ tcin ^ btop;

    regcap.exp    = cexp ^ {5{~denorm}};      // this is the ^0b11111 part
    top9          = {ttop, top8};
    base9         = {btop, base8};
    regcap.top    = top9;
    regcap.base   = base9;

    // (regcap.exp >= RESETEXP);
    addrmi9       = (regcap.exp[4] & regcap.exp[3]) ? {1'b0, lsw[8:1]} : lsw[8:0];

    regcap.otype  = msw[25:23];
    sealed        = (regcap.otype != OTYPE_UNSEALED);

    // cperms_mem = {lsw[31], msw[31:26]};
    cperms_mem    = msw[31:26];
    regcap.cperms = mask_clcperms(cperms_mem, clrperm, regcap.valid, sealed);
    regcap.rsvd   = lsw[31];

    // tmp3 = update_temp_fields(regcap.top, regcap.base, addrmi9);
    top_hi   = (btop ^ ttop) ? ~ttop : tcin;
    addr_hi  = (addrmi9 < base9);

    regcap.top_cor  = (top_hi == addr_hi)? 2'b00 : ((top_hi && (!addr_hi))? 2'b01 : 2'b11);
    regcap.base_cor = (addr_hi) ? 1'b1 : 1'b0;

    return regcap;

  endfunction

  // mem to reg, addr32, both original and IT8 encoding, memfmt1
  function automatic logic[32:0] mem2regaddr_fmt1 (logic [32:0] msw, logic [32:0] lsw, reg_cap_t regcap);    // xyz
    logic [32:0] addr33;
    logic [31:0] addrmi, addrhi, addrlo;
    logic [31:0] mask1, mask2;

    // (regcap.exp >= RESETEXP)
    if (regcap.exp[4] & regcap.exp[3]) begin
      addrhi   = 32'h0;
      addrmi   = {lsw[8:0], 23'h0};
      addrlo   = {9'h0, msw[22:0]};
    end else begin
      addrmi   = {23'h0, lsw[8:0]} << regcap.exp;
      mask1    = {32{1'b1}} << regcap.exp;
      mask2    = mask1 << 9;
      addrhi   = ({9'h0, msw[22:0]} << 9) & mask2;
      addrlo   = {9'h0, msw[22:0]} & (~mask1);
    end

    addr33 = {lsw[32], addrhi | addrmi | addrlo};

    return addr33;
  endfunction

  // reg to mem, original cap bound encoding, memfmt1
  function automatic logic[65:0] reg2mem_fmt1 (reg_cap_t reg_cap, logic[31:0] addr);

    logic [32:0] msw, lsw;
    logic [31:0] mask1, mask2;

    msw[32]    = reg_cap.valid;
    msw[31:26] = reg_cap.cperms[5:0];
    msw[25:23] = reg_cap.otype;
    lsw[32]    = reg_cap.valid ;
    lsw[31]    = reg_cap.rsvd;
    lsw[26:18] = reg_cap.base;
    lsw[17:9]  = reg_cap.top;

    if (reg_cap.exp == RESETEXP) begin
      msw[22:0]  = addr[22:0];
      lsw[30:27] = RESETCEXP;
      lsw[8:0]   = addr[31:23];
    end else begin
      mask1    = {32{1'b1}} << reg_cap.exp;
      mask2    = mask1 << 9;

      msw[22:0]  = 23'((addr & ~mask1) | ((addr & mask2) >> 9));
      lsw[30:27] = reg_cap.exp[CEXP_W-1:0];
      lsw[8:0]   = 9'(addr >> reg_cap.exp);
    end

    return {msw, lsw};

  endfunction

  // reg to mem, IT8 encoding, memfmt1
  function automatic logic[65:0] reg2mem_it8_fmt1 (reg_cap_t regcap, logic[31:0] addr);        // xyz

    logic [32:0] msw, lsw;
    logic [31:0] mask1, mask2;
    logic        denorm, ltop, cor;
    logic  [9:0] top10, base10, len10;

    cor    = (regcap.top_cor == {2{regcap.base_cor}});
    top10  = {~cor, regcap.top};
    base10 = {1'b0, regcap.base};
    len10  = top10-base10;
    ltop   = len10[9] | len10[8];

    denorm = (regcap.exp == 0) && ~ltop;

    msw[32]    = regcap.valid;
    msw[31:26] = regcap.cperms[5:0];
    msw[25:23] = regcap.otype;
    lsw[32]    = regcap.valid ;
    lsw[31]    = regcap.rsvd;
    lsw[30:26] = regcap.exp ^ {5{~denorm}} ;
    lsw[25:18] = regcap.top[7:0];
    lsw[17:9]  = regcap.base;

    // (regcap.exp >= RESETEXP)
    if (regcap.exp[4] & regcap.exp[3]) begin
      msw[22:0]  = addr[22:0];
      lsw[8:0]   = addr[31:23];
    end else begin
      mask1    = {32{1'b1}} << regcap.exp;
      mask2    = mask1 << 9;
      msw[22:0]  = 23'((addr & ~mask1) | ((addr & mask2) >> 9));
      lsw[8:0]   = 9'(addr >> regcap.exp);
    end

    return {msw, lsw};

  endfunction

  // simply cast regcap to a 38-bit vector
  // (different from the mem format, here we keep all regcap fields including corrections, exp and top9)
  // we can do this with systemverilog casting but let's be explicit here
  function automatic logic [REGCAP_W-1:0] reg2vec (reg_cap_t regcap);

    logic [REGCAP_W-1:0] vec_out;

    vec_out[REGCAP_W-1]  = regcap.valid ;
    vec_out[34+:2]       = regcap.top_cor;
    vec_out[33+:1]       = regcap.base_cor;
    vec_out[28+:EXP_W]   = regcap.exp;
    vec_out[19+:TOP_W]   = regcap.top   ;
    vec_out[10+:BOT_W]   = regcap.base  ;
    vec_out[7+:OTYPE_W]  = regcap.otype ;
    vec_out[6+:1]        = regcap.rsvd;
    vec_out[0+:CPERMS_W] = regcap.cperms;

    return vec_out;
  endfunction

  function automatic reg_cap_t vec2reg (logic [REGCAP_W-1:0] vec_in);

    reg_cap_t regcap;

    regcap.valid    = vec_in[REGCAP_W-1];
    regcap.top_cor  = vec_in[34+:2];
    regcap.base_cor = vec_in[33+:1];
    regcap.exp      = vec_in[28+:EXP_W];
    regcap.top      = vec_in[19+:TOP_W];
    regcap.base     = vec_in[10+:BOT_W];
    regcap.otype    = vec_in[7+:OTYPE_W];
    regcap.rsvd     = vec_in[6+:1];
    regcap.cperms   = vec_in[0+:CPERMS_W];

    return regcap;
  endfunction

  // test whether 2 caps are equal
  function automatic logic is_equal (full_cap_t cap_a, full_cap_t cap_b,
                                     logic [31:0] addra, logic[31:0] addrb);

    is_equal =  (cap_a.valid  == cap_b.valid) &&
                (cap_a.top  == cap_b.top) && (cap_a.base == cap_b.base) &&
                (cap_a.cperms  == cap_b.cperms) && (cap_a.rsvd == cap_b.rsvd) &&
                (cap_a.exp    == cap_b.exp) && (cap_a.otype  == cap_b.otype) &&
                (addra == addrb);
    return is_equal;

  endfunction

  // clear tag of a regcap if needed, otherwise simply pass through
  function automatic reg_cap_t and_regcap_tag (reg_cap_t in_cap, logic tag_mask);
    reg_cap_t out_cap;

    out_cap = in_cap;
    out_cap.valid = in_cap.valid & tag_mask;
    return out_cap;

  endfunction

  // parameters and constants

  parameter logic[6:0] CHERI_INSTR_OPCODE = 7'h5b;
  parameter int OPDW = 36;      // Must >= number of cheri operator/instructions we support

  typedef enum logic [5:0] {
    CGET_PERM        = 6'h00,
    CGET_TYPE        = 6'h01,
    CGET_BASE        = 6'h02,
    CGET_LEN         = 6'h03,
    CGET_TAG         = 6'h04,
    CGET_TOP         = 6'h05,
    CGET_HIGH        = 6'h06,
    CGET_ADDR        = 6'h07,
    CSEAL            = 6'h08,
    CUNSEAL          = 6'h09,
    CAND_PERM        = 6'h0a,
    CSET_ADDR        = 6'h0b,
    CINC_ADDR        = 6'h0c,
    CINC_ADDR_IMM    = 6'h0d,
    CSET_BOUNDS      = 6'h0e,
    CSET_BOUNDS_EX   = 6'h0f,
    CSET_BOUNDS_IMM  = 6'h10,
    CIS_SUBSET       = 6'h11,
    CIS_EQUAL        = 6'h12,
    CMOVE_CAP        = 6'h13,
    CSUB_CAP         = 6'h14,
    CCLEAR_TAG       = 6'h15,
    CLOAD_CAP        = 6'h16,
    CSET_HIGH        = 6'h17,
    CSTORE_CAP       = 6'h18,
    CCSR_RW          = 6'h19,
    CJALR            = 6'h1a,
    CJAL             = 6'h1b,
    CAUIPCC          = 6'h1c,
    CAUICGP          = 6'h1d,
    CRRL             = 6'h1e,
    CRAM             = 6'h1f,
    CSET_BOUNDS_RNDN = 6'h20
  } cheri_op_e;

  typedef enum logic [4:0] {
    CHERI_CSR_NULL,
    CHERI_CSR_RW
  } cheri_csr_op_e;

  parameter logic [4:0] CHERI_SCR_MEPCC      = 5'd31;
  parameter logic [4:0] CHERI_SCR_MSCRATCHC  = 5'd30;
  parameter logic [4:0] CHERI_SCR_MTDC       = 5'd29;
  parameter logic [4:0] CHERI_SCR_MTCC       = 5'd28;
  parameter logic [4:0] CHERI_SCR_ZTOPC      = 5'd27;
  parameter logic [4:0] CHERI_SCR_DSCRATCHC1 = 5'd26;
  parameter logic [4:0] CHERI_SCR_DSCRATCHC0 = 5'd25;
  parameter logic [4:0] CHERI_SCR_DEPCC      = 5'd24;

  // permission violations
  parameter int unsigned W_PVIO = 8;

  parameter logic [2:0] PVIO_TAG   = 3'h0;
  parameter logic [2:0] PVIO_SEAL  = 3'h1;
  parameter logic [2:0] PVIO_EX    = 3'h2;
  parameter logic [2:0] PVIO_LD    = 3'h3;
  parameter logic [2:0] PVIO_SD    = 3'h4;
  parameter logic [2:0] PVIO_SC    = 3'h5;
  parameter logic [2:0] PVIO_ASR   = 3'h6;
  parameter logic [2:0] PVIO_ALIGN = 3'h7;


  function automatic logic [4:0] vio_cause_enc (logic bound_vio, logic[W_PVIO-1:0] perm_vio_vec);
    logic [4:0] vio_cause;

    if (perm_vio_vec[PVIO_TAG])
      vio_cause = 5'h2;
    else if (perm_vio_vec[PVIO_SEAL])
      vio_cause = 5'h3;
    else if (perm_vio_vec[PVIO_EX])
      vio_cause = 5'h11;
    else if (perm_vio_vec[PVIO_LD])
      vio_cause = 5'h12;
    else if (perm_vio_vec[PVIO_SD])
      vio_cause = 5'h13;
    else if (perm_vio_vec[PVIO_SC])
      vio_cause = 5'h15;
    else if (perm_vio_vec[PVIO_ASR])
      vio_cause = 5'h18;
    else if (bound_vio)
      vio_cause = 5'h1;
    else
      vio_cause = 5'h0;

    return vio_cause;
  endfunction

endpackage
