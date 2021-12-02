// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Zk Extension unit: An implemenation for the RISC-V Cryptography Extension.
 */
module ibex_zk #(
  parameter ibex_pkg::rv32zk_e RV32Zk = ibex_pkg::RV32ZkNone
) (
  input  ibex_pkg::alu_op_e operator_i,
  input  logic [31:0]       operand_a_i,
  input  logic [31:0]       operand_b_i,

  output logic [31:0]       result_o,
  output logic              zk_val_o
);
  import ibex_pkg::*;
`define RORI32(a,b) ((a >> b) | (a << 32-b))
`define ROLI32(a,b) ((a << b) | (a >> 32-b))
`define SRLI32(a,b) ((a >> b)              )
`define SLLI32(a,b) ((a << b)              )

// 32-bit Barrel Right Rotation
function automatic logic [31:0] ror32(logic [31:0] x, logic [4:0] amt);
    logic [31:0] ro, l8, l4, l2, l1, l0;
    assign l0 = x;
    assign l1 = ({32{amt[0]}} & {l0[   0], l0[31: 1]}) | ({32{!amt[0]}} & l0[31:0]);
    assign l2 = ({32{amt[1]}} & {l1[ 1:0], l1[31: 2]}) | ({32{!amt[1]}} & l1[31:0]);
    assign l4 = ({32{amt[2]}} & {l2[ 3:0], l2[31: 4]}) | ({32{!amt[2]}} & l2[31:0]);
    assign l8 = ({32{amt[3]}} & {l4[ 7:0], l4[31: 8]}) | ({32{!amt[3]}} & l4[31:0]);
    assign ro = ({32{amt[4]}} & {l8[15:0], l8[31:16]}) | ({32{!amt[4]}} & l8[31:0]);
    return ro;
endfunction

// 32-bit Barrel Left Rotation
function automatic logic [31:0] rol32(logic [31:0] x, logic [4:0] amt);
    logic [31:0] ro, l8, l4, l2, l1, l0;
    assign l0 = x;
    assign l1 = ({32{amt[0]}} & {l0[30:0], l0[31   ]}) | ({32{!amt[0]}} & l0[31:0]);
    assign l2 = ({32{amt[1]}} & {l1[29:0], l1[31:30]}) | ({32{!amt[1]}} & l1[31:0]);
    assign l4 = ({32{amt[2]}} & {l2[27:0], l2[31:28]}) | ({32{!amt[2]}} & l2[31:0]);
    assign l8 = ({32{amt[3]}} & {l4[23:0], l4[31:24]}) | ({32{!amt[3]}} & l4[31:0]);
    assign ro = ({32{amt[4]}} & {l8[15:0], l8[31:16]}) | ({32{!amt[4]}} & l8[31:0]);
    return ro;
endfunction

// reverse 8 bits
function automatic logic [7:0] rev8(logic [7:0] x);
    logic [7:0]  rb;
    for (int i = 0;  i < 8; i = i + 1) begin
        assign rb[i] = x[8-i-1];
    end
    return rb;
endfunction

// 32-bit Zip
function automatic logic [31:0] zip32(logic [31:0] x);
    logic [31:0] uz;
    for (int i = 0;  i < 16; i = i + 1) begin
        assign uz[2*i  ] = x[i];
        assign uz[2*i+1] = x[i+16];
    end
    return uz;
endfunction

// 32-bit UnZip
function automatic logic [31:0] unzip32(logic [31:0] x);
    logic [15:0] zh, zl;
    for (int i = 0;  i < 16; i = i + 1) begin
        assign zh[i] = x[2*i + 1];
        assign zl[i] = x[2*i    ];
    end
    return {zh, zl};
endfunction


// Multiply by 2 in GF(2^8) modulo 8'h1b
function automatic logic [7:0] xtime2(logic [7:0] a);
    logic [7:0] xtime2;
    xtime2  = {a[6:0],1'b0} ^ (a[7] ? 8'h1b : 8'b0 );
    return xtime2;
endfunction

// Paired down multiply by X in GF(2^8)
function automatic logic [7:0] xtimeN(logic [7:0] a, logic [3:0] b);
    logic [7:0] xtimeN;
    xtimeN = (b[0] ?                      a   : 0) ^
             (b[1] ? xtime2(              a)  : 0) ^
             (b[2] ? xtime2(xtime2(       a)) : 0) ^
             (b[3] ? xtime2(xtime2(xtime2(a))): 0) ;
    return xtimeN;
endfunction

  logic        zkb_val;
  logic [31:0] zkb_result;
  if (RV32Zk != RV32ZkNone) begin : gen_zkb
    logic ror_sel, rol_sel, rori_sel, andn_sel, orn_sel, xnor_sel;
    logic pack_sel, packh_sel, brev8_sel, rev8_sel, zip_sel, unzip_sel;
    logic clmull_sel, clmulh_sel, xperm8_sel, xperm4_sel;
    assign    ror_sel = (operator_i == ZKB_ROR);
    assign    rol_sel = (operator_i == ZKB_ROL);
    assign   rori_sel = (operator_i == ZKB_RORI);
    assign   andn_sel = (operator_i == ZKB_ANDN);
    assign    orn_sel = (operator_i == ZKB_ORN);
    assign   xnor_sel = (operator_i == ZKB_XNOR);
    assign   pack_sel = (operator_i == ZKB_PACK);
    assign  packh_sel = (operator_i == ZKB_PACKH);
    assign  brev8_sel = (operator_i == ZKB_BREV8);
    assign   rev8_sel = (operator_i == ZKB_REV8);
    assign    zip_sel = (operator_i == ZKB_ZIP);
    assign  unzip_sel = (operator_i == ZKB_UNZIP);
    assign clmull_sel = (operator_i == ZKB_CLMUL );
    assign clmulh_sel = (operator_i == ZKB_CLMULH);
    assign xperm8_sel = (operator_i == ZKB_XPERM8);
    assign xperm4_sel = (operator_i == ZKB_XPERM4);

    logic [ 4:0] shamt;
    assign shamt  = operand_b_i[4:0];

    logic [31:0] wror, wrol, wandn, worn, wxnor, wpack, wpackh;
    assign wror   = ror32(operand_a_i, shamt);
    assign wrol   = rol32(operand_a_i, shamt);
    assign wandn  = operand_a_i & (~operand_b_i);
    assign worn   = operand_a_i | (~operand_b_i);
    assign wxnor  = operand_a_i ^ (~operand_b_i);
    assign wpack  = {       operand_b_i[15:0], operand_a_i[15:0]};
    assign wpackh = {16'd0, operand_b_i[ 7:0], operand_a_i[ 7:0]};

    logic [ 7:0] rs1_b0, rs1_b1, rs1_b2, rs1_b3;
    assign rs1_b0  = operand_a_i[ 7: 0];
    assign rs1_b1  = operand_a_i[15: 8];
    assign rs1_b2  = operand_a_i[23:16];
    assign rs1_b3  = operand_a_i[31:24];

    logic [ 7:0] brev8_0, brev8_1, brev8_2, brev8_3;
    assign brev8_0 = rev8(rs1_b0);
    assign brev8_1 = rev8(rs1_b1);
    assign brev8_2 = rev8(rs1_b2);
    assign brev8_3 = rev8(rs1_b3);

    logic [31:0] wbrev8, wrev8;
    assign wbrev8  = {brev8_3, brev8_2, brev8_1, brev8_0};
    assign wrev8   = {rs1_b0,  rs1_b1,  rs1_b2,  rs1_b3};

    logic [31:0] wzip, wunzip;
    assign wzip   = zip32(  operand_a_i);
    assign wunzip = unzip32(operand_a_i);

    // Xperm instructions
    // indexable access 4-bit LUT.
    logic [ 3:0] lut_4b [8];
    logic [31:0] wxperm4;
    for(genvar i = 0; i < 8; i = i + 1) begin : gen_lut_xperm4
      // generate table.
      assign lut_4b[i] = operand_a_i[4*i+:4];

      logic [2:0] lut_8idx;
      assign lut_8idx   = operand_b_i[4*i+:3];

      logic [3:0] lut4_out;
      assign lut4_out = lut_4b[lut_8idx];
      assign wxperm4[i*4+:4]  = operand_b_i[4*i+3] ? 4'b0000 : lut4_out;
    end

   // indexable access 8-bit LUT.
    logic [ 7:0] lut_8b [4];
    logic [31:0] wxperm8;
    for(genvar i = 0; i < 4; i = i + 1) begin : gen_lut_xperm8
      // generate table.
      assign lut_8b[i] = operand_a_i[8*i+:8];

      logic [1:0] lut_4idx;
      assign lut_4idx   = operand_b_i[8*i+:2];

      logic [7:0] lut8_out;
      assign lut8_out = lut_8b[lut_4idx];
      assign wxperm8[i*8+:8]  = |{operand_b_i[8*i+7:8*i+2]} ? 8'd0 : lut8_out;
    end

    // clmul instructions
    logic [15:0] lhs0, rhs0, lhs1, rhs1, lhs2, rhs2;
    assign lhs0 = clmulh_sel? operand_a_i[31:16] : operand_a_i[15: 0];
    assign rhs0 = clmulh_sel? operand_b_i[31:16] : operand_b_i[15: 0];

    assign lhs1 = operand_a_i[15: 0];
    assign rhs1 = operand_b_i[31:16];

    assign lhs2 = operand_a_i[31:16];
    assign rhs2 = operand_b_i[15: 0];

    logic [31:0]  polymul0, polymul1, polymul2;
    ibex_poly16_mul mul16_ins0(.a(lhs0), .b(rhs0), .r(polymul0));
    ibex_poly16_mul mul16_ins1(.a(lhs1), .b(rhs1), .r(polymul1));
    ibex_poly16_mul mul16_ins2(.a(lhs2), .b(rhs2), .r(polymul2));

    logic [31:0] wclmull, wclmulh, clmulm;
    assign clmulm  = polymul1 ^ polymul2;
    assign wclmulh = {polymul0[31:16], (polymul0[15: 0] ^ clmulm[31:16])                 };
    assign wclmull = {                 (polymul0[31:16] ^ clmulm[15: 0]), polymul0[15: 0]};

    assign zkb_val    = |{ror_sel, rol_sel, rori_sel, andn_sel, orn_sel, xnor_sel,
                          pack_sel, packh_sel, brev8_sel, rev8_sel, zip_sel, unzip_sel,
                          clmull_sel, clmulh_sel, xperm8_sel, xperm4_sel};
    assign zkb_result = {32{   ror_sel}} & wror    |
                        {32{   rol_sel}} & wrol    |
                        {32{  rori_sel}} & wror    |
                        {32{  andn_sel}} & wandn   |
                        {32{   orn_sel}} & worn    |
                        {32{  xnor_sel}} & wxnor   |
                        {32{  pack_sel}} & wpack   |
                        {32{ packh_sel}} & wpackh  |
                        {32{ brev8_sel}} & wbrev8  |
                        {32{  rev8_sel}} & wrev8   |
                        {32{   zip_sel}} & wzip    |
                        {32{ unzip_sel}} & wunzip  |
                        {32{clmull_sel}} & wclmull |
                        {32{clmulh_sel}} & wclmulh |
                        {32{xperm8_sel}} & wxperm8 |
                        {32{xperm4_sel}} & wxperm4 ;
  end else begin : gen_no_zkb
    assign zkb_val    =  1'b0;
    assign zkb_result = 32'd0;
  end

  logic        zkn_val;
  logic [31:0] zkn_result;

  if (RV32Zk == RV32Zkn) begin : gen_zkn
    logic bs0, bs1, bs2, bs3; //byte select in aes instructions
    assign bs0 = (operator_i == ZKN_AES32DSB0) || (operator_i == ZKN_AES32DSMB0) ||
                 (operator_i == ZKN_AES32ESB0) || (operator_i == ZKN_AES32ESMB0) ;
    assign bs1 = (operator_i == ZKN_AES32DSB1) || (operator_i == ZKN_AES32DSMB1) ||
                 (operator_i == ZKN_AES32ESB1) || (operator_i == ZKN_AES32ESMB1) ;
    assign bs2 = (operator_i == ZKN_AES32DSB2) || (operator_i == ZKN_AES32DSMB2) ||
                 (operator_i == ZKN_AES32ESB2) || (operator_i == ZKN_AES32ESMB2) ;
    assign bs3 = (operator_i == ZKN_AES32DSB3) || (operator_i == ZKN_AES32DSMB3) ||
                 (operator_i == ZKN_AES32ESB3) || (operator_i == ZKN_AES32ESMB3) ;

    logic decs_sel, encs_sel, decsm_sel, encsm_sel; //operation select in aes instructions
    assign decs_sel  = (operator_i == ZKN_AES32DSB0)  || (operator_i == ZKN_AES32DSB1)  ||
                       (operator_i == ZKN_AES32DSB2)  || (operator_i == ZKN_AES32DSB3)  ;
    assign encs_sel  = (operator_i == ZKN_AES32ESB0)  || (operator_i == ZKN_AES32ESB1)  ||
                       (operator_i == ZKN_AES32ESB2)  || (operator_i == ZKN_AES32ESB3)  ;
    assign decsm_sel = (operator_i == ZKN_AES32DSMB0) || (operator_i == ZKN_AES32DSMB1) ||
                       (operator_i == ZKN_AES32DSMB2) || (operator_i == ZKN_AES32DSMB3) ;
    assign encsm_sel = (operator_i == ZKN_AES32ESMB0) || (operator_i == ZKN_AES32ESMB1) ||
                       (operator_i == ZKN_AES32ESMB2) || (operator_i == ZKN_AES32ESMB3) ;
    logic  aes32_sel;
    assign aes32_sel = decs_sel || encs_sel || encsm_sel || decsm_sel;

    logic  [7:0] sel_byte;
    assign       sel_byte = {8{bs0}} & operand_b_i[ 7: 0] |
                            {8{bs1}} & operand_b_i[15: 8] |
                            {8{bs2}} & operand_b_i[23:16] |
                            {8{bs3}} & operand_b_i[31:24] ;

    logic  dec, mix;
    assign dec      = decs_sel  || decsm_sel  ;
    assign mix      = encsm_sel || decsm_sel  ;

    logic [7:0] sbox_out;
    // SBOX instances
    ibex_aes_sbox  i_aes_sbox(
        .fw (~dec            ),
        .in (sel_byte    ),
        .fx (sbox_out)
    );

    logic [7:0] mix_b0, mix_b1, mix_b2, mix_b3;
    assign mix_b3 =       xtimeN(sbox_out, (dec ? 11  : 3))            ;
    assign mix_b2 = dec ? xtimeN(sbox_out, (           13)) : sbox_out ;
    assign mix_b1 = dec ? xtimeN(sbox_out, (            9)) : sbox_out ;
    assign mix_b0 =       xtimeN(sbox_out, (dec ? 14  : 2))            ;

    logic [31:0] mixed, sbox_mix, rotated;
    assign mixed    = {mix_b3, mix_b2, mix_b1, mix_b0};
    assign sbox_mix = mix ? mixed : {24'b0, sbox_out};
    assign rotated  = {32{bs0}} & {sbox_mix                        } |
                      {32{bs1}} & {sbox_mix[23:0], sbox_mix[31:24] } |
                      {32{bs2}} & {sbox_mix[15:0], sbox_mix[31:16] } |
                      {32{bs3}} & {sbox_mix[ 7:0], sbox_mix[31: 8] } ;

    // sha2 instructions
    logic  sha256_sum0_sel, sha256_sum1_sel, sha256_sig0_sel, sha256_sig1_sel;
    assign sha256_sum0_sel  = (operator_i == ZKN_SHA256SUM0);
    assign sha256_sum1_sel  = (operator_i == ZKN_SHA256SUM1);
    assign sha256_sig0_sel  = (operator_i == ZKN_SHA256SIG0);
    assign sha256_sig1_sel  = (operator_i == ZKN_SHA256SIG1);

    logic  sha512_sum0r_sel, sha512_sum1r_sel;
    logic  sha512_sig0l_sel, sha512_sig1l_sel;
    logic  sha512_sig0h_sel, sha512_sig1h_sel;
    assign sha512_sum0r_sel = (operator_i == ZKN_SHA512SUM0R);
    assign sha512_sum1r_sel = (operator_i == ZKN_SHA512SUM1R);
    assign sha512_sig0l_sel = (operator_i == ZKN_SHA512SIG0L);
    assign sha512_sig0h_sel = (operator_i == ZKN_SHA512SIG0H);
    assign sha512_sig1l_sel = (operator_i == ZKN_SHA512SIG1L);
    assign sha512_sig1h_sel = (operator_i == ZKN_SHA512SIG1H);


    logic[31:0]  sha256_sum0, sha256_sum1, sha256_sig0, sha256_sig1;
    assign sha256_sig0 = `RORI32(operand_a_i, 7) ^ `RORI32(operand_a_i,18) ^
                         `SRLI32(operand_a_i, 3);
    assign sha256_sig1 = `RORI32(operand_a_i,17) ^ `RORI32(operand_a_i,19) ^
                         `SRLI32(operand_a_i,10);
    assign sha256_sum0 = `RORI32(operand_a_i, 2) ^ `RORI32(operand_a_i,13) ^
                         `RORI32(operand_a_i,22);
    assign sha256_sum1 = `RORI32(operand_a_i, 6) ^ `RORI32(operand_a_i,11) ^
                         `RORI32(operand_a_i,25);

    logic[31:0]  sha512_sum0r, sha512_sum1r;
    logic[31:0]  sha512_sig0l, sha512_sig1l;
    logic[31:0]  sha512_sig0h, sha512_sig1h;
    assign sha512_sum0r = `SLLI32(operand_a_i,25)^`SLLI32(operand_a_i,30)^`SRLI32(operand_a_i,28)^
                          `SRLI32(operand_b_i, 7)^`SRLI32(operand_b_i, 2)^`SLLI32(operand_b_i, 4);
    assign sha512_sum1r = `SLLI32(operand_a_i,23)^`SRLI32(operand_a_i,14)^`SRLI32(operand_a_i,18)^
                          `SRLI32(operand_b_i, 9)^`SLLI32(operand_b_i,18)^`SLLI32(operand_b_i,14);
    assign sha512_sig0l = `SRLI32(operand_a_i, 1)^`SRLI32(operand_a_i, 7)^`SRLI32(operand_a_i, 8)^
                          `SLLI32(operand_b_i,31)^`SLLI32(operand_b_i,25)^`SLLI32(operand_b_i,24);
    assign sha512_sig0h = `SRLI32(operand_a_i, 1)^`SRLI32(operand_a_i, 7)^`SRLI32(operand_a_i, 8)^
                          `SLLI32(operand_b_i,31)                        ^`SLLI32(operand_b_i,24);
    assign sha512_sig1l = `SLLI32(operand_a_i, 3)^`SRLI32(operand_a_i, 6)^`SRLI32(operand_a_i,19)^
                          `SRLI32(operand_b_i,29)^`SLLI32(operand_b_i,26)^`SLLI32(operand_b_i,13);
    assign sha512_sig1h = `SLLI32(operand_a_i, 3)^`SRLI32(operand_a_i, 6)^`SRLI32(operand_a_i,19)^
                          `SRLI32(operand_b_i,29)                        ^`SLLI32(operand_b_i,13);

    assign zkn_val      = |{sha256_sum0_sel, sha256_sum1_sel, sha256_sig0_sel, sha256_sig1_sel,
                           sha512_sum0r_sel, sha512_sum1r_sel,
                           sha512_sig0l_sel, sha512_sig1l_sel,
                           sha512_sig0h_sel, sha512_sig1h_sel, aes32_sel};
    assign zkn_result   = {32{aes32_sel       }} & (rotated ^ operand_a_i) |
                          {32{sha256_sig0_sel }} & sha256_sig0  |
                          {32{sha256_sig1_sel }} & sha256_sig1  |
                          {32{sha256_sum0_sel }} & sha256_sum0  |
                          {32{sha256_sum1_sel }} & sha256_sum1  |
                          {32{sha512_sum0r_sel}} & sha512_sum0r |
                          {32{sha512_sum1r_sel}} & sha512_sum1r |
                          {32{sha512_sig0l_sel}} & sha512_sig0l |
                          {32{sha512_sig0h_sel}} & sha512_sig0h |
                          {32{sha512_sig1l_sel}} & sha512_sig1l |
                          {32{sha512_sig1h_sel}} & sha512_sig1h ;
  end else begin : gen_no_zkn
    assign zkn_val    =  1'b0;
    assign zkn_result = 32'd0;
  end

  logic        zks_val;
  logic [31:0] zks_result;
  if (RV32Zk == RV32Zks) begin : gen_zks
    logic  sm4ed_sel, sm4ks_sel, sm3p0_sel, sm3p1_sel;
    assign sm4ed_sel = (operator_i == ZKS_SM4EDB0) || (operator_i == ZKS_SM4EDB2) ||
                       (operator_i == ZKS_SM4EDB1) || (operator_i == ZKS_SM4EDB3) ;
    assign sm4ks_sel = (operator_i == ZKS_SM4KSB0) || (operator_i == ZKS_SM4KSB2) ||
                       (operator_i == ZKS_SM4KSB1) || (operator_i == ZKS_SM4KSB3) ;
    assign sm3p0_sel = (operator_i == ZKS_SM3P0);
    assign sm3p1_sel = (operator_i == ZKS_SM3P1);

    logic zks_bs0, zks_bs1, zks_bs2, zks_bs3; //byte select in aes instructions
    assign zks_bs0 = (operator_i == ZKS_SM4EDB0) || (operator_i == ZKS_SM4KSB0) ;
    assign zks_bs1 = (operator_i == ZKS_SM4EDB1) || (operator_i == ZKS_SM4KSB1) ;
    assign zks_bs2 = (operator_i == ZKS_SM4EDB2) || (operator_i == ZKS_SM4KSB2) ;
    assign zks_bs3 = (operator_i == ZKS_SM4EDB3) || (operator_i == ZKS_SM4KSB3) ;
    logic  [7:0] sbox_in;
    assign       sbox_in = {8{zks_bs0}} & operand_b_i[ 7: 0] |
                           {8{zks_bs1}} & operand_b_i[15: 8] |
                           {8{zks_bs2}} & operand_b_i[23:16] |
                           {8{zks_bs3}} & operand_b_i[31:24] ;
    logic [ 7:0] sm4_sbox_out;
    // Submodule - SBox
    ibex_sm4_sbox ism4_sbox (
      .in (sbox_in),
      .fx (sm4_sbox_out)
    );

    logic [31:0] s;
    assign s     = {24'b0, sm4_sbox_out};

    // ED Instruction
    logic [31:0] ed1, ed2;
    assign ed1   = s   ^  (s           <<  8) ^ (s << 2) ^ (s << 18);
    assign ed2   = ed1 ^ ((s & 32'h3F) << 26) ^ ((s & 32'hC0) << 10);

    // KS Instruction
    logic [31:0] ks1, ks2;
    assign ks1   = s   ^ ((s & 32'h07) << 29) ^ ((s & 32'hFE) <<  7);
    assign ks2   = ks1 ^ ((s & 32'h01) << 23) ^ ((s & 32'hF8) << 13);

    // Rotate and XOR result
    logic [31:0] rot_in, rot_out, sm4;
    assign rot_in  = sm4ks_sel ? ks2 : ed2;
    assign rot_out = {32{zks_bs0}} & {rot_in                      } |
                     {32{zks_bs1}} & {rot_in[23:0], rot_in[31:24] } |
                     {32{zks_bs2}} & {rot_in[15:0], rot_in[31:16] } |
                     {32{zks_bs3}} & {rot_in[ 7:0], rot_in[31: 8] } ;
    assign sm4     = rot_out ^ operand_a_i ;

    logic [31:0] sm3_p0, sm3_p1;
    assign sm3_p0  = operand_a_i ^ `ROLI32(operand_a_i,  9) ^ `ROLI32(operand_a_i,17);
    assign sm3_p1  = operand_a_i ^ `ROLI32(operand_a_i, 15) ^ `ROLI32(operand_a_i,23);

    assign zks_val    =|{sm4ed_sel, sm4ks_sel, sm3p0_sel, sm3p1_sel};
    assign zks_result = {32{sm4ed_sel}} & sm4    |
                        {32{sm4ks_sel}} & sm4    |
                        {32{sm3p0_sel}} & sm3_p0 |
                        {32{sm3p1_sel}} & sm3_p1 ;
  end else begin : gen_no_zks
    assign zks_val    =  1'b0;
    assign zks_result = 32'd0;
  end

  assign zk_val_o = zkb_val   || zkn_val   || zks_val;
  assign result_o = zkb_result | zkn_result | zks_result;

`undef RORI32
`undef ROLI32
`undef SRLI32
`undef SLLI32

endmodule
