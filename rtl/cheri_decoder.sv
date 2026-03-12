// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Cheri instruction decoder
// should we merge this with cheri_EX? let's leave it alone for now since we may look into
// a separate decoder PL stage later

module cheri_decoder import cheri_pkg::*; # (
  parameter bit CheriPPLBC = 1'b1,
  parameter bit CheriSBND2 = 1'b0
) (
  input  logic [31:0]     instr_rdata_i,
  input  logic            cheri_opcode_en_i,       // op = 0x5b
  input  logic            cheri_tsafe_en_i,
  input  logic            cheri_auipcc_en_i,        // op = 0x17 (AUIPC)
  input  logic            cheri_auicgp_en_i,        // op = 0x7b (AUIGCP)
  input  logic            cheri_jalr_en_i,          // op = 0x67 (JALR)
  input  logic            cheri_jal_en_i,           // op = 0x6f (JAL)
  input  logic            cheri_cload_en_i,         // op = 0x3, [14:12] = 0x3 (LD)
  input  logic            cheri_cstore_en_i,        // op = 0x23, [14:12] = 0x3 (SD)
  output logic            instr_is_cheri_o,         // instr in cheri space
  output logic            instr_is_legal_cheri_o,   // legal cheri instruction
  output logic [11:0]     cheri_imm12_o,
  output logic [19:0]     cheri_imm20_o,
  output logic [20:0]     cheri_imm21_o,
  output logic [OPDW-1:0] cheri_operator_o,
  output logic  [4:0]     cheri_cs2_dec_o,
  output logic            cheri_rf_ren_a_o,
  output logic            cheri_rf_ren_b_o,
  output logic            cheri_rf_we_dec_o,
  output logic            cheri_multicycle_dec_o
  );

  logic  [6:0] unused_opcode;
  logic  [2:0] func3_op;
  logic  [6:0] func7_op;
  logic  [4:0] imm5_op;
  logic  [4:0] rd_op;

  // note there are 3 encoding formats of CHERI instructions
  //  - fmt1: I-format, func3(14:12) = subFuc.
  //  - fmt2: R-format, func3(14:12) = 0x0, func7(31:25) = subFunc, etc.
  //  - fmt3: I-format, func3(14:12) = 0x0, func7(31:25) = 0x7f, imm5(24:20) = subFunc
  //  - opcode [6:0] == 0x5b for all CHERI instructions
  assign unused_opcode = instr_rdata_i[6:0];
  assign func3_op      = instr_rdata_i[14:12];
  assign func7_op      = instr_rdata_i[31:25];
  assign imm5_op       = instr_rdata_i[24:20];
  assign rd_op         = instr_rdata_i[11:7];

  always_comb begin
    cheri_operator_o = OPDW'('h0);

    cheri_operator_o[CCSR_RW]         = cheri_opcode_en_i && (func3_op==0) && (func7_op==7'h01);
    cheri_operator_o[CSET_BOUNDS]     = cheri_opcode_en_i && (func3_op==0) && (func7_op==7'h08);
    cheri_operator_o[CSET_BOUNDS_EX]  = cheri_opcode_en_i && (func3_op==0) && (func7_op==7'h09);
    cheri_operator_o[CSET_BOUNDS_RNDN]= cheri_opcode_en_i && (func3_op==0) && (func7_op==7'h0a);
    cheri_operator_o[CSEAL]           = cheri_opcode_en_i && (func3_op==0) && (func7_op==7'h0b);
    cheri_operator_o[CUNSEAL]         = cheri_opcode_en_i && (func3_op==0) && (func7_op==7'h0c);
    cheri_operator_o[CAND_PERM]       = cheri_opcode_en_i && (func3_op==0) && (func7_op==7'h0d);
    cheri_operator_o[CSET_ADDR]       = cheri_opcode_en_i && (func3_op==0) && (func7_op==7'h10);
    cheri_operator_o[CINC_ADDR]       = cheri_opcode_en_i && (func3_op==0) && (func7_op==7'h11);
    cheri_operator_o[CSUB_CAP]        = cheri_opcode_en_i && (func3_op==0) && (func7_op==7'h14);
    cheri_operator_o[CSET_HIGH]       = cheri_opcode_en_i && (func3_op==0) && (func7_op==7'h16);
    cheri_operator_o[CIS_SUBSET]      = cheri_opcode_en_i && (func3_op==0) && (func7_op==7'h20);
    cheri_operator_o[CIS_EQUAL]       = cheri_opcode_en_i && (func3_op==0) && (func7_op==7'h21);


    cheri_operator_o[CGET_PERM]       = cheri_opcode_en_i && (func3_op==0) && (func7_op==7'h7f) && (imm5_op==5'h00);
    cheri_operator_o[CGET_TYPE]       = cheri_opcode_en_i && (func3_op==0) && (func7_op==7'h7f) && (imm5_op==5'h01);
    cheri_operator_o[CGET_BASE]       = cheri_opcode_en_i && (func3_op==0) && (func7_op==7'h7f) && (imm5_op==5'h02);
    cheri_operator_o[CGET_HIGH]        = cheri_opcode_en_i && (func3_op==0) && (func7_op==7'h7f) && (imm5_op==5'h17);
    cheri_operator_o[CGET_TOP]        = cheri_opcode_en_i && (func3_op==0) && (func7_op==7'h7f) && (imm5_op==5'h18);
    cheri_operator_o[CGET_LEN]        = cheri_opcode_en_i && (func3_op==0) && (func7_op==7'h7f) && (imm5_op==5'h03);
    cheri_operator_o[CGET_TAG]        = cheri_opcode_en_i && (func3_op==0) && (func7_op==7'h7f) && (imm5_op==5'h04);
    cheri_operator_o[CRRL]            = cheri_opcode_en_i && (func3_op==0) && (func7_op==7'h7f) && (imm5_op==5'h08);
    cheri_operator_o[CRAM]            = cheri_opcode_en_i && (func3_op==0) && (func7_op==7'h7f) && (imm5_op==5'h09);
    cheri_operator_o[CGET_ADDR]       = cheri_opcode_en_i && (func3_op==0) && (func7_op==7'h7f) && (imm5_op==5'h0f);
    cheri_operator_o[CMOVE_CAP]       = cheri_opcode_en_i && (func3_op==0) && (func7_op==7'h7f) && (imm5_op==5'h0a);
    cheri_operator_o[CCLEAR_TAG]      = cheri_opcode_en_i && (func3_op==0) && (func7_op==7'h7f) && (imm5_op==5'h0b);

    cheri_operator_o[CINC_ADDR_IMM]   = cheri_opcode_en_i && (func3_op == 1);
    cheri_operator_o[CSET_BOUNDS_IMM] = cheri_opcode_en_i && (func3_op == 2);


    cheri_operator_o[CAUIPCC]         = cheri_auipcc_en_i;
    cheri_operator_o[CAUICGP]         = cheri_auicgp_en_i;
    cheri_operator_o[CJALR]           = cheri_jalr_en_i;
    cheri_operator_o[CJAL]            = cheri_jal_en_i;
    cheri_operator_o[CLOAD_CAP]       = cheri_cload_en_i;
    // cheri_operator_o[CLBC]            = cheri_cload_en_i & ~func3_op[2] & cheri_tsafe_en_i;
    cheri_operator_o[CSTORE_CAP]      = cheri_cstore_en_i;
  end

  // partially decoded, early signal to control muxing and regfile read
  assign instr_is_cheri_o       = cheri_opcode_en_i | cheri_jalr_en_i | cheri_jal_en_i |
                                  cheri_auipcc_en_i | cheri_auicgp_en_i | cheri_cload_en_i | cheri_cstore_en_i;

  assign instr_is_legal_cheri_o = |cheri_operator_o;

  assign cheri_cs2_dec_o  = cheri_operator_o[CCSR_RW] ? imm5_op : 0;

  assign cheri_imm12_o    = (cheri_operator_o[CJALR]|cheri_operator_o[CSET_BOUNDS_IMM]|
                             cheri_operator_o[CINC_ADDR_IMM]|cheri_operator_o[CLOAD_CAP]) ?
                            {func7_op, imm5_op}:(cheri_operator_o[CSTORE_CAP]?{func7_op, rd_op}:0);

  assign cheri_imm20_o    = (cheri_operator_o[CAUIPCC]|cheri_operator_o[CAUICGP])  ? instr_rdata_i[31:12] : 0;

  assign cheri_imm21_o    = cheri_operator_o[CJAL]  ? {instr_rdata_i[31], instr_rdata_i[19:12],
                                                       instr_rdata_i[20], instr_rdata_i[30:21], 1'b0} : 0;

  // register dependency decoding (ren_a, ren_b, we)
  // only handled opcode=0x5b case here.
  // Will be qualified and combined with other cases by ibexc_decoder
  assign cheri_rf_ren_a_o = 1'b1;
  assign cheri_rf_ren_b_o = (func3_op == 0) && (func7_op != 7'h7f) && (func7_op !=7'h01);

  // cheri_rf_we_dec_o is not used to generate the actual regfile write enables in the case of
  // cheri instructions (which is in cheri_ex and  muxed with rf_we in wb_stage).
  // However it is merged into the overall rf_we and used to generate stall_cheri_trvk
  assign cheri_rf_we_dec_o = cheri_opcode_en_i & (|cheri_operator_o);

  assign cheri_multicycle_dec_o = (cheri_operator_o[CLOAD_CAP] & cheri_tsafe_en_i & ~CheriPPLBC) |
                                  (CheriSBND2 & (cheri_operator_o[CSET_BOUNDS] |
                                   cheri_operator_o[CSET_BOUNDS_IMM] |
                                   cheri_operator_o[CSET_BOUNDS_EX] |
                                   cheri_operator_o[CRRL] | cheri_operator_o[CRAM]));

endmodule
