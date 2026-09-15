/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* ********************************************************************* */
/* This file specifies the compressed floating-point instructions.
 *
 * These instructions are only legal if misa[C] and misa[F]
 * are set.
 */

/* ****************************************************************** */
union clause ast = C_FLWSP : (bits(6), regidx)

mapping clause encdec_compressed = C_FLWSP(ui76 @ ui5 @ ui42, rd)
      if sizeof(xlen) == 32 & haveRVC() & haveFExt()
  <-> 0b011 @ ui5 : bits(1) @ rd : regidx @ ui42 : bits(3) @ ui76 : bits(2) @ 0b10
      if sizeof(xlen) == 32 & haveRVC() & haveFExt()

function clause execute (C_FLWSP(imm, rd)) = {
  let imm : bits(12) = zero_extend(imm @ 0b00);
  execute(LOAD_FP(imm, sp, rd, WORD))
}

mapping clause assembly = C_FLWSP(imm, rd)
      if sizeof(xlen) == 32
  <-> "c.flwsp" ^ spc() ^ reg_name(rd) ^ sep() ^ hex_bits_6(imm)
      if sizeof(xlen) == 32

/* ****************************************************************** */
union clause ast = C_FSWSP : (bits(6), regidx)

mapping clause encdec_compressed = C_FSWSP(ui76 @ ui52, rs2)
      if sizeof(xlen) == 32 & haveRVC() & haveFExt()
  <-> 0b111 @ ui52 : bits(4) @ ui76 : bits(2) @ rs2 : regidx @ 0b10
      if sizeof(xlen) == 32 & haveRVC() & haveFExt()

function clause execute (C_FSWSP(uimm, rs2)) = {
  let imm : bits(12) = zero_extend(uimm @ 0b00);
  execute(STORE_FP(imm, rs2, sp, WORD))
}

mapping clause assembly = C_FSWSP(uimm, rs2)
      if sizeof(xlen) == 32
  <-> "c.fswsp" ^ spc() ^ reg_name(rs2) ^ sep() ^ hex_bits_6(uimm)
      if sizeof(xlen) == 32

/* ****************************************************************** */
union clause ast = C_FLW : (bits(5), cregidx, cregidx)

mapping clause encdec_compressed = C_FLW(ui6 @ ui53 @ ui2, rs1, rd)
      if sizeof(xlen) == 32 & haveRVC() & haveFExt()
  <-> 0b011 @ ui53 : bits(3) @ rs1 : cregidx @ ui2 : bits(1) @ ui6 : bits(1) @ rd : cregidx @ 0b00
      if sizeof(xlen) == 32 & haveRVC() & haveFExt()

function clause execute (C_FLW(uimm, rsc, rdc)) = {
  let imm : bits(12) = zero_extend(uimm @ 0b00);
  let rd = creg2reg_idx(rdc);
  let rs = creg2reg_idx(rsc);
  execute(LOAD_FP(imm, rs, rd, WORD))
}

mapping clause assembly = C_FLW(uimm, rsc, rdc)
      if sizeof(xlen) == 32
  <-> "c.flw" ^ spc() ^ creg_name(rdc) ^ sep() ^ creg_name(rsc) ^ sep() ^ hex_bits_7(uimm @ 0b00)
      if sizeof(xlen) == 32

/* ****************************************************************** */
union clause ast = C_FSW : (bits(5), cregidx, cregidx)

mapping clause encdec_compressed = C_FSW(ui6 @ ui53 @ ui2, rs1, rs2)
      if sizeof(xlen) == 32 & haveRVC() & haveFExt()
  <-> 0b111 @ ui53 : bits(3) @ rs1 : cregidx @ ui2 : bits(1) @ ui6 : bits(1) @ rs2 : cregidx @ 0b00
      if sizeof(xlen) == 32 & haveRVC() & haveFExt()

function clause execute (C_FSW(uimm, rsc1, rsc2)) = {
  let imm : bits(12) = zero_extend(uimm @ 0b00);
  let rs1 = creg2reg_idx(rsc1);
  let rs2 = creg2reg_idx(rsc2);
  execute(STORE_FP(imm, rs2, rs1, WORD))
}

mapping clause assembly = C_FSW(uimm, rsc1, rsc2)
      if sizeof(xlen) == 32
  <-> "c.fsw" ^ spc() ^ creg_name(rsc1) ^ sep() ^ creg_name(rsc2) ^ sep() ^ hex_bits_7(uimm @ 0b00)
      if sizeof(xlen) == 32
