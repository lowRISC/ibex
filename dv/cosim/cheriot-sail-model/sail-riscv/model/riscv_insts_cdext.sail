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
 * These instructions are only legal if misa[C] and misa[D]
 * are set.
 */

/* ****************************************************************** */
union clause ast = C_FLDSP : (bits(6), regidx)

mapping clause encdec_compressed = C_FLDSP(ui86 @ ui5 @ ui43, rd)
      if (sizeof(xlen) == 32 | sizeof(xlen) == 64) & haveRVC() & haveDExt()
  <-> 0b001 @ ui5 : bits(1) @ rd : regidx @ ui43 : bits(2) @ ui86 : bits(3) @ 0b10
      if (sizeof(xlen) == 32 | sizeof(xlen) == 64) & haveRVC() & haveDExt()

function clause execute (C_FLDSP(uimm, rd)) = {
  let imm : bits(12) = zero_extend(uimm @ 0b000);
  execute(LOAD_FP(imm, sp, rd, DOUBLE))
}

mapping clause assembly = C_FLDSP(uimm, rd)
      if (sizeof(xlen) == 32 | sizeof(xlen) == 64)
  <-> "c.fldsp" ^ spc() ^ reg_name(rd) ^ sep() ^ hex_bits_6(uimm)
      if (sizeof(xlen) == 32 | sizeof(xlen) == 64)

/* ****************************************************************** */
union clause ast = C_FSDSP : (bits(6), regidx)

mapping clause encdec_compressed = C_FSDSP(ui86 @ ui53, rs2)
      if (sizeof(xlen) == 32 | sizeof(xlen) == 64) & haveRVC() & haveDExt()
  <-> 0b101 @ ui53 : bits(3) @ ui86 : bits(3) @ rs2 : regidx @ 0b10
      if (sizeof(xlen) == 32 | sizeof(xlen) == 64) & haveRVC() & haveDExt()

function clause execute (C_FSDSP(uimm, rs2)) = {
  let imm : bits(12) = zero_extend(uimm @ 0b000);
  execute(STORE_FP(imm, rs2, sp, DOUBLE))
}

mapping clause assembly = C_FSDSP(uimm, rs2)
      if (sizeof(xlen) == 32 | sizeof(xlen) == 64)
  <-> "c.fsdsp" ^ spc() ^ reg_name(rs2) ^ sep() ^ hex_bits_6(uimm)
      if (sizeof(xlen) == 32 | sizeof(xlen) == 64)

/* ****************************************************************** */
union clause ast = C_FLD : (bits(5), cregidx, cregidx)

mapping clause encdec_compressed = C_FLD(ui76 @ ui53, rs1, rd)
      if (sizeof(xlen) == 32 | sizeof(xlen) == 64) & haveRVC() & haveDExt()
  <-> 0b001 @ ui53 : bits(3) @ rs1 : cregidx @ ui76 : bits(2) @ rd : cregidx @ 0b00
      if (sizeof(xlen) == 32 | sizeof(xlen) == 64) & haveRVC() & haveDExt()

function clause execute (C_FLD(uimm, rsc, rdc)) = {
  let imm : bits(12) = zero_extend(uimm @ 0b000);
  let rd = creg2reg_idx(rdc);
  let rs = creg2reg_idx(rsc);
  execute(LOAD_FP(imm, rs, rd, DOUBLE))
}

mapping clause assembly = C_FLD(uimm, rsc, rdc)
      if (sizeof(xlen) == 32 | sizeof(xlen) == 64)
  <-> "c.fld" ^ spc() ^ creg_name(rdc) ^ sep() ^ creg_name(rsc) ^ sep() ^ hex_bits_8(uimm @ 0b000)
      if (sizeof(xlen) == 32 | sizeof(xlen) == 64)

/* ****************************************************************** */
union clause ast = C_FSD : (bits(5), cregidx, cregidx)

mapping clause encdec_compressed = C_FSD(ui76 @ ui53, rs1, rs2)
      if (sizeof(xlen) == 32 | sizeof(xlen) == 64) & haveRVC() & haveDExt()
  <-> 0b101 @ ui53 : bits(3) @ rs1 : bits(3) @ ui76 : bits(2) @ rs2 : bits(3) @ 0b00
      if (sizeof(xlen) == 32 | sizeof(xlen) == 64) & haveRVC() & haveDExt()

function clause execute (C_FSD(uimm, rsc1, rsc2)) = {
  let imm : bits(12) = zero_extend(uimm @ 0b000);
  let rs1 = creg2reg_idx(rsc1);
  let rs2 = creg2reg_idx(rsc2);
  execute(STORE_FP(imm, rs2, rs1, DOUBLE))
}

mapping clause assembly = C_FSD(uimm, rsc1, rsc2)
      if (sizeof(xlen) == 32 | sizeof(xlen) == 64)
  <-> "c.fsd" ^ spc() ^ creg_name(rsc1) ^ sep() ^ creg_name(rsc2) ^ sep() ^ hex_bits_8(uimm @ 0b000)
      if (sizeof(xlen) == 32 | sizeof(xlen) == 64)
