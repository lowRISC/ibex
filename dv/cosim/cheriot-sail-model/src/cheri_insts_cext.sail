/*=======================================================================================*/
/*  CHERI RISCV Sail Model                                                               */
/*                                                                                       */
/*  This CHERI Sail RISC-V architecture model here, comprising all files and             */
/*  directories except for the snapshots of the Lem and Sail libraries in the            */
/*  prover_snapshots directory (which include copies of their licenses), is subject      */
/*  to the BSD two-clause licence below.                                                 */
/*                                                                                       */
/*  Copyright (c) 2017-2021                                                              */
/*    Alasdair Armstrong                                                                 */
/*    Thomas Bauereiss                                                                   */
/*    Brian Campbell                                                                     */
/*    Jessica Clarke                                                                     */
/*    Nathaniel Wesley Filardo (contributions prior to July 2020, thereafter Microsoft)  */
/*    Alexandre Joannou                                                                  */
/*    Microsoft                                                                          */
/*    Prashanth Mundkur                                                                  */
/*    Robert Norton-Wright (contributions prior to March 2020, thereafter Microsoft)     */
/*    Alexander Richardson                                                               */
/*    Peter Rugg                                                                         */
/*    Peter Sewell                                                                       */
/*                                                                                       */
/*  All rights reserved.                                                                 */
/*                                                                                       */
/*  This software was developed by SRI International and the University of               */
/*  Cambridge Computer Laboratory (Department of Computer Science and                    */
/*  Technology) under DARPA/AFRL contract FA8650-18-C-7809 ("CIFV"), and                 */
/*  under DARPA contract HR0011-18-C-0016 ("ECATS") as part of the DARPA                 */
/*  SSITH research programme.                                                            */
/*                                                                                       */
/*  This software was developed within the Rigorous Engineering of                       */
/*  Mainstream Systems (REMS) project, partly funded by EPSRC grant                      */
/*  EP/K008528/1, at the Universities of Cambridge and Edinburgh.                        */
/*                                                                                       */
/*  This project has received funding from the European Research Council                 */
/*  (ERC) under the European Union’s Horizon 2020 research and innovation                */
/*  programme (grant agreement 789108, ELVER).                                           */
/*                                                                                       */
/*  Redistribution and use in source and binary forms, with or without                   */
/*  modification, are permitted provided that the following conditions                   */
/*  are met:                                                                             */
/*  1. Redistributions of source code must retain the above copyright                    */
/*     notice, this list of conditions and the following disclaimer.                     */
/*  2. Redistributions in binary form must reproduce the above copyright                 */
/*     notice, this list of conditions and the following disclaimer in                   */
/*     the documentation and/or other materials provided with the                        */
/*     distribution.                                                                     */
/*                                                                                       */
/*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''                   */
/*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED                    */
/*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A                      */
/*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR                  */
/*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,                         */
/*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT                     */
/*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF                     */
/*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND                  */
/*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,                   */
/*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT                   */
/*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF                   */
/*  SUCH DAMAGE.                                                                         */
/*=======================================================================================*/

/* Compressed capability loads/stores (encodings differ between RV32/RV64) */
union clause ast = C_CLC : (cregidx, cregidx, bits(9))

mapping clause encdec_compressed_capmode = C_CLC(cdc, csc1, ui8 @ ui76 @ ui54 @ 0b0000) if sizeof(xlen) == 64
  <-> 0b001 @ ui54 : bits(2) @ ui8 : bits(1) @ csc1 : cregidx @ ui76 : bits(2) @ cdc : cregidx @ 0b00 if sizeof(xlen) == 64
mapping clause encdec_compressed_capmode = C_CLC(cdc, csc1, 0b0 @ ui76 @ ui53 @ 0b000) if sizeof(xlen) == 32
  <-> 0b011 @ ui53 : bits(3) @ csc1 : cregidx @ ui76 : bits(2) @ cdc : cregidx @ 0b00 if sizeof(xlen) == 32
mapping clause assembly = C_CLC(cdc, csc1, uimm)
  <-> "c.clc" ^ spc() ^ cap_creg_name(cdc) ^ sep() ^ cap_creg_name(csc1) ^ sep() ^ hex_bits_9(uimm)

/*!
 * Compressed 16-bit encoding for [CLC][LoadCapImm].
 *
 * ## Notes
 *
 * - This instruction is only available in capability encoding mode.
 * - For RV32 this replaces the encoding of [C.FLW], RV64 uses [C.FLD].
 */
function clause execute(C_CLC(cdc, csc1, uimm)) = {
  let cd = creg2reg_idx(cdc) in
  let cs1 = creg2reg_idx(csc1) in
  execute(LoadCapImm(cd, cs1, zero_extend(uimm)))
}

union clause ast = C_CLCSP : (regidx, bits(10))

mapping clause encdec_compressed_capmode = C_CLCSP(cd, ui96 @ ui5 @ ui4 @ 0b0000) if sizeof(xlen) == 64 & cd != zeros()
  <-> 0b001 @ ui5 : bits(1) @ cd : regidx @ ui4 : bits(1) @ ui96 : bits(4) @ 0b10 if sizeof(xlen) == 64 & cd != zeros()
mapping clause encdec_compressed_capmode = C_CLCSP(cd, 0b0 @ ui86 @ ui5 @ ui43 @ 0b000) if sizeof(xlen) == 32 & cd != zeros()
  <-> 0b011 @ ui5 : bits(1) @ cd : regidx @ ui43 : bits(2) @ ui86 : bits(3) @ 0b10 if sizeof(xlen) == 32 & cd != zeros()
mapping clause assembly = C_CLCSP(cd, uimm)
  <-> "c.clcsp" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ hex_bits_10(uimm)

/*!
 * Compressed 16-bit encoding for a stack-pointer-relative [CLC][LoadCapImm].
 *
 * ## Notes
 *
 * - This instruction is only available in capability encoding mode.
 * - For RV32 this replaces the encoding of [C.FLWSP], RV64 uses [C.FLDSP].
 * - The encoding with `cd == 0` is reserved and will raise an illegal
 *   instruction trap.
 */
function clause execute(C_CLCSP(cd, uimm)) =
  execute(LoadCapImm(cd, sp, zero_extend(uimm)))

/*
 * The c.clcsp encoding with cd == 0 should raise an illegal instruction trap
 * instead of falling back to the non-capmode (legal) instruction
 * `c.flwsp/fldsp f0` so we need an explicit capmode illegal match clause.
 */
mapping clause encdec_compressed_capmode = C_ILLEGAL(0b001 @ ui5 @ 0b00000 @ ui4 @ ui96 @ 0b10) if sizeof(xlen) == 64
  <-> 0b001 @ ui5 : bits(1) @ 0b00000 @ ui4 : bits(1) @ ui96 : bits(4) @ 0b10 if sizeof(xlen) == 64
mapping clause encdec_compressed_capmode = C_ILLEGAL(0b011 @ ui5 @ 0b00000 @ ui43 @ ui86 @ 0b10) if sizeof(xlen) == 32
  <-> 0b011 @ ui5 : bits(1) @ 0b00000 @ ui43 : bits(2) @ ui86 : bits(3) @ 0b10 if sizeof(xlen) == 32

union clause ast = C_CSC : (cregidx, cregidx, bits(9))

mapping clause encdec_compressed_capmode = C_CSC(csc2, csc1, ui8 @ ui76 @ ui54 @ 0b0000) if sizeof(xlen) == 64
  <-> 0b101 @ ui54 : bits(2) @ ui8 : bits(1) @ csc1 : bits(3) @ ui76 : bits(2) @ csc2 : bits(3) @ 0b00 if sizeof(xlen) == 64
mapping clause encdec_compressed_capmode = C_CSC(csc2, csc1, 0b0 @ ui76 @ ui53 @ 0b000) if sizeof(xlen) == 32
  <-> 0b111 @ ui53 : bits(3) @ csc1 : bits(3) @ ui76 : bits(2) @ csc2 : bits(3) @ 0b00 if sizeof(xlen) == 32
mapping clause assembly = C_CSC(csc2, csc1, uimm)
  <-> "c.csc" ^ spc() ^ cap_creg_name(csc2) ^ sep() ^ cap_creg_name(csc1) ^ sep() ^ hex_bits_9(uimm)

/*!
 * Compressed 16-bit encoding for [CSC][StoreCapImm].
 *
 * ## Notes
 *
 * - This instruction is only available in capability encoding mode.
 * - For RV32 this replaces the encoding of [C.FSW], RV64 uses [C.FSD].
 */
function clause execute(C_CSC(csc2, csc1, uimm)) = {
  let cs2 = creg2reg_idx(csc2) in
  let cs1 = creg2reg_idx(csc1) in
  execute(StoreCapImm(cs2, cs1, zero_extend(uimm)))
}

union clause ast = C_CSCSP : (regidx, bits(10))

mapping clause encdec_compressed_capmode = C_CSCSP(cs2, ui96 @ ui54 @ 0b0000) if sizeof(xlen) == 64
  <-> 0b101 @ ui54 : bits(2) @ ui96 : bits(4) @ cs2 : regidx @ 0b10 if sizeof(xlen) == 64
mapping clause encdec_compressed_capmode = C_CSCSP(cs2, 0b0 @ ui86 @ ui53 @ 0b000) if sizeof(xlen) == 32
  <-> 0b111 @ ui53 : bits(3) @ ui86 : bits(3) @ cs2 : regidx @ 0b10 if sizeof(xlen) == 32
mapping clause assembly = C_CSCSP(cs2, uimm)
  <-> "c.cscsp" ^ spc() ^ cap_reg_name(cs2) ^ sep() ^ hex_bits_10(uimm)

/*!
 * Compressed 16-bit encoding for a stack-pointer-relative [CSC][StoreCapImm].
 *
 * ## Notes
 *
 * - This instruction is only available in capability encoding mode.
 * - For RV32 this replaces the encoding of [C.FSWSP], RV64 uses [C.FSDSP].
 */
function clause execute(C_CSCSP(cs2, uimm)) =
  execute(StoreCapImm(cs2, sp, zero_extend(uimm)))

/* Capability arithmetic instructions */
union clause ast = C_CIncAddr16CSP : (bits(10))

mapping clause encdec_compressed_capmode = C_CIncAddr16CSP(nzi9 @ nzi87 @ nzi6 @ nzi5 @ nzi4 @ 0b0000)
      if nzi9 @ nzi87 @ nzi6 @ nzi5 @ nzi4 != 0b000000
  <-> 0b011 @ nzi9 : bits(1) @ /* x2 */ 0b00010 @ nzi4 : bits(1) @ nzi6 : bits(1) @ nzi87 : bits(2) @ nzi5 : bits(1) @ 0b01
      if nzi9 @ nzi87 @ nzi6 @ nzi5 @ nzi4 != 0b000000
mapping clause assembly = C_CIncAddr16CSP(nzimm) if nzimm != 0b0000000000
  <-> "c.cincaddr16csp" ^ spc() ^ hex_bits_10(nzimm) if nzimm != 0b0000000000

/*!
 * Compressed 16-bit encoding for [CIncAddrImmediate] with source and
 * destination registers set to `csp` and an immediate scaled by 16.
 *
 * ## Notes
 *
 * - This instruction is only available in capability encoding mode.
 * - This instruction replaces the encoding of [C.ADDI16SP].
 */
function clause execute(C_CIncAddr16CSP(nzimm)) =
  execute(CIncAddrImmediate(sp, sp, sign_extend(nzimm)))

union clause ast = C_CIncAddr4CSPN : (cregidx, bits(10))

mapping clause encdec_compressed_capmode = C_CIncAddr4CSPN(cdc, nz96 @ nz54 @ nz3 @ nz2 @ 0b00)
      if nz96 @ nz54 @ nz3 @ nz2 != 0b00000000
  <-> 0b000 @ nz54 : bits(2) @ nz96 : bits(4) @ nz2 : bits(1) @ nz3 : bits(1) @ cdc : cregidx @ 0b00
      if nz96 @ nz54 @ nz3 @ nz2 != 0b00000000
mapping clause assembly = C_CIncAddr4CSPN(cdc, nzuimm) if nzuimm != 0b0000000000
  <-> "c.cincaddr4cspn" ^ spc() ^ cap_creg_name(cdc) ^ sep() ^ hex_bits_10(nzuimm) if nzuimm != 0b0000000000

/*!
 * Compressed 16-bit encoding for [CIncAddrImmediate] with the source register
 * set to `csp` and an immediate scaled by 4.
 *
 * ## Notes
 *
 * - This instruction is only available in capability encoding mode.
 * - This instruction replaces the encoding of [C.ADDI4SPN].
 */
function clause execute(C_CIncAddr4CSPN(cdc, nzuimm)) = {
  let cd = creg2reg_idx(cdc) in
  execute(CIncAddrImmediate(cd, sp, zero_extend(nzuimm)))
}

/* Control flow */
union clause ast = C_CJALR : (regidx)

mapping clause encdec_compressed_capmode = C_CJALR(cs1) if cs1 != zreg
  <-> 0b100 @ 0b1 @ cs1 : regidx @ 0b00000 @ 0b10 if cs1 != zreg
mapping clause assembly = C_CJALR(cs1) if cs1 != zreg
  <-> "c.cjalr" ^ spc() ^ reg_name(cs1) if cs1 != zreg

/*!
 * Compressed 16-bit encoding for [CJALR] with the destination register set
 * to `cra`.
 *
 * ## Notes
 *
 * - This instruction is only available in capability encoding mode.
 * - This instruction replaces the encoding of [C.JALR].
 */
function clause execute(C_CJALR(cs1)) = execute(CJALR(zeros(), cs1, ra))

union clause ast = C_CJR : (regidx)

mapping clause encdec_compressed_capmode = C_CJR(cs1) if cs1 != zreg
  <-> 0b100 @ 0b0 @ cs1 : regidx @ 0b00000 @ 0b10 if cs1 != zreg
mapping clause assembly = C_CJR(cs1) if cs1 != zreg
  <-> "c.cjr" ^ spc() ^ reg_name(cs1) if cs1 != zreg

/*!
 * Compressed 16-bit encoding for [CJALR] with the source register set to
 * `cnull` and destination register set to `cra`.
 *
 * ## Notes
 *
 * - This instruction is only available in capability encoding mode.
 * - This instruction replaces the encoding of [C.JR].
 */
function clause execute(C_CJR(cs1)) = execute(CJALR(zeros(), cs1, zreg))

union clause ast = C_CJAL : (bits(12))

mapping clause encdec_compressed_capmode = C_CJAL(i11 @ i10 @ i98 @ i7 @ i6 @ i5 @ i4 @ i31 @ 0b0) if sizeof(xlen) == 32
  <-> 0b001 @ i11 : bits(1) @ i4 : bits(1) @ i98 : bits(2) @ i10 : bits(1) @ i6 : bits(1) @ i7 : bits(1) @ i31 : bits(3) @ i5 : bits(1) @ 0b01
      if sizeof(xlen) == 32
mapping clause assembly = C_CJAL(imm) if sizeof(xlen) == 32
  <-> "c.cjal" ^ spc() ^ hex_bits_12(imm) if sizeof(xlen) == 32

/*!
 * Compressed 16-bit encoding for [CJAL] with the destination register set
 * to `cra`.
 *
 * ## Notes
 *
 * - This instruction is only available in capability encoding mode.
 * - This instruction is only available in RV32.
 * - This instruction replaces the encoding of [C.JAL].
 */
function clause execute(C_CJAL(imm)) = execute(CJAL(sign_extend(imm), ra))
