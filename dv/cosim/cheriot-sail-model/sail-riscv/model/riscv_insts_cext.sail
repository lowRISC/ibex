/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* ********************************************************************* */
/* This file specifies the compressed instructions in the 'C' extension. */

/* These instructions are only legal if misa[C] is true.  Instead of
 * checking this in every execute clause, we currently do the check in one place
 * in the fetch-execute logic.
 */

/* ****************************************************************** */
union clause ast = C_NOP : unit

mapping clause encdec_compressed = C_NOP()
  <-> 0b000 @ 0b0 @ 0b00000 @ 0b00000 @ 0b01

function clause execute C_NOP() = RETIRE_SUCCESS

mapping clause assembly = C_NOP() <-> "c.nop"

/* ****************************************************************** */

union clause ast = C_ADDI4SPN : (cregidx, bits(8))

mapping clause encdec_compressed = C_ADDI4SPN(rd, nz96 @ nz54 @ nz3 @ nz2)
      if nz96 @ nz54 @ nz3 @ nz2 != 0b00000000
  <-> 0b000 @ nz54 : bits(2) @ nz96 : bits(4) @ nz2 : bits(1) @ nz3 : bits(1) @ rd : cregidx @ 0b00
      if nz96 @ nz54 @ nz3 @ nz2 != 0b00000000

function clause execute (C_ADDI4SPN(rdc, nzimm)) = {
  let imm : bits(12) = (0b00 @ nzimm @ 0b00);
  let rd = creg2reg_idx(rdc);
  execute(ITYPE(imm, sp, rd, RISCV_ADDI))
}

mapping clause assembly = C_ADDI4SPN(rdc, nzimm)
      if nzimm != 0b00000000
  <-> "c.addi4spn" ^ spc() ^ creg_name(rdc) ^ sep() ^ hex_bits_10(nzimm @ 0b00)
      if nzimm != 0b00000000

/* ****************************************************************** */
union clause ast = C_LW : (bits(5), cregidx, cregidx)

mapping clause encdec_compressed = C_LW(ui6 @ ui53 @ ui2, rs1, rd)
  <-> 0b010 @ ui53 : bits(3) @ rs1 : cregidx @ ui2 : bits(1) @ ui6 : bits(1) @ rd : cregidx @ 0b00

function clause execute (C_LW(uimm, rsc, rdc)) = {
  let imm : bits(12) = zero_extend(uimm @ 0b00);
  let rd = creg2reg_idx(rdc);
  let rs = creg2reg_idx(rsc);
  execute(LOAD(imm, rs, rd, false, WORD, false, false))
}

mapping clause assembly = C_LW(uimm, rsc, rdc)
  <-> "c.lw" ^ spc() ^ creg_name(rdc) ^ sep() ^ creg_name(rsc) ^ sep() ^ hex_bits_7(uimm @ 0b00)

/* ****************************************************************** */
union clause ast = C_LD : (bits(5), cregidx, cregidx)

mapping clause encdec_compressed = C_LD(ui76 @ ui53, rs1, rd)
      if sizeof(xlen) == 64
  <-> 0b011 @ ui53 : bits(3) @ rs1 : cregidx @ ui76 : bits(2) @ rd : cregidx @ 0b00
      if sizeof(xlen) == 64

function clause execute (C_LD(uimm, rsc, rdc)) = {
  let imm : bits(12) = zero_extend(uimm @ 0b000);
  let rd = creg2reg_idx(rdc);
  let rs = creg2reg_idx(rsc);
  execute(LOAD(imm, rs, rd, false, DOUBLE, false, false))
}

mapping clause assembly = C_LD(uimm, rsc, rdc)
      if sizeof(xlen) == 64
  <-> "c.ld" ^ spc() ^ creg_name(rdc) ^ sep() ^ creg_name(rsc) ^ sep() ^ hex_bits_8(uimm @ 0b000)
      if sizeof(xlen) == 64

/* ****************************************************************** */
union clause ast = C_SW : (bits(5), cregidx, cregidx)

mapping clause encdec_compressed = C_SW(ui6 @ ui53 @ ui2, rs1, rs2)
  <-> 0b110 @ ui53 : bits(3) @ rs1 : cregidx @ ui2 : bits(1) @ ui6 : bits(1) @ rs2 : cregidx @ 0b00

function clause execute (C_SW(uimm, rsc1, rsc2)) = {
  let imm : bits(12) = zero_extend(uimm @ 0b00);
  let rs1 = creg2reg_idx(rsc1);
  let rs2 = creg2reg_idx(rsc2);
  execute(STORE(imm, rs2, rs1, WORD, false, false))
}

mapping clause assembly = C_SW(uimm, rsc1, rsc2)
  <-> "c.sw" ^ spc() ^ creg_name(rsc1) ^ sep() ^ creg_name(rsc2) ^ sep() ^ hex_bits_7(uimm @ 0b00)

/* ****************************************************************** */
union clause ast = C_SD : (bits(5), cregidx, cregidx)

mapping clause encdec_compressed = C_SD(ui76 @ ui53, rs1, rs2)
      if sizeof(xlen) == 64
  <-> 0b111 @ ui53 : bits(3) @ rs1 : bits(3) @ ui76 : bits(2) @ rs2 : bits(3) @ 0b00
      if sizeof(xlen) == 64

function clause execute (C_SD(uimm, rsc1, rsc2)) = {
  let imm : bits(12) = zero_extend(uimm @ 0b000);
  let rs1 = creg2reg_idx(rsc1);
  let rs2 = creg2reg_idx(rsc2);
  execute(STORE(imm, rs2, rs1, DOUBLE, false, false))
}

mapping clause assembly = C_SD(uimm, rsc1, rsc2)
      if sizeof(xlen) == 64
  <-> "c.sd" ^ spc() ^ creg_name(rsc1) ^ sep() ^ creg_name(rsc2) ^ sep() ^ hex_bits_8(uimm @ 0b000)
      if sizeof(xlen) == 64

/* ****************************************************************** */
union clause ast = C_ADDI : (bits(6), regidx)

mapping clause encdec_compressed = C_ADDI(nzi5 @ nzi40, rsd)
      if nzi5 @ nzi40 != 0b000000 & rsd != zreg
  <-> 0b000 @ nzi5 : bits(1) @ rsd : regidx @ nzi40 : bits(5) @ 0b01
      if nzi5 @ nzi40 != 0b000000 & rsd != zreg

function clause execute (C_ADDI(nzi, rsd)) = {
  let imm : bits(12) = sign_extend(nzi);
  execute(ITYPE(imm, rsd, rsd, RISCV_ADDI))
}

mapping clause assembly = C_ADDI(nzi, rsd)
      if nzi != 0b000000 & rsd != zreg
  <-> "c.addi" ^ spc() ^ reg_name(rsd) ^ sep() ^ hex_bits_6(nzi)
      if nzi != 0b000000 & rsd != zreg

/* ****************************************************************** */
union clause ast = C_JAL : (bits(11))

mapping clause encdec_compressed = C_JAL(i11 @ i10 @ i98 @ i7 @ i6 @ i5 @ i4 @ i31)
      if sizeof(xlen) == 32
  <-> 0b001 @ i11 : bits(1) @ i4 : bits(1) @ i98 : bits(2) @ i10 : bits(1) @ i6 : bits(1) @ i7 : bits(1) @ i31 : bits(3) @ i5 : bits(1) @ 0b01
      if sizeof(xlen) == 32

function clause execute (C_JAL(imm)) =
  execute(RISCV_JAL(sign_extend(imm @ 0b0), ra))

mapping clause assembly = C_JAL(imm)
      if sizeof(xlen) == 32
  <-> "c.jal" ^ spc() ^ hex_bits_12(imm @ 0b0)
      if sizeof(xlen) == 32

/* ****************************************************************** */
union clause ast = C_ADDIW : (bits(6), regidx)

mapping clause encdec_compressed = C_ADDIW(imm5 @ imm40, rsd)
      if rsd != zreg & sizeof(xlen) == 64
  <-> 0b001 @ imm5 : bits(1) @ rsd : regidx @ imm40 : bits(5) @ 0b01
      if rsd != zreg & sizeof(xlen) == 64

function clause execute (C_ADDIW(imm, rsd)) =
  execute(ADDIW(sign_extend(imm), rsd, rsd))

mapping clause assembly = C_ADDIW(imm, rsd)
      if sizeof(xlen) == 64
  <-> "c.addiw" ^ spc() ^ reg_name(rsd) ^ sep() ^ hex_bits_6(imm)
      if sizeof(xlen) == 64

/* ****************************************************************** */
union clause ast = C_LI : (bits(6), regidx)

mapping clause encdec_compressed = C_LI(imm5 @ imm40, rd)
      if rd != zreg
  <-> 0b010 @ imm5 : bits(1) @ rd : regidx @ imm40 : bits(5) @ 0b01
      if rd != zreg

function clause execute (C_LI(imm, rd)) = {
  let imm : bits(12) = sign_extend(imm);
  execute(ITYPE(imm, zreg, rd, RISCV_ADDI))
}

mapping clause assembly = C_LI(imm, rd)
      if rd != zreg
  <-> "c.li" ^ spc() ^ reg_name(rd) ^ sep() ^ hex_bits_6(imm)
      if rd != zreg

/* ****************************************************************** */
union clause ast = C_ADDI16SP : (bits(6))

mapping clause encdec_compressed = C_ADDI16SP(nzi9 @ nzi87 @ nzi6 @ nzi5 @ nzi4)
      if nzi9 @ nzi87 @ nzi6 @ nzi5 @ nzi4 != 0b000000
  <-> 0b011 @ nzi9 : bits(1) @ /* x2 */ 0b00010 @ nzi4 : bits(1) @ nzi6 : bits(1) @ nzi87 : bits(2) @ nzi5 : bits(1) @ 0b01
      if nzi9 @ nzi87 @ nzi6 @ nzi5 @ nzi4 != 0b000000

function clause execute (C_ADDI16SP(imm)) = {
  let imm : bits(12) = sign_extend(imm @ 0x0);
  execute(ITYPE(imm, sp, sp, RISCV_ADDI))
}

mapping clause assembly = C_ADDI16SP(imm)
      if imm != 0b000000
  <-> "c.addi16sp" ^ spc() ^ hex_bits_6(imm)
      if imm != 0b000000

/* ****************************************************************** */
union clause ast = C_LUI : (bits(6), regidx)

mapping clause encdec_compressed = C_LUI(imm17 @ imm1612, rd)
      if rd != zreg & rd != sp & imm17 @ imm1612 != 0b000000
  <-> 0b011 @ imm17 : bits(1) @ rd : regidx @ imm1612 : bits(5) @ 0b01
      if rd != zreg & rd != sp & imm17 @ imm1612 != 0b000000

function clause execute (C_LUI(imm, rd)) = {
  let res : bits(20) = sign_extend(imm);
  execute(UTYPE(res, rd, RISCV_LUI))
}

mapping clause assembly = C_LUI(imm, rd)
      if rd != zreg & rd != sp & imm != 0b000000
  <-> "c.lui" ^ spc() ^ reg_name(rd) ^ sep() ^ hex_bits_6(imm)
      if rd != zreg & rd != sp & imm != 0b000000

/* ****************************************************************** */
union clause ast = C_SRLI : (bits(6), cregidx)

mapping clause encdec_compressed = C_SRLI(nzui5 @ nzui40, rsd)
      if nzui5 @ nzui40 != 0b000000
  <-> 0b100 @ nzui5 : bits(1) @ 0b00 @ rsd : cregidx @ nzui40 : bits(5) @ 0b01
      if nzui5 @ nzui40 != 0b000000

function clause execute (C_SRLI(shamt, rsd)) = {
  let rsd = creg2reg_idx(rsd);
  execute(SHIFTIOP(shamt, rsd, rsd, RISCV_SRLI))
}

mapping clause assembly = C_SRLI(shamt, rsd)
      if shamt != 0b000000
  <-> "c.srli" ^ spc() ^ creg_name(rsd) ^ sep() ^ hex_bits_6(shamt)
      if shamt != 0b000000

/* ****************************************************************** */
union clause ast = C_SRAI : (bits(6), cregidx)

mapping clause encdec_compressed = C_SRAI(nzui5 @ nzui40, rsd)
      if nzui5 @ nzui40 != 0b000000
  <-> 0b100 @ nzui5 : bits(1) @ 0b01 @ rsd : cregidx @ nzui40 : bits(5) @ 0b01
      if nzui5 @ nzui40 != 0b000000

function clause execute (C_SRAI(shamt, rsd)) = {
  let rsd = creg2reg_idx(rsd);
  execute(SHIFTIOP(shamt, rsd, rsd, RISCV_SRAI))
}

mapping clause assembly = C_SRAI(shamt, rsd)
      if shamt != 0b000000
  <-> "c.srai" ^ spc() ^ creg_name(rsd) ^ sep() ^ hex_bits_6(shamt)
      if shamt != 0b000000

/* ****************************************************************** */
union clause ast = C_ANDI : (bits(6), cregidx)

mapping clause encdec_compressed = C_ANDI(i5 @ i40, rsd)
  <-> 0b100 @ i5 : bits(1) @ 0b10 @ rsd : cregidx @ i40 : bits(5) @ 0b01

function clause execute (C_ANDI(imm, rsd)) = {
  let rsd = creg2reg_idx(rsd);
  execute(ITYPE(sign_extend(imm), rsd, rsd, RISCV_ANDI))
}

mapping clause assembly = C_ANDI(imm, rsd)
  <-> "c.andi" ^ spc() ^ creg_name(rsd) ^ sep() ^ hex_bits_6(imm)

/* ****************************************************************** */
union clause ast = C_SUB : (cregidx, cregidx)

mapping clause encdec_compressed = C_SUB(rsd, rs2)
  <-> 0b100 @ 0b0 @ 0b11 @ rsd : cregidx @ 0b00 @ rs2 : cregidx @ 0b01

function clause execute (C_SUB(rsd, rs2)) = {
  let rsd = creg2reg_idx(rsd);
  let rs2 = creg2reg_idx(rs2);
  execute(RTYPE(rs2, rsd, rsd, RISCV_SUB))
}

mapping clause assembly = C_SUB(rsd, rs2)
  <-> "c.sub" ^ spc() ^ creg_name(rsd) ^ sep() ^ creg_name(rs2)

/* ****************************************************************** */
union clause ast = C_XOR : (cregidx, cregidx)

mapping clause encdec_compressed = C_XOR(rsd, rs2)
  <-> 0b100 @ 0b0 @ 0b11 @ rsd : cregidx @ 0b01 @ rs2 : cregidx @ 0b01

function clause execute (C_XOR(rsd, rs2)) = {
  let rsd = creg2reg_idx(rsd);
  let rs2 = creg2reg_idx(rs2);
  execute(RTYPE(rs2, rsd, rsd, RISCV_XOR))
}

mapping clause assembly = C_XOR(rsd, rs2)
  <-> "c.xor" ^ spc() ^ creg_name(rsd) ^ sep() ^ creg_name(rs2)

/* ****************************************************************** */
union clause ast = C_OR : (cregidx, cregidx)

mapping clause encdec_compressed = C_OR(rsd, rs2)
  <-> 0b100 @ 0b0 @ 0b11 @ rsd : cregidx @ 0b10 @ rs2 : cregidx @ 0b01

function clause execute (C_OR(rsd, rs2)) = {
  let rsd = creg2reg_idx(rsd);
  let rs2 = creg2reg_idx(rs2);
  execute(RTYPE(rs2, rsd, rsd, RISCV_OR))
}

mapping clause assembly = C_OR(rsd, rs2)
  <-> "c.or" ^ spc() ^ creg_name(rsd) ^ sep() ^ creg_name(rs2)

/* ****************************************************************** */
union clause ast = C_AND : (cregidx, cregidx)

mapping clause encdec_compressed = C_AND(rsd, rs2)
  <-> 0b100 @ 0b0 @ 0b11 @ rsd : cregidx @ 0b11 @ rs2 : cregidx @ 0b01

function clause execute (C_AND(rsd, rs2)) = {
  let rsd = creg2reg_idx(rsd);
  let rs2 = creg2reg_idx(rs2);
  execute(RTYPE(rs2, rsd, rsd, RISCV_AND))
}

mapping clause assembly = C_AND(rsd, rs2)
  <-> "c.and" ^ spc() ^ creg_name(rsd) ^ sep() ^ creg_name(rs2)

/* ****************************************************************** */
union clause ast = C_SUBW : (cregidx, cregidx)

mapping clause encdec_compressed = C_SUBW(rsd, rs2)
      if sizeof(xlen) == 64
  <-> 0b100 @ 0b1 @ 0b11 @ rsd : cregidx @ 0b00 @ rs2 : cregidx @ 0b01
      if sizeof(xlen) == 64

function clause execute (C_SUBW(rsd, rs2)) = {
  let rsd = creg2reg_idx(rsd);
  let rs2 = creg2reg_idx(rs2);
  execute(RTYPEW(rs2, rsd, rsd, RISCV_SUBW))
}

mapping clause assembly = C_SUBW(rsd, rs2)
      if sizeof(xlen) == 64
  <-> "c.subw" ^ spc() ^ creg_name(rsd) ^ sep() ^ creg_name(rs2)
      if sizeof(xlen) == 64

/* ****************************************************************** */
union clause ast = C_ADDW : (cregidx, cregidx)

mapping clause encdec_compressed = C_ADDW(rsd, rs2)
      if sizeof(xlen) == 64
  <-> 0b100 @ 0b1 @ 0b11 @ rsd : cregidx @ 0b01 @ rs2 : cregidx @ 0b01
      if sizeof(xlen) == 64

function clause execute (C_ADDW(rsd, rs2)) = {
  let rsd = creg2reg_idx(rsd);
  let rs2 = creg2reg_idx(rs2);
  execute(RTYPEW(rs2, rsd, rsd, RISCV_ADDW))
}

mapping clause assembly = C_ADDW(rsd, rs2)
      if sizeof(xlen) == 64
  <-> "c.addw" ^ spc() ^ creg_name(rsd) ^ sep() ^ creg_name(rs2)
      if sizeof(xlen) == 64

/* ****************************************************************** */
union clause ast = C_J : (bits(11))

mapping clause encdec_compressed = C_J(i11 @ i10 @ i98 @ i7 @ i6 @ i5 @ i4 @ i31)
  <-> 0b101 @ i11 : bits(1) @ i4 : bits(1) @ i98 : bits(2) @ i10 : bits(1) @ i6 : bits(1) @ i7 : bits(1) @ i31 : bits(3) @ i5 : bits(1) @ 0b01

function clause execute (C_J(imm)) =
  execute(RISCV_JAL(sign_extend(imm @ 0b0), zreg))

mapping clause assembly = C_J(imm)
  <-> "c.j" ^ spc() ^ hex_bits_11(imm)

/* ****************************************************************** */
union clause ast = C_BEQZ : (bits(8), cregidx)

mapping clause encdec_compressed = C_BEQZ(i8 @ i76 @ i5 @ i43 @ i21, rs)
  <-> 0b110 @ i8 : bits(1) @ i43 : bits(2) @ rs : cregidx @ i76 : bits(2) @ i21 : bits(2) @ i5 : bits(1) @ 0b01

function clause execute (C_BEQZ(imm, rs)) =
  execute(BTYPE(sign_extend(imm @ 0b0), zreg, creg2reg_idx(rs), RISCV_BEQ))

mapping clause assembly = C_BEQZ(imm, rs)
  <-> "c.beqz" ^ spc() ^ creg_name(rs) ^ sep() ^ hex_bits_8(imm)

/* ****************************************************************** */
union clause ast = C_BNEZ : (bits(8), cregidx)

mapping clause encdec_compressed = C_BNEZ(i8 @ i76 @ i5 @ i43 @ i21, rs)
  <-> 0b111 @ i8 : bits(1) @ i43 : bits(2) @ rs : cregidx @ i76 : bits(2) @ i21 : bits(2) @ i5 : bits(1) @ 0b01

function clause execute (C_BNEZ(imm, rs)) =
  execute(BTYPE(sign_extend(imm @ 0b0), zreg, creg2reg_idx(rs), RISCV_BNE))

mapping clause assembly = C_BNEZ(imm, rs)
  <-> "c.bnez" ^ spc() ^ creg_name(rs) ^ sep() ^ hex_bits_8(imm)

/* ****************************************************************** */
union clause ast = C_SLLI : (bits(6), regidx)

mapping clause encdec_compressed = C_SLLI(nzui5 @ nzui40, rsd)
      if nzui5 @ nzui40 != 0b000000 & rsd != zreg & (sizeof(xlen) == 64 | nzui5 == 0b0)
  <-> 0b000 @ nzui5 : bits(1) @ rsd : regidx @ nzui40 : bits(5) @ 0b10
      if nzui5 @ nzui40 != 0b000000 & rsd != zreg & (sizeof(xlen) == 64 | nzui5 == 0b0)

function clause execute (C_SLLI(shamt, rsd)) =
  execute(SHIFTIOP(shamt, rsd, rsd, RISCV_SLLI))

mapping clause assembly = C_SLLI(shamt, rsd)
      if shamt != 0b000000 & rsd != zreg
  <-> "c.slli" ^ spc() ^ reg_name(rsd) ^ sep() ^ hex_bits_6(shamt)
      if shamt != 0b000000 & rsd != zreg

/* ****************************************************************** */
union clause ast = C_LWSP : (bits(6), regidx)

mapping clause encdec_compressed = C_LWSP(ui76 @ ui5 @ ui42, rd)
      if rd != zreg
  <-> 0b010 @ ui5 : bits(1) @ rd : regidx @ ui42 : bits(3) @ ui76 : bits(2) @ 0b10
      if rd != zreg

function clause execute (C_LWSP(uimm, rd)) = {
  let imm : bits(12) = zero_extend(uimm @ 0b00);
  execute(LOAD(imm, sp, rd, false, WORD, false, false))
}

mapping clause assembly = C_LWSP(uimm, rd)
      if rd != zreg
  <-> "c.lwsp" ^ spc() ^ reg_name(rd) ^ sep() ^ hex_bits_6(uimm)
      if rd != zreg

/* ****************************************************************** */
union clause ast = C_LDSP : (bits(6), regidx)

mapping clause encdec_compressed = C_LDSP(ui86 @ ui5 @ ui43, rd)
      if rd != zreg & sizeof(xlen) == 64
  <-> 0b011 @ ui5 : bits(1) @ rd : regidx @ ui43 : bits(2) @ ui86 : bits(3) @ 0b10
      if rd != zreg & sizeof(xlen) == 64

function clause execute (C_LDSP(uimm, rd)) = {
  let imm : bits(12) = zero_extend(uimm @ 0b000);
  execute(LOAD(imm, sp, rd, false, DOUBLE, false, false))
}

mapping clause assembly = C_LDSP(uimm, rd)
      if rd != zreg & sizeof(xlen) == 64
  <-> "c.ldsp" ^ spc() ^ reg_name(rd) ^ sep() ^ hex_bits_6(uimm)
      if rd != zreg & sizeof(xlen) == 64

/* ****************************************************************** */
union clause ast = C_SWSP : (bits(6), regidx)

mapping clause encdec_compressed = C_SWSP(ui76 @ ui52, rs2)
  <-> 0b110 @ ui52 : bits(4) @ ui76 : bits(2) @ rs2 : regidx @ 0b10

function clause execute (C_SWSP(uimm, rs2)) = {
  let imm : bits(12) = zero_extend(uimm @ 0b00);
  execute(STORE(imm, rs2, sp, WORD, false, false))
}

mapping clause assembly = C_SWSP(uimm, rs2)
  <-> "c.swsp" ^ spc() ^ reg_name(rs2) ^ sep() ^ hex_bits_6(uimm)

/* ****************************************************************** */
union clause ast = C_SDSP : (bits(6), regidx)

mapping clause encdec_compressed = C_SDSP(ui86 @ ui53, rs2)
      if sizeof(xlen) == 64
  <-> 0b111 @ ui53 : bits(3) @ ui86 : bits(3) @ rs2 : regidx @ 0b10
      if sizeof(xlen) == 64

function clause execute (C_SDSP(uimm, rs2)) = {
  let imm : bits(12) = zero_extend(uimm @ 0b000);
  execute(STORE(imm, rs2, sp, DOUBLE, false, false))
}

mapping clause assembly = C_SDSP(uimm, rs2)
      if sizeof(xlen) == 64
  <-> "c.sdsp" ^ spc() ^ reg_name(rs2) ^ sep() ^ hex_bits_6(uimm)
      if sizeof(xlen) == 64

/* ****************************************************************** */
union clause ast = C_JR : (regidx)

mapping clause encdec_compressed = C_JR(rs1)
      if rs1 != zreg
  <-> 0b100 @ 0b0 @ rs1 : regidx @ 0b00000 @ 0b10
      if rs1 != zreg

function clause execute (C_JR(rs1)) =
  execute(RISCV_JALR(zero_extend(0b0), rs1, zreg))

mapping clause assembly = C_JR(rs1)
      if rs1 != zreg
  <-> "c.jr" ^ spc() ^ reg_name(rs1)
      if rs1 != zreg

/* ****************************************************************** */
union clause ast = C_JALR : (regidx)

mapping clause encdec_compressed = C_JALR(rs1)
      if rs1 != zreg
  <-> 0b100 @ 0b1 @ rs1 : regidx @ 0b00000 @ 0b10
      if rs1 != zreg

function clause execute (C_JALR(rs1)) =
  execute(RISCV_JALR(zero_extend(0b0), rs1, ra))

mapping clause assembly = C_JALR(rs1)
      if rs1 != zreg
  <-> "c.jalr" ^ spc() ^ reg_name(rs1)
      if rs1 != zreg

/* ****************************************************************** */
union clause ast = C_MV : (regidx, regidx)

mapping clause encdec_compressed = C_MV(rd, rs2)
      if rd != zreg & rs2 != zreg
  <-> 0b100 @ 0b0 @ rd : regidx @ rs2 : regidx @ 0b10
      if rd != zreg & rs2 != zreg

function clause execute (C_MV(rd, rs2)) =
  execute(RTYPE(rs2, zreg, rd, RISCV_ADD))

mapping clause assembly = C_MV(rd, rs2)
      if rd != zreg & rs2 != zreg
  <-> "c.mv" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs2)
      if rd != zreg & rs2 != zreg

/* ****************************************************************** */
union clause ast = C_EBREAK : unit

mapping clause encdec_compressed = C_EBREAK()
  <-> 0b100 @ 0b1 @ 0b00000 @ 0b00000 @ 0b10

function clause execute C_EBREAK() =
  execute(EBREAK())

mapping clause assembly = C_EBREAK() <-> "c.ebreak"

/* ****************************************************************** */
union clause ast = C_ADD : (regidx, regidx)

mapping clause encdec_compressed = C_ADD(rsd, rs2)
      if rsd != zreg & rs2 != zreg
  <-> 0b100 @ 0b1 @ rsd : regidx @ rs2 : regidx @ 0b10
      if rsd != zreg & rs2 != zreg

function clause execute (C_ADD(rsd, rs2)) =
  execute(RTYPE(rs2, rsd, rsd, RISCV_ADD))

mapping clause assembly = C_ADD(rsd, rs2)
      if rsd != zreg & rs2 != zreg
  <-> "c.add" ^ spc() ^ reg_name(rsd) ^ sep() ^ reg_name(rs2)
      if rsd != zreg & rs2 != zreg
