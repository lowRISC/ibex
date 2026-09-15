/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* ****************************************************************** */
union clause ast = RISCV_RORIW : (bits(5), regidx, regidx)

mapping clause encdec = RISCV_RORIW(shamt, rs1, rd) if (haveZbb() | haveZbkb()) & sizeof(xlen) == 64
  <-> 0b0110000 @ shamt @ rs1 @ 0b101 @ rd @ 0b0011011 if (haveZbb() | haveZbkb()) & sizeof(xlen) == 64

mapping clause assembly = RISCV_RORIW(shamt, rs1, rd)
  <-> "roriw" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_5(shamt)

function clause execute (RISCV_RORIW(shamt, rs1, rd)) = {
  let rs1_val = (X(rs1, rs_1))[31..0];
  let result : xlenbits = sign_extend(rs1_val >>> shamt);
  X(rd) = result;
  RETIRE_SUCCESS
}

/* ****************************************************************** */
union clause ast = RISCV_RORI : (bits(6), regidx, regidx)

mapping clause encdec = RISCV_RORI(shamt, rs1, rd) if (haveZbb() | haveZbkb()) & (sizeof(xlen) == 64 | shamt[5] == bitzero)
  <-> 0b011000 @ shamt @ rs1 @ 0b101 @ rd @ 0b0010011 if (haveZbb() | haveZbkb()) & (sizeof(xlen) == 64 | shamt[5] == bitzero)

mapping clause assembly = RISCV_RORI(shamt, rs1, rd)
  <-> "rori" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_6(shamt)

function clause execute (RISCV_RORI(shamt, rs1, rd)) = {
  let rs1_val = X(rs1, rs_1);
  let result : xlenbits = if sizeof(xlen) == 32
                          then rs1_val >>> shamt[4..0]
                          else rs1_val >>> shamt;
  X(rd) = result;
  RETIRE_SUCCESS
}

/* ****************************************************************** */
union clause ast = ZBB_RTYPEW : (regidx, regidx, regidx, bropw_zbb)

mapping clause encdec = ZBB_RTYPEW(rs2, rs1, rd, RISCV_ROLW) if (haveZbb() | haveZbkb()) & sizeof(xlen) == 64
  <-> 0b0110000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b0111011 if (haveZbb() | haveZbkb()) & sizeof(xlen) == 64

mapping clause encdec = ZBB_RTYPEW(rs2, rs1, rd, RISCV_RORW) if (haveZbb() | haveZbkb()) & sizeof(xlen) == 64
  <-> 0b0110000 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011 if (haveZbb() | haveZbkb()) & sizeof(xlen) == 64

mapping zbb_rtypew_mnemonic : bropw_zbb <-> string = {
  RISCV_ROLW <-> "rolw",
  RISCV_RORW <-> "rorw"
}

mapping clause assembly = ZBB_RTYPEW(rs2, rs1, rd, op)
  <-> zbb_rtypew_mnemonic(op) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

function clause execute (ZBB_RTYPEW(rs2, rs1, rd, op)) = {
  let rs1_val = (X(rs1, rs_1))[31..0];
  let shamt = (X(rs2, rs_2))[4..0];
  let result : bits(32) = match op {
    RISCV_ROLW => rs1_val <<< shamt,
    RISCV_RORW => rs1_val >>> shamt
  };
  X(rd) = sign_extend(result);
  RETIRE_SUCCESS
}

/* ****************************************************************** */
union clause ast = ZBB_RTYPE : (regidx, regidx, regidx, brop_zbb)

mapping clause encdec = ZBB_RTYPE(rs2, rs1, rd, RISCV_ANDN) if haveZbb() | haveZbkb()
  <-> 0b0100000 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0110011 if haveZbb() | haveZbkb()

mapping clause encdec = ZBB_RTYPE(rs2, rs1, rd, RISCV_ORN) if haveZbb() | haveZbkb()
  <-> 0b0100000 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0110011 if haveZbb() | haveZbkb()

mapping clause encdec = ZBB_RTYPE(rs2, rs1, rd, RISCV_XNOR) if haveZbb() | haveZbkb()
  <-> 0b0100000 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0110011 if haveZbb() | haveZbkb()

mapping clause encdec = ZBB_RTYPE(rs2, rs1, rd, RISCV_MAX) if haveZbb()
  <-> 0b0000101 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0110011 if haveZbb()

mapping clause encdec = ZBB_RTYPE(rs2, rs1, rd, RISCV_MAXU) if haveZbb()
  <-> 0b0000101 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0110011 if haveZbb()

mapping clause encdec = ZBB_RTYPE(rs2, rs1, rd, RISCV_MIN) if haveZbb()
  <-> 0b0000101 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0110011 if haveZbb()

mapping clause encdec = ZBB_RTYPE(rs2, rs1, rd, RISCV_MINU) if haveZbb()
  <-> 0b0000101 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0110011 if haveZbb()

mapping clause encdec = ZBB_RTYPE(rs2, rs1, rd, RISCV_ROL) if haveZbb() | haveZbkb()
  <-> 0b0110000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b0110011 if haveZbb() | haveZbkb()

mapping clause encdec = ZBB_RTYPE(rs2, rs1, rd, RISCV_ROR) if haveZbb() | haveZbkb()
  <-> 0b0110000 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0110011 if haveZbb() | haveZbkb()

mapping zbb_rtype_mnemonic : brop_zbb <-> string = {
  RISCV_ANDN <-> "andn",
  RISCV_ORN  <-> "orn",
  RISCV_XNOR <-> "xnor",
  RISCV_MAX  <-> "max",
  RISCV_MAXU <-> "maxu",
  RISCV_MIN  <-> "min",
  RISCV_MINU <-> "minu",
  RISCV_ROL  <-> "rol",
  RISCV_ROR  <-> "ror"
}

mapping clause assembly = ZBB_RTYPE(rs2, rs1, rd, op)
  <-> zbb_rtype_mnemonic(op) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

function clause execute (ZBB_RTYPE(rs2, rs1, rd, op)) = {
  let rs1_val = X(rs1, rs_1);
  let rs2_val = X(rs2, rs_2);
  let result : xlenbits = match op {
    RISCV_ANDN => rs1_val & ~(rs2_val),
    RISCV_ORN  => rs1_val | ~(rs2_val),
    RISCV_XNOR => ~(rs1_val ^ rs2_val),
    RISCV_MAX  => to_bits(sizeof(xlen), max(signed(rs1_val),   signed(rs2_val))),
    RISCV_MAXU => to_bits(sizeof(xlen), max(unsigned(rs1_val), unsigned(rs2_val))),
    RISCV_MIN  => to_bits(sizeof(xlen), min(signed(rs1_val),   signed(rs2_val))),
    RISCV_MINU => to_bits(sizeof(xlen), min(unsigned(rs1_val), unsigned(rs2_val))),
    RISCV_ROL  => if sizeof(xlen) == 32
                  then rs1_val <<< rs2_val[4..0]
                  else rs1_val <<< rs2_val[5..0],
    RISCV_ROR  => if sizeof(xlen) == 32
                  then rs1_val >>> rs2_val[4..0]
                  else rs1_val >>> rs2_val[5..0]
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

/* ****************************************************************** */
union clause ast = ZBB_EXTOP : (regidx, regidx, extop_zbb)

mapping clause encdec = ZBB_EXTOP(rs1, rd, RISCV_SEXTB) if haveZbb()
  <-> 0b0110000 @ 0b00100 @ rs1 @ 0b001 @ rd @ 0b0010011 if haveZbb()

mapping clause encdec = ZBB_EXTOP(rs1, rd, RISCV_SEXTH) if haveZbb()
  <-> 0b0110000 @ 0b00101 @ rs1 @ 0b001 @ rd @ 0b0010011 if haveZbb()

mapping clause encdec = ZBB_EXTOP(rs1, rd, RISCV_ZEXTH) if haveZbb() & sizeof(xlen) == 32
  <-> 0b0000100 @ 0b00000 @ rs1 @ 0b100 @ rd @ 0b0110011 if haveZbb() & sizeof(xlen) == 32

mapping clause encdec = ZBB_EXTOP(rs1, rd, RISCV_ZEXTH) if haveZbb() & sizeof(xlen) == 64
  <-> 0b0000100 @ 0b00000 @ rs1 @ 0b100 @ rd @ 0b0111011 if haveZbb() & sizeof(xlen) == 64

mapping zbb_extop_mnemonic : extop_zbb <-> string = {
  RISCV_SEXTB <-> "sext.b",
  RISCV_SEXTH <-> "sext.h",
  RISCV_ZEXTH <-> "zext.h"
}

mapping clause assembly = ZBB_EXTOP(rs1, rd, op)
  <-> zbb_extop_mnemonic(op) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)

function clause execute (ZBB_EXTOP(rs1, rd, op)) = {
  let rs1_val = X(rs1, rs_1);
  let result : xlenbits = match op {
    RISCV_SEXTB => sign_extend(rs1_val[7..0]),
    RISCV_SEXTH => sign_extend(rs1_val[15..0]),
    RISCV_ZEXTH => zero_extend(rs1_val[15..0])
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

/* ****************************************************************** */
union clause ast = RISCV_REV8 : (regidx, regidx)

mapping clause encdec = RISCV_REV8(rs1, rd) if (haveZbb() | haveZbkb()) & sizeof(xlen) == 32
  <-> 0b011010011000 @ rs1 @ 0b101 @ rd @ 0b0010011 if (haveZbb() | haveZbkb()) & sizeof(xlen) == 32

mapping clause encdec = RISCV_REV8(rs1, rd) if (haveZbb() | haveZbkb()) & sizeof(xlen) == 64
  <-> 0b011010111000 @ rs1 @ 0b101 @ rd @ 0b0010011 if (haveZbb() | haveZbkb()) & sizeof(xlen) == 64

mapping clause assembly = RISCV_REV8(rs1, rd)
  <-> "rev8" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)

function clause execute (RISCV_REV8(rs1, rd)) = {
  let rs1_val = X(rs1, rs_1);
  result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 8) by 8)
    result[(i + 7) .. i] = rs1_val[(sizeof(xlen) - i - 1) .. (sizeof(xlen) - i - 8)];
  X(rd) = result;
  RETIRE_SUCCESS
}

/* ****************************************************************** */
union clause ast = RISCV_ORCB : (regidx, regidx)

mapping clause encdec = RISCV_ORCB(rs1, rd) if haveZbb()
  <-> 0b001010000111 @ rs1 @ 0b101 @ rd @ 0b0010011 if haveZbb()

mapping clause assembly = RISCV_ORCB(rs1, rd)
  <-> "orc.b" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)

function clause execute (RISCV_ORCB(rs1, rd)) = {
  let rs1_val = X(rs1, rs_1);
  result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 8) by 8)
    result[(i + 7) .. i] = if rs1_val[(i + 7) .. i] == zeros()
                           then 0x00
                           else 0xFF;
  X(rd) = result;
  RETIRE_SUCCESS
}

/* ****************************************************************** */
union clause ast = RISCV_CPOP : (regidx, regidx)

mapping clause encdec = RISCV_CPOP(rs1, rd) if haveZbb()
  <-> 0b011000000010 @ rs1 @ 0b001 @ rd @ 0b0010011 if haveZbb()

mapping clause assembly = RISCV_CPOP(rs1, rd)
  <-> "cpop" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)

function clause execute (RISCV_CPOP(rs1, rd)) = {
  let rs1_val = X(rs1, rs_1);
  result : nat = 0;
  foreach (i from 0 to (xlen_val - 1))
    if rs1_val[i] == bitone then result = result + 1;
  X(rd) = to_bits(sizeof(xlen), result);
  RETIRE_SUCCESS
}

/* ****************************************************************** */
union clause ast = RISCV_CPOPW : (regidx, regidx)

mapping clause encdec = RISCV_CPOPW(rs1, rd) if haveZbb() & sizeof(xlen) == 64
  <-> 0b011000000010 @ rs1 @ 0b001 @ rd @ 0b0011011 if haveZbb() & sizeof(xlen) == 64

mapping clause assembly = RISCV_CPOPW(rs1, rd)
  <-> "cpopw" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)

function clause execute (RISCV_CPOPW(rs1, rd)) = {
  let rs1_val = X(rs1, rs_1);
  result : nat = 0;
  foreach (i from 0 to 31)
    if rs1_val[i] == bitone then result = result + 1;
  X(rd) = to_bits(sizeof(xlen), result);
  RETIRE_SUCCESS
}

/* ****************************************************************** */
union clause ast = RISCV_CLZ : (regidx, regidx)

mapping clause encdec = RISCV_CLZ(rs1, rd) if haveZbb()
  <-> 0b011000000000 @ rs1 @ 0b001 @ rd @ 0b0010011 if haveZbb()

mapping clause assembly = RISCV_CLZ(rs1, rd)
  <-> "clz" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)

function clause execute (RISCV_CLZ(rs1, rd)) = {
  let rs1_val = X(rs1, rs_1);
  result : nat = 0;
  done : bool = false;
  foreach (i from (sizeof(xlen) - 1) downto 0)
    if not(done) then if rs1_val[i] == bitzero
                    then result = result + 1
                    else done = true;
  X(rd) = to_bits(sizeof(xlen), result);
  RETIRE_SUCCESS
}

/* ****************************************************************** */
union clause ast = RISCV_CLZW : (regidx, regidx)

mapping clause encdec = RISCV_CLZW(rs1, rd) if haveZbb() & sizeof(xlen) == 64
  <-> 0b011000000000 @ rs1 @ 0b001 @ rd @ 0b0011011 if haveZbb() & sizeof(xlen) == 64

mapping clause assembly = RISCV_CLZW(rs1, rd)
  <-> "clzw" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)

function clause execute (RISCV_CLZW(rs1, rd)) = {
  let rs1_val = X(rs1, rs_1);
  result : nat = 0;
  done : bool = false;
  foreach (i from 31 downto 0)
    if not(done) then if rs1_val[i] == bitzero
                    then result = result + 1
                    else done = true;
  X(rd) = to_bits(sizeof(xlen), result);
  RETIRE_SUCCESS
}

/* ****************************************************************** */
union clause ast = RISCV_CTZ : (regidx, regidx)

mapping clause encdec = RISCV_CTZ(rs1, rd) if haveZbb()
  <-> 0b011000000001 @ rs1 @ 0b001 @ rd @ 0b0010011 if haveZbb()

mapping clause assembly = RISCV_CTZ(rs1, rd)
  <-> "ctz" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)

function clause execute (RISCV_CTZ(rs1, rd)) = {
  let rs1_val = X(rs1, rs_1);
  result : nat = 0;
  done : bool = false;
  foreach (i from 0 to (sizeof(xlen) - 1))
    if not(done) then if rs1_val[i] == bitzero
                    then result = result + 1
                    else done = true;
  X(rd) = to_bits(sizeof(xlen), result);
  RETIRE_SUCCESS
}

/* ****************************************************************** */
union clause ast = RISCV_CTZW : (regidx, regidx)

mapping clause encdec = RISCV_CTZW(rs1, rd) if haveZbb() & sizeof(xlen) == 64
  <-> 0b011000000001 @ rs1 @ 0b001 @ rd @ 0b0011011 if haveZbb() & sizeof(xlen) == 64

mapping clause assembly = RISCV_CTZW(rs1, rd)
  <-> "ctzw" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)

function clause execute (RISCV_CTZW(rs1, rd)) = {
  let rs1_val = X(rs1, rs_1);
  result : nat = 0;
  done : bool = false;
  foreach (i from 0 to 31)
    if not(done) then if rs1_val[i] == bitzero
                    then result = result + 1
                    else done = true;
  X(rd) = to_bits(sizeof(xlen), result);
  RETIRE_SUCCESS
}
