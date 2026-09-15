/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* ****************************************************************** */
union clause ast = RISCV_SLLIUW : (bits(6), regidx, regidx)

mapping clause encdec = RISCV_SLLIUW(shamt, rs1, rd) if haveZba() & sizeof(xlen) == 64
  <-> 0b000010 @ shamt @ rs1 @ 0b001 @ rd @ 0b0011011 if haveZba() & sizeof(xlen) == 64

mapping clause assembly = RISCV_SLLIUW(shamt, rs1, rd)
  <-> "slli.uw" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_6(shamt)

function clause execute (RISCV_SLLIUW(shamt, rs1, rd)) = {
  let rs1_val = X(rs1, rs_1);
  let result : xlenbits = zero_extend(rs1_val[31..0]) << shamt;
  X(rd) = result;
  RETIRE_SUCCESS
}

/* ****************************************************************** */
union clause ast = ZBA_RTYPEUW : (regidx, regidx, regidx, bropw_zba)

mapping clause encdec = ZBA_RTYPEUW(rs2, rs1, rd, RISCV_ADDUW) if haveZba() & sizeof(xlen) == 64
  <-> 0b0000100 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011 if haveZba() & sizeof(xlen) == 64

mapping clause encdec = ZBA_RTYPEUW(rs2, rs1, rd, RISCV_SH1ADDUW) if haveZba() & sizeof(xlen) == 64
  <-> 0b0010000 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0111011 if haveZba() & sizeof(xlen) == 64

mapping clause encdec = ZBA_RTYPEUW(rs2, rs1, rd, RISCV_SH2ADDUW) if haveZba() & sizeof(xlen) == 64
  <-> 0b0010000 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0111011 if haveZba() & sizeof(xlen) == 64

mapping clause encdec = ZBA_RTYPEUW(rs2, rs1, rd, RISCV_SH3ADDUW) if haveZba() & sizeof(xlen) == 64
  <-> 0b0010000 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0111011 if haveZba() & sizeof(xlen) == 64

mapping zba_rtypeuw_mnemonic : bropw_zba <-> string = {
  RISCV_ADDUW    <-> "add.uw",
  RISCV_SH1ADDUW <-> "sh1add.uw",
  RISCV_SH2ADDUW <-> "sh2add.uw",
  RISCV_SH3ADDUW <-> "sh3add.uw"
}

mapping clause assembly = ZBA_RTYPEUW(rs2, rs1, rd, op)
  <-> zba_rtypeuw_mnemonic(op) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

function clause execute (ZBA_RTYPEUW(rs2, rs1, rd, op)) = {
  let rs1_val = X(rs1, rs_1);
  let rs2_val = X(rs2, rs_2);
  let shamt : bits(2) = match op {
    RISCV_ADDUW    => 0b00,
    RISCV_SH1ADDUW => 0b01,
    RISCV_SH2ADDUW => 0b10,
    RISCV_SH3ADDUW => 0b11
  };
  let result : xlenbits = (zero_extend(rs1_val[31..0]) << shamt) + rs2_val;
  X(rd) = result;
  RETIRE_SUCCESS
}

/* ****************************************************************** */
union clause ast = ZBA_RTYPE : (regidx, regidx, regidx, brop_zba)

mapping clause encdec = ZBA_RTYPE(rs2, rs1, rd, RISCV_SH1ADD) if haveZba()
  <-> 0b0010000 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0110011 if haveZba()
mapping clause encdec = ZBA_RTYPE(rs2, rs1, rd, RISCV_SH2ADD) if haveZba()
  <-> 0b0010000 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0110011 if haveZba()
mapping clause encdec = ZBA_RTYPE(rs2, rs1, rd, RISCV_SH3ADD) if haveZba()
  <-> 0b0010000 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0110011 if haveZba()

mapping zba_rtype_mnemonic : brop_zba <-> string = {
  RISCV_SH1ADD <-> "sh1add",
  RISCV_SH2ADD <-> "sh2add",
  RISCV_SH3ADD <-> "sh3add"
}

mapping clause assembly = ZBA_RTYPE(rs2, rs1, rd, op)
  <-> zba_rtype_mnemonic(op) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

function clause execute (ZBA_RTYPE(rs2, rs1, rd, op)) = {
  let rs1_val = X(rs1, rs_1);
  let rs2_val = X(rs2, rs_2);
  let shamt : bits(2) = match op {
    RISCV_SH1ADD => 0b01,
    RISCV_SH2ADD => 0b10,
    RISCV_SH3ADD => 0b11
  };
  let result : xlenbits = (rs1_val << shamt) + rs2_val;
  X(rd) = result;
  RETIRE_SUCCESS
}
