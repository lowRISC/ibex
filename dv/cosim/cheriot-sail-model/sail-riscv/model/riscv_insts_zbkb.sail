/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* ****************************************************************** */
union clause ast = ZBKB_RTYPE : (regidx, regidx, regidx, brop_zbkb)

mapping clause encdec = ZBKB_RTYPE(rs2, rs1, rd, RISCV_PACK) if haveZbkb()
  <-> 0b0000100 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0110011 if haveZbkb()

mapping clause encdec = ZBKB_RTYPE(rs2, rs1, rd, RISCV_PACKH) if haveZbkb()
  <-> 0b0000100 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0110011 if haveZbkb()

mapping zbkb_rtype_mnemonic : brop_zbkb <-> string = {
  RISCV_PACK  <-> "pack",
  RISCV_PACKH <-> "packh"
}

mapping clause assembly = ZBKB_RTYPE(rs2, rs1, rd, op)
  <-> zbkb_rtype_mnemonic(op) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

function clause execute (ZBKB_RTYPE(rs2, rs1, rd, op)) = {
  let rs1_val = X(rs1, rs_1);
  let rs2_val = X(rs2, rs_2);
  let result : xlenbits = match op {
    RISCV_PACK  => rs2_val[(sizeof(xlen_bytes)*4 - 1)..0] @ rs1_val[(sizeof(xlen_bytes)*4 - 1)..0],
    RISCV_PACKH => zero_extend(rs2_val[7..0] @ rs1_val[7..0])
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

/* ****************************************************************** */
union clause ast = ZBKB_PACKW : (regidx, regidx, regidx)

mapping clause encdec = ZBKB_PACKW(rs2, rs1, rd) if haveZbkb() & sizeof(xlen) == 64
  <-> 0b0000100 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0111011 if haveZbkb() & sizeof(xlen) == 64

mapping clause assembly = ZBKB_PACKW(rs2, rs1, rd)
  <-> "packw" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

function clause execute (ZBKB_PACKW(rs2, rs1, rd)) = {
  assert(sizeof(xlen) == 64);
  let rs1_val = X(rs1, rs_1);
  let rs2_val = X(rs2, rs_2);
  let result : bits(32) = rs2_val[15..0] @ rs1_val[15..0];
  X(rd) = sign_extend(result);
  RETIRE_SUCCESS
}

/* ****************************************************************** */
union clause ast = RISCV_ZIP : (regidx, regidx)

mapping clause encdec = RISCV_ZIP(rs1, rd) if haveZbkb() & sizeof(xlen) == 32
  <-> 0b000010001111 @ rs1 @ 0b001 @ rd @ 0b0010011 if haveZbkb() & sizeof(xlen) == 32

mapping clause assembly = RISCV_ZIP(rs1, rd)
  <-> "zip" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)

function clause execute (RISCV_ZIP(rs1, rd)) = {
  assert(sizeof(xlen) == 32);
  let rs1_val = X(rs1, rs_1);
  result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen_bytes)*4 - 1)) {
    result[i*2] = rs1_val[i];
    result[i*2 + 1] = rs1_val[i + sizeof(xlen_bytes)*4];
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

/* ****************************************************************** */
union clause ast = RISCV_UNZIP : (regidx, regidx)

mapping clause encdec = RISCV_UNZIP(rs1, rd) if haveZbkb() & sizeof(xlen) == 32
  <-> 0b000010001111 @ rs1 @ 0b101 @ rd @ 0b0010011 if haveZbkb() & sizeof(xlen) == 32

mapping clause assembly = RISCV_UNZIP(rs1, rd)
  <-> "unzip" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)

function clause execute (RISCV_UNZIP(rs1, rd)) = {
  assert(sizeof(xlen) == 32);
  let rs1_val = X(rs1, rs_1);
  result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen_bytes)*4 - 1)) {
    result[i] = rs1_val[i*2];
    result[i + sizeof(xlen_bytes)*4] = rs1_val[i*2 + 1];
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

/* ****************************************************************** */
union clause ast = RISCV_BREV8 : (regidx, regidx)

mapping clause encdec = RISCV_BREV8(rs1, rd) if haveZbkb()
  <-> 0b011010000111 @ rs1 @ 0b101 @ rd @ 0b0010011 if haveZbkb()

mapping clause assembly = RISCV_BREV8(rs1, rd)
  <-> "brev8" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)

function clause execute (RISCV_BREV8(rs1, rd)) = {
  let rs1_val = X(rs1, rs_1);
  result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 8) by 8)
    result[i+7..i] = reverse(rs1_val[i+7..i]);
  X(rd) = result;
  RETIRE_SUCCESS
}
