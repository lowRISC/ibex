/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* ****************************************************************** */
union clause ast = RISCV_CLMUL : (regidx, regidx, regidx)

mapping clause encdec = RISCV_CLMUL(rs2, rs1, rd) if haveZbc() | haveZbkc()
  <-> 0b0000101 @ rs2 @ rs1 @ 0b001 @ rd @ 0b0110011 if haveZbc() | haveZbkc()

mapping clause assembly = RISCV_CLMUL(rs2, rs1, rd)
  <-> "clmul" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

function clause execute (RISCV_CLMUL(rs2, rs1, rd)) = {
  let rs1_val = X(rs1, rs_1);
  let rs2_val = X(rs2, rs_2);
  result : xlenbits = zeros();
  foreach (i from 0 to (xlen_val - 1))
    if rs2_val[i] == bitone then result = result ^ (rs1_val << i);
  X(rd) = result;
  RETIRE_SUCCESS
}

/* ****************************************************************** */
union clause ast = RISCV_CLMULH : (regidx, regidx, regidx)

mapping clause encdec = RISCV_CLMULH(rs2, rs1, rd) if haveZbc() | haveZbkc()
  <-> 0b0000101 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0110011 if haveZbc() | haveZbkc()

mapping clause assembly = RISCV_CLMULH(rs2, rs1, rd)
  <-> "clmulh" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

function clause execute (RISCV_CLMULH(rs2, rs1, rd)) = {
  let rs1_val = X(rs1, rs_1);
  let rs2_val = X(rs2, rs_2);
  result : xlenbits = zeros();
  foreach (i from 0 to (xlen_val - 1))
    if rs2_val[i] == bitone then result = result ^ (rs1_val >> (xlen_val - i));
  X(rd) = result;
  RETIRE_SUCCESS
}

/* ****************************************************************** */
union clause ast = RISCV_CLMULR : (regidx, regidx, regidx)

mapping clause encdec = RISCV_CLMULR(rs2, rs1, rd) if haveZbc()
  <-> 0b0000101 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0110011 if haveZbc()

mapping clause assembly = RISCV_CLMULR(rs2, rs1, rd)
  <-> "clmulr" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

function clause execute (RISCV_CLMULR(rs2, rs1, rd)) = {
  let rs1_val = X(rs1, rs_1);
  let rs2_val = X(rs2, rs_2);
  result : xlenbits = zeros();
  foreach (i from 0 to (xlen_val - 1))
    if rs2_val[i] == bitone then result = result ^ (rs1_val >> (xlen_val - i - 1));
  X(rd) = result;
  RETIRE_SUCCESS
}
