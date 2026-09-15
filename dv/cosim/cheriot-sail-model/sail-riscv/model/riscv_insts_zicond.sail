/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

union clause ast = ZICOND_RTYPE : (regidx, regidx, regidx, zicondop)

mapping clause encdec = ZICOND_RTYPE(rs2, rs1, rd, RISCV_CZERO_EQZ) if haveZicond()
  <-> 0b0000111 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0110011 if haveZicond()
mapping clause encdec = ZICOND_RTYPE(rs2, rs1, rd, RISCV_CZERO_NEZ) if haveZicond()
  <-> 0b0000111 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0110011 if haveZicond()

mapping zicond_mnemonic : zicondop <-> string = {
  RISCV_CZERO_EQZ <-> "czero.eqz",
  RISCV_CZERO_NEZ <-> "czero.nez"
}

mapping clause assembly = ZICOND_RTYPE(rs2, rs1, rd, op)
  <-> zicond_mnemonic(op) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

function clause execute (ZICOND_RTYPE(rs2, rs1, rd, RISCV_CZERO_EQZ)) = {
  let value = X(rs1, rs_1);
  let condition = X(rs2, rs_2);
  let result : xlenbits = if condition == zeros() then zeros()
						    else value;
  X(rd) = result;
  RETIRE_SUCCESS
}

function clause execute (ZICOND_RTYPE(rs2, rs1, rd, RISCV_CZERO_NEZ)) = {
  let value = X(rs1, rs_1);
  let condition = X(rs2, rs_2);
  let result : xlenbits = if (condition != zeros()) then zeros()
						    else value;
  X(rd) = result;
  RETIRE_SUCCESS
}
