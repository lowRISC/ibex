/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* The definition for the memory model. */

function clause execute (RISCV_JALR(imm, rs1, rd)) = {
  /* FIXME: this does not check for a misaligned target address. See riscv_jalr_seq.sail. */
  /* write rd before anything else to prevent unintended strength */
  X(rd) = nextPC; /* compatible with JALR, C.JR and C.JALR */
  let newPC : xlenbits = X(rs1, rs_1) + sign_extend(imm);
  nextPC = [newPC with 0 = bitzero];  /* Clear newPC[0] */
  RETIRE_SUCCESS
}
