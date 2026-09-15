/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* Instruction definitions.
 *
 * This includes decoding, execution, and assembly parsing and printing.
 */

scattered union ast

/* returns whether an instruction was retired, used for computing minstret */
val execute : ast -> Retired
scattered function execute

val assembly : ast <-> string
scattered mapping assembly

val encdec : ast <-> bits(32)
scattered mapping encdec

val encdec_compressed : ast <-> bits(16)
scattered mapping encdec_compressed

/*
 * We declare the ILLEGAL/C_ILLEGAL ast clauses here instead of in
 * riscv_insts_end, so that model extensions can make use of them.
 * However, the encdec mapping must come last to ensure that all
 * unmatched encodings decode to an illegal instruction.
 */
union clause ast = ILLEGAL : word
union clause ast = C_ILLEGAL : half
