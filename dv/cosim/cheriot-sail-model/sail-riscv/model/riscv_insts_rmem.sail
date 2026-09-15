/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* *******************************************************************  */
/* This file specifies some internal pseudo instructions used by RMEM. */

/* ****************************************************************** */

union clause ast = STOP_FETCHING : unit

/* RMEM stop fetching sentinel, using RISCV encoding space custom-0 */
mapping clause encdec = STOP_FETCHING()
  <-> 0xfade @ 0b00000000 @ 0b0 @ 0b00 @ 0b010 @ 0b11

function clause execute (STOP_FETCHING()) = RETIRE_SUCCESS

mapping clause assembly = STOP_FETCHING() <-> "stop_fetching"

union clause ast = THREAD_START : unit

/* RMEM thread start sentinel, using RISCV encoding space custom-0 */
mapping clause encdec = THREAD_START()
  <-> 0xc0de @ 0b00000000 @ 0b0 @ 0b00 @ 0b010 @ 0b11

function clause execute (THREAD_START()) = RETIRE_SUCCESS

mapping clause assembly = THREAD_START() <-> "thread_start"
