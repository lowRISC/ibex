/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* *****************************************************************/
/* This file specifies the instruction added by the 'N' extension. */

union clause ast = URET : unit

mapping clause encdec = URET()
  <-> 0b0000000 @ 0b00010 @ 0b00000 @ 0b000 @ 0b00000 @ 0b1110011

function clause execute URET() = {
  if   not(haveUsrMode()) | not(sys_enable_next())
  then handle_illegal()
  else if not(ext_check_xret_priv(User))
  then ext_fail_xret_priv()
  else set_next_pc(exception_handler(cur_privilege, CTL_URET(), PC));
  RETIRE_FAIL
}

mapping clause assembly = URET() <-> "uret"
