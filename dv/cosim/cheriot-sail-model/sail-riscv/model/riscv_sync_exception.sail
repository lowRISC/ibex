/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* model context for synchronous exceptions, parameterized for extensions */

struct sync_exception = {
  trap    : ExceptionType,
  excinfo : option(xlenbits),
  ext     : option(ext_exception)   /* for extensions */
}
