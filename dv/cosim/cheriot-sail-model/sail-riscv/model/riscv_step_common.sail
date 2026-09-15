/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* The result of a fetch, which includes any possible error
 * from an extension that interposes on the fetch operation.
 */

union FetchResult = {
  F_Ext_Error : ext_fetch_addr_error,      /* For extensions */
  F_Base      : word,                      /* Base ISA */
  F_RVC       : half,                      /* Compressed ISA */
  F_Error     : (ExceptionType, xlenbits)  /* standard exception and PC */
}
