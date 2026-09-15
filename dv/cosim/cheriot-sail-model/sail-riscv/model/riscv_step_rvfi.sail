/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* Step hooks for rvfi. */

function ext_fetch_hook(f : FetchResult) -> FetchResult = f

function ext_pre_step_hook()  -> unit = ()

function ext_post_step_hook() -> unit = {
  /* record the next pc */
  rvfi_pc_data->rvfi_pc_wdata() = zero_extend(get_arch_pc())
}

val ext_init : unit -> unit
function ext_init() = {
  init_base_regs();
  init_fdext_regs();
  /* these are here so that the C backend doesn't prune them out. */
  // let _ = rvfi_step(0);
  ext_rvfi_init();
  ()
}
