/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

function main () : unit -> unit = {
  // initialize extensions
  ext_init ();

  // PC = __GetSlice_int(64, elf_entry(), 0);
  PC = sail_zero_extend(0x1000, sizeof(xlen));
  print_bits("PC = ", PC);

  try {
    init_model();
    loop()
  } catch {
    Error_not_implemented(s) => print_string("Error: Not implemented: ", s),
    Error_internal_error() => print("Error: internal error")
  }
}
