// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "dpi_memutil.h"
#include "verilated_toplevel.h"
#include "verilator_memutil.h"
#include "verilator_sim_ctrl.h"

int main(int argc, char **argv) {
  ibex_riscv_compliance top;
  VerilatorMemUtil memutil;
  VerilatorSimCtrl &simctrl = VerilatorSimCtrl::GetInstance();
  simctrl.SetTop(&top, &top.IO_CLK, &top.IO_RST_N,
                 VerilatorSimCtrlFlags::ResetPolarityNegative);

  MemAreaLoc ram_loc = {.base = 0x00000000, .size = 64 * 1024};
  memutil.RegisterMemoryArea(
      "ram", "TOP.ibex_riscv_compliance.u_ram.u_ram.gen_generic.u_impl_generic",
      32, &ram_loc);
  simctrl.RegisterExtension(&memutil);

  return simctrl.Exec(argc, argv).first;
}
