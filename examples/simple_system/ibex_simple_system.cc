// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <fstream>
#include <iostream>

#include "ibex_pcounts.h"
#include "verilated_toplevel.h"
#include "verilator_memutil.h"
#include "verilator_sim_ctrl.h"
#include "cosim.h"
#include "spike_cosim.h"

SpikeCosim* cosim;

extern "C" {
void* get_spike_cosim() {
  return static_cast<Cosim*>(cosim);
}
}

void copy_mem_area_to_cosim(MemArea* area, uint32_t base_addr) {
  auto mem_data = area->Read(0, area->GetSizeWords());
  cosim->backdoor_write_mem(base_addr, area->GetSizeBytes(), &mem_data[0]);
}

int main(int argc, char **argv) {
  ibex_simple_system top;
  VerilatorMemUtil memutil;
  VerilatorSimCtrl &simctrl = VerilatorSimCtrl::GetInstance();

  cosim = new SpikeCosim;

  simctrl.SetTop(&top, &top.IO_CLK, &top.IO_RST_N,
                 VerilatorSimCtrlFlags::ResetPolarityNegative);

  MemArea ram("TOP.ibex_simple_system.u_ram.u_ram.gen_generic.u_impl_generic",
              1024 * 1024 / 4, 4);

  cosim->add_memory(0x100000, 1024 * 1024);
  cosim->add_memory(0x20000, 4096);

  memutil.RegisterMemoryArea("ram", 0x0, &ram);
  simctrl.RegisterExtension(&memutil);

  bool exit_app = false;
  int ret_code = simctrl.ParseCommandArgs(argc, argv, exit_app);
  if (exit_app) {
    return ret_code;
  }

  copy_mem_area_to_cosim(&ram, 0x100000);

  std::cout << "Simulation of Ibex" << std::endl
            << "==================" << std::endl
            << std::endl;


  simctrl.RunSimulation();

  if (!simctrl.WasSimulationSuccessful()) {
    return 1;
  }

  // Set the scope to the root scope, the ibex_pcount_string function otherwise
  // doesn't know the scope itself. Could be moved to ibex_pcount_string, but
  // would require a way to set the scope name from here, similar to MemUtil.
  svSetScope(svGetScopeFromName("TOP.ibex_simple_system"));

  std::cout << "\nPerformance Counters" << std::endl
            << "====================" << std::endl;
  std::cout << ibex_pcount_string(false);

  std::ofstream pcount_csv("ibex_simple_system_pcount.csv");
  pcount_csv << ibex_pcount_string(true);

  return 0;
}
