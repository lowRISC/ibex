// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "verilated_toplevel.h"
#include "verilator_memutil.h"

class SimpleSystem {
 public:
  static constexpr uint32_t kRAM_BaseAddr = 0x100000u;
  static constexpr uint32_t kRAM_SizeBytes = 0x100000u;

  SimpleSystem(const char *ram_hier_path, int ram_size_words);
  virtual ~SimpleSystem() {}
  virtual int Main(int argc, char **argv);

  // Return an ISA string, as understood by Spike, for the system being
  // simulated.
  std::string GetIsaString() const;

 protected:
  ibex_simple_system _top;
  VerilatorMemUtil _memutil;
  MemArea _ram;

  virtual int Setup(int argc, char **argv, bool &exit_app);
  virtual void Run();
  virtual bool Finish();
};
