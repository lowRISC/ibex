// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Sanity test seq
//
// This is unlikely to find many cache hits (since it branches all over the 4GiB address space).

class ibex_icache_core_sanity_seq extends ibex_icache_core_base_seq;
  `uvm_object_utils(ibex_icache_core_sanity_seq)
  `uvm_object_new

  task body();
    // No overrides needed in base sequence
    run_reqs();
  endtask

endclass
