// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Passthru test sequence
//
// This is used for the passthru test. We constrain branch targets and leave the cache disabled.

class ibex_icache_core_passthru_seq extends ibex_icache_core_base_seq;
  `uvm_object_utils(ibex_icache_core_passthru_seq)
  `uvm_object_new

  task body();
    // Overrides for base sequence
    constrain_branches = 1'b1;
    force_disable = 1'b1;

    run_reqs();
  endtask

endclass
