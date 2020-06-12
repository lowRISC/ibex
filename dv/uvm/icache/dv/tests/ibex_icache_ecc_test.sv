// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_ecc_test extends ibex_icache_base_test;

  `uvm_component_utils(ibex_icache_ecc_test)
  `uvm_component_new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Tell the scoreboard not to track cache hit ratios. This test corrupts data in the ICache's
    // memory. The corruptions are spotted, and behave as if the cache missed. This (obviously)
    // lowers the cache hit rate, so we don't want the test to make sure it's high enough.
    cfg.disable_caching_ratio_test = 1'b1;
  endfunction

endclass : ibex_icache_ecc_test
