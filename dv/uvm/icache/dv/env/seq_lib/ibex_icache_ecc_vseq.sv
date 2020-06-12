// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence that injects ECC errors and checks we deal with them correctly.
//
// This is based on the caching vseq, which means we should see lots of cache hits (some of which
// will be corrupt).

class ibex_icache_ecc_vseq extends ibex_icache_caching_vseq;

  `uvm_object_utils(ibex_icache_ecc_vseq)
  `uvm_object_new

  virtual task pre_start();
    enable_ecc_errors = 1'b1;
    super.pre_start();
  endtask : pre_start

endclass : ibex_icache_ecc_vseq
