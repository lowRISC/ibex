// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Covergroups that are dependent on run-time parameters that may be available
 * only in build_phase can be defined here
 * Covergroups may also be wrapped inside helper classes if needed.
 */

class ibex_icache_env_cov extends dv_base_env_cov #(.CFG_T (ibex_icache_env_cfg));

  `uvm_component_utils(ibex_icache_env_cov)

  // the base class provides the following handles for use:
  // ibex_icache_env_cfg: cfg

  // A line the cache read from memory before an invalidation is read from memory again after it,
  // so the invalidation dropped it. Sampled by the scoreboard from the memory and core interfaces.
  covergroup inval_refetch_cg with function sample (bit inval_while_busy, bit first_read);
    // Whether the cache was busy (filling or still invalidating) when the invalidation started.
    cp_inval_while_busy: coverpoint inval_while_busy;
    // Whether this was the first memory read after the invalidation.
    cp_first_read: coverpoint first_read;
    inval_refetch_cross: cross cp_inval_while_busy, cp_first_read;
  endgroup

  function new(string name, uvm_component parent);
    super.new(name, parent);
    inval_refetch_cg = new();
  endfunction : new

endclass
