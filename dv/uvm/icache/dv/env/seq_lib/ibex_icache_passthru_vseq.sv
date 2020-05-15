// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_passthru_vseq extends ibex_icache_base_vseq;

  `uvm_object_utils(ibex_icache_passthru_vseq)
  `uvm_object_new

  ibex_icache_core_base_seq core_seq;
  ibex_icache_mem_resp_seq  mem_seq;

  task body();
    // Start the core and memory sequences. We use fork/join_any so that we don't wait for the
    // memory sequence (which is reactive so will never finish).
    fork
      begin
        `uvm_create_on(core_seq, p_sequencer.core_sequencer_h)

        // Constrain branch targets and leave the cache disabled.
        core_seq.constrain_branches = 1'b1;
        core_seq.force_disable      = 1'b1;

        `DV_CHECK_RANDOMIZE_FATAL(core_seq)
        core_seq.start(p_sequencer.core_sequencer_h);
      end
      begin
        `uvm_create_on(mem_seq, p_sequencer.mem_sequencer_h)

        // Increase the frequency of seed updates
        mem_seq.gap_between_seeds = 49;

        `DV_CHECK_RANDOMIZE_FATAL(mem_seq)
        mem_seq.start(p_sequencer.mem_sequencer_h);
      end
    join_any
  endtask : body

endclass : ibex_icache_passthru_vseq
