// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A "combination vseq", which runs proper virtual sequences in a random order.

class ibex_icache_combo_vseq
  extends dv_base_vseq #(
    .CFG_T               (ibex_icache_env_cfg),
    .COV_T               (ibex_icache_env_cov),
    .VIRTUAL_SEQUENCER_T (ibex_icache_virtual_sequencer)
  );
  `uvm_object_utils(ibex_icache_combo_vseq)
  `uvm_object_new

  // The number of transactions across the combined sequences
  constraint num_trans_c { num_trans inside {[800:1000]}; }

  // The virtual sequences from which we'll build the test. Note that this doesn't contain
  // "ibex_icache_oldval_vseq": that sequence is for a specific test, which has a slightly different
  // checker.
  string seq_names[] = {"ibex_icache_back_line_vseq",
                        "ibex_icache_base_vseq", // for sanity test
                        "ibex_icache_caching_vseq",
                        "ibex_icache_ecc_vseq",
                        "ibex_icache_invalidation_vseq",
                        "ibex_icache_many_errors_vseq",
                        "ibex_icache_passthru_vseq"};

  // How many sequences have we executed so far?
  int unsigned seqs_so_far = 0;

  // The child (virtual) sequence
  ibex_icache_base_vseq child_seq;

  // The previous sequence that we ran.
  ibex_icache_base_vseq prev_seq = null;

  task body();
    int unsigned trans_so_far = 0;

    while (trans_so_far < num_trans) begin
      int unsigned seq_idx;
      uvm_sequence seq;
      int unsigned trans_now;
      bit          should_reset;

      seq_idx = $urandom_range(0, seq_names.size - 1);

      // Pick the number of transactions to run. We don't want too many, because the whole point is
      // that we're interested in the edges between sequences. Note that we don't bother to ensure
      // that trans_so_far + trans_now <= num_trans: it won't really matter if we overshoot by a
      // little.
      trans_now = $urandom_range(50, 100);

      should_reset = $urandom_range(0, 1);

      `uvm_info(`gfn,
                $sformatf("Running sequence '%s' (%0d transactions; reset=%0d).",
                          seq_names[seq_idx], trans_now, should_reset),
                UVM_HIGH)

      seq = create_seq_by_name(seq_names[seq_idx]);
      `downcast(child_seq, seq)

      child_seq.set_sequencer(p_sequencer);
      `DV_CHECK_RANDOMIZE_FATAL(child_seq)

      child_seq.num_trans = trans_now;
      child_seq.do_dut_init = should_reset;
      child_seq.prev_sequence = prev_seq;

      child_seq.start(p_sequencer, this);

      prev_seq = child_seq;
      trans_so_far += trans_now;
      seqs_so_far  += 1;
    end
  endtask : body

endclass : ibex_icache_combo_vseq
