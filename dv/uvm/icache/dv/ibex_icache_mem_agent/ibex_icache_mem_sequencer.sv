// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequencer class for the icache memory agent.

class ibex_icache_mem_sequencer
  extends dv_base_sequencer #(.ITEM_T (ibex_icache_mem_resp_item),
                              .CFG_T  (ibex_icache_mem_agent_cfg));

  `uvm_component_utils(ibex_icache_mem_sequencer)
  `uvm_component_new

  uvm_tlm_analysis_fifo #(ibex_icache_mem_req_item) request_fifo;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    request_fifo   = new("request_fifo", this);
  endfunction

endclass
