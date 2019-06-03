// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// ibex processor core environment class
// ---------------------------------------------
class core_ibex_env extends uvm_env;

  ibex_mem_intf_slave_agent   data_if_slave_agent;
  ibex_mem_intf_slave_agent   instr_if_slave_agent;
  core_ibex_vseqr             vseqr;

  `uvm_component_utils(core_ibex_env)
  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    data_if_slave_agent = ibex_mem_intf_slave_agent::type_id::
                          create("data_if_slave_agent", this);
    instr_if_slave_agent = ibex_mem_intf_slave_agent::type_id::
                           create("instr_if_slave_agent", this);
    // Create virtual sequencer
    vseqr = core_ibex_vseqr::type_id::create("vseqr", this);
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    vseqr.data_if_seqr = data_if_slave_agent.sequencer;
    vseqr.instr_if_seqr = instr_if_slave_agent.sequencer;
  endfunction : connect_phase

endclass
