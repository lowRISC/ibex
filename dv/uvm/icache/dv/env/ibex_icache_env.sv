// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_env extends dv_base_env #(
    .CFG_T              (ibex_icache_env_cfg),
    .COV_T              (ibex_icache_env_cov),
    .VIRTUAL_SEQUENCER_T(ibex_icache_virtual_sequencer),
    .SCOREBOARD_T       (ibex_icache_scoreboard)
  );
  `uvm_component_utils(ibex_icache_env)

  ibex_icache_core_agent core_agent;
  ibex_icache_mem_agent  mem_agent;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // create components
    core_agent = ibex_icache_core_agent::type_id::create("core_agent", this);
    uvm_config_db#(ibex_icache_core_agent_cfg)::set(this, "core_agent*", "cfg", cfg.core_agent_cfg);

    mem_agent = ibex_icache_mem_agent::type_id::create("mem_agent", this);
    uvm_config_db#(ibex_icache_mem_agent_cfg)::set(this, "mem_agent*", "cfg", cfg.mem_agent_cfg);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg.en_scb) begin
      core_agent.monitor.analysis_port.connect(scoreboard.core_fifo.analysis_export);
      mem_agent.monitor.analysis_port.connect(scoreboard.mem_fifo.analysis_export);
    end
    if (cfg.is_active && cfg.core_agent_cfg.is_active) begin
      virtual_sequencer.core_sequencer_h = core_agent.sequencer;
    end
    if (cfg.is_active && cfg.mem_agent_cfg.is_active) begin
      virtual_sequencer.mem_sequencer_h = mem_agent.sequencer;
    end
  endfunction

endclass
