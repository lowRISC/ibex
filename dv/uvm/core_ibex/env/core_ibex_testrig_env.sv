class core_ibex_testrig_env extends uvm_env;
  ibex_testrig_agent testrig_agent;

  `uvm_component_utils(core_ibex_testrig_env)
  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    testrig_agent = ibex_testrig_agent::type_id::create("testrig_agent", this);
  endfunction : build_phase
endclass
