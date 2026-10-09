import uvm_pkg::*;
import core_ibex_testrig_env_pkg::*;

class core_ibex_testrig_test extends uvm_test;
  `uvm_component_utils(core_ibex_testrig_test)
  `uvm_component_new

  core_ibex_testrig_env testrig_env;

  virtual clk_rst_if clk_vif;

  virtual function void build_phase(uvm_phase phase);
    testrig_env = core_ibex_testrig_env::type_id::create("testrig_env", this);

    if (!uvm_config_db#(virtual clk_rst_if)::get(null, "", "clk_if", clk_vif)) begin
      `uvm_fatal(`gfn, "Cannot get clk_if")
    end
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
  endtask
endclass
