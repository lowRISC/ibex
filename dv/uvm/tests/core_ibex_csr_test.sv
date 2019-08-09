// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class core_ibex_csr_test extends core_ibex_base_test;

  `uvm_component_utils(core_ibex_csr_test)

  function new(string name="", uvm_component parent=null);
    super.new(name, parent);
  endfunction

  virtual task wait_for_test_done();
    fork
    begin
      wait(dmem_vif.request && dmem_vif.we && dmem_vif.grant &&
           dmem_vif.addr == cfg.end_signature_addr);
      if (dmem_vif.wdata == cfg.pass_val) begin
        `uvm_info(`gfn, "CSR test completed successfully!", UVM_LOW)
      end else if (dmem_vif.wdata == cfg.fail_val) begin
        `uvm_error(`gfn, "CSR TEST_FAILED!")
      end else begin
        `uvm_fatal(`gfn, "CSR test values are not configured properly")
      end
    end
    begin
      clk_vif.wait_clks(timeout_in_cycles);
      `uvm_fatal(`gfn, "TEST TIMEOUT!!")
    end
    join_any
  endtask

endclass
