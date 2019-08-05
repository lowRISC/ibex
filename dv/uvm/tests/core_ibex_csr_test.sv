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
      wait(dut_vif.ecall === 1'b1);
      `uvm_info(`gfn, "ECALL instruction is detected, test done", UVM_LOW)
      //dut_vif.fetch_enable = 1'b0;
      wait(regfile_vif.we_a && regfile_vif.waddr_a === 3);
      if (regfile_vif.wdata_a === 1) begin
        `uvm_info(`gfn, "CSR TEST PASSED", UVM_LOW)
      end else if (regfile_vif.wdata_a === 2) begin
        // error/fatal
        `uvm_info(`gfn, "CSR TEST FAILED", UVM_LOW)
      end
    end
    begin
      clk_vif.wait_clks(timeout_in_cycles);
      `uvm_fatal(`gfn, "TEST TIMEOUT!!")
    end
    join_any
  endtask

endclass
