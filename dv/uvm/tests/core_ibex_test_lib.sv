// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// CSR test class
class core_ibex_csr_test extends core_ibex_base_test;

  `uvm_component_utils(core_ibex_csr_test)
  `uvm_component_new

  virtual task wait_for_test_done();
    bit[ibex_mem_intf_agent_pkg::DATA_WIDTH-1:0] signature_data;
    fork
    begin
      fork
        wait_for_mem_txn(cfg.signature_addr, cfg.pass_val, signature_data);
        wait_for_mem_txn(cfg.signature_addr, cfg.fail_val, signature_data);
      join_any
      disable fork;
      if (signature_data == cfg.pass_val) begin
        `uvm_info(`gfn, "CSR test completed successfully!", UVM_LOW)
      end else if (signature_data == cfg.fail_val) begin
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

// Debug test class
class core_ibex_debug_test extends core_ibex_base_test;

  bit[ibex_mem_intf_agent_pkg::DATA_WIDTH-1:0] core_start_data;

  `uvm_component_utils(core_ibex_debug_test)
  `uvm_component_new

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    dut_vif.fetch_enable = 1'b0;
    clk_vif.wait_clks(100);
    load_binary_to_mem();
    dut_vif.fetch_enable = 1'b1;
    fork
      vseq.start(env.vseqr);
      begin
        if (cfg.require_signature_addr) begin
          wait_for_mem_txn(cfg.signature_addr, cfg.core_start_req, core_start_data);
        end else begin
          // If no signature_addr functionality is desired, then the test will
          // simply wait for an adequate number of cycles
          clk_vif.wait_clks(stimulus_delay);
        end
        fork
          if (cfg.enable_irq_seq) begin
            vseq.start_irq_seq();
          end
          if (cfg.enable_debug_seq) begin
            vseq.start_debug_seq();
          end
        join_none
      end
    join_none
    wait_for_test_done();
    phase.drop_objection(this);
  endtask

endclass
