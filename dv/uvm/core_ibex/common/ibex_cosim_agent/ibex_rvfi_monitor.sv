// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_rvfi_monitor extends uvm_monitor;
  protected virtual core_ibex_rvfi_if vif;

  uvm_analysis_port#(ibex_rvfi_seq_item) item_collected_port;

  `uvm_component_utils(ibex_rvfi_monitor)
  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    item_collected_port = new("item_collected_port", this);

    if(!uvm_config_db#(virtual core_ibex_rvfi_if)::get(this, "", "rvfi_if", vif)) begin
      `uvm_fatal("NOVIF", {"virtual interface must be set for: ", get_full_name(), ".vif"});
    end
  endfunction: build_phase

  virtual task run_phase(uvm_phase phase);
    ibex_rvfi_seq_item trans_collected;

    wait (vif.monitor_cb.reset === 1'b0);

    forever begin
      // Wait for a retired instruction
      while(!(vif.monitor_cb.valid || vif.monitor_cb.ext_irq_valid)) vif.wait_clks(1);

      // Read instruction details from RVFI interface
      trans_collected                  = ibex_rvfi_seq_item::type_id::create("trans_collected");
      trans_collected.irq_only         = !vif.monitor_cb.valid && vif.monitor_cb.ext_irq_valid;
      trans_collected.trap             = vif.monitor_cb.trap;
      trans_collected.pc               = vif.monitor_cb.pc_rdata;
      trans_collected.rd_addr          = vif.monitor_cb.rd_addr;
      trans_collected.rd_wdata         = vif.monitor_cb.rd_wdata;
      trans_collected.order            = vif.monitor_cb.order;
      trans_collected.pre_mip          = vif.monitor_cb.ext_pre_mip;
      trans_collected.post_mip         = vif.monitor_cb.ext_post_mip;
      trans_collected.nmi              = vif.monitor_cb.ext_nmi;
      trans_collected.nmi_int          = vif.monitor_cb.ext_nmi_int;
      trans_collected.debug_req        = vif.monitor_cb.ext_debug_req;
      trans_collected.rf_wr_suppress   = vif.monitor_cb.ext_rf_wr_suppress;
      trans_collected.mcycle           = vif.monitor_cb.ext_mcycle;
      trans_collected.ic_scr_key_valid = vif.monitor_cb.ext_ic_scr_key_valid;

      for (int i=0; i < 10; i++) begin
       trans_collected.mhpmcounters[i]  = vif.monitor_cb.ext_mhpmcounters[i];
       trans_collected.mhpmcountersh[i] = vif.monitor_cb.ext_mhpmcountersh[i];
      end

      `uvm_info(get_full_name(), $sformatf("Seen instruction:\n%s", trans_collected.sprint()),
        UVM_HIGH)

      item_collected_port.write(trans_collected);

      vif.wait_clks(1);
    end
  endtask : run_phase
endclass : ibex_rvfi_monitor
