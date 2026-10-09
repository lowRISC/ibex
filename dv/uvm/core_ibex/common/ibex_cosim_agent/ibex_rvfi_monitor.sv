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
      logic [31:0] mem_wmask_bits;
      logic [31:0] mem_rmask_bits;

      // Wait for a retired instruction
      while(!(vif.monitor_cb.valid || vif.monitor_cb.ext_irq_valid)) vif.wait_clks(1);

      // Read instruction details from RVFI interface.
      trans_collected                   = ibex_rvfi_seq_item::type_id::create("trans_collected");
      // Most of these are used by both Ibex co-simulation and TestRIG.
      // Some are used only by either Ibex cosim or TestRIG.
      trans_collected.intr              = vif.monitor_cb.intr; // TestRIG
      trans_collected.irq_only          = !vif.monitor_cb.valid && vif.monitor_cb.ext_irq_valid; // ibex cosim
      trans_collected.trap              = vif.monitor_cb.trap;
      trans_collected.insn              = vif.monitor_cb.insn;
      trans_collected.pc                = vif.monitor_cb.pc_rdata;
      trans_collected.pc_wdata          = vif.monitor_cb.pc_wdata;
      trans_collected.rd_addr           = vif.monitor_cb.rd_addr;
      trans_collected.rd_wdata          = vif.monitor_cb.rd_wdata;
      trans_collected.rd_wcap           = vif.monitor_cb.rd_wcap;
      trans_collected.order             = vif.monitor_cb.order;
      trans_collected.rs1_addr          = vif.monitor_cb.rs1_addr;
      trans_collected.rs1_data          = vif.monitor_cb.rs1_rdata;
      trans_collected.rs1_rcap          = vif.monitor_cb.rs1_rcap;
      trans_collected.rs2_addr          = vif.monitor_cb.rs2_addr;
      trans_collected.rs2_data          = vif.monitor_cb.rs2_rdata;
      trans_collected.rs2_rcap          = vif.monitor_cb.rs2_rcap;
      trans_collected.pre_mip           = vif.monitor_cb.ext_pre_mip;
      trans_collected.post_mip          = vif.monitor_cb.ext_post_mip;
      trans_collected.nmi               = vif.monitor_cb.ext_nmi;
      trans_collected.nmi_int           = vif.monitor_cb.ext_nmi_int;
      trans_collected.debug_req         = vif.monitor_cb.ext_debug_req;
      trans_collected.rf_wr_suppress    = vif.monitor_cb.ext_rf_wr_suppress;
      trans_collected.mcycle            = vif.monitor_cb.ext_mcycle;
      trans_collected.ic_scr_key_valid  = vif.monitor_cb.ext_ic_scr_key_valid;

      // TestRIG memory access details
      trans_collected.mem_wmask = vif.monitor_cb.mem_wmask;
      trans_collected.mem_rmask = vif.monitor_cb.mem_rmask;
      mem_wmask_bits = {{8{vif.monitor_cb.mem_wmask[3]}},
                        {8{vif.monitor_cb.mem_wmask[2]}},
                        {8{vif.monitor_cb.mem_wmask[1]}},
                        {8{vif.monitor_cb.mem_wmask[0]}}};
      mem_rmask_bits = {{8{vif.monitor_cb.mem_rmask[3]}},
                        {8{vif.monitor_cb.mem_rmask[2]}},
                        {8{vif.monitor_cb.mem_rmask[1]}},
                        {8{vif.monitor_cb.mem_rmask[0]}}};
      trans_collected.mem_wdata  = vif.monitor_cb.mem_wdata & mem_wmask_bits;
      trans_collected.mem_rdata  = vif.monitor_cb.mem_rdata & mem_rmask_bits;
      trans_collected.mem_is_cap = vif.monitor_cb.mem_is_cap;
      trans_collected.mem_wcap   = vif.monitor_cb.mem_wcap;
      trans_collected.mem_rcap   = vif.monitor_cb.mem_rcap;
      trans_collected.mem_addr   =
        vif.monitor_cb.mem_wmask != 0 || vif.monitor_cb.mem_rmask != 0 ? vif.monitor_cb.mem_addr :
                                                                         '0;

      // Ibex cosim counter details
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
