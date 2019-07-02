// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class irq_master_driver extends uvm_driver #(irq_seq_item);

  // The virtual interface used to drive and view HDL signals.
  protected virtual irq_if vif;

  `uvm_component_utils(irq_master_driver)
  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual irq_if)::get(this, "", "vif", vif)) begin
      `uvm_fatal("NOVIF",{"virtual interface must be set for: ",get_full_name(),".vif"});
    end
  endfunction: build_phase

  virtual task run_phase(uvm_phase phase);
    fork
      get_and_drive();
      reset_signals();
    join
  endtask : run_phase

  virtual protected task get_and_drive();
    @(negedge vif.reset);
    forever begin
      seq_item_port.try_next_item(req);
      if (req != null) begin
        $cast(rsp, req.clone());
        rsp.set_id_info(req);
        drive_seq_item(rsp);
        seq_item_port.item_done(rsp);
      end else begin
        @(posedge vif.clock);
      end
    end
  endtask : get_and_drive

  virtual protected task reset_signals();
    forever begin
      @(posedge vif.reset);
      vif.irq_i      <= 'h0;
      vif.irq_id_i   <= 'hz;
    end
  endtask : reset_signals

  virtual protected task drive_seq_item (irq_seq_item trans);
    if (trans.delay > 0) begin
      repeat(trans.delay) @(posedge vif.clock);
    end
    vif.irq_i     <= 1'b1;
    vif.irq_id_i  <= trans.irq_id;
    @(posedge vif.clock);
    while (vif.irq_ack_o !== 1'b1) begin
      @(posedge vif.clock);
    end
    trans.irq_id_o = vif.irq_id_o;
    vif.irq_i     <= 'h0;
    vif.irq_id_i  <= 'hz;
  endtask : drive_seq_item

endclass : irq_master_driver

