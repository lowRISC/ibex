// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

typedef class ibex_testrig_agent;

// This driver is a plain uvm_component rather than a uvm_driver because it has no need for the
// sequence functionality. It's being controlled directly by DII packets from TestRIG. This is all
// handled internally to the class rather than using an external sequencer to feed in the packets.
class ibex_testrig_dii_driver extends uvm_component;
  `uvm_component_utils(ibex_testrig_dii_driver)
  `uvm_component_new

  ibex_testrig_agent agent;

  // Instruction to inject once we've hit a reset packet and we're waiting for the remaining
  // instruction to retire.
  parameter bit [31:0] DII_END_INSN = 32'h13; // NOP addi x0, x0, 0

  typedef enum logic [7:0] {
    DII_CMD_RST = 0,
    DII_CMD_INSN = 1
    //TODO add interrupt command.
  } dii_cmd_e;

  virtual core_ibex_dii_intf dii_vif;
  virtual clk_rst_if clk_vif;
  chandle testrig_conn;
  bit     dii_stream_begun;
  int     insn_wait_timeouts;
  int     insn_wait_timeout_limit = 10;

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if (!uvm_config_db#(virtual clk_rst_if)::get(this, "*", "clk_if", clk_vif)) begin
      `uvm_fatal(`gfn, "clk_if must be provided");
    end

    if (!uvm_config_db#(chandle)::get(this, "*", "testrig_conn", testrig_conn)) begin
      `uvm_fatal(`gfn, "testrig_conn must be provided");
    end

    if (!uvm_config_db#(virtual core_ibex_dii_intf)::get(this, "*", "dii_if", dii_vif)) begin
      `uvm_fatal(`gfn, "dif_if must be provided");
    end
  endfunction : build_phase

  task run_phase(uvm_phase phase);
    bit [31:0] dii_insn;
    bit [15:0] dii_time;
    bit [7:0]  dii_cmd;

    super.run_phase(phase);

    dii_vif.cb.dii_insn <= '0;
    dii_stream_begun = 0;

    clk_vif.wait_for_reset();
    @dii_vif.cb;
    dii_vif.enable_count_instr();

    forever begin
      `uvm_info(`gfn, "Waiting for next DII packet", UVM_HIGH)

      while (!testrig_get_next_instruction(testrig_conn, dii_insn, dii_time, dii_cmd)) begin
        //TODO remove timeout once VCS launch and kill is under the control of
        // TestRIG's run script. Otherwise the simulation will not survive the
        // wait for a user to input a filename after a failing trace.
        if (dii_stream_begun) begin
          // Once we've begun receiving DII packets we'll timeout and kill the simulation if we
          // don't see one for longer than the timeout interval.
          insn_wait_timeouts++;

          if (insn_wait_timeouts > insn_wait_timeout_limit) begin
            `uvm_fatal(`gfn, "Timeout waiting for next DII packet")
          end
        end
      end

      dii_stream_begun = 1;
      insn_wait_timeouts = 0;

      `uvm_info(`gfn, $sformatf("Receive a DII packet %x %x %x", dii_insn, dii_time, dii_cmd),
        UVM_HIGH);

      if (dii_cmd == DII_CMD_RST) begin
        `uvm_info(`gfn, "Received reset command, inject NOPs until remaining instructions retire",
          UVM_LOW);

        // We need to wait until all of the injected instructions have retired so begin issuing NOPs
        // and stop counting instructions in (as we've now counted all of the DII instructions).
        dii_vif.cb.dii_insn <= DII_END_INSN;
        dii_vif.disable_count_instr();

        `uvm_info(`gfn,
          $sformatf("Seen %d instructions in and %d instructions out, waiting for the rest",
          dii_vif.instr_in, dii_vif.instr_out), UVM_LOW);

        // Tell the agent how many instructions that have been injected. The hold will stop it
        // sending more than that number back on RVFI.
        agent.set_hold_rvfi_send(dii_vif.instr_in);

        // Wait for all of the injected instructions to retire and RVFI
        // instruction packets to be sent.
        wait (dii_vif.instr_out >= dii_vif.instr_in);
        @dii_vif.cb;

        // Reset the core.
        `uvm_info(`gfn, "Performing reset", UVM_LOW);
        clk_vif.apply_reset(.reset_width_clks(2));
        @dii_vif.cb;
        // Restart counting instructions in after reset (the reset itself will have cleared the
        // instruction counts)
        dii_vif.enable_count_instr();
      end if (dii_cmd == DII_CMD_INSN) begin
        `uvm_info(`gfn, $sformatf("Injecting instruction %x", dii_insn), UVM_HIGH);

        dii_vif.cb.dii_insn <= dii_insn;
        @dii_vif.cb;

        while (!dii_vif.cb.dii_ack) begin
          @dii_vif.cb;
          `uvm_info(`gfn, "Waiting for ack", UVM_HIGH);
        end

        `uvm_info(`gfn, "Ack seen", UVM_HIGH);
      end
    end
  endtask : run_phase
endclass
