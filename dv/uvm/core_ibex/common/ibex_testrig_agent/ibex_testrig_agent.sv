// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// UVM agent to connect an Ibex simulation to TestRIG. TestRIG provides instructions as DII (direct
// instruction injection) packets and the simulation provides the results of retired instructions
// a RVFI (RISC-V formal interface) packets. The agent uses a DPI interface (contained in
// dv/testrig/dpi) to communicate with TestRIG via a socket interface.
//
// This agent contains a driver (ibex_testrig_dii_driver) which is responsible for handling all of
// the DII packets directly which include things such as reset and interrupts, along with
// instructions. The agent uses ibex_rvfi_monitor to gather retired instruction data from RVFI and
// send them back to TestRIG.
//
// TestRIG runs multiple tests against a single simulator session. It issues a reset command
// between tests. It expects one RVFI packet for each instruction issued via DII. After the final
// instruction has been issued and a reset packet is seen NOPs are injected into the pipeline until
// all of the injected instructions have been retired. The driver and agent keep track of the number
// of instructions injected in before the reset command is seen and ensure the same number of RVFI
// responses is sent back and no more. This prevents the NOPs injected at the end of the test being
// sent back to TestRIG on RVFI.

class ibex_testrig_agent extends uvm_agent;
  `uvm_component_utils(ibex_testrig_agent)

  ibex_rvfi_monitor rvfi_monitor;
  ibex_testrig_dii_driver dii_driver;
  virtual clk_rst_if clk_vif;
  chandle testrig_conn;

  bit hold_rvfi_send;
  int hold_rvfi_limit;
  int rvfi_num_seen;

  uvm_tlm_analysis_fifo #(ibex_rvfi_seq_item) rvfi_port;

  function new(string name="", uvm_component parent=null);
    super.new(name, parent);

    rvfi_port = new("rvfi_port", this);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    testrig_rvfi_exec_pkt_t exec_pkt = '0;

    super.build_phase(phase);

    //TODO make the port number a runtime argument.
    testrig_conn = testrig_create(6000);

    rvfi_monitor = ibex_rvfi_monitor::type_id::create("rvfi_monitor", this);
    dii_driver = ibex_testrig_dii_driver::type_id::create("dii_driver", this);

    if (!uvm_config_db#(virtual clk_rst_if)::get(this, "*", "clk_if", clk_vif)) begin
      `uvm_fatal(`gfn, "clk_if must be provided");
    end

    uvm_config_db#(chandle)::set(this, "*", "testrig_conn", testrig_conn);
  endfunction : build_phase

  virtual function void connect_phase(uvm_phase phase);
    dii_driver.agent = this;

    rvfi_monitor.item_collected_port.connect(rvfi_port.analysis_export);
  endfunction : connect_phase

  virtual task run_phase(uvm_phase phase);
    fork
      watch_for_reset();
      process_rvfi();
    join

  endtask : run_phase

  task watch_for_reset();
    clk_vif.wait_for_reset();

    forever begin
      `uvm_info(`gfn, "Watching for next reset", UVM_HIGH);
      @(negedge clk_vif.rst_n)

      // Wait a cycle to allow the RVFI monitor to see a final instruction
      clk_vif.wait_clks(1);

      if (rvfi_num_seen != 0 && !hold_rvfi_send) begin
        // When the core is reset either we've not injected any instructions (TestRIG will do
        // a reset before running any tests) or the DII driver should have signalled its seen
        // a reset packet after a number of instructions and set the RVFI hold. If we don't have
        // either of these cases something may have got out of sync.
        `uvm_warning(`gfn, {"Saw reset after a non-zero number of retired instructions but DII ",
                            "driver hasn't asked to hold send yet"})
      end

      `uvm_info(`gfn, "Seen reset, sending RVFI halt", UVM_LOW);
      `uvm_info(`gfn, $sformatf("%d total RVFI seen, %d RVFI send limit", rvfi_num_seen,
        hold_rvfi_limit), UVM_LOW);

      testrig_send_rvfi_halt(testrig_conn);

      rvfi_num_seen = 0;
      hold_rvfi_send = 1'b0;
    end
  endtask : watch_for_reset

  function testrig_rvfi_exec_pkt_t exec_pkt_from_rvfi(ibex_rvfi_seq_item seq_item);
    return '{
      rvfi_intr: seq_item.intr,
      rvfi_halt: 8'b0,
      rvfi_trap: seq_item.trap,

      rvfi_rd_addr:   seq_item.rd_addr,
      rvfi_rs2_addr:  seq_item.rs2_addr,
      rvfi_rs1_addr:  seq_item.rs1_addr,
      rvfi_mem_wmask: (seq_item.mem_is_cap && seq_item.mem_wmask != 0 ? 8'hFF : seq_item.mem_wmask),
      rvfi_mem_rmask: (seq_item.mem_is_cap && seq_item.mem_rmask != 0 ? 8'hFF : seq_item.mem_rmask),
      rvfi_mem_wdata: {seq_item.mem_wcap[31:0], seq_item.mem_wdata},
      rvfi_mem_rdata: {seq_item.mem_rcap[31:0], seq_item.mem_rdata},
      rvfi_mem_addr:  seq_item.mem_addr,

      rvfi_rd_wdata: {seq_item.rd_wcap[31:0], seq_item.rd_wdata},
      rvfi_rs2_data: {seq_item.rs1_rcap[31:0], seq_item.rs2_data},
      rvfi_rs1_data: {seq_item.rs2_rcap[31:0], seq_item.rs1_data},
      rvfi_insn:     seq_item.insn,
      rvfi_pc_wdata: seq_item.pc_wdata,
      rvfi_pc_rdata: seq_item.pc,
      rvfi_order:    seq_item.order
    };
  endfunction : exec_pkt_from_rvfi

  task process_rvfi();
    ibex_rvfi_seq_item rvfi_instr;
    testrig_rvfi_exec_pkt_t exec_pkt;

    hold_rvfi_send = 1'b0;
    rvfi_num_seen = 0;

    forever begin
      rvfi_port.get(rvfi_instr);
      exec_pkt = exec_pkt_from_rvfi(rvfi_instr);
      ++rvfi_num_seen;

      if (hold_rvfi_send) begin
        `uvm_info(`gfn, $sformatf("%d rvfi seen %d limit", rvfi_num_seen, hold_rvfi_limit),
          UVM_HIGH);
      end else begin
        `uvm_info(`gfn, $sformatf("%d rvfi seen no limit yet", rvfi_num_seen), UVM_HIGH);
      end

      if (hold_rvfi_send && rvfi_num_seen > hold_rvfi_limit) begin
        // When the DII driver receives a recent command it instructs the agent to hold RVFI at the
        // number of instructions injected. This stops the NOPs that are issued whilst the injected
        // instructions retire from being sent back to TestRIG.
        `uvm_info(`gfn, "At send limit, skipping send to testrig", UVM_HIGH);
        continue;
      end

      `uvm_info(`gfn, "Sending to testrig", UVM_HIGH);
      testrig_send_exec_pkt(testrig_conn, exec_pkt);
    end
  endtask : process_rvfi

  task set_hold_rvfi_send(int limit);
    hold_rvfi_send = 1'b1;
    hold_rvfi_limit = limit;
  endtask
endclass : ibex_testrig_agent
