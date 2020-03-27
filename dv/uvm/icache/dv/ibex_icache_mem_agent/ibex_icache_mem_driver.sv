// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Drive the memory <-> icache interface
//
// There are 3 different signals getting driven here:
//
//    (1) GNT:     This toggles randomly, completely ignoring any other signals.
//    (2) PMP_ERR: This can be set as a result of taking a bad request.
//    (3) RDATA:   This gets set with response data some time after granting a request.

class ibex_icache_mem_driver
  extends dv_base_driver #(.ITEM_T (ibex_icache_mem_resp_item),
                           .CFG_T  (ibex_icache_mem_agent_cfg));

  int unsigned min_grant_delay = 0;
  int unsigned max_grant_delay = 10;

  mailbox #(ibex_icache_mem_resp_item) rdata_queue;
  bit                                  pmp_driven;

  `uvm_component_utils(ibex_icache_mem_driver)
  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    rdata_queue = new("rdata_queue");
    pmp_driven  = 1'b0;
  endfunction

  virtual task reset_signals();
    cfg.vif.reset();
  endtask

  virtual task get_and_drive();
    // None of these processes terminate
    fork
      drive_grant();
      take_requests();
      drive_responses();
    join
  endtask

  // Drive the grant line. This toggles independently of any other signal on the bus.
  task automatic drive_grant();
    int gnt_delay;

    forever begin
      // Pick a number of cycles for the grant line to be low
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(gnt_delay,
                                         gnt_delay dist {
                                           min_grant_delay                         :/ 3,
                                           [min_grant_delay+1 : max_grant_delay-1] :/ 1,
                                           max_grant_delay                         :/ 1
                                         };)
      repeat(gnt_delay) @(cfg.vif.driver_cb);

      // Set the grant line high for a cycle then go around again. Note that the grant line will be
      // high for two consecutive cycles if gnt_delay is 0.
      cfg.vif.driver_cb.gnt <= 1'b1;
      @(cfg.vif.driver_cb);
      cfg.vif.driver_cb.gnt <= 1'b0;
    end
  endtask

  // Take requests from the sequencer.
  task automatic take_requests();
    forever begin
      seq_item_port.get_next_item(req);
      `uvm_info(`gfn, $sformatf("rcvd item:\n%0s", req.sprint()), UVM_HIGH)

      // Is this a request or a grant?
      if (!req.is_grant) begin
        // If a request, we'll deal with it immediately, spawning a process that drives the PMP line
        // until the request goes away.
        fork
          drive_pmp(req.err);
        join_none
      end else begin
        // If a grant, we take a copy and add it to the response queue (handled by drive_responses)
        $cast(rsp, req.clone());
        rsp.set_id_info(req);
        rdata_queue.put(rsp);
      end

      seq_item_port.item_done();
    end
  endtask

  // Drive the rdata/valid/err response lines
  task automatic drive_responses();
    int unsigned delay;
    ibex_icache_mem_resp_item item;

    forever begin
      rdata_queue.get(item);
      cfg.vif.wait_clks(item.delay);
      cfg.vif.send_response(item.err, item.rdata);
    end
  endtask

  // Drive the PMP line.
  //
  // This task gets spawned by take_requests each time a new address comes in. The driver should
  // have at most one instance running at once.
  //
  // If err is false, there is nothing to do. If err is true, it sets the PMP error flag and then
  // waits until either req is de-asserted or the address changes, at which point it clears the flag
  // and exits.
  task automatic drive_pmp(bit err);

    // This is a simple check to make sure that only one instance of the drive_pmp task is running
    // at a time. If not, you'll have multiple drivers for the cfg.vif.pmp_err signal, which is
    // probably going to be very confusing. The logic in the monitor's collect_requests() task is
    // supposed to be in sync with this code so that this can't happen, but it can't hurt to make
    // sure.
    if (pmp_driven) begin
      `uvm_error(`gfn, "drive_pmp is not re-entrant: bug in monitor?")
      return;
    end

    if (! err)
      return;

    pmp_driven = 1'b1;
    cfg.vif.pmp_err <= 1'b1;

    // Wait for an address change or req to de-assert
    @(negedge cfg.vif.req or cfg.vif.addr);

    cfg.vif.pmp_err <= 1'b0;
    pmp_driven = 1'b0;
  endtask

endclass
