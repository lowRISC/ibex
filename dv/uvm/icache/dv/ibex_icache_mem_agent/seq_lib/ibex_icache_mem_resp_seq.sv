// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Slave response sequence

class ibex_icache_mem_resp_seq extends ibex_icache_mem_base_seq;

  ibex_icache_mem_model #(.BusWidth (32)) mem_model;

  `uvm_object_utils(ibex_icache_mem_resp_seq)
  `uvm_object_new

  task pre_start();
    super.pre_start();
    mem_model = new("mem_model", cfg.disable_pmp_errs, cfg.disable_mem_errs);
  endtask

  task body();
    ibex_icache_mem_req_item  req_item  = new("req_item");
    ibex_icache_mem_resp_item resp_item = new("resp_item");

    forever begin
      // Wait for a transaction request.
      p_sequencer.request_fifo.get(req_item);

      if (!req_item.is_grant) begin
        // If this is a request (not a grant), check the memory model for a PMP error at this
        // address. The other fields are ignored.
        resp_item.is_grant = 1'b0;
        resp_item.err      = mem_model.is_pmp_error(req_item.address);
        resp_item.rdata    = 'X;
        `uvm_info(`gfn,
                  $sformatf("Seen request at address 0x%08h (PMP error? %0d)",
                            req_item.address, resp_item.err),
                  UVM_LOW)

      end else begin
        // If this is a grant, take any new seed then check the memory model for a (non-PMP) error
        // at this address. On success, look up the memory data too.

        if (req_item.seed != 32'd0) begin
          `uvm_info(`gfn, $sformatf("New memory seed: 0x%08h", req_item.seed), UVM_HIGH)
          mem_model.set_seed(req_item.seed);
        end

        resp_item.is_grant = 1'b1;
        resp_item.err      = mem_model.is_mem_error(req_item.address);
        resp_item.rdata    = resp_item.err ? 'X : mem_model.read_data(req_item.address);
      end

      // Use the response item as an entry in the sequence, randomising any delay
      start_item(resp_item);
      `DV_CHECK_RANDOMIZE_FATAL(resp_item)
      finish_item(resp_item);
    end
  endtask

endclass
