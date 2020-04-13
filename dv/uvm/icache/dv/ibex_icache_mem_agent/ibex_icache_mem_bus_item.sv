// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A transaction item that represents something happening on the memory bus. A 'request' is
// initiated by the cache and comes with an address. A 'response' comes from the memory system
// (including possibly the PMP checker). It comes with data and error flags.

class ibex_icache_mem_bus_item extends uvm_sequence_item;

  // Is this a request or a response?
  logic        is_response;

  // Request address (only valid for request transactions)
  logic [31:0] address;

  // Response data and error flags (only valid for response transactions)
  logic [31:0] rdata;
  logic        err;
  logic        pmp_err;

  `uvm_object_utils_begin(ibex_icache_mem_bus_item)
    `uvm_field_int(is_response, UVM_DEFAULT)
    `uvm_field_int(address,     UVM_DEFAULT | UVM_HEX)
    `uvm_field_int(rdata,       UVM_DEFAULT | UVM_HEX)
    `uvm_field_int(err,         UVM_DEFAULT)
    `uvm_field_int(pmp_err,     UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

endclass
