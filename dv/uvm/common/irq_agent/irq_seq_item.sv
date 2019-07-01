// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class irq_seq_item extends uvm_sequence_item;

  rand bit [4:0] irq_id;
  rand bit [3:0] delay;
  rand bit [4:0] irq_id_o;

  `uvm_object_utils_begin(irq_seq_item)
    `uvm_field_int(irq_id,   UVM_DEFAULT)
    `uvm_field_int(irq_id_o, UVM_DEFAULT)
    `uvm_field_int(delay,    UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

endclass : irq_seq_item
