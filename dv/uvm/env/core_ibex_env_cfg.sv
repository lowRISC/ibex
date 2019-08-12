// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class core_ibex_env_cfg extends uvm_object;

  bit       enable_irq_seq;
  bit       enable_debug_seq;
  bit[31:0] pass_val, fail_val;
  bit[31:0] end_signature_addr;

  `uvm_object_utils_begin(core_ibex_env_cfg)
    `uvm_field_int(enable_irq_seq,   UVM_DEFAULT)
    `uvm_field_int(enable_debug_seq, UVM_DEFAULT)
    `uvm_field_int(pass_val, UVM_DEFAULT)
    `uvm_field_int(fail_val, UVM_DEFAULT)
    `uvm_field_int(end_signature_addr, UVM_DEFAULT)
  `uvm_object_utils_end

  function new(string name = "");
    super.new(name);
    void'($value$plusargs("enable_irq_seq=%0d", enable_irq_seq));
    void'($value$plusargs("enable_debug_seq=%0d", enable_debug_seq));
    void'($value$plusargs("pass_val=%0h", pass_val));
    void'($value$plusargs("fail_val=%0h", fail_val));
    void'($value$plusargs("end_signature_addr=%0h", end_signature_addr));
  endfunction

endclass
