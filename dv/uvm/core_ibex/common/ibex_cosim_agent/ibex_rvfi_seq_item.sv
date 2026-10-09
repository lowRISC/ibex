// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_rvfi_seq_item extends uvm_sequence_item;
  bit        intr;
  bit        irq_only;
  bit        trap;
  bit [31:0] insn;
  bit [31:0] pc;
  bit [31:0] pc_wdata;
  bit [4:0]  rd_addr;
  bit [31:0] rd_wdata;
  bit [32:0] rd_wcap;
  bit [4:0]  rs1_addr;
  bit [31:0] rs1_data;
  bit [32:0] rs1_rcap;
  bit [4:0]  rs2_addr;
  bit [31:0] rs2_data;
  bit [32:0] rs2_rcap;
  bit [63:0] order;
  bit [31:0] pre_mip; // AKA "mip"
  bit [31:0] post_mip;
  bit        nmi;
  bit        nmi_int;
  bit        debug_req;
  bit        rf_wr_suppress;
  bit [63:0] mcycle;
  bit        ic_scr_key_valid;

  bit [3:0]  mem_wmask;
  bit [3:0]  mem_rmask;
  bit [31:0] mem_wdata;
  bit [31:0] mem_rdata;
  bit        mem_is_cap;
  bit [32:0] mem_wcap;
  bit [32:0] mem_rcap;
  bit [31:0] mem_addr;

  bit [31:0] mhpmcounters  [10];
  bit [31:0] mhpmcountersh [10];

  `uvm_object_utils_begin(ibex_rvfi_seq_item)
    `uvm_field_int (trap, UVM_DEFAULT)
    `uvm_field_int (insn, UVM_DEFAULT)
    `uvm_field_int (pc, UVM_DEFAULT)
    `uvm_field_int (pc_wdata, UVM_DEFAULT)
    `uvm_field_int (rd_addr, UVM_DEFAULT)
    `uvm_field_int (rd_wdata, UVM_DEFAULT)
    `uvm_field_int (rd_wcap, UVM_DEFAULT)
    `uvm_field_int (rs1_addr, UVM_DEFAULT)
    `uvm_field_int (rs1_data, UVM_DEFAULT)
    `uvm_field_int (rs1_rcap, UVM_DEFAULT)
    `uvm_field_int (rs2_addr, UVM_DEFAULT)
    `uvm_field_int (rs2_data, UVM_DEFAULT)
    `uvm_field_int (rs2_rcap, UVM_DEFAULT)
    `uvm_field_int (order, UVM_DEFAULT)
    `uvm_field_int (pre_mip, UVM_DEFAULT)
    `uvm_field_int (post_mip, UVM_DEFAULT)
    `uvm_field_int (nmi, UVM_DEFAULT)
    `uvm_field_int (nmi_int, UVM_DEFAULT)
    `uvm_field_int (debug_req, UVM_DEFAULT)
    `uvm_field_int (rf_wr_suppress, UVM_DEFAULT)
    `uvm_field_int (mcycle, UVM_DEFAULT)
    `uvm_field_int (ic_scr_key_valid, UVM_DEFAULT)

    `uvm_field_int (mem_wmask, UVM_DEFAULT)
    `uvm_field_int (mem_rmask, UVM_DEFAULT)
    `uvm_field_int (mem_wdata, UVM_DEFAULT)
    `uvm_field_int (mem_rdata, UVM_DEFAULT)
    `uvm_field_int (mem_is_cap, UVM_DEFAULT)
    `uvm_field_int (mem_wcap, UVM_DEFAULT)
    `uvm_field_int (mem_rcap, UVM_DEFAULT)
    `uvm_field_int (mem_addr, UVM_DEFAULT)

    `uvm_field_sarray_int (mhpmcounters, UVM_DEFAULT)
    `uvm_field_sarray_int (mhpmcountersh, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

endclass : ibex_rvfi_seq_item
