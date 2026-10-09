// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifndef TESTRIG_DPI_SVH
`define TESTRIG_DPI_SVH

// The layout of this must match the layout of the RVFI_DII_Execution_Packet structure in
// testrig.cc. WARNING: The fields listed here are in reverse order compared to C++.
typedef struct packed {
  bit [7:0] rvfi_intr;        // [87] Trap handler:                 Set for first instruction in trap handler.
  bit [7:0] rvfi_halt;        // [86] Halt indicator:               Marks the last instruction retired
                              //                                      before halting execution.
  bit [7:0] rvfi_trap;        // [85] Trap indicator:               Invalid decode, misaligned access or
                              //                                      jump command to misaligned address.
  bit [7:0] rvfi_rd_addr;     // [84]      Write register address:  MUST be 0 if not used.
  bit [7:0] rvfi_rs2_addr;    // [83]                               otherwise set as decoded.
  bit [7:0] rvfi_rs1_addr;    // [82]      Read register addresses: Can be arbitrary when not used,
  bit [7:0] rvfi_mem_wmask;   // [81]      Write mask:              Indicates valid bytes written. 0 if unused.
  bit [7:0] rvfi_mem_rmask;   // [80]      Read mask:               Indicates valid bytes read. 0 if unused.
  bit [63:0] rvfi_mem_wdata;  // [72 - 79] Write data:              Data written to memory by this command.
  bit [63:0] rvfi_mem_rdata;  // [64 - 71] Read data:               Data read from mem_addr (i.e. before write)
  bit [63:0] rvfi_mem_addr;   // [56 - 63] Memory access addr:      Points to byte address (aligned if define
                              //                                      is set). *Should* be straightforward.
                              //                                      0 if unused.
  bit [63:0] rvfi_rd_wdata;   // [48 - 55] Write register value:    MUST be 0 if rd_ is 0.
  bit [63:0] rvfi_rs2_data;   // [40 - 47]                          above. Must be 0 if register ID is 0.
  bit [63:0] rvfi_rs1_data;   // [32 - 39] Read register values:    Values as read from registers named
  bit [63:0] rvfi_insn;       // [24 - 31] Instruction word:        32-bit command value.
  bit [63:0] rvfi_pc_wdata;   // [16 - 23] PC after instr:          Following PC - either PC + 4 or jump/trap target.
  bit [63:0] rvfi_pc_rdata;   // [08 - 15] PC before instr:         PC for current instruction
  bit [63:0] rvfi_order;      // [00 - 07] Instruction number:      INSTRET value after completion.
} testrig_rvfi_exec_pkt_t;

import "DPI-C" function chandle testrig_create(int port);
import "DPI-C" function bit testrig_get_next_instruction(chandle testrig_conn,
                                                         output bit[31:0] dii_insn,
                                                         output bit[15:0] dii_time,
                                                         output bit[7:0]  dii_cmd);
import "DPI-C" function void testrig_send_rvfi_halt(chandle testrig_conn);
import "DPI-C" function void testrig_send_exec_pkt(chandle testrig_conn, testrig_rvfi_exec_pkt_t exec_pkt);

`endif
