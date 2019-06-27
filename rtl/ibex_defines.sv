// Copyright lowRISC contributors.
// Copyright 2017 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Matthias Baer - baermatt@student.ethz.ch                   //
//                                                                            //
// Additional contributions by:                                               //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                                                                            //
//                                                                            //
// Design Name:    RISC-V processor core                                      //
// Project Name:   ibex                                                       //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Defines for various constants used by the processor core.  //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

/**
 * Defines for various constants used by the processor core
 */
package ibex_defines;


/////////////
// Opcodes //
/////////////

typedef enum logic [6:0] {
  OPCODE_SYSTEM = 7'h73,
  OPCODE_FENCE  = 7'h0f,
  OPCODE_OP     = 7'h33,
  OPCODE_OPIMM  = 7'h13,
  OPCODE_STORE  = 7'h23,
  OPCODE_LOAD   = 7'h03,
  OPCODE_BRANCH = 7'h63,
  OPCODE_JALR   = 7'h67,
  OPCODE_JAL    = 7'h6f,
  OPCODE_AUIPC  = 7'h17,
  OPCODE_LUI    = 7'h37
} opcode_e;


////////////////////
// ALU operations //
////////////////////

typedef enum logic [4:0] {
  // Arithmetics
  ALU_ADD,
  ALU_SUB,

  // Logics
  ALU_XOR,
  ALU_OR,
  ALU_AND,

  // Shifts
  ALU_SRA,
  ALU_SRL,
  ALU_SLL,

  // Comparisons
  ALU_LT,
  ALU_LTU,
  ALU_LE,
  ALU_LEU,
  ALU_GT,
  ALU_GTU,
  ALU_GE,
  ALU_GEU,
  ALU_EQ,
  ALU_NE,

  // Set lower than
  ALU_SLT,
  ALU_SLTU,
  ALU_SLET,
  ALU_SLETU
} alu_op_e;

typedef enum logic [1:0] {
  // Multiplier/divider
  MD_OP_MULL,
  MD_OP_MULH,
  MD_OP_DIV,
  MD_OP_REM
} md_op_e;


//////////////////////////////////
// Control and status registers //
//////////////////////////////////

// CSR operations
typedef enum logic [1:0] {
  CSR_OP_READ,
  CSR_OP_WRITE,
  CSR_OP_SET,
  CSR_OP_CLEAR
} csr_op_e;

// Privileged mode
typedef enum logic[1:0] {
  PRIV_LVL_M = 2'b11,
  PRIV_LVL_H = 2'b10,
  PRIV_LVL_S = 2'b01,
  PRIV_LVL_U = 2'b00
} priv_lvl_e;

// Constants for the dcsr.xdebugver fields
typedef enum logic[3:0] {
   XDEBUGVER_NO     = 4'd0, // no external debug support
   XDEBUGVER_STD    = 4'd4, // external debug according to RISC-V debug spec
   XDEBUGVER_NONSTD = 4'd15 // debug not conforming to RISC-V debug spec
} x_debug_ver_e;


//////////////
// ID stage //
//////////////

// Operand a selection
typedef enum logic[1:0] {
  OP_A_REG_A,
  OP_A_FWD,
  OP_A_CURRPC,
  OP_A_IMM
} op_a_sel_e;

// Immediate a selection
typedef enum logic {
  IMM_A_Z,
  IMM_A_ZERO
} imm_a_sel_e;

// Operand b selection
typedef enum logic {
  OP_B_REG_B,
  OP_B_IMM
} op_b_sel_e;

// Immediate b selection
typedef enum logic [2:0] {
  IMM_B_I,
  IMM_B_S,
  IMM_B_B,
  IMM_B_U,
  IMM_B_J,
  IMM_B_INCR_PC,
  IMM_B_INCR_ADDR
} imm_b_sel_e;


//////////////
// IF stage //
//////////////

// PC mux selection
typedef enum logic [2:0] {
  PC_BOOT,
  PC_JUMP,
  PC_EXCEPTION,
  PC_ERET,
  PC_DRET
} pc_sel_e;

// Exception PC mux selection
typedef enum logic [2:0] {
  EXC_PC_ILLINSN,
  EXC_PC_ECALL,
  EXC_PC_LOAD,
  EXC_PC_STORE,
  EXC_PC_IRQ,
  EXC_PC_DBD,
  EXC_PC_DBGEXC, // Exception while in debug mode
  EXC_PC_BREAKPOINT
} exc_pc_sel_e;

// Exception cause
typedef enum logic [5:0] {
  EXC_CAUSE_INSN_ADDR_MISA     = 6'h00,
  EXC_CAUSE_ILLEGAL_INSN       = 6'h02,
  EXC_CAUSE_BREAKPOINT         = 6'h03,
  EXC_CAUSE_LOAD_ACCESS_FAULT  = 6'h05,
  EXC_CAUSE_STORE_ACCESS_FAULT = 6'h07,
  EXC_CAUSE_ECALL_MMODE        = 6'h0B
} exc_cause_e;

// Exceptions offsets
// target address = {boot_addr[31:8], EXC_OFF} (boot_addr must be 32 BYTE aligned!)
// offset 00 to 7e is used for external interrupts

// TODO: The behavior below follows an outdated (pre-1.10) RISC-V Privileged
// Spec to implement a "free-form" vectored trap handler.
// We need to update this code and crt0.S to follow the new mtvec spec.
typedef enum logic [7:0] {
  EXC_OFF_RST        = 8'h80,
  EXC_OFF_ILLINSN    = 8'h84,
  EXC_OFF_ECALL      = 8'h88,
  EXC_OFF_LSUERR     = 8'h8c,
  EXC_OFF_BREAKPOINT = 8'h90
} exc_off_e;

// Debug cause
typedef enum logic [2:0] {
  DBG_CAUSE_NONE    = 3'h0,
  DBG_CAUSE_EBREAK  = 3'h1,
  DBG_CAUSE_TRIGGER = 3'h2,
  DBG_CAUSE_HALTREQ = 3'h3,
  DBG_CAUSE_STEP    = 3'h4
} dbg_cause_e;

// CSRs
typedef enum logic[11:0] {
  // Machine information
  CSR_MHARTID   = 12'hF14,

  // Machine trap setup
  CSR_MSTATUS   = 12'h300,
  CSR_MISA      = 12'h301,
  CSR_MTVEC     = 12'h305,

  // Machine trap handling
  CSR_MEPC      = 12'h341,
  CSR_MCAUSE    = 12'h342,

  // Debug/trace
  CSR_DCSR      = 12'h7b0,
  CSR_DPC       = 12'h7b1,

  // Debug
  CSR_DSCRATCH0 = 12'h7b2, // optional
  CSR_DSCRATCH1 = 12'h7b3, // optional

  // Machine Counter/Timers
  CSR_MCOUNTINHIBIT      = 12'h320,
  CSR_MCYCLE             = 12'hB00,
  CSR_MCYCLEH            = 12'hB80,
  CSR_MINSTRET           = 12'hB02,
  CSR_MINSTRETH          = 12'hB82
} csr_num_e;

// CSR mhpmcounter-related offsets and mask
parameter logic [11:0] CSR_OFF_MCOUNTER_SETUP = 12'h320; // mcounter_setup @ 12'h323 - 12'h33F
parameter logic [11:0] CSR_OFF_MCOUNTER       = 12'hB00; // mcounter       @ 12'hB03 - 12'hB1F
parameter logic [11:0] CSR_OFF_MCOUNTERH      = 12'hB80; // mcounterh      @ 12'hB83 - 12'hB9F
parameter logic [11:0] CSR_MASK_MCOUNTER      = 12'hFE0;

endpackage
