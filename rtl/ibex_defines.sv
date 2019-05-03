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
// Project Name:   ibex                                                 //
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

parameter OPCODE_SYSTEM    = 7'h73;
parameter OPCODE_MISC_MEM  = 7'h0f;
parameter OPCODE_OP        = 7'h33;
parameter OPCODE_OPIMM     = 7'h13;
parameter OPCODE_STORE     = 7'h23;
parameter OPCODE_LOAD      = 7'h03;
parameter OPCODE_BRANCH    = 7'h63;
parameter OPCODE_JALR      = 7'h67;
parameter OPCODE_JAL       = 7'h6f;
parameter OPCODE_AUIPC     = 7'h17;
parameter OPCODE_LUI       = 7'h37;


////////////////////
// ALU operations //
////////////////////

parameter ALU_OP_WIDTH = 6;

parameter ALU_ADD   = 6'b011000;
parameter ALU_SUB   = 6'b011001;

parameter ALU_XOR   = 6'b101111;
parameter ALU_OR    = 6'b101110;
parameter ALU_AND   = 6'b010101;

// Shifts
parameter ALU_SRA   = 6'b100100;
parameter ALU_SRL   = 6'b100101;
parameter ALU_SLL   = 6'b100111;

// Comparisons
parameter ALU_LT    = 6'b000000;
parameter ALU_LTU   = 6'b000001;
parameter ALU_LE    = 6'b000100;
parameter ALU_LEU   = 6'b000101;
parameter ALU_GT    = 6'b001000;
parameter ALU_GTU   = 6'b001001;
parameter ALU_GE    = 6'b001010;
parameter ALU_GEU   = 6'b001011;
parameter ALU_EQ    = 6'b001100;
parameter ALU_NE    = 6'b001101;

// Set Lower Than operations
parameter ALU_SLT   = 6'b000010;
parameter ALU_SLTU  = 6'b000011;
parameter ALU_SLET  = 6'b000110;
parameter ALU_SLETU = 6'b000111;

parameter MD_OP_MULL  = 2'b00;
parameter MD_OP_MULH  = 2'b01;
parameter MD_OP_DIV   = 2'b10;
parameter MD_OP_REM   = 2'b11;


//////////////////////////////////
// Control and status registers //
//////////////////////////////////

// CSR operations
parameter CSR_OP_NONE  = 2'b00;
parameter CSR_OP_WRITE = 2'b01;
parameter CSR_OP_SET   = 2'b10;
parameter CSR_OP_CLEAR = 2'b11;

// Privileged mode
typedef enum logic[1:0] {
  PRIV_LVL_M = 2'b11,
  PRIV_LVL_H = 2'b10,
  PRIV_LVL_S = 2'b01,
  PRIV_LVL_U = 2'b00
} PrivLvl_t;

// Constants for the dcsr.xdebugver fields
typedef enum logic[3:0] {
   XDEBUGVER_NO  = 4'd0, // no external debug support
   XDEBUGVER_STD = 4'd4, // external debug according to RISC-V debug spec
   XDEBUGVER_NONSTD = 4'd15 // debug not conforming to RISC-V debug spec
} Xdebugver_t;

//////////////
// ID stage //
//////////////

// forwarding operand mux
parameter SEL_REGFILE      = 2'b00;
parameter SEL_MISALIGNED   = 2'b11;

// operand a selection
parameter OP_A_REGA_OR_FWD = 3'b000;
parameter OP_A_CURRPC      = 3'b001;
parameter OP_A_IMM         = 3'b010;

// immediate a selection
parameter IMMA_Z      = 1'b0;
parameter IMMA_ZERO   = 1'b1;

// operand b selection
parameter OP_B_REGB_OR_FWD = 3'b000;
parameter OP_B_IMM         = 3'b010;

// immediate b selection
parameter IMMB_I      = 4'b0000;
parameter IMMB_S      = 4'b0001;
parameter IMMB_U      = 4'b0010;
parameter IMMB_PCINCR = 4'b0011;
parameter IMMB_S2     = 4'b0100;
parameter IMMB_S3     = 4'b0101;
parameter IMMB_VS     = 4'b0110;
parameter IMMB_VU     = 4'b0111;
parameter IMMB_BI     = 4'b1011;
parameter IMMB_UJ     = 4'b1100;
parameter IMMB_SB     = 4'b1101;


//////////////
// IF stage //
//////////////

// PC mux selector defines
parameter PC_BOOT          = 3'b000;
parameter PC_JUMP          = 3'b010;
parameter PC_EXCEPTION     = 3'b100;
parameter PC_ERET          = 3'b101;
parameter PC_DRET          = 3'b111;

// Exception PC mux selector defines
parameter EXC_PC_ILLINSN    = 3'b000;
parameter EXC_PC_ECALL      = 3'b001;
parameter EXC_PC_LOAD       = 3'b010;
parameter EXC_PC_STORE      = 3'b010;
parameter EXC_PC_IRQ        = 3'b011;
parameter EXC_PC_DBD        = 3'b100;
parameter EXC_PC_DBGEXC     = 3'b101; // Exception while in debug mode
parameter EXC_PC_BREAKPOINT = 3'b110;

// Exception Cause
parameter EXC_CAUSE_ILLEGAL_INSN = 6'h02;
parameter EXC_CAUSE_BREAKPOINT   = 6'h03;
parameter EXC_CAUSE_ECALL_MMODE  = 6'h0B;

// Exceptions offsets
// target address = {boot_addr[31:8], EXC_OFF} (boot_addr must be 32 BYTE aligned!)
// offset 00 to 7e is used for external interrupts

// TODO: The behavior below follows an outdated (pre-1.10) RISC-V Privileged
// Spec to implement a "free-form" vectored trap handler.
// We need to update this code and crt0.S to follow the new mtvec spec.
parameter EXC_OFF_RST        = 8'h80;
parameter EXC_OFF_ILLINSN    = 8'h84;
parameter EXC_OFF_ECALL      = 8'h88;
parameter EXC_OFF_BREAKPOINT = 8'h90;

// Debug Cause
parameter DBG_CAUSE_EBREAK     = 3'h1;
parameter DBG_CAUSE_TRIGGER    = 3'h2;
parameter DBG_CAUSE_HALTREQ    = 3'h3;
parameter DBG_CAUSE_STEP       = 3'h4;

// CSRs
parameter CSR_MSTATUS        = 12'h300;
parameter CSR_MISA           = 12'h301;
parameter CSR_DCSR           = 12'h7b0;
parameter CSR_DPC            = 12'h7b1;
parameter CSR_DSCRATCH0      = 12'h7b2; // optional
parameter CSR_DSCRATCH1      = 12'h7b3; // optional
endpackage
