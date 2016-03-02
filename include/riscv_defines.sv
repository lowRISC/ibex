// Copyright 2015 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the “License”); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Matthias Baer - baermatt@student.ethz.ch                   //
//                                                                            //
// Additional contributions by:                                               //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                                                                            //
//                                                                            //
// Design Name:    RISC-V processor core                                      //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Defines for various constants used by the processor core.  //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

`ifndef _CORE_DEFINES
`define _CORE_DEFINES

// no traces for synthesis, they are not synthesizable
`ifndef SYNTHESIS
`define TRACE_EXECUTION
//`define SIMCHECKER
`endif


////////////////////////////////////////////////
//    ___         ____          _             //
//   / _ \ _ __  / ___|___   __| | ___  ___   //
//  | | | | '_ \| |   / _ \ / _` |/ _ \/ __|  //
//  | |_| | |_) | |__| (_) | (_| |  __/\__ \  //
//   \___/| .__/ \____\___/ \__,_|\___||___/  //
//        |_|                                 //
////////////////////////////////////////////////

`define OPCODE_SYSTEM     7'h73
`define OPCODE_FENCE      7'h0f
`define OPCODE_OP         7'h33
`define OPCODE_OPIMM      7'h13
`define OPCODE_STORE      7'h23
`define OPCODE_LOAD       7'h03
`define OPCODE_BRANCH     7'h63
`define OPCODE_JALR       7'h67
`define OPCODE_JAL        7'h6f
`define OPCODE_AUIPC      7'h17
`define OPCODE_LUI        7'h37

// those opcodes are now used for PULP custom instructions
// `define OPCODE_CUST0      7'h0b
// `define OPCODE_CUST1      7'h2b

// PULP custom
`define OPCODE_LOAD_POST  7'h0b
`define OPCODE_STORE_POST 7'h2b
`define OPCODE_PULP_OP    7'h5b
`define OPCODE_VECOP      7'h57
`define OPCODE_HWLOOP     7'h7b


// Source/Destination register instruction index
`define REG_S1 19:15
`define REG_S2 24:20
`define REG_S3 29:25
`define REG_D  11:07


`define REGC_ZERO  2'b00
`define REGC_RD    2'b01
`define REGC_S3    2'b10


//////////////////////////////////////////////////////////////////////////////
//      _    _    _   _    ___                       _   _                  //
//     / \  | |  | | | |  / _ \ _ __   ___ _ __ __ _| |_(_) ___  _ __  ___  //
//    / _ \ | |  | | | | | | | | '_ \ / _ \ '__/ _` | __| |/ _ \| '_ \/ __| //
//   / ___ \| |__| |_| | | |_| | |_) |  __/ | | (_| | |_| | (_) | | | \__ \ //
//  /_/   \_\_____\___/   \___/| .__/ \___|_|  \__,_|\__|_|\___/|_| |_|___/ //
//                             |_|                                          //
//////////////////////////////////////////////////////////////////////////////

`define ALU_OP_WIDTH 6

`define ALU_ADD   6'b100000
`define ALU_SUB   6'b100001
`define ALU_AVG   6'b100010
`define ALU_AVGU  6'b100011

`define ALU_XOR   6'b011011
`define ALU_OR    6'b011010
`define ALU_AND   6'b010101

// Shifts
`define ALU_SRA   6'b100100
`define ALU_SRL   6'b100101
`define ALU_ROR   6'b100110
`define ALU_SLL   6'b100111

// bit manipulation
`define ALU_BEXT  6'b101000
`define ALU_BEXTU 6'b101001
`define ALU_BINS  6'b101010
`define ALU_BCLR  6'b101011
`define ALU_BSET  6'b101100

// Bit counting
`define ALU_FF1   6'b010110
`define ALU_FL1   6'b010111
`define ALU_CNT   6'b011000
`define ALU_CLB   6'b011001

// Sign-/zero-extensions
`define ALU_EXTHS 6'b011100
`define ALU_EXTHZ 6'b011101
`define ALU_EXTBS 6'b011110
`define ALU_EXTBZ 6'b011111

// Comparisons
`define ALU_LTS   6'b000000
`define ALU_LTU   6'b000001
`define ALU_LES   6'b000100
`define ALU_LEU   6'b000101
`define ALU_GTS   6'b001000
`define ALU_GTU   6'b001001
`define ALU_GES   6'b001010
`define ALU_GEU   6'b001011
`define ALU_EQ    6'b001100
`define ALU_NE    6'b001101
`define ALU_EQALL 6'b001110

// Set Lower Than operations
`define ALU_SLTS  6'b000010
`define ALU_SLTU  6'b000011
`define ALU_SLETS 6'b000110
`define ALU_SLETU 6'b000111

// Absolute value
`define ALU_ABS   6'b010100

// Insert/extract
`define ALU_INS   6'b101101

// min/max
`define ALU_MIN   6'b010000
`define ALU_MINU  6'b010001
`define ALU_MAX   6'b010010
`define ALU_MAXU  6'b010011
`define ALU_MAXU  6'b010011


// vector modes
`define VEC_MODE32 2'b00
`define VEC_MODE16 2'b10
`define VEC_MODE8  2'b11


/////////////////////////////////////////////////////////
//    ____ ____    ____            _     _             //
//   / ___/ ___|  |  _ \ ___  __ _(_)___| |_ ___ _ __  //
//  | |   \___ \  | |_) / _ \/ _` | / __| __/ _ \ '__| //
//  | |___ ___) | |  _ <  __/ (_| | \__ \ ||  __/ |    //
//   \____|____/  |_| \_\___|\__, |_|___/\__\___|_|    //
//                           |___/                     //
/////////////////////////////////////////////////////////

// CSR operations
`define CSR_OP_NONE  2'b00
`define CSR_OP_WRITE 2'b01
`define CSR_OP_SET   2'b10
`define CSR_OP_CLEAR 2'b11


// SPR for debugger, not accessible by CPU
`define SP_DVR0       16'h3000
`define SP_DCR0       16'h3008
`define SP_DMR1       16'h3010
`define SP_DMR2       16'h3011

`define SP_DVR_MSB 8'h00
`define SP_DCR_MSB 8'h01
`define SP_DMR_MSB 8'h02
`define SP_DSR_MSB 8'h04


///////////////////////////////////////////////
//   ___ ____    ____  _                     //
//  |_ _|  _ \  / ___|| |_ __ _  __ _  ___   //
//   | || | | | \___ \| __/ _` |/ _` |/ _ \  //
//   | || |_| |  ___) | || (_| | (_| |  __/  //
//  |___|____/  |____/ \__\__,_|\__, |\___|  //
//                              |___/        //
///////////////////////////////////////////////

// forwarding operand mux
`define SEL_REGFILE      2'b00
`define SEL_FW_EX        2'b01
`define SEL_FW_WB        2'b10

// operand a selection
`define OP_A_REGA_OR_FWD 2'b00
`define OP_A_CURRPC      2'b01
`define OP_A_ZIMM        2'b10
`define OP_A_ZERO        2'b11

// operand b selection
`define OP_B_REGB_OR_FWD 2'b00
`define OP_B_REGC_OR_FWD 2'b01
`define OP_B_IMM         2'b10

// operand b immediate selection
`define IMM_I      3'b000
`define IMM_S      3'b001
`define IMM_U      3'b010
`define IMM_PCINCR 3'b011
`define IMM_S2     3'b100
`define IMM_S3     3'b101
`define IMM_VS     3'b110
`define IMM_VU     3'b111

// operand c selection
`define OP_C_REGC_OR_FWD 2'b00
`define OP_C_REGB_OR_FWD 2'b01
`define OP_C_JT          2'b10

// branch types
`define BRANCH_NONE 2'b00
`define BRANCH_JAL  2'b01
`define BRANCH_JALR 2'b10
`define BRANCH_COND 2'b11 // conditional branches

// jump target mux
`define JT_JAL  2'b01
`define JT_JALR 2'b10
`define JT_COND 2'b11


///////////////////////////////////////////////
//   ___ _____   ____  _                     //
//  |_ _|  ___| / ___|| |_ __ _  __ _  ___   //
//   | || |_    \___ \| __/ _` |/ _` |/ _ \  //
//   | ||  _|    ___) | || (_| | (_| |  __/  //
//  |___|_|     |____/ \__\__,_|\__, |\___|  //
//                              |___/        //
///////////////////////////////////////////////

// PC mux selector defines
`define PC_BOOT          3'b000
`define PC_JUMP          3'b010
`define PC_BRANCH        3'b011
`define PC_EXCEPTION     3'b100
`define PC_ERET          3'b101
`define PC_DBG_NPC       3'b111

// Exception PC mux selector defines
`define EXC_PC_ILLINSN   2'b00
`define EXC_PC_ECALL     2'b01
`define EXC_PC_LOAD      2'b10
`define EXC_PC_STORE     2'b10
`define EXC_PC_IRQ       2'b11

// Exceptions offsets
// target address = {boot_addr[31:8], EXC_OFF} (boot_addr must be 32 BYTE aligned!)
// offset 00 to 7e is used for external interrupts
`define EXC_OFF_RST      8'h80
`define EXC_OFF_ILLINSN  8'h84
`define EXC_OFF_ECALL    8'h88
`define EXC_OFF_LSUERR   8'h8c


// Debug module
`define N_WP      2     // #Watchpoints
`define DCR_DP    0
`define DCR_CC    3:1
`define DCR_SC    4
`define DCR_CT    7:5

`define DMR1_ST   22
`define DMR2_WGB0 12
`define DMR2_WBS0 22

`define DSR_IIE   0
`define DSR_INTE  1


`endif
