/*
 * Copyright 2019 Google LLC
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

//-----------------------------------------------------------------------------
// Processor feature configuration
//-----------------------------------------------------------------------------
// XLEN
parameter int XLEN = 32;

// Parameter for SATP mode, set to BARE if address translation is not supported
parameter satp_mode_t SATP_MODE = BARE;

// Supported Privileged mode
privileged_mode_t supported_privileged_mode[] = {MACHINE_MODE};

// Unsupported instructions
// Avoid generating these instructions in regular regression
// FENCE.I is intentionally treated as illegal instruction by ibex core
riscv_instr_name_t unsupported_instr[] = {FENCEI};

// ISA supported by the processor
riscv_instr_group_t supported_isa[$] = {RV32I, RV32M, RV32C};

// Interrupt mode support
mtvec_mode_t supported_interrupt_mode[$] = {VECTORED};

// Debug mode support
bit support_debug_mode = 1;

// Support delegate trap to user mode
bit support_umode_trap = 0;

// Support sfence.vma instruction
bit support_sfence = 0;

int max_interrupt_vector_num = 32;

//-----------------------------------------------------------------------------
// Kernel section setting, used by supervisor mode programs
//-----------------------------------------------------------------------------

// Number of kernel data pages
int num_of_kernel_data_pages = 2;

// Byte size of kernel data pages
int kernel_data_page_size = 4096;

// Kernel Stack section word length
int kernel_stack_len = 5000;

// Number of instructions for each kernel program
int kernel_program_instr_cnt = 400;

// ----------------------------------------------------------------------------
// Previleged CSR implementation
// ----------------------------------------------------------------------------

// Implemented previlieged CSR list
privileged_reg_t implemented_csr[$] = {
    // Machine mode mode CSR
    MVENDORID,  // Vendor ID
    MARCHID,    // Architecture ID
    MHARTID,    // Hardware thread ID
    MSTATUS,    // Machine status
    MISA,       // ISA and extensions
    MTVEC,      // Machine trap-handler base address
    MEPC,       // Machine exception program counter
    MCAUSE,     // Machine trap cause
    MTVAL,      // Machine bad address or instruction
    MIE         // Machine interrupt enable
    // TODO: Add performance CSRs and debug mode CSR
};
