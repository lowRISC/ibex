// -----------
// Copyright (c) 2020. RISC-V International. All rights reserved.
// SPDX-License-Identifier: BSD-3-Clause
// -----------
//
// This assembly file tests the fence.i instruction of the RISC-V Zifencei extension.
// 

#include "model_test.h"
#include "arch_test.h"

# Test Virtual Machine (TVM) used by program.
RVTEST_ISA("RV32I")

# Test code region
.section .text.init
.org 0x80
.globl rvtest_entry_point
rvtest_entry_point:
RVMODEL_BOOT
RVTEST_CODE_BEGIN
RVMODEL_IO_ASSERT_GPR_EQ(x31, x0, 0x00000000)
RVMODEL_IO_WRITE_STR(x31, "# Test Begin\n")

#ifdef TEST_CASE_1
  RVTEST_CASE(1,"// check ISA:=regex(.*32.*); check ISA:=regex(.*I.*); check ISA:=regex(.*Zifencei.*); def TEST_CASE_1=True", fencei)

    # ---------------------------------------------------------------------------------------------
    RVMODEL_IO_WRITE_STR(x31, "# Test part A - test fence\n");

    # Addresses for test data and results
    LA(     x16,test_A_data)
    LA(     x17,test_A_res)

    # Register initialization
    LI(     x3,0)

    # Load testdata
    lw      x1, 0(x16)
    lw      x2, 4(x16)

    # Test
    LA(     x20,instr_A_src)
    LA(     x21,instr_A_dst)
    lw      x15, 0(x20)
    sw      x15, 0(x21)
    fence.i
instr_A_dst:
    lui     x2, 0

    # Store results
    sw      x1, 0(x17)
    sw      x2, 4(x17)
    sw      x3, 8(x17)
    sw      x15, 12(x17)

    //
    // Assert
    //
    RVMODEL_IO_ASSERT_GPR_EQ(x17, x2,  0x00000012)
    RVMODEL_IO_ASSERT_GPR_EQ(x17, x3,  0x00000042)
    RVMODEL_IO_ASSERT_GPR_EQ(x17, x15, 0x001101B3)

    RVMODEL_IO_WRITE_STR(x31, "# Test part A1  - Complete\n");

    RVMODEL_IO_WRITE_STR(x31, "# Test End\n")

#endif

 # ---------------------------------------------------------------------------------------------
    # HALT
    RVMODEL_HALT

RVTEST_CODE_END

RVTEST_DATA_BEGIN
# Input data section.
    .data
    .align 4

instr_A_src:
    add     x3, x2, x1

test_A_data:
    .word 0x30
    .word 0x12
RVTEST_DATA_END


# Output data section.
RVMODEL_DATA_BEGIN
rvtest_sig_begin:
sig_begin_canary:
CANARY;
test_A_res:
    .fill 4, 4, 0xdeadbeef

#ifdef rvtest_mtrap_routine
mtrap_sigptr:
  .fill 4, 4, 0xdeadbeef
#endif

#ifdef rvtest_gpr_save
gpr_save:
    .fill 32*(XLEN/32), 4, 0xdeadbeef
#endif

sig_end_canary:
CANARY;
rvtest_sig_end:
RVMODEL_DATA_END
