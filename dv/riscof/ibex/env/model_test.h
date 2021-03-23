#ifndef _COMPLIANCE_MODEL_H
#define _COMPLIANCE_MODEL_H

//-----------------------------------------------------------------------
// Model specific Macros
//-----------------------------------------------------------------------

#define TESTUTIL_BASE 0x20000
#define TESTUTIL_ADDR_HALT (TESTUTIL_BASE + 0x0)
#define TESTUTIL_ADDR_BEGIN_SIGNATURE (TESTUTIL_BASE + 0x4)
#define TESTUTIL_ADDR_END_SIGNATURE (TESTUTIL_BASE + 0x8)

// clang-format off
// clang-format tries to combine .pushsection and .tohost to one word.
#define RVMODEL_DATA_SECTION             \
  .pushsection .tohost, "aw", @progbits; \
  .align 8;                              \
  .global tohost;                        \
  tohost:                                \
  .dword 0;                              \
  .align 8;                              \
  .global fromhost;                      \
  fromhost:                              \
  .dword 0;                              \
  .popsection;                           \
  .align 8;                              \
  .global begin_regstate;                \
  begin_regstate:                        \
  .word 128;                             \
  .align 8;                              \
  .global end_regstate;                  \
  end_regstate:                          \
  .word 4;
// clang-format on

// RV_COMPLIANCE_HALT
#define RVMODEL_HALT                                    \
  li x1, 1;                                             \
  .globl write_tohost;                                  \
  write_tohost:                                         \
  sw x1, tohost, t5;                                    \
  la t0, begin_signature;                               \
  li t1, TESTUTIL_ADDR_BEGIN_SIGNATURE;                 \
  sw t0, 0(t1);                                         \
  /* tell simulation about location of end_signature */ \
  la t0, end_signature;                                 \
  li t1, TESTUTIL_ADDR_END_SIGNATURE;                   \
  sw t0, 0(t1);                                         \
  /* dump signature and terminate simulation */         \
  li t0, 1;                                             \
  li t1, TESTUTIL_ADDR_HALT;                            \
  sw t0, 0(t1);                                         \
  self_loop:                                            \
  j self_loop;

#define RVMODEL_BOOT  // Define the boot sequence for the implementation here.

// RV_COMPLIANCE_DATA_BEGIN
// Change the definition in the following macros if the implementation expects
// different labels for identifying the signature section.
// clang-format off
// clang-format tries to combine RVMODEL_DATA_SECTION and .global
#define RVMODEL_DATA_BEGIN \
  RVMODEL_DATA_SECTION     \
  .global begin_signature; \
  begin_signature:
// clang-format on

// RV_COMPLIANCE_DATA_END
#define RVMODEL_DATA_END \
  .global end_signature; \
  end_signature:

// Define the IO macros as required.
// RVTEST_IO_INIT
#define RVMODEL_IO_INIT

// RVTEST_IO_WRITE_STR
#define RVMODEL_IO_WRITE_STR(_R, _STR)

// RVTEST_IO_CHECK
#define RVMODEL_IO_CHECK()

// RVTEST_IO_ASSERT_GPR_EQ
#define RVMODEL_IO_ASSERT_GPR_EQ(_S, _R, _I)

// RVTEST_IO_ASSERT_SFPR_EQ
#define RVMODEL_IO_ASSERT_SFPR_EQ(_F, _R, _I)

// RVTEST_IO_ASSERT_DFPR_EQ
#define RVMODEL_IO_ASSERT_DFPR_EQ(_D, _R, _I)

#define RVMODEL_SET_MSW_INT

#define RVMODEL_CLEAR_MSW_INT

#define RVMODEL_CLEAR_MTIMER_INT

#define RVMODEL_CLEAR_MEXT_INT

#endif  // _COMPLIANCE_MODEL_H
