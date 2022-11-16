#ifndef _COMPLIANCE_MODEL_H
#define _COMPLIANCE_MODEL_H

#define TESTUTIL_BASE 0x82000000
#define TESTUTIL_ADDR_HALT (TESTUTIL_BASE + 0x0)
#define TESTUTIL_ADDR_BEGIN_SIGNATURE (TESTUTIL_BASE + 0x4)
#define TESTUTIL_ADDR_END_SIGNATURE (TESTUTIL_BASE + 0x8)


//RV_COMPLIANCE_HALT
#define RVMODEL_HALT                                                          \
   /* tell simulation about location of begin_signature */                    \
        la t0, begin_signature;                                               \
        li t1, TESTUTIL_ADDR_BEGIN_SIGNATURE;                                 \
        sw t0, 0(t1);                                                         \
        /* tell simulation about location of end_signature */                 \
        la t0, end_signature;                                                 \
        li t1, TESTUTIL_ADDR_END_SIGNATURE;                                   \
        sw t0, 0(t1);                                                         \
        /* dump signature and terminate simulation */                         \
        li t0, 1;                                                             \
        li t1, TESTUTIL_ADDR_HALT;                                            \
        sw t0, 0(t1);                                                         \
        nop ;                                                                 \
        li gp, 1;                                                             \
        SWSIG (0, TESTNUM);                                                   \
        ecall;

// #define RVMODEL_BOOT                                                         \
//         .fill 31, 4, 0x00000013;


#define RVMODEL_DATA_BEGIN                                              \
    .align 4; .global begin_signature; begin_signature: \

#define RVMODEL_DATA_END                                                      \
    .align 4; .global end_signature; end_signature:   \


#define RVMODEL_BOOT \
.section .text.init;                                            \
        .align  4;                                                      \
        .fill 31, 4, 0x00000013;                                        \
        .globl _start;                                                  \
_start:  


#define LOCAL_IO_WRITE_STR(_STR) RVMODEL_IO_WRITE_STR(x31, _STR)
#define RVMODEL_IO_WRITE_STR(_SP, _STR)
#define LOCAL_IO_PUSH(_SP)
#define LOCAL_IO_POP(_SP)
#define RVMODEL_IO_ASSERT_GPR_EQ(_SP, _R, _I)
#define RVMODEL_IO_ASSERT_SFPR_EQ(_F, _R, _I)
#define RVMODEL_IO_ASSERT_DFPR_EQ(_D, _R, _I)

#define RVMODEL_SET_MSW_INT
#define RVMODEL_CLEAR_MSW_INT
#define RVMODEL_CLEAR_MTIMER_INT
#define RVMODEL_CLEAR_MEXT_INT

#endif // _COMPLIANCE_MODEL_H