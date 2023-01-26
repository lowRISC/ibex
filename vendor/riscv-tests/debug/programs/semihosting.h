#include <sys/types.h>

#ifndef _SEMIHOSTING_H_
#define _SEMIHOSTING_H_

// ----------------------------------------------------------------------------

// Semihosting operations.
enum Semihost_Sys_Op {
    // Regular operations
    SEMIHOST_SYS_CLOCK = 0x10,
    SEMIHOST_SYS_CLOSE = 0x02,
    SEMIHOST_SYS_ELAPSED = 0x30,
    SEMIHOST_SYS_ERRNO = 0x13,
    SEMIHOST_SYS_EXIT = 0x18,
    SEMIHOST_SYS_EXIT_EXTENDED = 0x20,
    SEMIHOST_SYS_FLEN = 0x0C,
    SEMIHOST_SYS_GET_CMDLINE = 0x15,
    SEMIHOST_SYS_HEAPINFO = 0x16,
    SEMIHOST_SYS_ISERROR = 0x08,
    SEMIHOST_SYS_ISTTY = 0x09,
    SEMIHOST_SYS_OPEN = 0x01,
    SEMIHOST_SYS_READ = 0x06,
    SEMIHOST_SYS_READC = 0x07,
    SEMIHOST_SYS_REMOVE = 0x0E,
    SEMIHOST_SYS_RENAME = 0x0F,
    SEMIHOST_SYS_SEEK = 0x0A,
    SEMIHOST_SYS_SYSTEM = 0x12,
    SEMIHOST_SYS_TICKFREQ = 0x31,
    SEMIHOST_SYS_TIME = 0x11,
    SEMIHOST_SYS_TMPNAM = 0x0D,
    SEMIHOST_SYS_WRITE = 0x05,
    SEMIHOST_SYS_WRITEC = 0x03,
    SEMIHOST_SYS_WRITE0 = 0x04,
};

enum ADP_Code {
    ADP_Stopped_BranchThroughZero = 0x20000,
    ADP_Stopped_UndefinedInstr = 0x20001,
    ADP_Stopped_SoftwareInterrupt = 0x20002,
    ADP_Stopped_PrefetchAbort = 0x20003,
    ADP_Stopped_DataAbort = 0x20004,
    ADP_Stopped_AddressException = 0x20005,
    ADP_Stopped_IRQ = 0x20006,
    ADP_Stopped_FIQ = 0x20007,
    ADP_Stopped_BreakPoint = 0x20020,
    ADP_Stopped_WatchPoint = 0x20021,
    ADP_Stopped_StepComplete = 0x20022,
    ADP_Stopped_RunTimeErrorUnknown = 0x20023,
    ADP_Stopped_InternalError = 0x20024,
    ADP_Stopped_UserInterruption = 0x20025,
    ADP_Stopped_ApplicationExit = 0x20026,
    ADP_Stopped_StackOverflow = 0x20027,
    ADP_Stopped_DivisionByZero = 0x20028,
    ADP_Stopped_OSSpecific = 0x20029,
};

typedef struct {
    uintptr_t param1;
    uintptr_t param2;
    uintptr_t param3;
} semihostparam_t;

static inline uintptr_t __attribute__((always_inline))
semihost_call_host(uintptr_t op, uintptr_t arg) {
    register uintptr_t r0 asm("a0") = op;
    register uintptr_t r1 asm("a1") = arg;

    asm volatile(".option push               \n"
                 ".option norvc              \n"
                 " slli    zero,zero,0x1f    \n"
                 " ebreak                    \n"
                 " srai    zero,zero,0x7     \n"
                 ".option pop                \n"

                 : "=r"(r0)         /* Outputs */
                 : "r"(r0), "r"(r1) /* Inputs */
                 : "memory");
    return r0;
}

#endif