#include "init.h"
#include "encoding.h"

int main(void);

trap_handler_t trap_handler[NHARTS] = {0};

void set_trap_handler(trap_handler_t handler)
{
    unsigned hartid = read_csr(mhartid);
    trap_handler[hartid] = handler;
}

void enable_timer_interrupts()
{
    set_csr(mie, MIP_MTIP);
    set_csr(mstatus, MSTATUS_MIE);
}

void handle_trap(unsigned int mcause, void *mepc, void *sp)
{
    unsigned hartid = read_csr(mhartid);
    if (trap_handler[hartid]) {
        trap_handler[hartid](hartid, mcause, mepc, sp);
        return;
    }

    while (1)
        ;
}

void _exit(int status)
{
    // Make sure gcc doesn't inline _exit, so we can actually set a breakpoint
    // on it.
    volatile int i = 42;
    while (i)
        ;
    // _exit isn't supposed to return.
    while (1)
        ;
}

void _init()
{
    _exit(main());
}
