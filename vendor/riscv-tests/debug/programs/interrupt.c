#include "init.h"
#include "encoding.h"

static volatile unsigned interrupt_count;
static volatile unsigned local;
static volatile unsigned keep_running;

static unsigned delta = 0x100;
void *increment_count(unsigned hartid, unsigned mcause, void *mepc, void *sp)
{
    interrupt_count++;
    // There is no guarantee that the interrupt is cleared immediately when
    // MTIMECMP is written, so stick around here until that happens.
    while (read_csr(mip) & MIP_MTIP) {
        MTIMECMP[hartid] = MTIME + delta;
    }
    return mepc;
}

int main()
{
    interrupt_count = 0;
    local = 0;
    keep_running = 1;
    unsigned hartid = read_csr(mhartid);

    set_trap_handler(increment_count);
    MTIMECMP[hartid] = MTIME - 1;
    enable_timer_interrupts();

    while (keep_running) {
        local++;
    }
    return 10;
}
