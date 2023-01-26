#include <stdint.h>

#include "init.h"
#include "encoding.h"

typedef struct {
    int counter;
} atomic_t;

static inline int atomic_xchg(atomic_t *v, int n)
{
    register int c;

    __asm__ __volatile__ (
            "amoswap.w.aqrl %0, %2, %1"
            : "=r" (c), "+A" (v->counter)
            : "r" (n));
    return c;
}

static inline void mb(void)
{
    __asm__ __volatile__ ("fence");
}

void get_lock(atomic_t *lock)
{
    while (atomic_xchg(lock, 1) == 1)
        ;
    mb();
}

void put_lock(atomic_t *lock)
{
    mb();
    atomic_xchg(lock, 0);
}

static atomic_t buf_lock = { .counter = 0 };
static char buf[32];
static int buf_initialized;
static unsigned hart_count[NHARTS];
static unsigned interrupt_count[NHARTS];

static unsigned delta = 0x100;
void *increment_count(unsigned hartid, unsigned mcause, void *mepc, void *sp)
{
    interrupt_count[hartid]++;
    MTIMECMP[hartid] = MTIME + delta;
    return mepc;
}

int main()
{
    uint32_t hartid = read_csr(mhartid);
    hart_count[hartid] = 0;
    interrupt_count[hartid] = 0;

    set_trap_handler(increment_count);
    // Despite being memory-mapped, there appears to be one mtimecmp
    // register per hart. The spec does not address this.
    MTIMECMP[hartid] = MTIME + delta;
    enable_timer_interrupts();

    while (1) {
        get_lock(&buf_lock);

        if (!buf_initialized) {
            for (unsigned i = 0; i < sizeof(buf); i++) {
                buf[i] = 'A' + (i % 26);
            }
            buf_initialized = 1;
        }

        char first = buf[0];
        int offset = (first & ~0x20) - 'A';
        for (unsigned i = 0; i < sizeof(buf); i++) {
            while (buf[i] != (first - offset + ((offset + i) % 26)))
                ;

            if (hartid & 1)
                buf[i] = 'A' + ((i + hartid + hart_count[hartid]) % 26);
            else
                buf[i] = 'a' + ((i + hartid + hart_count[hartid]) % 26);
        }
        put_lock(&buf_lock);
        hart_count[hartid]++;
    }
}
