#ifndef INIT_H
#define INIT_H

#define MTIME           (*(volatile long long *)(0x02000000 + 0xbff8))
#define MTIMECMP        ((volatile long long *)(0x02000000 + 0x4000))

typedef void* (*trap_handler_t)(unsigned hartid, unsigned mcause, void *mepc,
        void *sp);
void set_trap_handler(trap_handler_t handler);
void enable_timer_interrupts();

#endif
