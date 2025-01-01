#if XLEN == 64
# define LREG ld
# define SREG sd
# define REGBYTES 8
#else
# define LREG lw
# define SREG sw
# define REGBYTES 4
#endif

        .global main
main:
        li      s0, 0
        li      s1, 0x0200bff8
loop:
        addi    s0, s0, 1
        LREG    s2, 0(s1)
        j       loop
