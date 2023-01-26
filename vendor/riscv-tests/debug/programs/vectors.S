#include "encoding.h"

#if XLEN == 64
# define LREG ld
# define SREG sd
# define REGBYTES 8
#else
# define LREG lw
# define SREG sw
# define REGBYTES 4
#endif

#define get_field(reg, mask) (((reg) & (mask)) / ((mask) & ~((mask) << 1)))
#define set_field(reg, mask, val) (((reg) & ~(mask)) | (((val) * ((mask) & ~((mask) << 1))) & (mask)))

        .global main
        .global main_end
        .global main_post_csrr

        // Load constants into all registers so we can test no register are
        // clobbered after attaching.
main:
        SREG    ra, 0(sp)
        addi    sp, sp, REGBYTES

        // Set VS=1
        csrr    t0, CSR_MSTATUS
        li      t1, set_field(0, MSTATUS_VS, 1)
        or      t0, t0, t1
        csrw    CSR_MSTATUS, t0

        // copy a to b
        la      a0, a
        jal     vector_load_v4
        la      a0, b
        jal     shift_store_v4

        // assert a == b
        la      a0, a
        la      a1, b
        jal     check_equal
test0:
        bne     a0, zero, return_from_main

        // copy b to c
        la      a0, b
        jal     shift_load_v4
        la      a0, c
        jal     vector_store_v4

        // assert b == c
        la      a0, b
        la      a1, c
        jal     check_equal
test1:
        bne     a0, zero, return_from_main

return_from_main:
        addi    sp, sp, -REGBYTES
        LREG    ra, 0(sp)
        ret

vector_load_v4:
        // a0: point to memory to load from
        csrr    s0, vlenb
        vsetvli zero, s0, e8, m1  # Vectors of 8b
        vle8.v v4, 0(a0)          # Load bytes
        ret

vector_store_v4:
        // a0: point to memory to store to
        csrr    s0, vlenb
        vsetvli zero, s0, e8, m1  # Vectors of 8b
        vse8.v v4, 0(a0)          # Load bytes
        ret

shift_load_v4:
        // a0: pointer to memory to load from

        // Configure all elements in the chain
        csrr    s0, vlenb
#if XLEN == 32
        vsetvli zero, s0, e32
#else
        vsetvli zero, s0, e64
#endif

        // Figure out how long the chain is.
        csrr    s0, vlenb
        li      s1, XLEN/8
        divu    s0, s0, s1

1:
        LREG    s2, 0(a0)
        vslide1down.vx  v4, v4, s2
        addi    a0, a0, REGBYTES
        addi    s0, s0, -1
        bne     s0, zero, 1b

        ret

shift_store_v4:
        // a0: pointer to memory to store to

        // Configure all elements in the chain
        csrr    s0, vlenb
#if XLEN == 32
        vsetvli zero, s0, e32
#else
        vsetvli zero, s0, e64
#endif

        // Figure out how long the chain is.
        csrr    s0, vlenb
        li      s1, XLEN/8
        divu    s0, s0, s1

1:
        vmv.x.s s2, v4
        SREG    s2, 0(a0)
        vslide1down.vx  v4, v4, s2
        addi    a0, a0, REGBYTES
        addi    s0, s0, -1
        bne     s0, zero, 1b

        ret

check_equal:
        csrr    s0, vlenb
1:
        lb      s1, 0(a0)
        lb      s2, 0(a1)
        bne     s1, s2, 2f
        addi    a0, a0, 1
        addi    a1, a1, 1
        addi    s0, s0, -1
        bne     s0, zero, 1b
        li      a0, 0   // equal
        ret
2:      // unequal
        li      a0, 1
        ret

        .data
        .align  6
a:      .word   0xaa00, 0xaa01, 0xaa02, 0xaa03, 0xaa04, 0xaa05, 0xaa06, 0xaa07
        .word   0xaa08, 0xaa09, 0xaa0a, 0xaa0b, 0xaa0c, 0xaa0d, 0xaa0e, 0xaa0f
        .word   0xaa10, 0xaa11, 0xaa12, 0xaa13, 0xaa14, 0xaa15, 0xaa16, 0xaa17
        .word   0xaa18, 0xaa19, 0xaa1a, 0xaa1b, 0xaa1c, 0xaa1d, 0xaa1e, 0xaa1f

b:      .word   0xbb00, 0xbb01, 0xbb02, 0xbb03, 0xbb04, 0xbb05, 0xbb06, 0xbb07
        .word   0xbb08, 0xbb09, 0xbb0b, 0xbb0b, 0xbb0c, 0xbb0d, 0xbb0e, 0xbb0f
        .word   0xbb10, 0xbb11, 0xbb13, 0xbb13, 0xbb14, 0xbb15, 0xbb16, 0xbb17
        .word   0xbb18, 0xbb19, 0xbb1b, 0xbb1b, 0xbb1c, 0xbb1d, 0xbb1e, 0xbb1f

c:      .word   0xcc00, 0xcc01, 0xcc02, 0xcc03, 0xcc04, 0xcc05, 0xcc06, 0xcc07
        .word   0xcc08, 0xcc09, 0xcc0c, 0xcc0c, 0xcc0c, 0xcc0d, 0xcc0e, 0xcc0f
        .word   0xcc10, 0xcc11, 0xcc13, 0xcc13, 0xcc14, 0xcc15, 0xcc16, 0xcc17
        .word   0xcc18, 0xcc19, 0xcc1c, 0xcc1c, 0xcc1c, 0xcc1d, 0xcc1e, 0xcc1f