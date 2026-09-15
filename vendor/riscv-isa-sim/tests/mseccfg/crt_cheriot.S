# See LICENSE for license details.
#
# CHERIoT-aware startup: identical to crt.S but initialises the capability
# stack pointer (c2) from DDC before entering _init.
#
# In CHERIoT mode every memory store uses the capability register file.
# Standard crt.S sets x2 (SP) via integer arithmetic, leaving c2 untagged.
# The first store in _init (c.swsp / c.cscsp) then faults because c2.tag=0.
#
# Fix: after computing the integer SP, load DDC into c2 (giving it tag=1 and
# full-memory bounds), then point c2's cursor at the integer SP value in x2.
#
#   cspecialr c2, ddc   -- 0x0210015B  (rd=x2, SCR=DDC)
#   csetaddr  c2, c2, x2 -- 0x2021015B  (rd=x2, cs1=x2, rs2=x2)
#
# Encodings derived from:
#   cspecialr ca0, ddc  = 0x0210055B  (rd=a0=x10 → rd=x2 changes bits[11:7])
#   csetaddr  a0, a0, a1 = 0x20B5055B  (all regs → x2 changes rs1,rs2,rd fields)

#include "encoding.h"

#if __riscv_xlen == 64
# define LREG ld
# define SREG sd
# define REGBYTES 8
#else
# define LREG lw
# define SREG sw
# define REGBYTES 4
#endif

  .section ".text.init"
  .org 0x80
  .globl _start
_start:
  li  x1, 0
  li  x2, 0
  li  x3, 0
  li  x4, 0
  li  x5, 0
  li  x6, 0
  li  x7, 0
  li  x8, 0
  li  x9, 0
  li  x10,0
  li  x11,0
  li  x12,0
  li  x13,0
  li  x14,0
  li  x15,0
  # x16-x31 deliberately not zeroed here: this file is only used with
  # +enable_cheriot_seq=1 (see directed_testlist.yaml's cheriot-c-tests
  # config), and ibex_decoder.sv's illegal_reg_16 check makes ANY access to
  # a register >= x16 an illegal instruction once cheriot_enable_i is
  # asserted (CHERIoT only has 16 architectural registers). The original
  # crt.S x16-x31 zeroing loop, inherited unmodified from the plain RV32I
  # startup, faults immediately here with no trap handler installed yet --
  # the fault has nowhere to go but the boot vector, producing an infinite
  # reset loop.

  # enable FPU and accelerator if present
  li t0, MSTATUS_FS | MSTATUS_XS
  csrs mstatus, t0

  # make sure XLEN agrees with compilation choice
  li t0, 1
  slli t0, t0, 31
#if __riscv_xlen == 64
  bgez t0, 1f
#else
  bltz t0, 1f
#endif
2:
  li a0, 1
  sw a0, tohost, t0
  j 2b
1:

#ifdef __riscv_flen
  # initialize FPU if we have one
  # NOTE: unexercised by the cheriot-c-tests config (-march=rv32imc, no F
  # extension), so left as plain csrw. If this ever gets compiled with F
  # enabled under +enable_cheriot_seq=1, it needs the same fix as the real
  # "initialize trap vector" block below: csrw mtvec is illegal once
  # cheriot_enable_i is asserted (see REQ_SCR_07) -- use the
  # cspecialr/csetaddr/cspecialw MTCC sequence instead.
  la t0, 1f
  csrw mtvec, t0

  fssr    x0
  fmv.s.x f0, x0
  fmv.s.x f1, x0
  fmv.s.x f2, x0
  fmv.s.x f3, x0
  fmv.s.x f4, x0
  fmv.s.x f5, x0
  fmv.s.x f6, x0
  fmv.s.x f7, x0
  fmv.s.x f8, x0
  fmv.s.x f9, x0
  fmv.s.x f10,x0
  fmv.s.x f11,x0
  fmv.s.x f12,x0
  fmv.s.x f13,x0
  fmv.s.x f14,x0
  fmv.s.x f15,x0
  fmv.s.x f16,x0
  fmv.s.x f17,x0
  fmv.s.x f18,x0
  fmv.s.x f19,x0
  fmv.s.x f20,x0
  fmv.s.x f21,x0
  fmv.s.x f22,x0
  fmv.s.x f23,x0
  fmv.s.x f24,x0
  fmv.s.x f25,x0
  fmv.s.x f26,x0
  fmv.s.x f27,x0
  fmv.s.x f28,x0
  fmv.s.x f29,x0
  fmv.s.x f30,x0
  fmv.s.x f31,x0
1:
#endif

  # initialize trap vector
  #
  # ibex_cs_registers.sv (CSR_MTVEC case) makes any access to the plain mtvec
  # CSR illegal once cheriot_enable_i is asserted -- MTCC supersedes it
  # entirely, set only via cspecialrw (see REQ_SCR_07 in the verification
  # spec). csrw mtvec, t0 here would trap with no handler installed yet,
  # looping back to the boot vector forever.
  #
  # `la t0, trap_entry` lowers to AUIPC+ADDI, and AUIPC is architecturally
  # redefined as CAUIPCC under cheriot_enable_i (deriving a tagged capability
  # from PCC), but the following ADDI is a plain integer ALU op and clears
  # the tag again -- t0 ends up an ordinary untagged address, same as under
  # plain RV32I. So MTCC can't be written directly from t0 (that would leave
  # MTCC untagged/invalid); instead read MTCC's own valid reset capability
  # into a scratch capability register, move its cursor to trap_entry with
  # CSetAddr (preserving tag/bounds/EX permission), and write that back --
  # the same read-adjust-write idiom used above for c2's stack capability.
  #
  #   cspecialr c6, mtcc    = 0x03C0035B (funct7=0x01, SCR=28=11100 (MTCC),
  #                                       rs1=x0=00000, rd=c6=x6=00110)
  #   csetaddr  c6, c6, t0  = 0x2053035B (funct7=0x10, rs2=t0=x5=00101,
  #                                       cs1=rd=c6=x6=00110)
  #   cspecialw mtcc, c6    = 0x03C3005B (funct7=0x01, SCR=28=11100 (MTCC),
  #                                       rs1=c6=x6=00110, rd=x0=00000)
  la t0, trap_entry
  .word 0x03C0035B       # cspecialr c6, mtcc   -- c6 <- MTCC (tag=1, EX=1, full bounds)
  .word 0x2053035B       # csetaddr  c6, c6, t0 -- c6.cursor <- trap_entry, tag preserved
  .word 0x03C3005B       # cspecialw mtcc, c6   -- MTCC <- c6 (valid capability, cursor=trap_entry)

  # initialize global pointer
.option push
.option norelax
  la gp, __global_pointer$
.option pop

  la  tp, _end + 63
  and tp, tp, -64

  # get core id
  csrr a0, mhartid
  # for now, assume only 1 core
  li a1, 1
1:bgeu a0, a1, 1b

  # give each core 128KB of stack + TLS
#define STKSHIFT 17
  add sp, a0, 1
  sll sp, sp, STKSHIFT
  add sp, sp, tp
  sll a2, a0, STKSHIFT
  add tp, tp, a2

  # ── CHERIoT capability stack-pointer initialisation ─────────────────────────
  # In CHERIoT mode (cheriot_enable=IbexMuBiOn) every SW/LW is promoted to
  # CSC/CLC and requires the base register to carry a valid capability tag.
  # x2/c2 was set above by integer arithmetic: tag=0.  Derive c2 from MTDC
  # (machine data capability, SCR 29: tag=1, perms=0x07F, full-memory bounds)
  # and move its cursor to the just-computed integer SP address.
  #
  # ibex CHERIoT valid SCR addresses: 27=ZTOP, 28=MTCC, 29=MTDC, 30=MScratchC,
  # 31=MEPCC.  DDC (SCR 1) is illegal in ibex — it does not exist as a CSR.
  #
  # CRITICAL: cspecialr writes the SCR's cursor (0 for MTDC at reset) into the
  # destination register's INTEGER part, clobbering x2=SP.  Save SP to t0
  # (x5) first, then use t0 as the address argument in csetaddr.
  #
  # Encoding derivation:
  #   cspecialr ca0, mtcc = 0x03C0055B (funct7=0x01, SCR=28=11100, rd=a0, rs1=0)
  #   cspecialr ca0, mtdc = 0x03D0055B (SCR=29=11101: set bit20 in 0x03C0055B)
  #   cspecialr c2,  mtdc = 0x03D0015B (rd=x2=2: change bits[11:7] to 00010)
  #   csetaddr  a0, a0, a1 = 0x20B5055B (funct7=0x10, rs2=a1, rs1=a0, rd=a0)
  #   csetaddr  c2, c2, t0 = 0x2051015B (rs2=t0=x5=5: bits[24:20]=00101)
  mv    t0, sp           # t0 (x5) = integer SP value (0x80060000)
  .word 0x03D0015B       # cspecialr c2, mtdc -- c2 ← MTDC (tag=1); x2.int ← 0 (MTDC cursor)
  .word 0x2051015B       # csetaddr c2, c2, t0 -- c2.cursor ← t0 (original SP); x2.int ← SP

  # Skip _init: it uses auipc with rd=x16-x31 (e.g. auipc s4,0x10) which ibex CHERIoT
  # decodes as CAUIPCC c20 and flags as illegal (illegal_reg_cheri: rd[4]=1).
  # Call main(0, NULL) directly; ra=x1=c1 has rd[4]=0, so CAUIPCC c1 is legal.
  li    a0, 0             # argc = 0
  li    a1, 0             # argv = NULL
  call  main              # call main; ra/c1 set as return address (c1 valid CHERIoT)

  # CHERIoT-safe exit: tohost_exit() does `lui x15,0x90000; sw ...,0(x15)` which
  # clears c15.tag (lui is an integer op) → CHERI fault on the store.
  # Instead, derive address capability from MTDC (full-memory cap, tag=1, all perms).
  # Replicates tohost_exit(a0): writes (a0<<8)|CORE_STATUS then TEST_RESULT=1
  # to SIGNATURE_ADDR = 0x8FFFFFF8.
  slli  t0, a0, 8         # t0 = (exit_code << 8) | CORE_STATUS(0)
  li    t1, 1             # t1 = (TEST_PASS<<8) | TEST_RESULT = 0x00000001
  lui   a1, 0x90000       # a1 = 0x90000000 (integer; c11.tag=0, OK — used as addr only)
  addi  a1, a1, -8        # a1 = 0x8FFFFFF8 (SIGNATURE_ADDR)
  .word 0x03D0055B        # cspecialr c10, mtdc  -- c10 ← MTDC (tag=1, full 4GB bounds)
  .word 0x20B5055B        # csetaddr c10, c10, a1 -- c10.cursor ← 0x8FFFFFF8 (tag preserved)
  fence iorw, iorw
  sw    t0, 0(a0)         # CHERIoT store via c10: first sig word (exit_code<<8 | 0)
  sw    t1, 0(a0)         # CHERIoT store via c10: second sig word (TEST_PASS=1)
1:j 1b                    # infinite loop — testbench ends on tohost write above

  # mtvec.base must be 256 byte aligned - Ibex
  .balign 256
trap_entry:
  #addi sp, sp, -272
  # use shadow address
  SREG sp, 31*REGBYTES(gp)
  addi sp, gp, 512
  addi sp, gp, 512

  SREG x1, 1*REGBYTES(sp)
  SREG x2, 2*REGBYTES(sp)
  SREG x3, 3*REGBYTES(sp)
  SREG x4, 4*REGBYTES(sp)
  SREG x5, 5*REGBYTES(sp)
  SREG x6, 6*REGBYTES(sp)
  SREG x7, 7*REGBYTES(sp)
  SREG x8, 8*REGBYTES(sp)
  SREG x9, 9*REGBYTES(sp)
  SREG x10, 10*REGBYTES(sp)
  SREG x11, 11*REGBYTES(sp)
  SREG x12, 12*REGBYTES(sp)
  SREG x13, 13*REGBYTES(sp)
  SREG x14, 14*REGBYTES(sp)
  SREG x15, 15*REGBYTES(sp)
  SREG x16, 16*REGBYTES(sp)
  SREG x17, 17*REGBYTES(sp)
  SREG x18, 18*REGBYTES(sp)
  SREG x19, 19*REGBYTES(sp)
  SREG x20, 20*REGBYTES(sp)
  SREG x21, 21*REGBYTES(sp)
  SREG x22, 22*REGBYTES(sp)
  SREG x23, 23*REGBYTES(sp)
  SREG x24, 24*REGBYTES(sp)
  SREG x25, 25*REGBYTES(sp)
  SREG x26, 26*REGBYTES(sp)
  SREG x27, 27*REGBYTES(sp)
  SREG x28, 28*REGBYTES(sp)
  SREG x29, 29*REGBYTES(sp)
  SREG x30, 30*REGBYTES(sp)
  SREG x31, 31*REGBYTES(sp)

  csrr a0, mcause
  csrr a1, mepc
  mv a2, sp
  jal handle_trap
  csrw mepc, a0

  # Remain in M-mode after eret
  #li t0, MSTATUS_MPP
  #csrs mstatus, t0

  LREG x1, 1*REGBYTES(sp)
  LREG x2, 2*REGBYTES(sp)
  LREG x3, 3*REGBYTES(sp)
  LREG x4, 4*REGBYTES(sp)
  LREG x5, 5*REGBYTES(sp)
  LREG x6, 6*REGBYTES(sp)
  LREG x7, 7*REGBYTES(sp)
  LREG x8, 8*REGBYTES(sp)
  LREG x9, 9*REGBYTES(sp)
  LREG x10, 10*REGBYTES(sp)
  LREG x11, 11*REGBYTES(sp)
  LREG x12, 12*REGBYTES(sp)
  LREG x13, 13*REGBYTES(sp)
  LREG x14, 14*REGBYTES(sp)
  LREG x15, 15*REGBYTES(sp)
  LREG x16, 16*REGBYTES(sp)
  LREG x17, 17*REGBYTES(sp)
  LREG x18, 18*REGBYTES(sp)
  LREG x19, 19*REGBYTES(sp)
  LREG x20, 20*REGBYTES(sp)
  LREG x21, 21*REGBYTES(sp)
  LREG x22, 22*REGBYTES(sp)
  LREG x23, 23*REGBYTES(sp)
  LREG x24, 24*REGBYTES(sp)
  LREG x25, 25*REGBYTES(sp)
  LREG x26, 26*REGBYTES(sp)
  LREG x27, 27*REGBYTES(sp)
  LREG x28, 28*REGBYTES(sp)
  LREG x29, 29*REGBYTES(sp)
  LREG x30, 30*REGBYTES(sp)
  LREG x31, 31*REGBYTES(sp)

  #addi sp, sp, 272
  LREG sp, 31*REGBYTES(gp)
  mret

.section ".tohost","aw",@progbits
.align 6
.globl tohost
tohost: .dword 0
.align 6
.globl fromhost
fromhost: .dword 0
