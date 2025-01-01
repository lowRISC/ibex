# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

.section .text

.globl busy_work

# Does some computation on uint32 arrays received in a1, a2, a3 output to the
# array in a4. a0 specifies the number of elements in each array. Times how long
# it takes in cycles which is returned in a0.
busy_work:
  csrr t5, mcycle
loop:
  lw t1, 0(a1)
  lw t2, 0(a2)
  lw t3, 0(a3)

  div t4, t3, t2
  mul t4, t4, t1
  add t4, t4, t2
  sub t4, t4, t3
  and t4, t4, t1

  sw t4, 0(a4)

  addi a0, a0, -1
  addi a1, a1, 4
  addi a2, a2, 4
  addi a3, a3, 4
  addi a4, a4, 4

  bne zero, a0, loop

  csrr t6, mcycle
  sub a0, t6, t5
  jr ra
