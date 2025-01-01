# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

.section .text

.globl count_ones_zeros
.globl div_ones_zeros

# Counts the number of 0s and 1s found in a0, timing how many cycles it takes
# which is returned in a0.
count_ones_zeros:
  li t0, 32
  li t2, 0
  li t3, 0
  li t4, 0
  csrr t5, mcycle
count_ones_zeros.loop_start:
  andi t1, a0, 1
  beqz t1, count_ones_zeros.do_zero
  addi t2, t2, 1
  j count_ones_zeros.loop_end
count_ones_zeros.do_zero:
  addi t3, t3, 1
  j count_ones_zeros.loop_end
count_ones_zeros.loop_end:
  srli a0, a0, 1
  addi t4, t4, 1
  bne t4, t0, count_ones_zeros.loop_start
  csrr t6, mcycle
  sub a0, t6, t5
  jr ra

# Divides a0 by every bit in a0 one by one, shifting a0 right one bit every
# iteration. It times how many cycles it takes which is returned in a0.
div_ones_zeros:
  li t0, 32
  li t1, 0
  li t4, 0
  csrr t5, mcycle
div_ones_zeros.loop_start:
  andi t2, a0, 1
  div t3, a0, t2
  add t1, t1, t3

  srli a0, a0, 1
  addi t4, t4, 1
  bne t4, t0, div_ones_zeros.loop_start

  csrr t6, mcycle

  sub a0, t6, t5
  jr ra
