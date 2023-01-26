# See LICENSE for license details.

#*****************************************************************************
# ma_data.S
#-----------------------------------------------------------------------------
#
# Test misaligned ld/st data.
# Based on rv64mi-ma_addr.S
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV64U
RVTEST_CODE_BEGIN

  la s0, data

#define SEXT(x, n) ((-((x) >> ((n)-1)) << (n)) | ((x) & ((1 << (n))-1)))

/* Check that a misaligned load reads the correct value. */
#define MISALIGNED_LOAD_TEST(testnum, insn, base, offset, res) \
  li TESTNUM, testnum; \
  li t1, res; \
  insn t2, offset(base); \
  bne t1, t2, fail; \
1:

# within quadword
  MISALIGNED_LOAD_TEST(1,  lh,  s0, 1, SEXT(0x0201, 16))
  MISALIGNED_LOAD_TEST(2,  lhu, s0, 1, 0x0201)
  MISALIGNED_LOAD_TEST(3,  lw,  s0, 1, SEXT(0x04030201, 32))
  MISALIGNED_LOAD_TEST(4,  lw,  s0, 2, SEXT(0x05040302, 32))
  MISALIGNED_LOAD_TEST(5,  lw,  s0, 3, SEXT(0x06050403, 32))

#if __riscv_xlen == 64
  MISALIGNED_LOAD_TEST(6,  lwu, s0, 1, 0x04030201)
  MISALIGNED_LOAD_TEST(7,  lwu, s0, 2, 0x05040302)
  MISALIGNED_LOAD_TEST(8,  lwu, s0, 3, 0x06050403)

  MISALIGNED_LOAD_TEST(9,  ld, s0, 1, 0x0807060504030201)
  MISALIGNED_LOAD_TEST(10, ld, s0, 2, 0x0908070605040302)
  MISALIGNED_LOAD_TEST(11, ld, s0, 3, 0x0a09080706050403)
  MISALIGNED_LOAD_TEST(12, ld, s0, 4, 0x0b0a090807060504)
  MISALIGNED_LOAD_TEST(13, ld, s0, 5, 0x0c0b0a0908070605)
  MISALIGNED_LOAD_TEST(14, ld, s0, 6, 0x0d0c0b0a09080706)
  MISALIGNED_LOAD_TEST(15, ld, s0, 7, 0x0e0d0c0b0a090807)
#endif

# octword crossing
  MISALIGNED_LOAD_TEST(16, lh,  s0, 31, SEXT(0x201f, 16))
  MISALIGNED_LOAD_TEST(17, lhu, s0, 31, 0x201f)
  MISALIGNED_LOAD_TEST(18, lw,  s0, 29, SEXT(0x201f1e1d, 32))
  MISALIGNED_LOAD_TEST(19, lw,  s0, 30, SEXT(0x21201f1e, 32))
  MISALIGNED_LOAD_TEST(20, lw,  s0, 31, SEXT(0x2221201f, 32))

#if __riscv_xlen == 64
  MISALIGNED_LOAD_TEST(21, lwu, s0, 29, 0x201f1e1d)
  MISALIGNED_LOAD_TEST(22, lwu, s0, 30, 0x21201f1e)
  MISALIGNED_LOAD_TEST(23, lwu, s0, 31, 0x2221201f)

  MISALIGNED_LOAD_TEST(24, ld, s0, 25, 0x201f1e1d1c1b1a19)
  MISALIGNED_LOAD_TEST(25, ld, s0, 26, 0x21201f1e1d1c1b1a)
  MISALIGNED_LOAD_TEST(26, ld, s0, 27, 0x2221201f1e1d1c1b)
  MISALIGNED_LOAD_TEST(27, ld, s0, 28, 0x232221201f1e1d1c)
  MISALIGNED_LOAD_TEST(28, ld, s0, 29, 0x24232221201f1e1d)
  MISALIGNED_LOAD_TEST(29, ld, s0, 30, 0x2524232221201f1e)
  MISALIGNED_LOAD_TEST(30, ld, s0, 31, 0x262524232221201f)
#endif

# cacheline crossing
  MISALIGNED_LOAD_TEST(31, lh,  s0, 63, SEXT(0x403f, 16))
  MISALIGNED_LOAD_TEST(32, lhu, s0, 63, 0x403f)
  MISALIGNED_LOAD_TEST(33, lw,  s0, 61, SEXT(0x403f3e3d, 32))
  MISALIGNED_LOAD_TEST(34, lw,  s0, 62, SEXT(0x41403f3e, 32))
  MISALIGNED_LOAD_TEST(35, lw,  s0, 63, SEXT(0x4241403f, 32))

#if __riscv_xlen == 64
  MISALIGNED_LOAD_TEST(36, lwu, s0, 61, 0x403f3e3d)
  MISALIGNED_LOAD_TEST(37, lwu, s0, 62, 0x41403f3e)
  MISALIGNED_LOAD_TEST(38, lwu, s0, 63, 0x4241403f)

  MISALIGNED_LOAD_TEST(39, ld, s0, 57, 0x403f3e3d3c3b3a39)
  MISALIGNED_LOAD_TEST(40, ld, s0, 58, 0x41403f3e3d3c3b3a)
  MISALIGNED_LOAD_TEST(41, ld, s0, 59, 0x4241403f3e3d3c3b)
  MISALIGNED_LOAD_TEST(42, ld, s0, 60, 0x434241403f3e3d3c)
  MISALIGNED_LOAD_TEST(43, ld, s0, 61, 0x44434241403f3e3d)
  MISALIGNED_LOAD_TEST(44, ld, s0, 62, 0x4544434241403f3e)
  MISALIGNED_LOAD_TEST(45, ld, s0, 63, 0x464544434241403f)
#endif


/* Check that a misaligned store writes the correct value. */
#define MISALIGNED_STORE_TEST(testnum, st_insn, ld_insn, base, offset, st_data) \
  li TESTNUM, testnum; \
  li t1, st_data; \
  st_insn t1, offset(base); \
  ld_insn t2, offset(base); \
  bne t1, t2, fail; \
1:

# within quadword
  MISALIGNED_STORE_TEST(46, sh, lh,  s0, 1, SEXT(0x8180, 16))
  MISALIGNED_STORE_TEST(47, sh, lhu, s0, 1, 0x8382)
  MISALIGNED_STORE_TEST(48, sw, lw,  s0, 1, SEXT(0x87868584, 32))
  MISALIGNED_STORE_TEST(49, sw, lw,  s0, 2, SEXT(0x8b8a8988, 32))
  MISALIGNED_STORE_TEST(50, sw, lw,  s0, 3, SEXT(0x8f8e8d8c, 32))

#if __riscv_xlen == 64
  MISALIGNED_STORE_TEST(51, sw, lwu, s0, 1, 0x93929190)
  MISALIGNED_STORE_TEST(52, sw, lwu, s0, 2, 0x97969594)
  MISALIGNED_STORE_TEST(53, sw, lwu, s0, 3, 0x9b9a9998)

  MISALIGNED_STORE_TEST(54, sd, ld, s0, 1, 0xa3a2a1a09f9e9d9c)
  MISALIGNED_STORE_TEST(55, sd, ld, s0, 2, 0xabaaa9a8a7a6a5a4)
  MISALIGNED_STORE_TEST(56, sd, ld, s0, 3, 0xb3b2b1b0afaeadac)
  MISALIGNED_STORE_TEST(57, sd, ld, s0, 4, 0xbbbab9b8b7b6b5b4)
  MISALIGNED_STORE_TEST(58, sd, ld, s0, 5, 0xc3c2c1c0bfbebdbc)
  MISALIGNED_STORE_TEST(59, sd, ld, s0, 6, 0xcbcac9c8c7c6c5c4)
  MISALIGNED_STORE_TEST(60, sd, ld, s0, 7, 0xd3d2d1d0cfcecdcc)
#endif

# octword crossing
  MISALIGNED_STORE_TEST(61, sh, lh,  s0, 31, SEXT(0xd5d4, 16))
  MISALIGNED_STORE_TEST(62, sh, lhu, s0, 31, 0xd7d6)
  MISALIGNED_STORE_TEST(63, sw, lw,  s0, 29, SEXT(0xdbdad9d8, 32))
  MISALIGNED_STORE_TEST(64, sw, lw,  s0, 30, SEXT(0xdfdedddc, 32))
  MISALIGNED_STORE_TEST(65, sw, lw,  s0, 31, SEXT(0xe3e2e1e0, 32))

#if __riscv_xlen == 64
  MISALIGNED_STORE_TEST(66, sw, lwu, s0, 29, 0xe7e6e5e4)
  MISALIGNED_STORE_TEST(67, sw, lwu, s0, 30, 0xebeae9e8)
  MISALIGNED_STORE_TEST(68, sw, lwu, s0, 31, 0xefeeedec)

  MISALIGNED_STORE_TEST(69, sd, ld, s0, 25, 0xf7f6f5f4f3f2f1f0)
  MISALIGNED_STORE_TEST(70, sd, ld, s0, 26, 0xfffefdfcfbfaf9f8)
  MISALIGNED_STORE_TEST(71, sd, ld, s0, 27, 0x0706050403020100)
  MISALIGNED_STORE_TEST(72, sd, ld, s0, 28, 0x0f0e0d0c0b0a0908)
  MISALIGNED_STORE_TEST(73, sd, ld, s0, 29, 0x1716151413121110)
  MISALIGNED_STORE_TEST(74, sd, ld, s0, 30, 0x1f1e1d1c1b1a1918)
  MISALIGNED_STORE_TEST(75, sd, ld, s0, 31, 0x2726252423222120)
#endif

# cacheline crossing
  MISALIGNED_STORE_TEST(76, sh, lh,  s0, 63, SEXT(0x3534, 16))
  MISALIGNED_STORE_TEST(77, sh, lhu, s0, 63, 0x3736)
  MISALIGNED_STORE_TEST(78, sw, lw,  s0, 61, SEXT(0x3b3a3938, 32))
  MISALIGNED_STORE_TEST(79, sw, lw,  s0, 62, SEXT(0x3f3e3d3c, 32))
  MISALIGNED_STORE_TEST(80, sw, lw,  s0, 63, SEXT(0x43424140, 32))

#if __riscv_xlen == 64
  MISALIGNED_STORE_TEST(81, sw, lwu, s0, 61, 0x47464544)
  MISALIGNED_STORE_TEST(82, sw, lwu, s0, 62, 0x4b4a4948)
  MISALIGNED_STORE_TEST(83, sw, lwu, s0, 63, 0x4f4e4d4c)

  MISALIGNED_STORE_TEST(84, sd, ld, s0, 57, 0x5756555453525150)
  MISALIGNED_STORE_TEST(85, sd, ld, s0, 58, 0x5f5e5d5c5b5a5958)
  MISALIGNED_STORE_TEST(86, sd, ld, s0, 59, 0x6766656463626160)
  MISALIGNED_STORE_TEST(87, sd, ld, s0, 60, 0x6f6e6d6c6b6a6968)
  MISALIGNED_STORE_TEST(88, sd, ld, s0, 61, 0x7776757473727170)
  MISALIGNED_STORE_TEST(89, sd, ld, s0, 62, 0x7f7e7d7c7b7a7978)
  MISALIGNED_STORE_TEST(90, sd, ld, s0, 63, 0x8786858483828180)
#endif


/* Check that a misaligned store writes the correct value, checked by a narrower load. */
#define MISMATCHED_STORE_TEST(testnum, st_insn, ld_insn, base, st_offset, ld_offset, st_data, ld_data) \
  li TESTNUM, testnum; \
  li t1, st_data; \
  li t2, ld_data; \
  st_insn t1, st_offset(base); \
  ld_insn t3, ld_offset(base); \
  bne t2, t3, fail; \
1:

# within quadword
  MISMATCHED_STORE_TEST(91,  sh, lb,  s0, 1, 1, 0x9998, SEXT(0x98, 8))
  MISMATCHED_STORE_TEST(92,  sh, lb,  s0, 1, 2, 0x9b9a, SEXT(0x9b, 8))
  MISMATCHED_STORE_TEST(93,  sh, lbu, s0, 1, 1, 0x9d9c, 0x9c)
  MISMATCHED_STORE_TEST(94,  sh, lbu, s0, 1, 2, 0x9f9e, 0x9f)
  MISMATCHED_STORE_TEST(95,  sw, lb,  s0, 1, 1, 0xa3a2a1a0, SEXT(0xa0, 8))
  MISMATCHED_STORE_TEST(96,  sw, lbu, s0, 2, 3, 0xa7a6a5a4, 0xa5)
  MISMATCHED_STORE_TEST(97,  sw, lh,  s0, 3, 4, 0xabaaa9a8, SEXT(0xaaa9, 16))
  MISMATCHED_STORE_TEST(98,  sw, lhu, s0, 3, 5, 0xafaeadac, 0xafae)

#if __riscv_xlen == 64
  MISMATCHED_STORE_TEST(99,  sd, lb,  s0, 1, 7, 0xb7b6b5b4b3b2b1b0, SEXT(0xb6, 8))
  MISMATCHED_STORE_TEST(100, sd, lbu, s0, 2, 3, 0xbfbebdbcbbbab9b8, 0xb9)
  MISMATCHED_STORE_TEST(101, sd, lh,  s0, 3, 9, 0xc7c6c5c4c3c2c1c0, SEXT(0xc7c6, 16))
  MISMATCHED_STORE_TEST(102, sd, lhu, s0, 4, 5, 0xcfcecdcccbcac9c8, 0xcac9)
  MISMATCHED_STORE_TEST(103, sd, lw,  s0, 5, 9, 0xd7d6d5d4d3d2d1d0, SEXT(0xd7d6d5d4, 32))
  MISMATCHED_STORE_TEST(104, sd, lw,  s0, 6, 8, 0xdfdedddcdbdad9d8, SEXT(0xdddcdbda, 32))
  MISMATCHED_STORE_TEST(105, sd, lwu, s0, 7, 8, 0xe7e6e5e4e3e2e1e0, 0xe4e3e2e1)
#endif

# octword crossing
  MISMATCHED_STORE_TEST(106, sh, lb,  s0, 31, 31, 0xe9e8, SEXT(0xe8, 8))
  MISMATCHED_STORE_TEST(107, sh, lb,  s0, 31, 32, 0xebea, SEXT(0xeb, 8))
  MISMATCHED_STORE_TEST(108, sh, lbu, s0, 31, 31, 0xedec, 0xec)
  MISMATCHED_STORE_TEST(109, sh, lbu, s0, 31, 32, 0xefee, 0xef)
  MISMATCHED_STORE_TEST(110, sw, lb,  s0, 29, 29, 0xf3f2f1f0, SEXT(0xf0, 8))
  MISMATCHED_STORE_TEST(111, sw, lbu, s0, 30, 32, 0xf7f6f5f4, 0xf6)
  MISMATCHED_STORE_TEST(112, sw, lh,  s0, 29, 31, 0xfbfaf9f8, SEXT(0xfbfa, 16))
  MISMATCHED_STORE_TEST(113, sw, lhu, s0, 31, 31, 0xfffefdfc, 0xfdfc)

#if __riscv_xlen == 64
  MISMATCHED_STORE_TEST(114, sd, lb,  s0, 25, 32, 0x0706050403020100, SEXT(0x07, 8))
  MISMATCHED_STORE_TEST(115, sd, lbu, s0, 26, 33, 0x0f0e0d0c0b0a0908, 0x0f)
  MISMATCHED_STORE_TEST(116, sd, lh,  s0, 27, 31, 0x1716151413121110, SEXT(0x1514, 16))
  MISMATCHED_STORE_TEST(117, sd, lhu, s0, 28, 31, 0x1f1e1d1c1b1a1918, 0x1c1b)
  MISMATCHED_STORE_TEST(118, sd, lw,  s0, 29, 29, 0x2726252423222120, SEXT(0x23222120, 32))
  MISMATCHED_STORE_TEST(119, sd, lw,  s0, 30, 30, 0x2f2e2d2c2b2a2928, SEXT(0x2b2a2928, 32))
  MISMATCHED_STORE_TEST(120, sd, lwu, s0, 31, 31, 0x3736353433323130, 0x33323130)
#endif

# cacheline crossing
  MISMATCHED_STORE_TEST(121, sh, lb,  s0, 63, 63, 0x4948, SEXT(0x48, 8))
  MISMATCHED_STORE_TEST(122, sh, lb,  s0, 63, 64, 0x4b4a, SEXT(0x4b, 8))
  MISMATCHED_STORE_TEST(123, sh, lbu, s0, 63, 63, 0x4d4c, 0x4c)
  MISMATCHED_STORE_TEST(124, sh, lbu, s0, 63, 64, 0x4f4e, 0x4f)
  MISMATCHED_STORE_TEST(125, sw, lb,  s0, 61, 61, 0x53525150, SEXT(0x50, 8))
  MISMATCHED_STORE_TEST(126, sw, lbu, s0, 62, 64, 0x57565554, 0x56)
  MISMATCHED_STORE_TEST(127, sw, lh,  s0, 61, 63, 0x5b5a5958, SEXT(0x5b5a, 16))
  MISMATCHED_STORE_TEST(128, sw, lhu, s0, 63, 63, 0x5f5e5d5c, 0x5d5c)

#if __riscv_xlen == 64
  MISMATCHED_STORE_TEST(129, sd, lb,  s0, 57, 64, 0x6766656463626160, SEXT(0x67, 8))
  MISMATCHED_STORE_TEST(130, sd, lbu, s0, 58, 65, 0x6f6e6d6c6b6a6968, 0x6f)
  MISMATCHED_STORE_TEST(131, sd, lh,  s0, 59, 63, 0x7776757473727170, SEXT(0x7574, 16))
  MISMATCHED_STORE_TEST(132, sd, lhu, s0, 60, 63, 0x7f7e7d7c7b7a7978, 0x7c7b)
  MISMATCHED_STORE_TEST(133, sd, lw,  s0, 61, 61, 0x8786858483828180, SEXT(0x83828180, 32))
  MISMATCHED_STORE_TEST(134, sd, lw,  s0, 62, 62, 0x8f8e8d8c8b8a8988, SEXT(0x8b8a8988, 32))
  MISMATCHED_STORE_TEST(135, sd, lwu, s0, 63, 63, 0x9796959493929190, 0x93929190)
#endif

/* Memory contents at this point should be:
.word 0x10080000
.word 0x30282018
.word 0x34333231
.word 0x0f373635
.word 0x13121110
.word 0x17161514
.word 0x10080018
.word 0x30282018

.word 0x34333231
.word 0x27373635
.word 0x2b2a2928
.word 0x2f2e2d2c
.word 0x33323130
.word 0x37363534
.word 0x70686038
.word 0x90888078

.word 0x94939291
.word 0x47979695
.word 0x4b4a4948
.word 0x4f4e4d4c
.word 0x53525150
.word 0x57565554
.word 0x5b5a5958
.word 0x5f5e5d5c
.word 0x63626160
.word 0x67666564
.word 0x6b6a6968
.word 0x6f6e6d6c
.word 0x73727170
.word 0x77767574
.word 0x7b7a7978
.word 0x7f7e7d7c
*/

/* Check that a misaligned store writes the correct value, checked by a wider load. */

# within quadword
  MISMATCHED_STORE_TEST(136, sb, lh,  s0, 1, 1, 0x98, SEXT(0xb898, 16))
  MISMATCHED_STORE_TEST(137, sb, lhu, s0, 2, 1, 0x99, 0x9998)
  MISMATCHED_STORE_TEST(138, sh, lw,  s0, 1, 1, 0x9b9a, SEXT(0xc8c09b9a, 32))
  MISMATCHED_STORE_TEST(139, sh, lw,  s0, 3, 2, 0x9d9c, SEXT(0xd09d9c9b, 32))
  MISMATCHED_STORE_TEST(140, sh, lw,  s0, 5, 3, 0x9f9e, SEXT(0x9f9e9d9c, 32))

#if __riscv_xlen == 64
  MISMATCHED_STORE_TEST(141, sb, lwu, s0, 2, 1, 0xa0, 0x9d9ca09a)
  MISMATCHED_STORE_TEST(142, sh, lwu, s0, 3, 2, 0xa2a1, 0x9ea2a1a0)
  MISMATCHED_STORE_TEST(143, sh, lwu, s0, 5, 3, 0xa4a3, 0xa4a3a2a1)

  MISMATCHED_STORE_TEST(144, sb, ld, s0, 2,  1, 0xa5, 0xe1e0a4a3a2a1a59a)
  MISMATCHED_STORE_TEST(145, sh, ld, s0, 7,  2, 0xa7a6, 0xe2a7a6a4a3a2a1a5)
  MISMATCHED_STORE_TEST(146, sh, ld, s0, 9,  3, 0xa9a8, 0xa9a8a7a6a4a3a2a1)
  MISMATCHED_STORE_TEST(147, sw, ld, s0, 5,  4, 0xadacabaa, 0xe4a9a8adacabaaa2)
  MISMATCHED_STORE_TEST(148, sw, ld, s0, 7,  5, 0xb1b0afae, 0xe5e4b1b0afaeabaa)
  MISMATCHED_STORE_TEST(149, sw, ld, s0, 9,  6, 0xb5b4b3b2, 0xe6b5b4b3b2afaeab)
  MISMATCHED_STORE_TEST(150, sw, ld, s0, 11, 7, 0xb9b8b7b6, 0xb9b8b7b6b3b2afae)
#endif

# octword crossing
  MISMATCHED_STORE_TEST(151, sb, lh,  s0, 31, 31, 0xba, SEXT(0x31ba, 16))
  MISMATCHED_STORE_TEST(152, sb, lhu, s0, 32, 31, 0xbb, 0xbbba)
  MISMATCHED_STORE_TEST(153, sh, lw,  s0, 30, 30, 0xbdbc, SEXT(0x32bbbdbc, 32))
  MISMATCHED_STORE_TEST(154, sh, lw,  s0, 31, 30, 0xbfbe, SEXT(0x32bfbebc, 32))
  MISMATCHED_STORE_TEST(155, sh, lw,  s0, 32, 30, 0xc1c0, SEXT(0xc1c0bebc, 32))

#if __riscv_xlen == 64
  MISMATCHED_STORE_TEST(156, sb, lwu, s0, 32, 31, 0xc2, 0x33c1c2be)
  MISMATCHED_STORE_TEST(157, sh, lwu, s0, 31, 29, 0xc4c3, 0xc4c3bc20)
  MISMATCHED_STORE_TEST(158, sh, lwu, s0, 32, 30, 0xc6c5, 0xc6c5c3bc)

  MISMATCHED_STORE_TEST(159, sb, ld, s0, 32, 25, 0xc7, 0xc7c3bc2018100800)
  MISMATCHED_STORE_TEST(160, sh, ld, s0, 31, 26, 0xc9c8, 0xc6c9c8bc20181008)
  MISMATCHED_STORE_TEST(161, sh, ld, s0, 31, 27, 0xcbca, 0x33c6cbcabc201810)
  MISMATCHED_STORE_TEST(162, sw, ld, s0, 32, 28, 0xcfcecdcc, 0xcfcecdcccabc2018)
  MISMATCHED_STORE_TEST(163, sw, ld, s0, 31, 29, 0xd3d2d1d0, 0x35cfd3d2d1d0bc20)
  MISMATCHED_STORE_TEST(164, sw, ld, s0, 30, 30, 0xd7d6d5d4, 0x3635cfd3d7d6d5d4)
  MISMATCHED_STORE_TEST(165, sw, ld, s0, 29, 31, 0xdbdad9d8, 0x373635cfd3d7dbda)
#endif

# cacheline crossing
  MISMATCHED_STORE_TEST(166, sb, lh,  s0, 63, 63, 0xdc, SEXT(0x91dc, 16))
  MISMATCHED_STORE_TEST(167, sb, lhu, s0, 64, 63, 0xdd, 0xdddc)
  MISMATCHED_STORE_TEST(168, sh, lw,  s0, 62, 62, 0xdfde, SEXT(0x92dddfde, 32))
  MISMATCHED_STORE_TEST(169, sh, lw,  s0, 63, 62, 0xe1e0, SEXT(0x92e1e0de, 32))
  MISMATCHED_STORE_TEST(170, sh, lw,  s0, 64, 62, 0xe3e2, SEXT(0xe3e2e0de, 32))

#if __riscv_xlen == 64
  MISMATCHED_STORE_TEST(171, sb, lwu, s0, 64, 63, 0xe4, 0x93e3e4e0)
  MISMATCHED_STORE_TEST(172, sh, lwu, s0, 63, 61, 0xe6e5, 0xe6e5de80)
  MISMATCHED_STORE_TEST(173, sh, lwu, s0, 64, 62, 0xe8e7, 0xe8e7e5de)

  MISMATCHED_STORE_TEST(174, sb, ld, s0, 64, 57, 0xe9, 0xe9e5de8078706860)
  MISMATCHED_STORE_TEST(175, sh, ld, s0, 63, 58, 0xebea, 0xe8ebeade80787068)
  MISMATCHED_STORE_TEST(176, sh, ld, s0, 63, 59, 0xedec, 0x93e8edecde807870)
  MISMATCHED_STORE_TEST(177, sw, ld, s0, 64, 60, 0xf1f0efee, 0xf1f0efeeecde8078)
  MISMATCHED_STORE_TEST(178, sw, ld, s0, 63, 61, 0xf5f4f3f2, 0x95f1f5f4f3f2de80)
  MISMATCHED_STORE_TEST(179, sw, ld, s0, 62, 62, 0xf9f8f7f6, 0x9695f1f5f9f8f7f6)
  MISMATCHED_STORE_TEST(180, sw, ld, s0, 61, 63, 0xfdfcfbfa, 0x979695f1f5f9fdfc)
#endif

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

data:
  .align 3

.word 0x03020100
.word 0x07060504
.word 0x0b0a0908
.word 0x0f0e0d0c
.word 0x13121110
.word 0x17161514
.word 0x1b1a1918
.word 0x1f1e1d1c
.word 0x23222120
.word 0x27262524
.word 0x2b2a2928
.word 0x2f2e2d2c
.word 0x33323130
.word 0x37363534
.word 0x3b3a3938
.word 0x3f3e3d3c

.word 0x43424140
.word 0x47464544
.word 0x4b4a4948
.word 0x4f4e4d4c
.word 0x53525150
.word 0x57565554
.word 0x5b5a5958
.word 0x5f5e5d5c
.word 0x63626160
.word 0x67666564
.word 0x6b6a6968
.word 0x6f6e6d6c
.word 0x73727170
.word 0x77767574
.word 0x7b7a7978
.word 0x7f7e7d7c

.fill 0xff, 1, 80


  TEST_DATA

RVTEST_DATA_END
