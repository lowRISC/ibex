/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/*
 * Scalar Cryptography Extension - Scalar SHA256 instructions (RV32/RV64)
 * ----------------------------------------------------------------------
 */

union clause ast = SHA256SIG0 : (regidx, regidx)
union clause ast = SHA256SIG1 : (regidx, regidx)
union clause ast = SHA256SUM0 : (regidx, regidx)
union clause ast = SHA256SUM1 : (regidx, regidx)

mapping clause encdec = SHA256SUM0 (rs1, rd) if haveZknh()
  <-> 0b00 @ 0b01000 @ 0b00000 @ rs1 @ 0b001 @ rd @ 0b0010011

mapping clause encdec = SHA256SUM1 (rs1, rd) if haveZknh()
  <-> 0b00 @ 0b01000 @ 0b00001 @ rs1 @ 0b001 @ rd @ 0b0010011

mapping clause encdec = SHA256SIG0 (rs1, rd) if haveZknh()
  <-> 0b00 @ 0b01000 @ 0b00010 @ rs1 @ 0b001 @ rd @ 0b0010011

mapping clause encdec = SHA256SIG1 (rs1, rd) if haveZknh()
  <-> 0b00 @ 0b01000 @ 0b00011 @ rs1 @ 0b001 @ rd @ 0b0010011

mapping clause assembly = SHA256SIG0 (rs1, rd)
  <-> "sha256sig0" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)

mapping clause assembly = SHA256SIG1 (rs1, rd)
  <-> "sha256sig1" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)

mapping clause assembly = SHA256SUM0 (rs1, rd)
  <-> "sha256sum0" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)

mapping clause assembly = SHA256SUM1 (rs1, rd)
  <-> "sha256sum1" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)

function clause execute (SHA256SIG0(rs1, rd)) = {
  let inb    : bits(32) = X(rs1, rs_1)[31..0];
  let result : bits(32) = (inb >>> 7) ^ (inb >>> 18) ^ (inb >>  3);
  X(rd)      = sign_extend(result);
  RETIRE_SUCCESS
}

function clause execute (SHA256SIG1(rs1, rd)) = {
  let inb    : bits(32) = X(rs1, rs_1)[31..0];
  let result : bits(32) = (inb >>> 17) ^ (inb >>> 19) ^ (inb >> 10);
  X(rd)      = sign_extend(result);
  RETIRE_SUCCESS
}

function clause execute (SHA256SUM0(rs1, rd)) = {
  let inb    : bits(32) = X(rs1, rs_1)[31..0];
  let result : bits(32) = (inb >>> 2) ^ (inb >>> 13) ^ (inb >>> 22);
  X(rd)      = sign_extend(result);
  RETIRE_SUCCESS
}

function clause execute (SHA256SUM1(rs1, rd)) = {
  let inb    : bits(32) = X(rs1, rs_1)[31..0];
  let result : bits(32) = (inb >>> 6) ^ (inb >>> 11) ^ (inb >>> 25);
  X(rd)      = sign_extend(result);
  RETIRE_SUCCESS
}

/*
 * Scalar Cryptography Extension - Scalar 32-bit AES instructions (encrypt)
 * ----------------------------------------------------------------------
 */

union clause ast = AES32ESMI : (bits(2), regidx, regidx, regidx)

mapping clause encdec = AES32ESMI (bs, rs2, rs1, rd) if haveZkne() & sizeof(xlen) == 32
  <-> bs @ 0b10011 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0110011

mapping clause assembly = AES32ESMI (bs, rs2, rs1, rd) <->
    "aes32esmi" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2) ^ sep() ^ hex_bits_2(bs)

function clause execute (AES32ESMI (bs, rs2, rs1, rd)) = {
  let shamt   : bits( 5) = bs @ 0b000; /* shamt = bs*8 */
  let si      : bits( 8) = (X(rs2, rs_2) >> shamt)[7..0]; /* SBox Input */
  let so      : bits( 8) = aes_sbox_fwd(si);
  let mixed   : bits(32) = aes_mixcolumn_byte_fwd(so);
  let result  : bits(32) = X(rs1, rs_1)[31..0] ^ (mixed <<< shamt);
  X(rd) = sign_extend(result);
  RETIRE_SUCCESS
}

union clause ast = AES32ESI : (bits(2), regidx, regidx, regidx)

mapping clause encdec = AES32ESI (bs, rs2, rs1, rd) if haveZkne() & sizeof(xlen) == 32
  <-> bs @ 0b10001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0110011

mapping clause assembly = AES32ESI (bs, rs2, rs1, rd) <->
    "aes32esi" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2) ^ sep() ^ hex_bits_2(bs)

function clause execute (AES32ESI (bs, rs2, rs1, rd)) = {
  let shamt   : bits( 5) = bs @ 0b000; /* shamt = bs*8 */
  let si      : bits( 8) = (X(rs2, rs_2) >> shamt)[7..0]; /* SBox Input */
  let so      : bits(32) = 0x000000 @ aes_sbox_fwd(si);
  let result  : bits(32) = X(rs1, rs_1)[31..0] ^ (so <<< shamt);
  X(rd) = sign_extend(result);
  RETIRE_SUCCESS
}

/*
 * Scalar Cryptography Extension - Scalar 32-bit AES instructions (decrypt)
 * ----------------------------------------------------------------------
 */

union clause ast = AES32DSMI : (bits(2), regidx, regidx, regidx)

mapping clause encdec = AES32DSMI (bs, rs2, rs1, rd) if haveZknd() & sizeof(xlen) == 32
  <-> bs @ 0b10111 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0110011

mapping clause assembly = AES32DSMI (bs, rs2, rs1, rd) <->
    "aes32dsmi" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2) ^ sep() ^ hex_bits_2(bs)

function clause execute (AES32DSMI (bs, rs2, rs1, rd)) = {
  let shamt   : bits( 5) = bs @ 0b000; /* shamt = bs*8 */
  let si      : bits( 8) = (X(rs2, rs_2) >> shamt)[7..0]; /* SBox Input */
  let so      : bits( 8) = aes_sbox_inv(si);
  let mixed   : bits(32) = aes_mixcolumn_byte_inv(so);
  let result  : bits(32) = X(rs1, rs_1)[31..0] ^ (mixed <<< shamt);
  X(rd) = sign_extend(result);
  RETIRE_SUCCESS
}

union clause ast = AES32DSI  : (bits(2), regidx, regidx, regidx)

mapping clause encdec = AES32DSI (bs, rs2, rs1, rd) if haveZknd() & sizeof(xlen) == 32
  <-> bs @ 0b10101 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0110011

mapping clause assembly = AES32DSI (bs, rs2, rs1, rd) <->
    "aes32dsi" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2) ^ sep() ^ hex_bits_2(bs)

function clause execute (AES32DSI (bs, rs2, rs1, rd)) = {
  let shamt   : bits( 5) = bs @ 0b000; /* shamt = bs*8 */
  let si      : bits( 8) = (X(rs2, rs_2) >> shamt)[7..0]; /* SBox Input */
  let so      : bits(32) = 0x000000 @ aes_sbox_inv(si);
  let result  : bits(32) = X(rs1, rs_1)[31..0] ^ (so <<< shamt);
  X(rd) = sign_extend(result);
  RETIRE_SUCCESS
}

/*
 * Scalar Cryptography Extension - Scalar 32-bit SHA512 instructions
 * ----------------------------------------------------------------------
 */

union clause ast = SHA512SIG0L : (regidx, regidx, regidx)
union clause ast = SHA512SIG0H : (regidx, regidx, regidx)
union clause ast = SHA512SIG1L : (regidx, regidx, regidx)
union clause ast = SHA512SIG1H : (regidx, regidx, regidx)
union clause ast = SHA512SUM0R : (regidx, regidx, regidx)
union clause ast = SHA512SUM1R : (regidx, regidx, regidx)

mapping clause encdec = SHA512SUM0R (rs2, rs1, rd) if haveZknh() & sizeof(xlen) == 32
  <-> 0b01 @ 0b01000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0110011

mapping clause encdec = SHA512SUM1R (rs2, rs1, rd) if haveZknh() & sizeof(xlen) == 32
  <-> 0b01 @ 0b01001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0110011

mapping clause encdec = SHA512SIG0L (rs2, rs1, rd) if haveZknh() & sizeof(xlen) == 32
  <-> 0b01 @ 0b01010 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0110011

mapping clause encdec = SHA512SIG0H (rs2, rs1, rd) if haveZknh() & sizeof(xlen) == 32
  <-> 0b01 @ 0b01110 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0110011

mapping clause encdec = SHA512SIG1L (rs2, rs1, rd) if haveZknh() & sizeof(xlen) == 32
  <-> 0b01 @ 0b01011 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0110011

mapping clause encdec = SHA512SIG1H (rs2, rs1, rd) if haveZknh() & sizeof(xlen) == 32
  <-> 0b01 @ 0b01111 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0110011

mapping clause assembly = SHA512SIG0L (rs2, rs1, rd)
  <-> "sha512sig0l" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

mapping clause assembly = SHA512SIG0H (rs2, rs1, rd)
  <-> "sha512sig0h" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

mapping clause assembly = SHA512SIG1L (rs2, rs1, rd)
  <-> "sha512sig1l" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

mapping clause assembly = SHA512SIG1H (rs2, rs1, rd)
  <-> "sha512sig1h" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

mapping clause assembly = SHA512SUM0R (rs2, rs1, rd)
  <-> "sha512sum0r" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

mapping clause assembly = SHA512SUM1R (rs2, rs1, rd)
  <-> "sha512sum1r" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

function clause execute (SHA512SIG0H(rs2, rs1, rd)) = {
  X(rd) = sign_extend((X(rs1, rs_1) >>  1) ^ (X(rs1, rs_1) >>  7) ^ (X(rs1, rs_1) >>  8) ^
               (X(rs2, rs_2) << 31)                  ^ (X(rs2, rs_2) << 24));
  RETIRE_SUCCESS
}

function clause execute (SHA512SIG0L(rs2, rs1, rd)) = {
  X(rd) = sign_extend((X(rs1, rs_1) >>  1) ^ (X(rs1, rs_1) >>  7) ^ (X(rs1, rs_1) >>  8) ^
               (X(rs2, rs_2) << 31) ^ (X(rs2, rs_2) << 25) ^ (X(rs2, rs_2) << 24));
  RETIRE_SUCCESS
}

function clause execute (SHA512SIG1H(rs2, rs1, rd)) = {
  X(rd) = sign_extend((X(rs1, rs_1) <<  3) ^ (X(rs1, rs_1) >>  6) ^ (X(rs1, rs_1) >> 19) ^
               (X(rs2, rs_2) >> 29)                  ^ (X(rs2, rs_2) << 13));
  RETIRE_SUCCESS
}

function clause execute (SHA512SIG1L(rs2, rs1, rd)) = {
  X(rd) = sign_extend((X(rs1, rs_1) <<  3) ^ (X(rs1, rs_1) >>  6) ^ (X(rs1, rs_1) >> 19) ^
               (X(rs2, rs_2) >> 29) ^ (X(rs2, rs_2) << 26) ^ (X(rs2, rs_2) << 13));
  RETIRE_SUCCESS
}

function clause execute (SHA512SUM0R(rs2, rs1, rd)) = {
  X(rd) = sign_extend((X(rs1, rs_1) << 25) ^ (X(rs1, rs_1) << 30) ^ (X(rs1, rs_1) >> 28) ^
               (X(rs2, rs_2) >>  7) ^ (X(rs2, rs_2) >>  2) ^ (X(rs2, rs_2) <<  4));
  RETIRE_SUCCESS
}

function clause execute (SHA512SUM1R(rs2, rs1, rd)) = {
  X(rd) = sign_extend((X(rs1, rs_1) << 23) ^ (X(rs1, rs_1) >> 14) ^ (X(rs1, rs_1) >> 18) ^
               (X(rs2, rs_2) >>  9) ^ (X(rs2, rs_2) << 18) ^ (X(rs2, rs_2) << 14));
  RETIRE_SUCCESS
}

/*
 * Scalar Cryptography Extension - Scalar 64-bit AES instructions
 * ----------------------------------------------------------------------
 */

union clause ast = AES64KS1I : (bits(4), regidx, regidx)
union clause ast = AES64KS2  : (regidx, regidx, regidx)
union clause ast = AES64IM   : (regidx, regidx)
union clause ast = AES64ESM  : (regidx, regidx, regidx)
union clause ast = AES64ES   : (regidx, regidx, regidx)
union clause ast = AES64DSM  : (regidx, regidx, regidx)
union clause ast = AES64DS   : (regidx, regidx, regidx)

mapping clause encdec = AES64KS1I (rnum, rs1, rd) if (haveZkne() | haveZknd()) & (sizeof(xlen) == 64) & (rnum <_u 0xB)
  <-> 0b00 @ 0b11000 @ 0b1 @ rnum @ rs1 @ 0b001 @ rd @ 0b0010011

mapping clause encdec = AES64IM (rs1, rd) if haveZknd() & sizeof(xlen) == 64
  <-> 0b00 @ 0b11000 @ 0b00000 @ rs1 @ 0b001 @ rd @ 0b0010011

mapping clause encdec = AES64KS2 (rs2, rs1, rd) if (haveZkne() | haveZknd()) & sizeof(xlen) == 64
  <-> 0b01 @ 0b11111 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0110011

mapping clause encdec = AES64ESM (rs2, rs1, rd) if haveZkne() & sizeof(xlen) == 64
  <-> 0b00 @ 0b11011 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0110011

mapping clause encdec = AES64ES (rs2, rs1, rd) if haveZkne() & sizeof(xlen) == 64
  <-> 0b00 @ 0b11001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0110011

mapping clause encdec = AES64DSM (rs2, rs1, rd) if haveZknd() & sizeof(xlen) == 64
  <-> 0b00 @ 0b11111 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0110011

mapping clause encdec = AES64DS (rs2, rs1, rd) if haveZknd() & sizeof(xlen) == 64
  <-> 0b00 @ 0b11101 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0110011

mapping clause assembly = AES64KS1I (rnum, rs1, rd)
  <-> "aes64ks1i" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_4(rnum)

mapping clause assembly = AES64KS2 (rs2, rs1, rd)
  <-> "aes64ks2" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

mapping clause assembly = AES64IM (rs1, rd)
  <-> "aes64im" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)

mapping clause assembly = AES64ESM (rs2, rs1, rd)
  <-> "aes64esm" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

mapping clause assembly = AES64ES (rs2, rs1, rd)
  <-> "aes64es" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

mapping clause assembly = AES64DSM (rs2, rs1, rd)
  <-> "aes64dsm" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

mapping clause assembly = AES64DS (rs2, rs1, rd)
  <-> "aes64ds" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/* Note: The decoding for this instruction ensures that `rnum` is always in
   the range 0x0..0xA. See the encdec clause for AES64KS1I.
   The rum == 0xA case is used specifically for the AES-256 KeySchedule */
function clause execute (AES64KS1I(rnum, rs1, rd)) = {
  assert(sizeof(xlen) == 64);
  let prev     : bits(32) = X(rs1, rs_1)[63..32];
  let subwords : bits(32) = aes_subword_fwd(prev);
  let result   : bits(32) = if (rnum == 0xA) then subwords
                            else (subwords >>> 8) ^ aes_decode_rcon(rnum);
  X(rd) = result @ result;
  RETIRE_SUCCESS
}

function clause execute (AES64KS2(rs2, rs1, rd)) = {
  assert(sizeof(xlen) == 64);
  let w0 : bits(32) = X(rs1, rs_1)[63..32] ^ X(rs2, rs_2)[31..0];
  let w1 : bits(32) = X(rs1, rs_1)[63..32] ^ X(rs2, rs_2)[31..0] ^ X(rs2, rs_2)[63..32];
  X(rd)  = w1 @ w0;
  RETIRE_SUCCESS
}

function clause execute (AES64IM(rs1, rd)) = {
  assert(sizeof(xlen) == 64);
  let w0 : bits(32) = aes_mixcolumn_inv(X(rs1, rs_1)[31.. 0]);
  let w1 : bits(32) = aes_mixcolumn_inv(X(rs1, rs_1)[63..32]);
  X(rd)  = w1 @ w0;
  RETIRE_SUCCESS
}

function clause execute (AES64ESM(rs2, rs1, rd)) = {
  assert(sizeof(xlen) == 64);
  let sr : bits(64) = aes_rv64_shiftrows_fwd(X(rs2, rs_2), X(rs1, rs_1));
  let wd : bits(64) = sr[63..0];
  let sb : bits(64) = aes_apply_fwd_sbox_to_each_byte(wd);
  X(rd)  = aes_mixcolumn_fwd(sb[63..32]) @ aes_mixcolumn_fwd(sb[31..0]);
  RETIRE_SUCCESS
}

function clause execute (AES64ES(rs2, rs1, rd)) = {
  assert(sizeof(xlen) == 64);
  let sr : bits(64) = aes_rv64_shiftrows_fwd(X(rs2, rs_2), X(rs1, rs_1));
  let wd : bits(64) = sr[63..0];
  X(rd) = aes_apply_fwd_sbox_to_each_byte(wd);
  RETIRE_SUCCESS
}

function clause execute (AES64DSM(rs2, rs1, rd)) = {
  assert(sizeof(xlen) == 64);
  let sr : bits(64) = aes_rv64_shiftrows_inv(X(rs2, rs_2), X(rs1, rs_1));
  let wd : bits(64) = sr[63..0];
  let sb : bits(64) = aes_apply_inv_sbox_to_each_byte(wd);
  X(rd) = aes_mixcolumn_inv(sb[63..32]) @ aes_mixcolumn_inv(sb[31..0]);
  RETIRE_SUCCESS
}

function clause execute (AES64DS(rs2, rs1, rd)) = {
  assert(sizeof(xlen) == 64);
  let sr : bits(64) = aes_rv64_shiftrows_inv(X(rs2, rs_2), X(rs1, rs_1));
  let wd : bits(64) = sr[63..0];
  X(rd) = aes_apply_inv_sbox_to_each_byte(wd);
  RETIRE_SUCCESS
}

/*
 * Scalar Cryptography Extension - Scalar 64-bit SHA512 instructions
 * ----------------------------------------------------------------------
 */

union clause ast = SHA512SIG0 : (regidx, regidx)
union clause ast = SHA512SIG1 : (regidx, regidx)
union clause ast = SHA512SUM0 : (regidx, regidx)
union clause ast = SHA512SUM1 : (regidx, regidx)

mapping clause encdec = SHA512SUM0 (rs1, rd) if haveZknh() & sizeof(xlen) == 64
  <-> 0b00 @ 0b01000 @ 0b00100 @ rs1 @ 0b001 @ rd @ 0b0010011

mapping clause encdec = SHA512SUM1 (rs1, rd) if haveZknh() & sizeof(xlen) == 64
  <-> 0b00 @ 0b01000 @ 0b00101 @ rs1 @ 0b001 @ rd @ 0b0010011

mapping clause encdec = SHA512SIG0 (rs1, rd) if haveZknh() & sizeof(xlen) == 64
  <-> 0b00 @ 0b01000 @ 0b00110 @ rs1 @ 0b001 @ rd @ 0b0010011

mapping clause encdec = SHA512SIG1 (rs1, rd) if haveZknh() & sizeof(xlen) == 64
  <-> 0b00 @ 0b01000 @ 0b00111 @ rs1 @ 0b001 @ rd @ 0b0010011

mapping clause assembly = SHA512SIG0 (rs1, rd)
  <-> "sha512sig0" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)

mapping clause assembly = SHA512SIG1 (rs1, rd)
  <-> "sha512sig1" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)

mapping clause assembly = SHA512SUM0 (rs1, rd)
  <-> "sha512sum0" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)

mapping clause assembly = SHA512SUM1 (rs1, rd)
  <-> "sha512sum1" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)

/* Execute clauses for the 64-bit SHA512 instructions. */

function clause execute (SHA512SIG0(rs1, rd)) = {
  assert(sizeof(xlen) == 64);
  let input  : bits(64) = X(rs1, rs_1);
  let result : bits(64) = (input >>>  1) ^ (input >>>  8) ^ (input >> 7);
  X(rd) = result;
  RETIRE_SUCCESS
}

function clause execute (SHA512SIG1(rs1, rd)) = {
  assert(sizeof(xlen) == 64);
  let input  : bits(64) = X(rs1, rs_1);
  let result : bits(64) = (input >>> 19) ^ (input >>> 61) ^ (input >> 6);
  X(rd) = result;
  RETIRE_SUCCESS
}

function clause execute (SHA512SUM0(rs1, rd)) = {
  assert(sizeof(xlen) == 64);
  let input  : bits(64) = X(rs1, rs_1);
  let result : bits(64) = (input >>> 28) ^ (input >>> 34) ^ (input >>> 39);
  X(rd) = result;
  RETIRE_SUCCESS
}

function clause execute (SHA512SUM1(rs1, rd)) = {
  assert(sizeof(xlen) == 64);
  let input  : bits(64) = X(rs1, rs_1);
  let result : bits(64) = (input >>> 14) ^ (input >>> 18) ^ (input >>> 41);
  X(rd) = result;
  RETIRE_SUCCESS
}
