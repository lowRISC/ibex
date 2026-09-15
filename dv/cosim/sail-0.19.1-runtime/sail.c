/****************************************************************************/
/*     Sail                                                                 */
/*                                                                          */
/*  Sail and the Sail architecture models here, comprising all files and    */
/*  directories except the ASL-derived Sail code in the aarch64 directory,  */
/*  are subject to the BSD two-clause licence below.                        */
/*                                                                          */
/*  The ASL derived parts of the ARMv8.3 specification in                   */
/*  aarch64/no_vector and aarch64/full are copyright ARM Ltd.               */
/*                                                                          */
/*  Copyright (c) 2013-2021                                                 */
/*    Kathyrn Gray                                                          */
/*    Shaked Flur                                                           */
/*    Stephen Kell                                                          */
/*    Gabriel Kerneis                                                       */
/*    Robert Norton-Wright                                                  */
/*    Christopher Pulte                                                     */
/*    Peter Sewell                                                          */
/*    Alasdair Armstrong                                                    */
/*    Brian Campbell                                                        */
/*    Thomas Bauereiss                                                      */
/*    Anthony Fox                                                           */
/*    Jon French                                                            */
/*    Dominic Mulligan                                                      */
/*    Stephen Kell                                                          */
/*    Mark Wassell                                                          */
/*    Alastair Reid (Arm Ltd)                                               */
/*                                                                          */
/*  All rights reserved.                                                    */
/*                                                                          */
/*  This work was partially supported by EPSRC grant EP/K008528/1 <a        */
/*  href="http://www.cl.cam.ac.uk/users/pes20/rems">REMS: Rigorous          */
/*  Engineering for Mainstream Systems</a>, an ARM iCASE award, EPSRC IAA   */
/*  KTF funding, and donations from Arm.  This project has received         */
/*  funding from the European Research Council (ERC) under the European     */
/*  Union’s Horizon 2020 research and innovation programme (grant           */
/*  agreement No 789108, ELVER).                                            */
/*                                                                          */
/*  This software was developed by SRI International and the University of  */
/*  Cambridge Computer Laboratory (Department of Computer Science and       */
/*  Technology) under DARPA/AFRL contracts FA8650-18-C-7809 ("CIFV")        */
/*  and FA8750-10-C-0237 ("CTSRD").                                         */
/*                                                                          */
/*  SPDX-License-Identifier: BSD-2-Clause                                   */
/****************************************************************************/

#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif
#include<assert.h>
#include<inttypes.h>
#include<stdbool.h>
#include<stdio.h>
#include<stdlib.h>
#include<string.h>
#include<time.h>

#include"sail.h"

#ifdef __cplusplus
extern "C" {
#endif

// zero bits from high index, same semantics as bzhi intrinsic
uint64_t bzhi_u64(uint64_t bits, uint64_t len)
{
  return bits & (UINT64_MAX >> (64 - len));
}

/*
 * Temporary mpzs for use in functions below. To avoid conflicts, only
 * use in functions that do not call other functions in this file.
 */
static sail_int sail_lib_tmp1, sail_lib_tmp2, sail_lib_tmp3;
static real sail_lib_tmp_real;

#define FLOAT_PRECISION 255

void setup_library(void)
{
  srand(0x0);
  mpz_init(sail_lib_tmp1);
  mpz_init(sail_lib_tmp2);
  mpz_init(sail_lib_tmp3);
  mpq_init(sail_lib_tmp_real);
  mpf_set_default_prec(FLOAT_PRECISION);
}

void cleanup_library(void)
{
  mpz_clear(sail_lib_tmp1);
  mpz_clear(sail_lib_tmp2);
  mpz_clear(sail_lib_tmp3);
  mpq_clear(sail_lib_tmp_real);
}

bool EQUAL(unit)(const unit a, const unit b)
{
  return true;
}

unit UNDEFINED(unit)(const unit u)
{
  return UNIT;
}

unit skip(const unit u)
{
  return UNIT;
}

/* ***** Sail bit type ***** */

bool eq_bit(const fbits a, const fbits b)
{
  return a == b;
}

/* ***** Sail booleans ***** */

bool EQUAL(bool)(const bool a, const bool b) {
  return a == b;
}

bool UNDEFINED(bool)(const unit u) {
  return false;
}

/* ***** Sail strings ***** */

void CREATE(sail_string)(sail_string *str)
{
  char *istr = (char *) sail_malloc(1 * sizeof(char));
  istr[0] = '\0';
  *str = istr;
}

void RECREATE(sail_string)(sail_string *str)
{
  sail_free(*str);
  char *istr = (char *) sail_malloc(1 * sizeof(char));
  istr[0] = '\0';
  *str = istr;
}

void COPY(sail_string)(sail_string *str1, const_sail_string str2)
{
  size_t len = strlen(str2);
  *str1 = (sail_string)realloc(*str1, len + 1);
  *str1 = strcpy(*str1, str2);
}

void KILL(sail_string)(sail_string *str)
{
  sail_free(*str);
}

void dec_str(sail_string *str, const mpz_t n)
{
  sail_free(*str);
  gmp_asprintf(str, "%Zd", n);
}

void hex_str(sail_string *str, const mpz_t n)
{
  sail_free(*str);

  if (mpz_cmp_si(n, 0) < 0) {
    mpz_t abs;
    mpz_init(abs);
    mpz_abs(abs, n);
    gmp_asprintf(str, "-0x%Zx", abs);
    mpz_clear(abs);
  } else {
    gmp_asprintf(str, "0x%Zx", n);
  }
}

void hex_str_upper(sail_string *str, const mpz_t n)
{
  sail_free(*str);

  if (mpz_cmp_si(n, 0) < 0) {
    mpz_t abs;
    mpz_init(abs);
    mpz_abs(abs, n);
    gmp_asprintf(str, "-0x%ZX", abs);
    mpz_clear(abs);
  } else {
    gmp_asprintf(str, "0x%ZX", n);
  }
}

bool eq_string(const_sail_string str1, const_sail_string str2)
{
  return strcmp(str1, str2) == 0;
}

bool EQUAL(sail_string)(const_sail_string str1, const_sail_string str2)
{
  return strcmp(str1, str2) == 0;
}

void undefined_string(sail_string *str, const unit u) {}

void concat_str(sail_string *stro, const_sail_string str1, const_sail_string str2)
{
  sail_string in1;
  sail_string in2;
  size_t in1_len = strlen(str1);
  size_t in2_len = strlen(str2);
  bool in1_free = false;
  bool in2_free = false;

  if (*stro == str1) {
    in1 = (sail_string)sail_malloc(in1_len + 1);
    strcpy(in1, str1);
    in1_free = true;
  } else {
    in1 = (sail_string)str1;
  }

  if (*stro == str2) {
    in2 = (sail_string)sail_malloc(in2_len + 1);
    strcpy(in2, str2);
    in2_free = true;
  } else {
    in2 = (sail_string)str2;
  }

  *stro = (sail_string)realloc(*stro, in1_len + in2_len + 1);
  (*stro)[0] = '\0';
  strcat(*stro, in1);
  strcat(*stro, in2);

  if (in1_free) sail_free(in1);
  if (in2_free) sail_free(in2);
}

bool string_startswith(const_sail_string s, const_sail_string prefix)
{
  return strstr(s, prefix) == s;
}

void string_length(sail_int *len, const_sail_string s)
{
  mpz_set_ui(*len, strlen(s));
}

void string_drop(sail_string *dst, const_sail_string s, sail_int ns)
{
  size_t len = strlen(s);
  mach_int n = CREATE_OF(mach_int, sail_int)(ns);
  if (len >= n) {
    *dst = (sail_string)realloc(*dst, (len - n) + 1);
    memcpy(*dst, s + n, len - n);
    (*dst)[len - n] = '\0';
  } else {
    *dst = (sail_string)realloc(*dst, 1);
    **dst = '\0';
  }
}

void string_take(sail_string *dst, const_sail_string s, sail_int ns)
{
  size_t len = strlen(s);
  mach_int n = CREATE_OF(mach_int, sail_int)(ns);
  mach_int to_copy;
  if (len <= n) {
    to_copy = len;
  } else {
    to_copy = n;
  }
  *dst = (sail_string)realloc(*dst, to_copy + 1);
  memcpy(*dst, s, to_copy);
  (*dst)[to_copy] = '\0';
}

/* ***** Sail integers ***** */

uint64_t sail_int_get_ui(const mpz_t op)
{
  return mpz_get_ui(op);
}

bool EQUAL(mach_int)(const mach_int op1, const mach_int op2)
{
  return op1 == op2;
}

#ifndef USE_INT128

void COPY(sail_int)(sail_int *rop, const sail_int op)
{
  mpz_set(*rop, op);
}

void CREATE(sail_int)(sail_int *rop)
{
  mpz_init(*rop);
}

void RECREATE(sail_int)(sail_int *rop)
{
  mpz_set_ui(*rop, 0);
}

void KILL(sail_int)(sail_int *rop)
{
  mpz_clear(*rop);
}

void CREATE_OF(sail_int, mach_int)(sail_int *rop, mach_int op)
{
  mpz_init_set_si(*rop, op);
}

mach_int CREATE_OF(mach_int, sail_int)(const sail_int op)
{
  return mpz_get_ui(op);
}

void RECREATE_OF(sail_int, mach_int)(sail_int *rop, mach_int op)
{
  mpz_set_si(*rop, op);
}

void CREATE_OF(sail_int, sail_string)(sail_int *rop, const_sail_string str)
{
  mpz_init_set_str(*rop, str, 10);
}

void CONVERT_OF(sail_int, sail_string)(sail_int *rop, const_sail_string str)
{
  mpz_set_str(*rop, str, 10);
}

void RECREATE_OF(sail_int, sail_string)(mpz_t *rop, const_sail_string str)
{
  mpz_set_str(*rop, str, 10);
}

mach_int CONVERT_OF(mach_int, sail_int)(const sail_int op)
{
  return mpz_get_si(op);
}

void CONVERT_OF(sail_int, mach_int)(sail_int *rop, const mach_int op)
{
  mpz_set_si(*rop, op);
}

bool eq_int(const sail_int op1, const sail_int op2)
{
  return !abs(mpz_cmp(op1, op2));
}

bool EQUAL(sail_int)(const sail_int op1, const sail_int op2)
{
  return !abs(mpz_cmp(op1, op2));
}

bool lt(const sail_int op1, const sail_int op2)
{
  return mpz_cmp(op1, op2) < 0;
}

bool gt(const mpz_t op1, const mpz_t op2)
{
  return mpz_cmp(op1, op2) > 0;
}

bool lteq(const mpz_t op1, const mpz_t op2)
{
  return mpz_cmp(op1, op2) <= 0;
}

bool gteq(const mpz_t op1, const mpz_t op2)
{
  return mpz_cmp(op1, op2) >= 0;
}

void shl_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  mpz_mul_2exp(*rop, op1, mpz_get_ui(op2));
}

mach_int shl_mach_int(const mach_int op1, const mach_int op2)
{
  return op1 << op2;
}

void shr_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  mpz_fdiv_q_2exp(*rop, op1, mpz_get_ui(op2));
}

mach_int shr_mach_int(const mach_int op1, const mach_int op2)
{
  return op1 >> op2;
}

void undefined_int(sail_int *rop, const int n)
{
  mpz_set_ui(*rop, (uint64_t) n);
}

void undefined_nat(sail_int *rop, const unit u)
{
  mpz_set_ui(*rop, 0);
}

void undefined_range(sail_int *rop, const sail_int l, const sail_int u)
{
  mpz_set(*rop, l);
}

void add_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  mpz_add(*rop, op1, op2);
}

void sub_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  mpz_sub(*rop, op1, op2);
}

void sub_nat(sail_int *rop, const sail_int op1, const sail_int op2)
{
  mpz_sub(*rop, op1, op2);
  if (mpz_cmp_ui(*rop, 0) < 0ul) {
    mpz_set_ui(*rop, 0ul);
  }
}

void mult_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  mpz_mul(*rop, op1, op2);
}

void ediv_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  /* GMP doesn't have Euclidean division but we can emulate it using 
     flooring and ceiling division. */
  if (mpz_sgn(op2) >= 0) {
    mpz_fdiv_q(*rop, op1, op2);
  } else {
    mpz_cdiv_q(*rop, op1, op2);
  }
}

void emod_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  /* The documentation isn't that explicit but I think this is 
     Euclidean mod. */
  mpz_mod(*rop, op1, op2);
}

void tdiv_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  mpz_tdiv_q(*rop, op1, op2);
}

void tmod_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  mpz_tdiv_r(*rop, op1, op2);
}

void fdiv_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  mpz_fdiv_q(*rop, op1, op2);
}

void fmod_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  mpz_fdiv_r(*rop, op1, op2);
}

void max_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  if (lt(op1, op2)) {
    mpz_set(*rop, op2);
  } else {
    mpz_set(*rop, op1);
  }
}

void min_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  if (gt(op1, op2)) {
    mpz_set(*rop, op2);
  } else {
    mpz_set(*rop, op1);
  }
}

void neg_int(sail_int *rop, const sail_int op)
{
  mpz_neg(*rop, op);
}

void abs_int(sail_int *rop, const sail_int op)
{
  mpz_abs(*rop, op);
}

void pow_int(sail_int *rop, const sail_int op1, const sail_int op2)
{
  uint64_t n = mpz_get_ui(op2);
  mpz_pow_ui(*rop, op1, n);
}

void pow2(sail_int *rop, const sail_int exp)
{
  /* Assume exponent is never more than 2^64... */
  uint64_t exp_ui = mpz_get_ui(exp);
  mpz_t base;
  mpz_init_set_ui(base, 2ul);
  mpz_pow_ui(*rop, base, exp_ui);
  mpz_clear(base);
}

#endif

/* ***** Sail bitvectors ***** */

bool EQUAL(fbits)(const fbits op1, const fbits op2)
{
  return op1 == op2;
}

bool EQUAL(ref_fbits)(const fbits *op1, const fbits *op2)
{
  return *op1 == *op2;
}

void CREATE(lbits)(lbits *rop)
{
  rop->bits = (mpz_t *)sail_malloc(sizeof(mpz_t));
  rop->len = 0;
  mpz_init(*rop->bits);
}

void RECREATE(lbits)(lbits *rop)
{
  rop->len = 0;
  mpz_set_ui(*rop->bits, 0);
}

void COPY(lbits)(lbits *rop, const lbits op)
{
  rop->len = op.len;
  mpz_set(*rop->bits, *op.bits);
}

void KILL(lbits)(lbits *rop)
{
  mpz_clear(*rop->bits);
  sail_free(rop->bits);
}

void CREATE_OF(lbits, fbits)(lbits *rop, const uint64_t op, const uint64_t len, const bool direction)
{
  rop->bits = (mpz_t *)sail_malloc(sizeof(mpz_t));
  rop->len = len;
  mpz_init_set_ui(*rop->bits, op);
}

fbits CREATE_OF(fbits, lbits)(const lbits op, const bool direction)
{
  return mpz_get_ui(*op.bits);
}

sbits CREATE_OF(sbits, lbits)(const lbits op, const bool direction)
{
  sbits rop;
  rop.bits = mpz_get_ui(*op.bits);
  rop.len = op.len;
  return rop;
}

sbits CREATE_OF(sbits, fbits)(const fbits op, const uint64_t len, const bool direction)
{
  sbits rop;
  rop.bits = op;
  rop.len = len;
  return rop;
}

void RECREATE_OF(lbits, fbits)(lbits *rop, const uint64_t op, const uint64_t len, const bool direction)
{
  rop->len = len;
  mpz_set_ui(*rop->bits, op);
}

void CREATE_OF(lbits, sbits)(lbits *rop, const sbits op, const bool direction)
{
  rop->bits = (mpz_t *)sail_malloc(sizeof(mpz_t));
  rop->len = op.len;
  mpz_init_set_ui(*rop->bits, op.bits);
}

void RECREATE_OF(lbits, sbits)(lbits *rop, const sbits op, const bool direction)
{
  rop->len = op.len;
  mpz_set_ui(*rop->bits, op.bits);
}

// Bitvector conversions

fbits CONVERT_OF(fbits, lbits)(const lbits op, const bool direction)
{
  return mpz_get_ui(*op.bits);
}

fbits CONVERT_OF(fbits, sbits)(const sbits op, const bool direction)
{
  return op.bits;
}

void CONVERT_OF(lbits, fbits)(lbits *rop, const fbits op, const uint64_t len, const bool direction)
{
  rop->len = len;
  // use safe_rshift to correctly handle the case when we have a 0-length vector.
  mpz_set_ui(*rop->bits, op & safe_rshift(UINT64_MAX, 64 - len));
}

void CONVERT_OF(lbits, sbits)(lbits *rop, const sbits op, const bool direction)
{
  rop->len = op.len;
  mpz_set_ui(*rop->bits, op.bits & safe_rshift(UINT64_MAX, 64 - op.len));
}

sbits CONVERT_OF(sbits, fbits)(const fbits op, const uint64_t len, const bool direction)
{
  sbits rop;
  rop.len = len;
  rop.bits = op;
  return rop;
}

sbits CONVERT_OF(sbits, lbits)(const lbits op, const bool direction)
{
  sbits rop;
  rop.len = op.len;
  rop.bits = mpz_get_ui(*op.bits);
  return rop;
}

void UNDEFINED(lbits)(lbits *rop, const sail_int len)
{
  zeros(rop, len);
}

fbits UNDEFINED(fbits)(const unit u) { return 0; }

sbits undefined_sbits(void)
{
  sbits rop;
  rop.bits = UINT64_C(0);
  rop.len = UINT64_C(0);
  return rop;
}

fbits safe_rshift(const fbits x, const fbits n)
{
  if (n >= 64) {
    return 0ul;
  } else {
    return x >> n;
  }
}

void normalize_lbits(lbits *rop) {
  /* TODO optimisation: keep a set of masks of various sizes handy */
  mpz_set_ui(sail_lib_tmp1, 1);
  mpz_mul_2exp(sail_lib_tmp1, sail_lib_tmp1, rop->len);
  mpz_sub_ui(sail_lib_tmp1, sail_lib_tmp1, 1);
  mpz_and(*rop->bits, *rop->bits, sail_lib_tmp1);
}

void append_64(lbits *rop, const lbits op, const fbits chunk)
{
  rop->len = rop->len + 64ul;
  mpz_mul_2exp(*rop->bits, *op.bits, 64ul);
  mpz_add_ui(*rop->bits, *rop->bits, chunk);
}

void add_bits(lbits *rop, const lbits op1, const lbits op2)
{
  rop->len = op1.len;
  mpz_add(*rop->bits, *op1.bits, *op2.bits);
  normalize_lbits(rop);
}

void sub_bits(lbits *rop, const lbits op1, const lbits op2)
{
  assert(op1.len == op2.len);
  rop->len = op1.len;
  mpz_sub(*rop->bits, *op1.bits, *op2.bits);
  normalize_lbits(rop);
}

void add_bits_int(lbits *rop, const lbits op1, const mpz_t op2)
{
  rop->len = op1.len;
  mpz_add(*rop->bits, *op1.bits, op2);
  normalize_lbits(rop);
}

void sub_bits_int(lbits *rop, const lbits op1, const mpz_t op2)
{
  rop->len = op1.len;
  mpz_sub(*rop->bits, *op1.bits, op2);
  normalize_lbits(rop);
}

void and_bits(lbits *rop, const lbits op1, const lbits op2)
{
  assert(op1.len == op2.len);
  rop->len = op1.len;
  mpz_and(*rop->bits, *op1.bits, *op2.bits);
}

void or_bits(lbits *rop, const lbits op1, const lbits op2)
{
  assert(op1.len == op2.len);
  rop->len = op1.len;
  mpz_ior(*rop->bits, *op1.bits, *op2.bits);
}

void xor_bits(lbits *rop, const lbits op1, const lbits op2)
{
  assert(op1.len == op2.len);
  rop->len = op1.len;
  mpz_xor(*rop->bits, *op1.bits, *op2.bits);
}

void not_bits(lbits *rop, const lbits op)
{
  rop->len = op.len;
  mpz_set(*rop->bits, *op.bits);
  for (mp_bitcnt_t i = 0; i < op.len; i++) {
    mpz_combit(*rop->bits, i);
  }
}

void mults_vec(lbits *rop, const lbits op1, const lbits op2)
{
  mpz_t op1_int, op2_int;
  mpz_init(op1_int);
  mpz_init(op2_int);
  sail_signed(&op1_int, op1);
  sail_signed(&op2_int, op2);
  rop->len = op1.len * 2;
  mpz_mul(*rop->bits, op1_int, op2_int);
  normalize_lbits(rop);
  mpz_clear(op1_int);
  mpz_clear(op2_int);
}

void mult_vec(lbits *rop, const lbits op1, const lbits op2)
{
  rop->len = op1.len * 2;
  mpz_mul(*rop->bits, *op1.bits, *op2.bits);
  normalize_lbits(rop); /* necessary? */
}


void zeros(lbits *rop, const sail_int op)
{
  rop->len = mpz_get_ui(op);
  mpz_set_ui(*rop->bits, 0);
}

void zero_extend(lbits *rop, const lbits op, const sail_int len)
{
  assert(op.len <= mpz_get_ui(len));
  rop->len = mpz_get_ui(len);
  mpz_set(*rop->bits, *op.bits);
}

fbits fast_zero_extend(const sbits op, const uint64_t n)
{
  return op.bits;
}

void sign_extend(lbits *rop, const lbits op, const sail_int len)
{
  assert(op.len <= mpz_get_ui(len));
  rop->len = mpz_get_ui(len);
  if(mpz_tstbit(*op.bits, op.len - 1)) {
    mpz_set(*rop->bits, *op.bits);
    for(mp_bitcnt_t i = rop->len - 1; i >= op.len; i--) {
      mpz_setbit(*rop->bits, i);
    }
  } else {
    mpz_set(*rop->bits, *op.bits);
  }
}

fbits fast_sign_extend(const fbits op, const uint64_t n, const uint64_t m)
{
  uint64_t rop = op;
  if (op & (UINT64_C(1) << (n - 1))) {
    for (uint64_t i = m - 1; i >= n; i--) {
      rop = rop | (UINT64_C(1) << i);
    }
    return rop;
  } else {
    return rop;
  }
}

fbits fast_sign_extend2(const sbits op, const uint64_t m)
{
  uint64_t rop = op.bits;
  if (op.bits & (UINT64_C(1) << (op.len - 1))) {
    for (uint64_t i = m - 1; i >= op.len; i--) {
      rop = rop | (UINT64_C(1) << i);
    }
    return rop;
  } else {
    return rop;
  }
}

void length_lbits(sail_int *rop, const lbits op)
{
  mpz_set_ui(*rop, op.len);
}

void count_leading_zeros(sail_int *rop, const lbits op)
{
  if (mpz_cmp_ui(*op.bits, 0) == 0) {
    mpz_set_ui(*rop, op.len);
  } else {
    size_t bits = mpz_sizeinbase(*op.bits, 2);
    mpz_set_ui(*rop, op.len - bits);
  }
}

void count_trailing_zeros(sail_int *rop, const lbits op)
{
  if (mpz_cmp_ui(*op.bits, 0) == 0) {
    mpz_set_ui(*rop, op.len);
  } else {
    mp_bitcnt_t ix = mpz_scan1(*op.bits, 0);
    mpz_set_ui(*rop, ix);
  }
}

bool eq_bits(const lbits op1, const lbits op2)
{
  assert(op1.len == op2.len);
  for (mp_bitcnt_t i = 0; i < op1.len; i++) {
    if (mpz_tstbit(*op1.bits, i) != mpz_tstbit(*op2.bits, i)) return false;
  }
  return true;
}

bool EQUAL(lbits)(const lbits op1, const lbits op2)
{
  return eq_bits(op1, op2);
}

bool EQUAL(ref_lbits)(const lbits *op1, const lbits *op2)
{
  return eq_bits(*op1, *op2);
}

bool neq_bits(const lbits op1, const lbits op2)
{
  assert(op1.len == op2.len);
  for (mp_bitcnt_t i = 0; i < op1.len; i++) {
    if (mpz_tstbit(*op1.bits, i) != mpz_tstbit(*op2.bits, i)) return true;
  }
  return false;
}

void vector_subrange_lbits(lbits *rop,
                           const lbits op,
                           const sail_int n_mpz,
                           const sail_int m_mpz)
{
  uint64_t n = mpz_get_ui(n_mpz);
  uint64_t m = mpz_get_ui(m_mpz);

  rop->len = n - (m - 1ul);
  mpz_fdiv_q_2exp(*rop->bits, *op.bits, m);
  normalize_lbits(rop);
}

void vector_subrange_inc_lbits(lbits *rop,
			       const lbits op,
			       const sail_int n_mpz,
			       const sail_int m_mpz)
{
  uint64_t n = mpz_get_ui(n_mpz);
  uint64_t m = mpz_get_ui(m_mpz);

  rop->len = m - (n - 1ul);
  mpz_fdiv_q_2exp(*rop->bits, *op.bits, (op.len - 1) - m);
  normalize_lbits(rop);
}

void sail_truncate(lbits *rop, const lbits op, const sail_int len)
{
  assert(op.len >= mpz_get_ui(len));
  rop->len = mpz_get_ui(len);
  mpz_set(*rop->bits, *op.bits);
  normalize_lbits(rop);
}

void sail_truncateLSB(lbits *rop, const lbits op, const sail_int len)
{
  uint64_t rlen = mpz_get_ui(len);
  assert(op.len >= rlen);
  rop->len = rlen;
  // similar to vector_subrange_lbits above -- right shift LSBs away
  mpz_fdiv_q_2exp(*rop->bits, *op.bits, op.len - rlen);
  normalize_lbits(rop);
}

fbits bitvector_access(const lbits op, const sail_int n_mpz)
{
  uint64_t n = mpz_get_ui(n_mpz);
  return (fbits) mpz_tstbit(*op.bits, n);
}

fbits bitvector_access_inc(const lbits op, const sail_int n_mpz)
{
  uint64_t n = mpz_get_ui(n_mpz);
  return (fbits) mpz_tstbit(*op.bits, (op.len - 1) - n);
}

fbits update_fbits(const fbits op, const uint64_t n, const fbits bit)
{
     if ((bit & 1) == 1) {
          return op | (bit << n);
     } else {
          return op & ~(bit << n);
     }
}

void sail_unsigned(sail_int *rop, const lbits op)
{
  /* Normal form of bv_t is always positive so just return the bits. */
  mpz_set(*rop, *op.bits);
}

void sail_signed(sail_int *rop, const lbits op)
{
  if (op.len == 0) {
    mpz_set_ui(*rop, 0);
  } else {
    mp_bitcnt_t sign_bit = op.len - 1;
    mpz_set(*rop, *op.bits);
    if (mpz_tstbit(*op.bits, sign_bit) != 0) {
      /* If sign bit is unset then we are done,
         otherwise clear sign_bit and subtract 2**sign_bit */
      mpz_set_ui(sail_lib_tmp1, 1);
      mpz_mul_2exp(sail_lib_tmp1, sail_lib_tmp1, sign_bit); /* 2**sign_bit */
      mpz_combit(*rop, sign_bit); /* clear sign_bit */
      mpz_sub(*rop, *rop, sail_lib_tmp1);
    }
  }
}

mach_int fast_unsigned(const fbits op)
{
  return (mach_int) op;
}

mach_int fast_signed(const fbits op, const uint64_t n)
{
  if (op & (UINT64_C(1) << (n - 1))) {
    uint64_t rop = op & ~(UINT64_C(1) << (n - 1));
    return (mach_int) (rop - (UINT64_C(1) << (n - 1)));
  } else {
    return (mach_int) op;
  }
}

void append(lbits *rop, const lbits op1, const lbits op2)
{
  rop->len = op1.len + op2.len;
  mpz_mul_2exp(*rop->bits, *op1.bits, op2.len);
  mpz_ior(*rop->bits, *rop->bits, *op2.bits);
}

sbits append_sf(const sbits op1, const fbits op2, const uint64_t len)
{
  sbits rop;
  rop.bits = (op1.bits << len) | op2;
  rop.len = op1.len + len;
  return rop;
}

sbits append_fs(const fbits op1, const uint64_t len, const sbits op2)
{
  sbits rop;
  rop.bits = (op1 << op2.len) | op2.bits;
  rop.len = len + op2.len;
  return rop;
}

sbits append_ss(const sbits op1, const sbits op2)
{
  sbits rop;
  rop.bits = (op1.bits << op2.len) | op2.bits;
  rop.len = op1.len + op2.len;
  return rop;
}

void replicate_bits(lbits *rop, const lbits op1, const mpz_t op2)
{
  uint64_t op2_ui = mpz_get_ui(op2);
  rop->len = op1.len * op2_ui;
  mpz_set_ui(*rop->bits, 0);
  for (int i = 0; i < op2_ui; i++) {
    mpz_mul_2exp(*rop->bits, *rop->bits, op1.len);
    mpz_ior(*rop->bits, *rop->bits, *op1.bits);
  }
}

uint64_t fast_replicate_bits(const uint64_t shift, const uint64_t v, const int64_t times)
{
  uint64_t r = v;
  for (int i = 1; i < times; ++i) {
    r |= (r << shift);
  }
  return r;
}

// Takes a slice of the (two's complement) binary representation of
// integer n, starting at bit start, and of length len. With the
// argument in the following order:
//
// get_slice_int(len, n, start)
//
// For example:
//
// get_slice_int(8, 1680, 4) =
//
//                    11           0
//                    V            V
// get_slice_int(8, 0b0110_1001_0000, 4) = 0b0110_1001
//                    <-------^
//                    (8 bit) 4
//
void get_slice_int(lbits *rop, const sail_int len_mpz, const sail_int n, const sail_int start_mpz)
{
  uint64_t start = mpz_get_ui(start_mpz);
  uint64_t len = mpz_get_ui(len_mpz);

  mpz_set_ui(*rop->bits, 0ul);
  rop->len = len;

  for (uint64_t i = 0; i < len; i++) {
    if (mpz_tstbit(n, i + start)) mpz_setbit(*rop->bits, i);
  }
}

// Set slice uses the same indexing scheme as get_slice_int, but it
// puts a bitvector slice into an integer rather than returning it.
void set_slice_int(sail_int *rop,
		   const sail_int len_mpz,
		   const sail_int n,
		   const sail_int start_mpz,
		   const lbits slice)
{
  uint64_t start = mpz_get_ui(start_mpz);

  mpz_set(*rop, n);

  for (uint64_t i = 0; i < slice.len; i++) {
    if (mpz_tstbit(*slice.bits, i)) {
      mpz_setbit(*rop, i + start);
    } else {
      mpz_clrbit(*rop, i + start);
    }
  }
}

void update_lbits(lbits *rop, const lbits op, const sail_int n_mpz, const uint64_t bit)
{
  uint64_t n = mpz_get_ui(n_mpz);

  mpz_set(*rop->bits, *op.bits);
  rop->len = op.len;

  if (bit == UINT64_C(0)) {
    mpz_clrbit(*rop->bits, n);
  } else {
    mpz_setbit(*rop->bits, n);
  }
}

void update_lbits_inc(lbits *rop, const lbits op, const sail_int n_mpz, const uint64_t bit)
{
  uint64_t n = mpz_get_ui(n_mpz);

  mpz_set(*rop->bits, *op.bits);
  rop->len = op.len;

  if (bit == UINT64_C(0)) {
    mpz_clrbit(*rop->bits, (op.len - 1) - n);
  } else {
    mpz_setbit(*rop->bits, (op.len - 1) - n);
  }
}

void vector_update_subrange_lbits(lbits *rop,
				 const lbits op,
				 const sail_int n_mpz,
				 const sail_int m_mpz,
				 const lbits slice)
{
  uint64_t n = mpz_get_ui(n_mpz);
  uint64_t m = mpz_get_ui(m_mpz);

  mpz_set(*rop->bits, *op.bits);
  rop->len = op.len;

  for (uint64_t i = 0; i < n - (m - 1ul); i++) {
    if (mpz_tstbit(*slice.bits, i)) {
      mpz_setbit(*rop->bits, i + m);
    } else {
      mpz_clrbit(*rop->bits, i + m);
    }
  }
}

void vector_update_subrange_inc_lbits(lbits *rop,
                                      const lbits op,
                                      const sail_int n_mpz,
                                      const sail_int m_mpz,
                                      const lbits slice)
{
  uint64_t n = mpz_get_ui(n_mpz);
  uint64_t m = mpz_get_ui(m_mpz);

  mpz_set(*rop->bits, *op.bits);
  rop->len = op.len;

  for (uint64_t i = 0; i < m - (n - 1ul); i++) {
    uint64_t out_bit = ((op.len - 1) - m) + i;
    if (mpz_tstbit(*slice.bits, (slice.len - 1) - i)) {
      mpz_setbit(*rop->bits, out_bit);
    } else {
      mpz_clrbit(*rop->bits, out_bit);
    }
  }
}

fbits fast_update_subrange(const fbits op,
			   const mach_int n,
			   const mach_int m,
			   const fbits slice)
{
  fbits rop = op;
  for (mach_int i = 0; i < n - (m - UINT64_C(1)); i++) {
    uint64_t bit = UINT64_C(1) << ((uint64_t) i);
    if (slice & bit) {
      rop |= (bit << m);
    } else {
      rop &= ~(bit << m);
    }
  }
  return rop;
}

void slice(lbits *rop, const lbits op, const sail_int start_mpz, const sail_int len_mpz)
{
  assert(mpz_get_ui(start_mpz) + mpz_get_ui(len_mpz) <= op.len);
  uint64_t start = mpz_get_ui(start_mpz);
  uint64_t len = mpz_get_ui(len_mpz);

  mpz_set_ui(*rop->bits, 0);
  rop->len = len;

  for (uint64_t i = 0; i < len; i++) {
    if (mpz_tstbit(*op.bits, i + start)) mpz_setbit(*rop->bits, i);
  }
}

void slice_inc(lbits *rop, const lbits op, const sail_int start_mpz, const sail_int len_mpz)
{
  assert(mpz_get_ui(start_mpz) + mpz_get_ui(len_mpz) <= op.len);
  uint64_t start = mpz_get_ui(start_mpz);
  uint64_t len = mpz_get_ui(len_mpz);

  mpz_set_ui(*rop->bits, 0);
  rop->len = len;

  for (uint64_t i = 0; i < len; i++) {
    if (mpz_tstbit(*op.bits, ((op.len - 1) - start) - i)) mpz_setbit(*rop->bits, (rop->len - 1) - i);
  }
}

sbits sslice(const fbits op, const mach_int start, const mach_int len)
{
  sbits rop;
  rop.bits = bzhi_u64(op >> start, len);
  rop.len = len;
  return rop;
}

void set_slice(lbits *rop,
	       const sail_int len_mpz,
	       const sail_int slen_mpz,
	       const lbits op,
	       const sail_int start_mpz,
	       const lbits slice)
{
  uint64_t start = mpz_get_ui(start_mpz);

  mpz_set(*rop->bits, *op.bits);
  rop->len = op.len;

  for (uint64_t i = 0; i < slice.len; i++) {
    if (mpz_tstbit(*slice.bits, i)) {
      mpz_setbit(*rop->bits, i + start);
    } else {
      mpz_clrbit(*rop->bits, i + start);
    }
  }
}

void shift_bits_left(lbits *rop, const lbits op1, const lbits op2)
{
  rop->len = op1.len;
  mpz_mul_2exp(*rop->bits, *op1.bits, mpz_get_ui(*op2.bits));
  normalize_lbits(rop);
}

void shift_bits_right(lbits *rop, const lbits op1, const lbits op2)
{
  rop->len = op1.len;
  mpz_tdiv_q_2exp(*rop->bits, *op1.bits, mpz_get_ui(*op2.bits));
}

/* FIXME */
void shift_bits_right_arith(lbits *rop, const lbits op1, const lbits op2)
{
  rop->len = op1.len;
  mp_bitcnt_t shift_amt = mpz_get_ui(*op2.bits);
  mp_bitcnt_t sign_bit = op1.len - 1;
  mpz_fdiv_q_2exp(*rop->bits, *op1.bits, shift_amt);
  if(mpz_tstbit(*op1.bits, sign_bit) != 0) {
    /* */
    for(; shift_amt > 0; shift_amt--) {
      mpz_setbit(*rop->bits, sign_bit - shift_amt + 1);
    }
  }
}

void arith_shiftr(lbits *rop, const lbits op1, const sail_int op2)
{
  rop->len = op1.len;
  mp_bitcnt_t shift_amt = mpz_get_ui(op2);
  mp_bitcnt_t sign_bit = op1.len - 1;
  mpz_fdiv_q_2exp(*rop->bits, *op1.bits, shift_amt);
  if(mpz_tstbit(*op1.bits, sign_bit) != 0) {
    /* */
    for(; shift_amt > 0; shift_amt--) {
      mpz_setbit(*rop->bits, sign_bit - shift_amt + 1);
    }
  }
}

void shiftl(lbits *rop, const lbits op1, const sail_int op2)
{
  rop->len = op1.len;
  mpz_mul_2exp(*rop->bits, *op1.bits, mpz_get_ui(op2));
  normalize_lbits(rop);
}

void shiftr(lbits *rop, const lbits op1, const sail_int op2)
{
  rop->len = op1.len;
  mpz_tdiv_q_2exp(*rop->bits, *op1.bits, mpz_get_ui(op2));
}

void reverse_endianness(lbits *rop, const lbits op)
{
  rop->len = op.len;
  if (rop->len == 64ul) {
    uint64_t x = mpz_get_ui(*op.bits);
    x = (x & 0xFFFFFFFF00000000) >> 32 | (x & 0x00000000FFFFFFFF) << 32;
    x = (x & 0xFFFF0000FFFF0000) >> 16 | (x & 0x0000FFFF0000FFFF) << 16;
    x = (x & 0xFF00FF00FF00FF00) >> 8  | (x & 0x00FF00FF00FF00FF) << 8;
    mpz_set_ui(*rop->bits, x);
  } else if (rop->len == 32ul) {
    uint64_t x = mpz_get_ui(*op.bits);
    x = (x & 0xFFFF0000FFFF0000) >> 16 | (x & 0x0000FFFF0000FFFF) << 16;
    x = (x & 0xFF00FF00FF00FF00) >> 8  | (x & 0x00FF00FF00FF00FF) << 8;
    mpz_set_ui(*rop->bits, x);
  } else if (rop->len == 16ul) {
    uint64_t x = mpz_get_ui(*op.bits);
    x = (x & 0xFF00FF00FF00FF00) >> 8  | (x & 0x00FF00FF00FF00FF) << 8;
    mpz_set_ui(*rop->bits, x);
  } else if (rop->len == 8ul) {
    mpz_set(*rop->bits, *op.bits);
  } else {
    /* For other numbers of bytes we reverse the bytes.
     * XXX could use mpz_import/export for this. */
    mpz_set_ui(sail_lib_tmp1, 0xff); // byte mask
    mpz_set_ui(*rop->bits, 0); // reset accumulator for result
    for(mp_bitcnt_t byte = 0; byte < op.len; byte+=8) {
      mpz_tdiv_q_2exp(sail_lib_tmp2, *op.bits, byte); // shift byte to bottom
      mpz_and(sail_lib_tmp2, sail_lib_tmp2, sail_lib_tmp1); // and with mask
      mpz_mul_2exp(*rop->bits, *rop->bits, 8); // shift result left 8
      mpz_ior(*rop->bits, *rop->bits, sail_lib_tmp2); // or byte into result
    }
  }
}

bool eq_sbits(const sbits op1, const sbits op2)
{
  return op1.bits == op2.bits;
}

bool neq_sbits(const sbits op1, const sbits op2)
{
  return op1.bits != op2.bits;
}

sbits not_sbits(const sbits op)
{
  sbits rop;
  rop.bits = (~op.bits) & bzhi_u64(UINT64_MAX, op.len);
  rop.len = op.len;
  return rop;
}

sbits xor_sbits(const sbits op1, const sbits op2)
{
  sbits rop;
  rop.bits = op1.bits ^ op2.bits;
  rop.len = op1.len;
  return rop;
}

sbits or_sbits(const sbits op1, const sbits op2)
{
  sbits rop;
  rop.bits = op1.bits | op2.bits;
  rop.len = op1.len;
  return rop;
}

sbits and_sbits(const sbits op1, const sbits op2)
{
  sbits rop;
  rop.bits = op1.bits & op2.bits;
  rop.len = op1.len;
  return rop;
}

sbits add_sbits(const sbits op1, const sbits op2)
{
  sbits rop;
  rop.bits = (op1.bits + op2.bits) & bzhi_u64(UINT64_MAX, op1.len);
  rop.len = op1.len;
  return rop;
}

sbits sub_sbits(const sbits op1, const sbits op2)
{
  sbits rop;
  rop.bits = (op1.bits - op2.bits) & bzhi_u64(UINT64_MAX, op1.len);
  rop.len = op1.len;
  return rop;
}

/* ***** Sail Reals ***** */

void CREATE(real)(real *rop)
{
  mpq_init(*rop);
}

void RECREATE(real)(real *rop)
{
  mpq_set_ui(*rop, 0, 1);
}

void KILL(real)(real *rop)
{
  mpq_clear(*rop);
}

void COPY(real)(real *rop, const real op)
{
  mpq_set(*rop, op);
}

void UNDEFINED(real)(real *rop, unit u)
{
  mpq_set_ui(*rop, 0, 1);
}

void neg_real(real *rop, const real op)
{
  mpq_neg(*rop, op);
}

void mult_real(real *rop, const real op1, const real op2) {
  mpq_mul(*rop, op1, op2);
}

void sub_real(real *rop, const real op1, const real op2)
{
  mpq_sub(*rop, op1, op2);
}

void add_real(real *rop, const real op1, const real op2)
{
  mpq_add(*rop, op1, op2);
}

void div_real(real *rop, const real op1, const real op2)
{
  mpq_div(*rop, op1, op2);
}

#define SQRT_PRECISION 30

/*
 * sqrt_real first checks whether the numerator and denominator are both
 * perfect squares (i.e. their square roots are integers), then it
 * will return the exact square root. If that's not the case we use the
 * Babylonian method to calculate the square root to SQRT_PRECISION decimal
 * places.
 */
void sqrt_real(mpq_t *rop, const mpq_t op)
{
  mpq_t tmp;
  mpz_t tmp_z;
  mpq_t p; /* previous estimate, p */
  mpq_t n; /* next estimate, n */

  mpq_init(tmp);
  mpz_init(tmp_z);
  mpq_init(p);
  mpq_init(n);

  /* calculate an initial guess using mpz_sqrt */
  mpz_sqrt(tmp_z, mpq_numref(op));
  mpq_set_num(p, tmp_z);
  mpz_sqrt(tmp_z, mpq_denref(op));
  mpq_set_den(p, tmp_z);

  /* Check if op is a square */
  mpq_mul(tmp, p, p);
  if (mpq_cmp(tmp, op) == 0) {
    mpq_set(*rop, p);

    mpq_clear(tmp);
    mpz_clear(tmp_z);
    mpq_clear(p);
    mpq_clear(n);
    return;
  }


  /* initialise convergence based on SQRT_PRECISION */
  /* convergence is the precision (in decimal places) we want to reach as a fraction 1/(10^precision) */
  mpq_t convergence;
  mpq_init(convergence);
  mpz_set_ui(tmp_z, 10);
  mpz_pow_ui(tmp_z, tmp_z, SQRT_PRECISION);
  mpz_set_ui(mpq_numref(convergence), 1);
  mpq_set_den(convergence, tmp_z);
  /* if op < 1 then we switch to checking relative precision for convergence */
  if (mpq_cmp_ui(op, 1, 1) < 0) {
      mpq_mul(convergence, op, convergence);
  }

  while (true) {
    // n = (p + op / p) / 2
    mpq_div(tmp, op, p);
    mpq_add(tmp, tmp, p);
    mpq_div_2exp(n, tmp, 1);

    /* calculate the difference between n and p */
    mpq_sub(tmp, p, n);
    mpq_abs(tmp, tmp);

    /* if the difference is small enough, return */
    if (mpq_cmp(tmp, convergence) < 0) {
      mpq_set(*rop, n);
      break;
    }

    mpq_swap(n, p);
  }

  mpq_clear(tmp);
  mpz_clear(tmp_z);
  mpq_clear(p);
  mpq_clear(n);
  mpq_clear(convergence);
}

void abs_real(real *rop, const real op)
{
  mpq_abs(*rop, op);
}

void round_up(sail_int *rop, const real op)
{
  mpz_cdiv_q(*rop, mpq_numref(op), mpq_denref(op));
}

void round_down(sail_int *rop, const real op)
{
  mpz_fdiv_q(*rop, mpq_numref(op), mpq_denref(op));
}

void to_real(real *rop, const sail_int op)
{
  mpq_set_z(*rop, op);
  mpq_canonicalize(*rop);
}

bool EQUAL(real)(const real op1, const real op2)
{
  return mpq_cmp(op1, op2) == 0;
}

bool lt_real(const real op1, const real op2)
{
  return mpq_cmp(op1, op2) < 0;
}

bool gt_real(const real op1, const real op2)
{
  return mpq_cmp(op1, op2) > 0;
}

bool lteq_real(const real op1, const real op2)
{
  return mpq_cmp(op1, op2) <= 0;
}

bool gteq_real(const real op1, const real op2)
{
  return mpq_cmp(op1, op2) >= 0;
}

void real_power(real *rop, const real base, const sail_int exp)
{
  int64_t exp_si = mpz_get_si(exp);

  mpz_set_ui(mpq_numref(*rop), 1);
  mpz_set_ui(mpq_denref(*rop), 1);

  real b;
  mpq_init(b);
  mpq_set(b, base);
  int64_t pexp = llabs(exp_si);
  while (pexp != 0) {
    // invariant: rop * b^pexp == base^abs(exp)
    if (pexp & 1) { // b^(e+1) = b * b^e
      mpq_mul(*rop, *rop, b);
      pexp -= 1;
    } else { // b^(2e) = (b*b)^e
      mpq_mul(b, b, b);
      pexp >>= 1;
    }
  }
  if (exp_si < 0) {
    mpq_inv(*rop, *rop);
  }
  mpq_clear(b);
}

void CREATE_OF(real, sail_string)(real *rop, const_sail_string op)
{
  int decimal;
  int total;

  mpq_init(*rop);
  gmp_sscanf(op, "%Zd.%n%Zd%n", sail_lib_tmp1, &decimal, sail_lib_tmp2, &total);

  int len = total - decimal;
  mpz_ui_pow_ui(sail_lib_tmp3, 10, len);
  mpz_set(mpq_numref(*rop), sail_lib_tmp2);
  mpz_set(mpq_denref(*rop), sail_lib_tmp3);
  mpq_canonicalize(*rop);
  mpz_set(mpq_numref(sail_lib_tmp_real), sail_lib_tmp1);
  mpz_set_ui(mpq_denref(sail_lib_tmp_real), 1);
  mpq_add(*rop, *rop, sail_lib_tmp_real);
}

void CONVERT_OF(real, sail_string)(real *rop, const_sail_string op)
{
  int decimal;
  int total;

  gmp_sscanf(op, "%Zd.%n%Zd%n", sail_lib_tmp1, &decimal, sail_lib_tmp2, &total);

  int len = total - decimal;
  mpz_ui_pow_ui(sail_lib_tmp3, 10, len);
  mpz_set(mpq_numref(*rop), sail_lib_tmp2);
  mpz_set(mpq_denref(*rop), sail_lib_tmp3);
  mpq_canonicalize(*rop);
  mpz_set(mpq_numref(sail_lib_tmp_real), sail_lib_tmp1);
  mpz_set_ui(mpq_denref(sail_lib_tmp_real), 1);
  mpq_add(*rop, *rop, sail_lib_tmp_real);
}

unit print_real(const_sail_string str, const real op)
{
  gmp_printf("%s%Qd\n", str, op);
  return UNIT;
}

unit prerr_real(const_sail_string str, const real op)
{
  gmp_fprintf(stderr, "%s%Qd\n", str, op);
  return UNIT;
}

void random_real(real *rop, const unit u)
{
  if (rand() & 1) {
    mpz_set_si(mpq_numref(*rop), rand());
  } else {
    mpz_set_si(mpq_numref(*rop), -rand());
  }
  mpz_set_si(mpq_denref(*rop), rand());
  mpq_canonicalize(*rop);
}

/* ***** Printing functions ***** */

void string_of_int(sail_string *str, const sail_int i)
{
  sail_free(*str);
  gmp_asprintf(str, "%Zd", i);
}

/* asprintf is a GNU extension, but it should exist on BSD */
void string_of_fbits(sail_string *str, const fbits op)
{
  sail_free(*str);
  int bytes = asprintf(str, "0x%" PRIx64, op);
  if (bytes == -1) {
    fprintf(stderr, "Could not print bits 0x%" PRIx64 "\n", op);
  }
}

void string_of_lbits(sail_string *str, const lbits op)
{
  sail_free(*str);
  if ((op.len % 4) == 0) {
    gmp_asprintf(str, "0x%*0ZX", op.len / 4, *op.bits);
  } else {
    *str = (char *) sail_malloc((op.len + 3) * sizeof(char));
    (*str)[0] = '0';
    (*str)[1] = 'b';
    for (int i = 1; i <= op.len; ++i) {
      (*str)[i + 1] = mpz_tstbit(*op.bits, op.len - i) + 0x30;
    }
    (*str)[op.len + 2] = '\0';
  }
}

void decimal_string_of_fbits(sail_string *str, const fbits op)
{
  sail_free(*str);
  int bytes = asprintf(str, "%" PRId64, op);
  if (bytes == -1) {
    fprintf(stderr, "Could not print bits %" PRId64 "\n", op);
  }
}

void decimal_string_of_lbits(sail_string *str, const lbits op)
{
  sail_free(*str);
  gmp_asprintf(str, "%Z", *op.bits);
}

void parse_dec_bits(lbits *res, const mpz_t n, const_sail_string dec)
{
    if (!valid_dec_bits(n, dec)) {
        goto failure;
    }

    mpz_t value;
    mpz_init(value);
    
    if (mpz_set_str(value, dec, 10) == 0) {
        res->len = mpz_get_ui(n);
        mpz_set(*(res->bits), value);
        mpz_clear(value);
        return;
    }
    mpz_clear(value);

failure:
    res->len = mpz_get_ui(n);
    mpz_set_ui(*(res->bits), 0);
}

bool valid_dec_bits(const mpz_t n, const_sail_string dec)
{
    size_t len = strlen(dec);

    if (len < 1) {
        return false;
    }

    for (size_t i = 0; i < len; i++) {
        if (!('0' <= dec[i] && dec[i] <= '9')) {
            return false;
        }
    }

    mpz_t value;
    mpz_init(value);

    if (mpz_set_str(value, dec, 10) != 0) {
        mpz_clear(value);
        return false;
    }

    size_t bit_width = mpz_sizeinbase(value, 2);

    bool valid = (bit_width <= mpz_get_ui(n));

    mpz_clear(value);
    return valid;
}

void parse_hex_bits(lbits *res, const mpz_t n, const_sail_string hex)
{
  if (!valid_hex_bits(n, hex)) {
    goto failure;
  }

  mpz_t value;
  mpz_init(value);
  if (mpz_set_str(value, hex + 2, 16) == 0) {
    res->len = mpz_get_ui(n);
    mpz_set(*res->bits, value);
    mpz_clear(value);
    return;
  }
  mpz_clear(value);

  // On failure, we return a zero bitvector of the correct width
failure:
  res->len = mpz_get_ui(n);
  mpz_set_ui(*res->bits, 0);
}

bool valid_hex_bits(const mpz_t n, const_sail_string hex) {
  // The string must be prefixed by '0x'
  if (strncmp(hex, "0x", 2) != 0) {
    return false;
  }

  size_t len = strlen(hex);

  // There must be at least one character after the '0x'
  if (len < 3) {
    return false;
  }

  // Ignore any leading zeros
  int non_zero = 2;
  while (hex[non_zero] == '0' && non_zero < len - 1) {
    non_zero++;
  }

  // Check how many bits we need for the first-non-zero (fnz) character.
  int fnz_width;
  char fnz = hex[non_zero];
  if (fnz == '0') {
    fnz_width = 0;
  } else if (fnz == '1') {
    fnz_width = 1;
  } else if (fnz >= '2' && fnz <= '3') {
    fnz_width = 2;
  } else if (fnz >= '4' && fnz <= '7') {
    fnz_width = 3;
  } else {
    fnz_width = 4;
  }

  // The width of the hex string is the width of the first non zero,
  // plus 4 times the remaining hex digits
  int hex_width = fnz_width + ((len - (non_zero + 1)) * 4);
  if (mpz_cmp_si(n, hex_width) < 0) {
    return false;
  }

  // All the non-zero characters must be valid hex digits
  for (int i = non_zero; i < len; i++) {
    char c = hex[i];
    if (!((c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F'))) {
      return false;
    }
  }

  return true;
}

void fprint_bits(const_sail_string pre,
		 const lbits op,
		 const_sail_string post,
		 FILE *stream)
{
  fputs(pre, stream);

  if (op.len % 4 == 0) {
    fputs("0x", stream);
    mpz_t buf;
    mpz_init_set(buf, *op.bits);

    char *hex = (char *)sail_malloc((op.len / 4) * sizeof(char));

    for (int i = 0; i < op.len / 4; ++i) {
      char c = (char) ((0xF & mpz_get_ui(buf)) + 0x30);
      hex[i] = (c < 0x3A) ? c : c + 0x7;
      mpz_fdiv_q_2exp(buf, buf, 4);
    }

    for (int i = op.len / 4; i > 0; --i) {
      fputc(hex[i - 1], stream);
    }

    sail_free(hex);
    mpz_clear(buf);
  } else {
    fputs("0b", stream);
    for (int i = op.len; i > 0; --i) {
      fputc(mpz_tstbit(*op.bits, i - 1) + 0x30, stream);
    }
  }

  fputs(post, stream);
}

unit print_bits(const_sail_string str, const lbits op)
{
  fprint_bits(str, op, "\n", stdout);
  return UNIT;
}

unit prerr_bits(const_sail_string str, const lbits op)
{
  fprint_bits(str, op, "\n", stderr);
  return UNIT;
}

unit print(const_sail_string str)
{
  printf("%s", str);
  return UNIT;
}

unit print_endline(const_sail_string str)
{
  printf("%s\n", str);
  return UNIT;
}

unit prerr(const_sail_string str)
{
  fprintf(stderr, "%s", str);
  return UNIT;
}

unit prerr_endline(const_sail_string str)
{
  fprintf(stderr, "%s\n", str);
  return UNIT;
}

unit print_int(const_sail_string str, const sail_int op)
{
  fputs(str, stdout);
  mpz_out_str(stdout, 10, op);
  putchar('\n');
  return UNIT;
}

unit prerr_int(const_sail_string str, const sail_int op)
{
  fputs(str, stderr);
  mpz_out_str(stderr, 10, op);
  fputs("\n", stderr);
  return UNIT;
}

unit sail_putchar(const sail_int op)
{
  char c = (char) mpz_get_ui(op);
  putchar(c);
  fflush(stdout);
  return UNIT;
}

void get_time_ns(sail_int *rop, const unit u)
{
  struct timespec t;
  clock_gettime(CLOCK_REALTIME, &t);
  mpz_set_si(*rop, t.tv_sec);
  mpz_mul_ui(*rop, *rop, 1000000000);
  mpz_add_ui(*rop, *rop, t.tv_nsec);
}

// ARM specific optimisations

void arm_align(lbits *rop, const lbits x_bv, const sail_int y_mpz)
{
  uint64_t x = mpz_get_ui(*x_bv.bits);
  uint64_t y = mpz_get_ui(y_mpz);
  uint64_t z = y * (x / y);
  mp_bitcnt_t n = x_bv.len;
  mpz_set_ui(*rop->bits, safe_rshift(UINT64_MAX, 64l - (n - 1)) & z);
  rop->len = n;
}

// Monomorphisation
void make_the_value(sail_int *rop, const sail_int op)
{
  mpz_set(*rop, op);
}

void size_itself_int(sail_int *rop, const sail_int op)
{
  mpz_set(*rop, op);
}

#ifdef __cplusplus
}
#endif
