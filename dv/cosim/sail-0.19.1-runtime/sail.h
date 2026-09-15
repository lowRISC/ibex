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

#ifndef SAIL_H
#define SAIL_H

#include <inttypes.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include <gmp.h>

#include <time.h>

#ifdef __cplusplus
extern "C" {
#endif

static inline void *sail_malloc(size_t size)
{
  return malloc(size);
}

static inline void sail_free(void *ptr)
{
  free(ptr);
}

#define sail_new(type) (type *)(sail_malloc(sizeof(type)))
#define sail_new_array(type, len) (type *)(sail_malloc((len) * sizeof(type)))

/*
 * Called by the RTS to initialise and clear any library state.
 */
void setup_library(void);
void cleanup_library(void);

/*
 * The Sail compiler expects functions to follow a specific naming
 * convention for allocation, deallocation, and (deep)-copying. These
 * macros implement this naming convention.
 */
#define CREATE(type) create_ ## type
#define RECREATE(type) recreate_ ## type
#define CREATE_OF(type1, type2) create_ ## type1 ## _of_ ## type2
#define RECREATE_OF(type1, type2) recreate_ ## type1 ## _of_ ## type2
#define CONVERT_OF(type1, type2) convert_ ## type1 ## _of_ ## type2
#define COPY(type) copy_ ## type
#define KILL(type) kill_ ## type
#define UNDEFINED(type) undefined_ ## type
#define EQUAL(type) eq_ ## type

#define SAIL_BUILTIN_TYPE_IMPL(type, const_type)\
  void create_ ## type(type *);\
  void recreate_ ## type(type *);\
  void copy_ ## type(type *, const_type);\
  void kill_ ## type(type *);
#define SAIL_BUILTIN_TYPE(type) SAIL_BUILTIN_TYPE_IMPL(type, const type)
/* ***** Sail unit type ***** */

typedef int unit;

#define UNIT 0

unit UNDEFINED(unit)(const unit);
bool EQUAL(unit)(const unit, const unit);

unit skip(const unit);

/* ***** Sail booleans ***** */

/*
 * and_bool and or_bool are special-cased by the compiler to ensure
 * short-circuiting evaluation.
 */
#ifndef __cplusplus
static inline bool not(bool b)
{
     return !b;
}
#endif
bool EQUAL(bool)(const bool, const bool);
bool UNDEFINED(bool)(const unit);

/* ***** Sail strings ***** */

/*
 * Sail strings are just C strings.
 */
typedef char *sail_string;
typedef const char *const_sail_string;

SAIL_BUILTIN_TYPE_IMPL(sail_string, const_sail_string)

void dec_str(sail_string *str, const mpz_t n);
void hex_str(sail_string *str, const mpz_t n);
void hex_str_upper(sail_string *str, const mpz_t n);

void undefined_string(sail_string *str, const unit u);

bool eq_string(const_sail_string, const_sail_string);
bool EQUAL(sail_string)(const_sail_string, const_sail_string);

void concat_str(sail_string *stro, const_sail_string str1, const_sail_string str2);
bool string_startswith(const_sail_string s, const_sail_string prefix);

/* ***** Sail integers ***** */

typedef int64_t mach_int;

bool EQUAL(mach_int)(const mach_int, const mach_int);

typedef mpz_t sail_int;

uint64_t sail_int_get_ui(const sail_int);

#define SAIL_INT_FUNCTION(fname, rtype, ...) void fname(rtype*, __VA_ARGS__)

SAIL_BUILTIN_TYPE(sail_int)

void CREATE_OF(sail_int, mach_int)(sail_int *, const mach_int);
void RECREATE_OF(sail_int, mach_int)(sail_int *, const mach_int);

mach_int CREATE_OF(mach_int, sail_int)(const sail_int);

void CREATE_OF(sail_int, sail_string)(sail_int *, const_sail_string);
void RECREATE_OF(sail_int, sail_string)(mpz_t *, const_sail_string);

void CONVERT_OF(sail_int, sail_string)(sail_int *, const_sail_string);

mach_int CONVERT_OF(mach_int, sail_int)(const sail_int);
void CONVERT_OF(sail_int, mach_int)(sail_int *, const mach_int);

/*
 * Comparison operators for integers
 */
bool eq_int(const sail_int, const sail_int);
bool EQUAL(sail_int)(const sail_int, const sail_int);

bool lt(const sail_int, const sail_int);
bool gt(const sail_int, const sail_int);
bool lteq(const sail_int, const sail_int);
bool gteq(const sail_int, const sail_int);

/*
 * Left and right shift for integers
 */
mach_int shl_mach_int(const mach_int, const mach_int);
mach_int shr_mach_int(const mach_int, const mach_int);
SAIL_INT_FUNCTION(shl_int, sail_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(shr_int, sail_int, const sail_int, const sail_int);

/*
 * undefined_int and undefined_range can't use the UNDEFINED(TYPE)
 * macro, because they're slightly magical. They take extra parameters
 * to ensure that no undefined int can violate any type-guaranteed
 * constraints.
 */
SAIL_INT_FUNCTION(undefined_int, sail_int, const int);
SAIL_INT_FUNCTION(undefined_nat, sail_int, const unit);
SAIL_INT_FUNCTION(undefined_range, sail_int, const sail_int, const sail_int);

/*
 * Arithmetic operations in integers. We include functions for both
 * truncating towards zero, and rounding towards -infinity (floor) as
 * fdiv/fmod and tdiv/tmod respectively.
 */
SAIL_INT_FUNCTION(add_int, sail_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(sub_int, sail_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(sub_nat, sail_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(mult_int, sail_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(ediv_int, sail_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(emod_int, sail_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(tdiv_int, sail_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(tmod_int, sail_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(fdiv_int, sail_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(fmod_int, sail_int, const sail_int, const sail_int);

SAIL_INT_FUNCTION(max_int, sail_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(min_int, sail_int, const sail_int, const sail_int);

SAIL_INT_FUNCTION(neg_int, sail_int, const sail_int);
SAIL_INT_FUNCTION(abs_int, sail_int, const sail_int);

SAIL_INT_FUNCTION(pow_int, sail_int, const sail_int, const sail_int);

SAIL_INT_FUNCTION(pow2, sail_int, const sail_int);

void make_the_value(sail_int *, const sail_int);
void size_itself_int(sail_int *, const sail_int);

/* ***** Sail bitvectors ***** */

typedef uint64_t fbits;

bool eq_bit(const fbits a, const fbits b);

static inline bool bit_to_bool(const fbits a)
{
  return (bool) a;
}

bool EQUAL(fbits)(const fbits, const fbits);
bool EQUAL(ref_fbits)(const fbits*, const fbits*);

typedef struct {
  uint64_t len;
  uint64_t bits;
} sbits;

typedef struct {
  mp_bitcnt_t len;
  mpz_t *bits;
} lbits;

// For backwards compatibility
typedef uint64_t mach_bits;
typedef lbits sail_bits;

SAIL_BUILTIN_TYPE(lbits)

void CREATE_OF(lbits, fbits)(lbits *,
			     const fbits op,
			     const uint64_t len,
			     const bool direction);

void RECREATE_OF(lbits, fbits)(lbits *,
			       const fbits op,
			       const uint64_t len,
			       const bool direction);

void CREATE_OF(lbits, sbits)(lbits *,
			     const sbits op,
			     const bool direction);

void RECREATE_OF(lbits, sbits)(lbits *,
			       const sbits op,
			       const bool direction);

sbits CREATE_OF(sbits, lbits)(const lbits op, const bool direction);
fbits CREATE_OF(fbits, lbits)(const lbits op, const bool direction);
sbits CREATE_OF(sbits, fbits)(const fbits op, const uint64_t len, const bool direction);

/* Bitvector conversions */

fbits CONVERT_OF(fbits, lbits)(const lbits, const bool);
fbits CONVERT_OF(fbits, sbits)(const sbits, const bool);

void CONVERT_OF(lbits, fbits)(lbits *, const fbits, const uint64_t, const bool);
void CONVERT_OF(lbits, sbits)(lbits *, const sbits, const bool);

sbits CONVERT_OF(sbits, fbits)(const fbits, const uint64_t, const bool);
sbits CONVERT_OF(sbits, lbits)(const lbits, const bool);

void UNDEFINED(lbits)(lbits *, const sail_int len);
fbits UNDEFINED(fbits)(const unit);

sbits undefined_sbits(void);

/*
 * Wrapper around >> operator to avoid UB when shift amount is greater
 * than or equal to 64.
 */
fbits safe_rshift(const fbits, const fbits);

/*
 * Used internally to construct large bitvector literals.
 */
void append_64(lbits *rop, const lbits op, const fbits chunk);

void add_bits(lbits *rop, const lbits op1, const lbits op2);
void sub_bits(lbits *rop, const lbits op1, const lbits op2);

void add_bits_int(lbits *rop, const lbits op1, const mpz_t op2);
void sub_bits_int(lbits *rop, const lbits op1, const mpz_t op2);

void and_bits(lbits *rop, const lbits op1, const lbits op2);
void or_bits(lbits *rop, const lbits op1, const lbits op2);
void xor_bits(lbits *rop, const lbits op1, const lbits op2);
void not_bits(lbits *rop, const lbits op);

void mults_vec(lbits *rop, const lbits op1, const lbits op2);
void mult_vec(lbits *rop, const lbits op1, const lbits op2);

void zeros(lbits *rop, const sail_int op);

void zero_extend(lbits *rop, const lbits op, const sail_int len);
fbits fast_zero_extend(const sbits op, const uint64_t n);
void sign_extend(lbits *rop, const lbits op, const sail_int len);
fbits fast_sign_extend(const fbits op, const uint64_t n, const uint64_t m);
fbits fast_sign_extend2(const sbits op, const uint64_t m);

void length_lbits(sail_int *rop, const lbits op);
void count_leading_zeros(sail_int *rop, const lbits op);
void count_trailing_zeros(sail_int *rop, const lbits op);

bool eq_bits(const lbits op1, const lbits op2);
bool EQUAL(lbits)(const lbits op1, const lbits op2);
bool EQUAL(ref_lbits)(const lbits *op1, const lbits *op2);
bool neq_bits(const lbits op1, const lbits op2);

void vector_subrange_lbits(lbits *rop,
                           const lbits op,
                           const sail_int n_mpz,
                           const sail_int m_mpz);

void vector_subrange_inc_lbits(lbits *rop,
			       const lbits op,
			       const sail_int n_mpz,
			       const sail_int m_mpz);

void sail_truncate(lbits *rop, const lbits op, const sail_int len);
void sail_truncateLSB(lbits *rop, const lbits op, const sail_int len);

fbits bitvector_access(const lbits op, const sail_int n_mpz);
fbits bitvector_access_inc(const lbits op, const sail_int n_mpz);

fbits update_fbits(const fbits op, const uint64_t n, const fbits bit);

void sail_unsigned(sail_int *rop, const lbits op);
void sail_signed(sail_int *rop, const lbits op);

mach_int fast_signed(const fbits, const uint64_t);
mach_int fast_unsigned(const fbits);

void append(lbits *rop, const lbits op1, const lbits op2);

sbits append_sf(const sbits, const fbits, const uint64_t);
sbits append_fs(const fbits, const uint64_t, const sbits);
sbits append_ss(const sbits, const sbits);

void replicate_bits(lbits *rop, const lbits op1, const sail_int op2);
fbits fast_replicate_bits(const fbits shift, const fbits v, const mach_int times);

void get_slice_int(lbits *rop, const sail_int len_mpz, const sail_int n, const sail_int start_mpz);

void set_slice_int(sail_int *rop,
		   const sail_int len_mpz,
		   const sail_int n,
		   const sail_int start_mpz,
		   const lbits slice);

void update_lbits(lbits *rop, const lbits op, const sail_int n_mpz, const uint64_t bit);
void update_lbits_inc(lbits *rop, const lbits op, const sail_int n_mpz, const uint64_t bit);

void vector_update_subrange_lbits(lbits *rop,
                                  const lbits op,
                                  const sail_int n_mpz,
                                  const sail_int m_mpz,
                                  const lbits slice);

void vector_update_subrange_inc_lbits(lbits *rop,
				      const lbits op,
				      const sail_int n_mpz,
				      const sail_int m_mpz,
				      const lbits slice);

fbits fast_update_subrange(const fbits op,
			   const mach_int n,
			   const mach_int m,
			   const fbits slice);

void slice(lbits *rop, const lbits op, const sail_int start_mpz, const sail_int len_mpz);
void slice_inc(lbits *rop, const lbits op, const sail_int start_mpz, const sail_int len_mpz);

sbits sslice(const fbits op, const mach_int start, const mach_int len);

void set_slice(lbits *rop,
	       const sail_int len_mpz,
	       const sail_int slen_mpz,
	       const lbits op,
	       const sail_int start_mpz,
	       const lbits slice);

void shift_bits_left(lbits *rop, const lbits op1, const lbits op2);
void shift_bits_right(lbits *rop, const lbits op1, const lbits op2);
void shift_bits_right_arith(lbits *rop, const lbits op1, const lbits op2);

void shiftl(lbits *rop, const lbits op1, const sail_int op2);
void shiftr(lbits *rop, const lbits op1, const sail_int op2);
void arith_shiftr(lbits *rop, const lbits op1, const sail_int op2);

void reverse_endianness(lbits*, lbits);

bool eq_sbits(const sbits op1, const sbits op2);
bool neq_sbits(const sbits op1, const sbits op2);
sbits not_sbits(const sbits op);
sbits xor_sbits(const sbits op1, const sbits op2);
sbits or_sbits(const sbits op1, const sbits op2);
sbits and_sbits(const sbits op1, const sbits op2);
sbits add_sbits(const sbits op1, const sbits op2);
sbits sub_sbits(const sbits op1, const sbits op2);

/* ***** Sail reals ***** */

typedef mpq_t real;

SAIL_BUILTIN_TYPE(real)

void CREATE_OF(real, sail_string)(real *rop, const_sail_string op);
void CONVERT_OF(real, sail_string)(real *rop, const_sail_string op);

void UNDEFINED(real)(real *rop, unit u);

void neg_real(real *rop, const real op);

void mult_real(real *rop, const real op1, const real op2);
void sub_real(real *rop, const real op1, const real op2);
void add_real(real *rop, const real op1, const real op2);
void div_real(real *rop, const real op1, const real op2);

void sqrt_real(real *rop, const real op);
void abs_real(real *rop, const real op);

void round_up(sail_int *rop, const real op);
void round_down(sail_int *rop, const real op);

void to_real(real *rop, const sail_int op);

bool EQUAL(real)(const real op1, const real op2);

bool lt_real(const real op1, const real op2);
bool gt_real(const real op1, const real op2);
bool lteq_real(const real op1, const real op2);
bool gteq_real(const real op1, const real op2);

void real_power(real *rop, const real base, const sail_int exp);

unit print_real(const_sail_string, const real);
unit prerr_real(const_sail_string, const real);

void random_real(real *rop, unit);

/* ***** String utilities ***** */

void string_length(sail_int *len, const_sail_string s);
void string_drop(sail_string *dst, const_sail_string s, sail_int len);
void string_take(sail_string *dst, const_sail_string s, sail_int len);


/* ***** Printing ***** */

void string_of_int(sail_string *str, const sail_int i);
void string_of_lbits(sail_string *str, const lbits op);
void string_of_fbits(sail_string *str, const fbits op);
void decimal_string_of_lbits(sail_string *str, const lbits op);
void decimal_string_of_fbits(sail_string *str, const fbits op);

/* ***** Mapping support ***** */

void parse_dec_bits(lbits *res, const mpz_t n, const char *dec);

bool valid_dec_bits(const mpz_t n, const char *dec);

void parse_hex_bits(lbits *stro, const mpz_t n, const_sail_string str);

bool valid_hex_bits(const mpz_t n, const_sail_string str);

/*
 * Utility function not callable from Sail!
 */
void fprint_bits(const_sail_string pre,
		 const lbits op,
		 const_sail_string post,
		 FILE *stream);

unit print_bits(const_sail_string str, const lbits op);
unit prerr_bits(const_sail_string str, const lbits op);

unit print(const_sail_string str);
unit print_endline(const_sail_string str);

unit prerr(const_sail_string str);
unit prerr_endline(const_sail_string str);

unit print_int(const_sail_string str, const sail_int op);
unit prerr_int(const_sail_string str, const sail_int op);

unit sail_putchar(const sail_int op);

/* ***** Misc ***** */

void get_time_ns(sail_int*, const unit);

/* ***** ARM optimisations ***** */

void arm_align(lbits *, const lbits, const sail_int);

#ifdef __cplusplus
}
#endif

#endif
