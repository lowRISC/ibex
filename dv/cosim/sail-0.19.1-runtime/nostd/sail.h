#ifndef __SAIL_LIB__
#define __SAIL_LIB__

/*
 * Only use libraries here that work with -ffreestanding and -nostdlib
 */
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

#ifdef SAIL_X86INTRIN
#include <x64intrin.h>
#endif

static inline uint64_t sail_bzhi_u64(uint64_t op1, uint64_t op2)
{
#ifdef SAIL_X64INTRIN
     return _bzhi_u64(op1, op2);
#else
     return (op1 << (64 - op2)) >> (64 - op2);
#endif
}

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

/*
 * This is only needed for types that are not just simple C types that
 * live on the stack, and need some kind of setup and teardown
 * routines, as Sail won't use these otherwise.
 */
#define SAIL_BUILTIN_TYPE(type)\
  void create_ ## type(type *);\
  void recreate_ ## type(type *);\
  void copy_ ## type(type *, const type);\
  void kill_ ## type(type *);

/* ********************************************************************** */
/* Sail unit type                                                         */
/* ********************************************************************** */

typedef int unit;

#define UNIT 0

static inline unit UNDEFINED(unit)(const unit u)
{
     return UNIT;
}

static inline bool EQUAL(unit)(const unit u1, const unit u2)
{
     return true;
}

/* ********************************************************************** */
/* Sail booleans                                                          */
/* ********************************************************************** */

/*
 * and_bool and or_bool are special-cased by the compiler to ensure
 * proper short-circuiting evaluation.
 */

#ifndef __cplusplus
static inline bool not(bool b)
{
     return !b;
}
#endif

static inline bool EQUAL(bool)(const bool a, const bool b)
{
     return a == b;
}

static inline bool UNDEFINED(bool)(const unit u)
{
     return false;
}

/* ********************************************************************** */
/* Sail strings                                                           */
/* ********************************************************************** */

/*
 * Sail strings are just C strings.
 */
typedef char *sail_string;
typedef const char *const_sail_string;

SAIL_BUILTIN_TYPE(sail_string)

void undefined_string(sail_string *str, const unit u);

bool eq_string(const_sail_string, const_sail_string);
bool EQUAL(sail_string)(const_sail_string, const_sail_string);

void concat_str(sail_string *stro, const_sail_string str1, const_sail_string str2);
bool string_startswith(const_sail_string s, const_sail_string prefix);

/* ********************************************************************** */
/* Sail integers                                                          */
/* ********************************************************************** */

/* First, we define a type for machine-precision integers, int64_t */

typedef int64_t mach_int;
#define MACH_INT_MAX INT64_MAX
#define MACH_INT_MIN INT64_MIN

static inline bool EQUAL(mach_int)(const mach_int a, const mach_int b)
{
     return a == b;
}

/*
 * For arbitrary precision types, we define a type sail_int. Currently
 * sail_int can either be using GMP arbitrary-precision integers
 * (default) or using __int128 or int64_t which is potentially unsound
 * but MUCH faster. the SAIL_INT_FUNCTION macro allows defining
 * function prototypes that work for either case.
 */
#if defined(SAIL_INT64) || defined(SAIL_INT128)

#ifdef SAIL_INT64
typedef int64_t sail_int;
#define SAIL_INT_MAX INT64_MAX
#define SAIL_INT_MIN INT64_MIN
#else
typedef __int128 sail_int;
#define SAIL_INT_MAX (((__int128) 0x7FFFFFFFFFFFFFFF << 64) | (__int128) 0xFFFFFFFFFFFFFFFF)
#define SAIL_INT_MIN (~SAIL_INT_MAX)
#endif
#define SAIL_INT_FUNCTION(fname, ...) sail_int fname(__VA_ARGS__)

static inline uint64_t sail_int_get_ui(const sail_int op)
{
     return (uint64_t) op;
}

#else

typedef mpz_t sail_int;
#define SAIL_INT_FUNCTION(fname, ...) void fname(sail_int*, __VA_ARGS__)

static inline uint64_t sail_int_get_ui(const sail_int op)
{
     return (uint64_t) mpz_get_ui(op);
}

#endif

SAIL_INT_FUNCTION(CREATE_OF(sail_int, mach_int), const mach_int);
SAIL_INT_FUNCTION(CREATE_OF(sail_int, sail_string), const_sail_string);
mach_int CREATE_OF(mach_int, sail_int)(const sail_int);

SAIL_INT_FUNCTION(CONVERT_OF(sail_int, mach_int), const mach_int);
SAIL_INT_FUNCTION(CONVERT_OF(sail_int, sail_string), const_sail_string);
mach_int CONVERT_OF(mach_int, sail_int)(const sail_int);

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
SAIL_INT_FUNCTION(shl_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(shr_int, const sail_int, const sail_int);

/*
 * undefined_int and undefined_range can't use the UNDEFINED(TYPE)
 * macro, because they're slightly magical. They take extra parameters
 * to ensure that no undefined integer can violate any type-guaranteed
 * constraints.
 */
SAIL_INT_FUNCTION(undefined_int, const int);
SAIL_INT_FUNCTION(undefined_range, const sail_int, const sail_int);

/*
 * Arithmetic operations in integers. We include functions for both
 * truncating towards zero, and rounding towards -infinity (floor) as
 * fdiv/fmod and tdiv/tmod respectively. Plus euclidian division
 * ediv/emod.
 */
SAIL_INT_FUNCTION(add_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(sub_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(sub_nat, const sail_int, const sail_int);
SAIL_INT_FUNCTION(mult_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(ediv_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(emod_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(tdiv_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(tmod_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(fdiv_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(fmod_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(max_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(min_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(neg_int, const sail_int);
SAIL_INT_FUNCTION(abs_int, const sail_int);
SAIL_INT_FUNCTION(pow_int, const sail_int, const sail_int);
SAIL_INT_FUNCTION(pow2, const sail_int);

/* ********************************************************************** */
/* Sail bitvectors                                                        */
/* ********************************************************************** */

/*
 * Sail bitvectors are divided into three types:
 * - (f)ixed, statically known bitvectors fbits
 * - (s)mall bitvectors of an unknown width, but guaranteed to be less than 64-bits, sbits
 * - Arbitrarily (l)arge bitvectors of an unknown width, lbits
 *
 * These types form a total order where each can be losslessly
 * converted upwards into the other.
 */

typedef uint64_t fbits;

static inline bool EQUAL(fbits)(const fbits op1, const fbits op2)
{
  return op1 == op2;
}

static inline fbits safe_rshift(const fbits x, const fbits n)
{
     if (n >= 64) {
          return 0;
     } else {
          return x >> n;
     }
}

/*
 * For backwards compatibility with older Sail C libraries
 */
typedef uint64_t mach_bits;

typedef struct {
     uint64_t len;
     uint64_t bits;
} sbits;

static inline sbits CONVERT_OF(sbits, fbits)(const fbits op, const uint64_t len, const bool order)
{
     sbits rop;
     rop.len = len;
     rop.bits = op;
     return rop;
}

static inline fbits CONVERT_OF(fbits, sbits)(const sbits op, const bool order)
{
     return op.bits;
}

/*
 * If the SAIL_BITS64 symbol is defined, we will use sbits as the
 * lbits type.
 */

#ifdef SAIL_BITS64

typedef sbits lbits;
#define SAIL_BITS_FUNCTION(fname, ...) lbits fname(__VA_ARGS__)

static inline lbits CREATE_OF(lbits, fbits)(const fbits op, const uint64_t len, const bool order)
{
     lbits rop;
     rop.bits = op;
     rop.len = len;
     return rop;
}

static inline lbits CREATE_OF(lbits, sbits)(const sbits op, const bool order)
{
     return op;
}

#else

typedef struct {
  mp_bitcnt_t len;
  mpz_t *bits;
} lbits;
#define SAIL_BITS_FUNCTION(fname, ...) void fname(lbits*, __VA_ARGS__)
SAIL_BUILTIN_TYPE(lbits)

SAIL_BITS_FUNCTION(CREATE_OF(lbits, fbits), const fbits, const uint64_t, const bool);
SAIL_BITS_FUNCTION(CREATE_OF(lbits, sbits), const fbits, const bool);
SAIL_BITS_FUNCTION(RECREATE_OF(lbits, fbits), const fbits, const uint64_t, const bool);
SAIL_BITS_FUNCTION(RECREATE_OF(lbits, sbits), const fbits, const bool);

#endif

SAIL_BITS_FUNCTION(CONVERT_OF(lbits, fbits), const fbits, const uint64_t, const bool);
fbits CONVERT_OF(fbits, lbits)(const lbits, const bool);
SAIL_BITS_FUNCTION(CONVERT_OF(lbits, sbits), const sbits, const bool);
sbits CONVERT_OF(sbits, lbits)(const lbits, const bool);

SAIL_BITS_FUNCTION(UNDEFINED(lbits), const sail_int);

bool eq_bits(const lbits, const lbits);
bool EQUAL(lbits)(const lbits, const lbits);
bool neq_bits(const lbits, const lbits);

SAIL_BITS_FUNCTION(not_bits, const lbits);
SAIL_BITS_FUNCTION(and_bits, const lbits, const lbits);
SAIL_BITS_FUNCTION(or_bits, const lbits, const lbits);
SAIL_BITS_FUNCTION(xor_bits, const lbits, const lbits);

SAIL_BITS_FUNCTION(add_bits, const lbits, const lbits);
SAIL_BITS_FUNCTION(sub_bits, const lbits, const lbits);
SAIL_BITS_FUNCTION(add_bits_int, const lbits, const sail_int);
SAIL_BITS_FUNCTION(sub_bits_int, const lbits, const sail_int);

SAIL_INT_FUNCTION(sail_signed, const lbits op);
SAIL_INT_FUNCTION(sail_unsigned, const lbits op);

fbits bitvector_access(const lbits bv, const sail_int n);
SAIL_BITS_FUNCTION(slice, const lbits, const sail_int, const sail_int);
SAIL_BITS_FUNCTION(set_slice, const sail_int len, const sail_int slen, const lbits op, const sail_int start, const lbits slice);
SAIL_BITS_FUNCTION(append, const lbits, const lbits);
SAIL_INT_FUNCTION(length_lbits, const lbits);
SAIL_BITS_FUNCTION(zeros, const sail_int);
SAIL_BITS_FUNCTION(replicate_bits, const lbits op, const sail_int n);
SAIL_BITS_FUNCTION(get_slice_int, const sail_int len, const sail_int n, const sail_int start);
SAIL_INT_FUNCTION(set_slice_int, const sail_int len, const sail_int n, const sail_int start, const lbits slice);
SAIL_BITS_FUNCTION(vector_subrange_lbits, const lbits op, const sail_int n, const sail_int m);
SAIL_BITS_FUNCTION(vector_update_subrange_lbits, const lbits op, const sail_int n, const sail_int m, const lbits slice);

/* ********************************************************************** */
/* Sail reals                                                             */
/* ********************************************************************** */

#ifdef SAIL_FLOATING_REAL
typedef double real;
#else
typedef mpq_t real;
#endif

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

SAIL_INT_FUNCTION(round_up, const real op);
SAIL_INT_FUNCTION(round_down, const real op);

void to_real(real *rop, const sail_int op);

bool EQUAL(real)(const real op1, const real op2);

bool lt_real(const real op1, const real op2);
bool gt_real(const real op1, const real op2);
bool lteq_real(const real op1, const real op2);
bool gteq_real(const real op1, const real op2);

void real_power(real *rop, const real base, const sail_int exp);

#endif
