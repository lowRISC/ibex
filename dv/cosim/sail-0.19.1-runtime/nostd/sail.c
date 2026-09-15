#include <sail_alloc.h>
#include <sail_failure.h>
#include <sail.h>


/* ********************************************************************** */
/* Sail strings                                                           */
/* ********************************************************************** */

/*
 * Implementation is /incredibly/ inefficient... but we don't use
 * strings that much anyway. A better implementation would not use
 * char* due to immutability requirements, but that would make
 * inter-operating with the C world harder.
 */

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

size_t sail_strlen(const_sail_string str)
{
     size_t i = 0;
     while (true) {
	  if (str[i] == '\0') {
	       return i;
	  }
	  i++;
     }
}

char *sail_strcpy(char *dest, const char *src)
{
     size_t i;
     for (i = 0; src[i] != '\0'; i++) {
	  dest[i] = src[i];
     }
     dest[i] = '\0';
     return dest;
}

int sail_strcmp(const char *str1, const char *str2)
{
     size_t i = 0;
     while (true) {
	  if (str1[i] == str2[i]) {
	       i++;
	  } else {
	       return str1[i] - str2[i];
	  }
     }
}

char *sail_strcat(char *dest, const char *src)
{
     size_t i = 0;
     while (dest[i] != '\0') {
	  i++;
     }
     return sail_strcpy(dest + i, src);
}

void COPY(sail_string)(sail_string *str1, const_sail_string str2)
{
     size_t len = sail_strlen(str2);
     *str1 = sail_realloc(*str1, len + 1);
     *str1 = sail_strcpy(*str1, str2);
}

void KILL(sail_string)(sail_string *str)
{
     sail_free(*str);
}

bool eq_string(const_sail_string str1, const_sail_string str2)
{
     return sail_strcmp(str1, str2) == 0;
}

bool EQUAL(sail_string)(const_sail_string str1, const_sail_string str2)
{
     return sail_strcmp(str1, str2) == 0;
}

void undefined_string(sail_string *str, const unit u) {}

void concat_str(sail_string *stro, const_sail_string str1, const_sail_string str2)
{
     *stro = sail_realloc(*stro, sail_strlen(str1) + sail_strlen(str2) + 1);
     (*stro)[0] = '\0';
     sail_strcat(*stro, str1);
     sail_strcat(*stro, str2);
}

/* ********************************************************************** */
/* Sail integers                                                          */
/* ********************************************************************** */

sail_int CREATE_OF(sail_int, mach_int)(const mach_int op)
{
     return (sail_int) op;
}

mach_int CREATE_OF(mach_int, sail_int)(const sail_int op)
{
     if (MACH_INT_MIN <= op && op <= MACH_INT_MAX) {
          return (mach_int) op;
     } else {
          sail_failure("Lost precision when converting from sail integer to machine integer");
          return -1;
     }
}

mach_int CONVERT_OF(mach_int, sail_int)(const sail_int op)
{
     if (MACH_INT_MIN <= op && op <= MACH_INT_MAX) {
          return (mach_int) op;
     } else {
          sail_failure("Lost precision when converting from sail integer to machine integer");
          return -1;
     }
}

sail_int CONVERT_OF(sail_int, mach_int)(const mach_int op)
{
     return (sail_int) op;
}

bool eq_int(const sail_int op1, const sail_int op2)
{
     return op1 == op2;
}

bool EQUAL(sail_int)(const sail_int op1, const sail_int op2)
{
     return op1 == op2;
}

bool lt(const sail_int op1, const sail_int op2)
{
     return op1 < op2;
}

bool gt(const sail_int op1, const sail_int op2)
{
     return op1 > op2;
}

bool lteq(const sail_int op1, const sail_int op2)
{
     return op1 <= op2;
}

bool gteq(const sail_int op1, const sail_int op2)
{
     return op1 >= op2;
}

// FIXME: Add overflow checks
sail_int shl_int(const sail_int op1, const sail_int op2)
{
     return op1 << op2;
}

mach_int shl_mach_int(const mach_int op1, const mach_int op2)
{
     return op1 << op2;
}

sail_int shr_int(const sail_int op1, const sail_int op2)
{
     return op1 >> op2;
}

mach_int shr_mach_int(const mach_int op1, const mach_int op2)
{
     return op1 >> op2;
}

sail_int undefined_int(const int n)
{
     return (sail_int) n;
}

sail_int undefined_range(const sail_int lower, const sail_int upper)
{
     return lower;
}

sail_int add_int(const sail_int op1, const sail_int op2)
{
     if ((op2 > 0) && (op1 > SAIL_INT_MAX - op2)) {
          sail_failure("Sail integer addition would overflow");
          return -1;
     } else if ((op2 < 0) && (op1 < SAIL_INT_MIN - op2)) {
          sail_failure("Sail integer addition would underflow");
          return -1;
     } else {
          return op1 + op2;
     }
}

sail_int sub_int(const sail_int op1, const sail_int op2)
{
     if ((op2 < 0) && (op1 > SAIL_INT_MAX + op2)) {
          sail_failure("Sail integer subtraction would overflow");
          return -1;
     } else if ((op2 > 0) && (op1 < SAIL_INT_MIN + op2)) {
          sail_failure("Sail integer subtraction would underflow");
          return -1;
     } else {
          return op1 - op2;
     }
}

sail_int sub_nat(const sail_int op1, const sail_int op2)
{
     sail_int rop = sub_int(op1, op2);
     if (rop < 0) {
          return (sail_int) 0;
     } else {
          return rop;
     }
}

sail_int mult_int(const sail_int op1, const sail_int op2)
{
     if (op1 > SAIL_INT_MAX / op2) {
          sail_failure("Sail integer multiplication would overflow");
          return -1;
     } else if (op1 < SAIL_INT_MIN / op2) {
          sail_failure("Sail integer multiplication would underflow");
          return -1;
     } else {
          return op1 * op2;
     }
}

// FIXME: Make all division operators do the right thing with rounding
sail_int ediv_int(const sail_int op1, const sail_int op2)
{
     return op1 / op2;
}

sail_int emod_int(const sail_int op1, const sail_int op2)
{
     return op1 % op2;
}

sail_int tdiv_int(const sail_int op1, const sail_int op2)
{
     return op1 / op2;
}

sail_int tmod_int(const sail_int op1, const sail_int op2)
{
     return op1 % op2;
}

sail_int fdiv_int(const sail_int op1, const sail_int op2)
{
     return op1 / op2;
}

sail_int fmod_int(const sail_int op1, const sail_int op2)
{
     return op1 % op2;
}

sail_int max_int(const sail_int op1, const sail_int op2)
{
     if (op1 < op2) {
          return op2;
     } else {
          return op1;
     }
}

sail_int min_int(const sail_int op1, const sail_int op2)
{
     if (op1 > op2) {
          return op2;
     } else {
          return op1;
     }
}

sail_int neg_int(const sail_int op)
{
     if (op == SAIL_INT_MIN) {
          sail_failure("Sail integer negation would overflow");
          return -1;
     }
     return -op;
}

sail_int abs_int(const sail_int op)
{
     if (op < 0) {
          return neg_int(op);
     } else {
          return op;
     }
}

sail_int pow_int(sail_int base, sail_int exp)
{
     sail_int result = 1;
     while (true)
     {
          if (exp & 1) {
               result *= base;
          }
          exp >>= 1;
          if (!exp) {
               break;
          }
          base *= base;
     }
     return result;
}

sail_int pow2(const sail_int exp)
{
     return pow_int(2, exp);
}

/* ********************************************************************** */
/* Sail bitvectors                                                        */
/* ********************************************************************** */

lbits CONVERT_OF(lbits, fbits)(const fbits op, const uint64_t len, const bool order)
{
     lbits rop;
     rop.len = len;
     rop.bits = op;
     return rop;
}

fbits CONVERT_OF(fbits, lbits)(const lbits op, const bool direction)
{
     return op.bits;
}

sbits CONVERT_OF(sbits, lbits)(const lbits op, const bool order)
{
     return op;
}

lbits CONVERT_OF(lbits, sbits)(const sbits op, const bool order)
{
     return op;
}

lbits UNDEFINED(lbits)(const sail_int len)
{
     lbits rop;
     rop.bits = 0;
     rop.len = (uint64_t) len;
     return rop;
}

bool eq_bits(const lbits op1, const lbits op2)
{
     return op1.bits == op2.bits;
}

bool EQUAL(lbits)(const lbits op1, const lbits op2)
{
     return op1.bits == op2.bits;
}

bool neq_bits(const lbits op1, const lbits op2)
{
     return op1.bits != op2.bits;
}

lbits not_bits(const lbits op)
{
     lbits rop;
     rop.bits = (~op.bits) & sail_bzhi_u64(UINT64_MAX, op.len);
     rop.len = op.len;
     return rop;
}

lbits and_bits(const lbits op1, const lbits op2)
{
     lbits rop;
     rop.bits = op1.bits & op2.bits;
     rop.len = op1.len;
     return rop;
}

lbits or_bits(const lbits op1, const lbits op2)
{
     lbits rop;
     rop.bits = op1.bits | op2.bits;
     rop.len = op1.len;
     return rop;
}

lbits xor_bits(const lbits op1, const lbits op2)
{
     lbits rop;
     rop.bits = op1.bits ^ op2.bits;
     rop.len = op1.len;
     return rop;
}

lbits add_bits(const lbits op1, const lbits op2)
{
     lbits rop;
     rop.bits = (op1.bits + op2.bits) & sail_bzhi_u64(UINT64_MAX, op1.len);
     rop.len = op1.len;
     return rop;
}

lbits sub_bits(const lbits op1, const lbits op2)
{
     lbits rop;
     rop.bits = (op1.bits - op2.bits) & sail_bzhi_u64(UINT64_MAX, op1.len);
     rop.len = op1.len;
     return rop;
}

lbits add_bits_int(const lbits op1, const sail_int op2)
{
     lbits rop;
     rop.bits = (op1.bits + ((uint64_t) op2)) & sail_bzhi_u64(UINT64_MAX, op1.len);
     rop.len = op1.len;
     return rop;
}


lbits sub_bits_int(const lbits op1, const sail_int op2)
{
     lbits rop;
     rop.bits = (op1.bits - ((uint64_t) op2)) & sail_bzhi_u64(UINT64_MAX, op1.len);
     rop.len = op1.len;
     return rop;
}

sail_int sail_unsigned(const lbits op)
{
     return (sail_int) op.bits;
}

sail_int sail_signed(const lbits op)
{
     return (sail_int) ((int64_t) op.bits);
}

fbits bitvector_access(const lbits bv, const sail_int n)
{
     return 1 & (bv.bits >> ((uint64_t) n));
}

lbits slice(const lbits op, const sail_int start, const sail_int len)
{
     uint64_t l = len;
     lbits rop;
     rop.bits = sail_bzhi_u64(op.bits >> ((uint64_t) start), l);
     rop.len = l;
     return rop;
}

lbits set_slice(const sail_int len,
                const sail_int slen,
                const lbits op,
                const sail_int start,
                const lbits slice)
{
     uint64_t s = start;
     uint64_t mask = (1 << (uint64_t) slen) - 1;
     lbits rop;
     rop.len = op.len;
     rop.bits = op.bits;
     rop.bits &= ~(mask << s);
     rop.bits |= slice.bits << s;
     return rop;
}

lbits append(const lbits op1, const lbits op2)
{
     lbits rop;
     rop.bits = (op1.bits << op2.len) | op2.bits;
     rop.len = op1.len + op2.len;
     return rop;
}

sail_int length_lbits(const lbits op)
{
     return (sail_int) op.len;
}

lbits zeros(const sail_int len)
{
     lbits rop;
     rop.bits = 0;
     rop.len = (uint64_t) len;
     return rop;
}

lbits replicate_bits(const lbits op, const sail_int n)
{
     return op;
}

lbits get_slice_int(const sail_int len, const sail_int n, const sail_int start)
{
     return zeros(len);
}

sail_int set_slice_int(const sail_int len, const sail_int n, const sail_int start, const lbits slice)
{
     return n;
}

lbits vector_subrange_lbits(const lbits op, const sail_int n, const sail_int m)
{
     return op;
}

lbits vector_update_subrange_lbits(const lbits op, const sail_int n, const sail_int m, const lbits slice)
{
     return op;
}

/* ********************************************************************** */
/* Sail reals                                                             */
/* ********************************************************************** */

void CREATE(real)(double *r) {}
void KILL(real)(double *r) {}

void to_real(real *rop, const sail_int op)
{
     *rop = (double) op;
}

void div_real(real *rop, const real op1, const real op2)
{
     *rop = op1 / op2;
}

sail_int round_up(const real op)
{
     return (sail_int) op;
}
