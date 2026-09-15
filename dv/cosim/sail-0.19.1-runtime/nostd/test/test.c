#include <stdint.h>
#include <assert.h>
#include <gmp.h>

#include <sail.h>

int main(void)
{
#ifdef SAIL_INT128
     /* Check that our 128-bit integer MIN/MAX macros do sensible things */
     assert(SAIL_INT_MAX > SAIL_INT_MIN);
     assert(SAIL_INT_MAX > 0);
     assert(SAIL_INT_MIN < 0);
     assert(SAIL_INT_MIN - SAIL_INT_MIN == 0);
     assert(SAIL_INT_MAX - SAIL_INT_MAX == 0);
     assert((uint64_t) (SAIL_INT_MAX >> 64) == 0x7FFFFFFFFFFFFFFF);
     assert((uint64_t) (SAIL_INT_MAX >> 127) == 0);
     assert((uint64_t) (SAIL_INT_MAX >> 126) == 1);
     assert((unsigned __int128) SAIL_INT_MAX + 1 == (unsigned __int128) SAIL_INT_MIN);
     assert((__int128) ((unsigned __int128) SAIL_INT_MAX + 1) == SAIL_INT_MIN);
     assert((__int128) ((unsigned __int128) SAIL_INT_MAX + 1) < 0);
     assert((uint64_t) SAIL_INT_MAX == 0xFFFFFFFFFFFFFFFF);

     /* Expect precision failures */
     assert(CREATE_OF(mach_int, sail_int)(SAIL_INT_MAX) == -1);
     assert(CREATE_OF(mach_int, sail_int)(SAIL_INT_MIN) == -1);

     /* Expect warnings for overflow/underflow */
     assert(add_int(SAIL_INT_MAX, SAIL_INT_MAX) == -1); //overflow
     assert(add_int(SAIL_INT_MAX, 1) == -1); //overflow
     assert(add_int(SAIL_INT_MAX, 0) == SAIL_INT_MAX);
     assert(add_int(SAIL_INT_MIN, SAIL_INT_MIN) == -1); //underflow
     assert(add_int(SAIL_INT_MIN, -1) == -1); //underflow
     assert(add_int(SAIL_INT_MIN, 0) == SAIL_INT_MIN);
#endif

     return 0;
}
