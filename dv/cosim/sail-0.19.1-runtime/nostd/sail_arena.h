#ifndef __SAIL_ARENA__
#define __SAIL_ARENA__

#include <stddef.h>

void sail_arena_init(void *buffer, size_t length);

void sail_arena_reset(void);

#endif
