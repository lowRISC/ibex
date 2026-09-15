#ifndef __SAIL_ALLOC__
#define __SAIL_ALLOC__

#include <stddef.h>

void *sail_malloc(size_t size);

void *sail_realloc(void *ptr, size_t new_size);

void sail_free(void *ptr);

#endif
