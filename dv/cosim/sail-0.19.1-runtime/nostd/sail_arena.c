#include <stdint.h>

#include <sail_alloc.h>
#include <sail_spinlock.h>
#include <sail_arena.h>

static unsigned char *sail_arena_buffer;
static size_t sail_arena_length;
static size_t sail_arena_offset;
static struct sail_spinlock sail_arena_lock;

void sail_arena_init(void *buffer, size_t length)
{
     sail_arena_buffer = buffer;
     sail_arena_length = length;
     sail_arena_offset = 0;
     sail_spin_init(&sail_arena_lock);
}

void sail_arena_reset(void)
{
     sail_spin_lock(&sail_arena_lock);
     sail_arena_offset = 0;
     sail_spin_unlock(&sail_arena_lock);
}

void *sail_malloc_align(size_t size, uintptr_t align)
{
     sail_spin_lock(&sail_arena_lock);
 
     uintptr_t offset = (uintptr_t)sail_arena_buffer + (uintptr_t)sail_arena_offset;

     uintptr_t modulo = offset & (align - 1);
     if (modulo != 0) {
          offset += align - modulo;
     }
     offset -= (uintptr_t)sail_arena_buffer;

     if (offset + size <= sail_arena_length) {
          void *ptr = &sail_arena_buffer[offset];
          sail_arena_offset = offset + size;

	  sail_spin_unlock(&sail_arena_lock);
          return ptr;
     }

     sail_spin_unlock(&sail_arena_lock);
     return NULL;
}

#ifndef SAIL_ARENA_ALIGNMENT
#define SAIL_ARENA_ALIGNMENT 4
#endif

void *sail_malloc(size_t size)
{
     return sail_malloc_align(size, SAIL_ARENA_ALIGNMENT);
}

void *sail_realloc(void *ptr, size_t new_size)
{
     return sail_malloc_align(new_size, SAIL_ARENA_ALIGNMENT);
}

void sail_free(void *ptr) {}
