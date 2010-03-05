/*
 * Wrappers for malloc/realloc/free:
 * abort if out of memory.
 */

#ifndef __MEMALLOC_H
#define __MEMALLOC_H

#include <stddef.h>
#include <stdlib.h>

/*
 * Print an error message then call exit(YICES_EXIT_OUT_OF_MEMORY)
 */
extern void out_of_memory(void) __attribute__ ((noreturn));

/*
 * Wrappers for malloc/realloc.
 */
extern void *safe_malloc(size_t size) __attribute__ ((malloc)); 
extern void *safe_realloc(void *ptr, size_t size) __attribute__ ((malloc));

/*
 * Safer free: check whether ptr is NULL before calling free.
 *
 * NOTE: C99 specifies that free shall have no effect if ptr
 * is NULL. It's safer to check anyway.
 */
static inline void safe_free(void *ptr) {
  if (ptr != NULL) free(ptr);
}


#endif
