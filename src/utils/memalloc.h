/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * WRAPPERS FOR MALLOC/REALLOC/FREE
 *
 * safe_malloc and safe_realloc abort if we run out of memory.
 */

#ifndef __MEMALLOC_H
#define __MEMALLOC_H

#include <stddef.h>
#include <stdlib.h>

/*
 * If INSTRUMENT_OUT_OF_MEMORY is non-zero, the code will print diagnostic
 * when we run out of memory. Otherwise, it just prints "Out of memory".
 */

#define INSTRUMENT_OUT_OF_MEMORY 1

#if INSTRUMENT_OUT_OF_MEMORY

extern void __out_of_memory(const char *file, const char *func, unsigned int line) __attribute__ ((noreturn));

extern void *__safe_malloc(size_t size, const char *file, const char *funct,
			   unsigned int line) __attribute__ ((malloc));

extern void *__safe_realloc(void *ptr, size_t size, const char *file, const char *funct, 
			    unsigned int line) __attribute__ ((malloc));


#define out_of_memory() (__out_of_memory(__FILE__, __func__, __LINE__))
#define safe_malloc(size) (__safe_malloc((size), __FILE__, __func__, __LINE__))
#define safe_realloc(ptr, size) (__safe_realloc((ptr), (size), __FILE__, __func__, __LINE__))

#else

// Non-instrumented versions
extern void out_of_memory(void) __attribute__ ((noreturn));
extern void *safe_malloc(size_t size) __attribute__ ((malloc));
extern void *safe_realloc(void *ptr, size_t size) __attribute__ ((malloc));

#endif

/*
 * Safer free: used to check whether ptr is NULL before calling free.
 *
 * Updated to just call free. The check is redundant on most
 * systems. The C99 standard specifies that free shall have no effect
 * if ptr is NULL.
 *
 */
static inline void safe_free(void *ptr)  {
  //  if (ptr != NULL) free(ptr);
  free(ptr);
}


#endif
