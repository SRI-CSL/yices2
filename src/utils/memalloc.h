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

#include <setjmp.h>
#include <stdlib.h>


/*
 * Pointer to a jmp-buffer to catch out-of-memory exceptions.
 * - if this pointer is not NULL then the function out_of_memory
 *   calls longjmp(*out_of_mem, -1)
 * - if this pointer is NULL, then out_of_memory will print an
 *   error message on stderr then call exit(YICES_EXIT_OUT_OF_MEMORY).
 * - it's the responsibility of the callers to setup and clean the
 *   
 */
extern jmp_buf *out_of_mem;

/*
 * Either calls longjmp(out_of_mem, -1) or prints an error message then
 * calls exit(YICES_EXIT_OUT_OF_MEMORY)
 * - this exit code is defined in yices_exit_codes.h
 */
extern void out_of_memory(void) __attribute__ ((noreturn));

/*
 * Wrappers for malloc/realloc.
 */
extern void *safe_malloc(size_t size) __attribute__ ((malloc));
extern void *safe_realloc(void *ptr, size_t size) __attribute__ ((malloc));


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
