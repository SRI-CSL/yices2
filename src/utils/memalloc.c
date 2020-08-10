/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */

/*
 * WRAPPERS FOR MALLOC/REALLOC/FREE
 */

#include <stdio.h>
#include <string.h>
#include <assert.h>

#include "utils/memalloc.h"

#include "yices_exit_codes.h"


/*
 * Callback function: give a chance to do something when
 * we run out of memory.
 */
out_of_mem_callback_t __out_of_mem_callback = NULL;


/*
 * Fatal error: out of memory
 */
void out_of_memory(void) {
  if (__out_of_mem_callback != NULL) {
    __out_of_mem_callback();
  } else {
    fprintf(stderr, "Out of memory\n");
  }
  exit(YICES_EXIT_OUT_OF_MEMORY);
}


/*
 * Local malloc: abort if out of memory.
 *
 * Special case: is size = 0, malloc(size) may
 * return NULL on some systems, but that does not
 * mean we're out of memory.
 */
void *safe_malloc(size_t size) {
  void *tmp;

  tmp = malloc(size);
  if (tmp == NULL && size > 0) {
    out_of_memory();
  }

  return tmp;
}

/*
 * Safer realloc to support lazy allocation.
 * If ptr == NULL, call malloc otherwise call realloc.
 * Abort if out of memory.
 *
 * NOTE: C99 specifies that realloc should behave like
 * malloc if ptr is NULL. This is what the Linux default
 * malloc does, but it's not clear whether other malloc
 * implementations (e.g., on MacOSX) follow the standard.
 * It's safer to check whether ptr is NULL and
 * call malloc or realloc accordingly.
 *
 * size must be positive: realloc(p, 0) is the same as free(ptr).
 */
void *safe_realloc(void *ptr, size_t size) {
  void *tmp;

  assert(size > 0);

  if (ptr == NULL) {
    tmp = malloc(size);
  } else {
    tmp = realloc(ptr, size);
  }
  if (tmp == NULL) out_of_memory();

  return tmp;
}


/*
 * Wrapper for strdup
 */
char *safe_strdup(const char *s) {
  char *tmp;

  tmp = strdup(s);
  if (tmp == NULL) {
    out_of_memory();
  }
  return tmp;
}
