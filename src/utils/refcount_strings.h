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
 * STRINGS WITH REFERENCE COUNTERS
 */

#ifndef __REFCOUNT_STRINGS
#define __REFCOUNT_STRINGS

#include <stdint.h>
#include <stddef.h>


/*
 * The reference counter is hidden in a header
 */
typedef struct {
  uint32_t ref;  // should be plenty; no check for overflow is implemented.
  char str[0];   // the real size is determined a allocation time.
} string_t;


/*
 * Bound on the string size: for a string of length n
 * we need to allocate (n + 1) + sizeof(string_t) bytes.
 * Just to be safe, we raise an 'out_of_memory' exception
 * if n is more than MAX_REFCOUNT_STRING_SIZE.
 */
#define MAX_REFCOUNT_STRING_SIZE (UINT32_MAX - sizeof(string_t) - 1)


/*
 * Make a copy of str with ref count 0.
 * - str must be terminated by '\0'
 * - may cause 'out_of_memory' error
 */
extern char *clone_string(const char *str);


/*
 * header of string s
 */
static inline string_t *string_header(const char *s) {
  return (string_t *) (s - offsetof(string_t, str));
}

/*
 * Increment ref counter for string s
 */
static inline void string_incref(char *s) {
  string_header(s)->ref ++;
}

/*
 * Decrement ref counter for s and free the string if the
 * counter is zero
 */
extern void string_decref(char *s);

#endif
