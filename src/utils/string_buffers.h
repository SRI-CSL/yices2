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
 * RESIZABLE STRING BUFFERS
 */

#ifndef __STRING_BUFFER_H
#define __STRING_BUFFER_H

#include <stdint.h>
#include <stdio.h>
#include <gmp.h>

#include "terms/bv_constants.h"
#include "terms/rationals.h"

/*
 * A character array data of the given size
 * strings are constructed by appending characters,
 * starting at the given index.
 */
typedef struct string_buffer_s {
  uint32_t index;
  uint32_t size;
  char *data;
} string_buffer_t;


/*
 * Initialize a buffer, n = initial size of the data array
 */
extern void init_string_buffer(string_buffer_t *s, uint32_t n);

/*
 * Delete a buffer s: free the memory
 */
extern void delete_string_buffer(string_buffer_t *s);


/*
 * Reset: empty the content
 */
static inline void string_buffer_reset(string_buffer_t *s) {
  s->index = 0;
}

/*
 * Get the length of the buffer (i.e., index value)
 */
static inline uint32_t string_buffer_length(string_buffer_t *s) {
  return s->index;
}

/*
 * Close: append '\0', do not increment the index
 */
extern void string_buffer_close(string_buffer_t *s);

/*
 * Append operations
 */
extern void string_buffer_append_char(string_buffer_t *s, char c);
extern void string_buffer_append_string(string_buffer_t *s, const char *s1);
extern void string_buffer_append_buffer(string_buffer_t *s, string_buffer_t *s1);
extern void string_buffer_append_int32(string_buffer_t *s, int32_t x);
extern void string_buffer_append_uint32(string_buffer_t *s, uint32_t x);
extern void string_buffer_append_double(string_buffer_t *s, double x);
extern void string_buffer_append_mpz(string_buffer_t *s, mpz_t z);
extern void string_buffer_append_mpq(string_buffer_t *s, mpq_t q);
extern void string_buffer_append_rational(string_buffer_t *s, const rational_t *q);

/*
 * bv = bitvector, n = size in bits
 * this stores a sequence of n binary digits ('0' or '1')
 * without any prefix
 */
extern void string_buffer_append_bvconst(string_buffer_t *s, uint32_t *bv, uint32_t n);



/*
 * Print the full buffer on stream f
 */
extern void string_buffer_print(FILE *f, string_buffer_t *s);


/*
 * Export:
 * - close the string (add '\0') then return it.
 * - store the string's size in *len.
 * - reset the buffer.
 *
 * The returned string must be deleted when no-longer needed using
 * free (or safe_free in utils/memalloc).
 */
extern char *string_buffer_export(string_buffer_t *s, uint32_t *len);


#endif /* __STRING_BUFFER_H */
