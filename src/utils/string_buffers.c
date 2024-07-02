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
 * Resizable string buffers
 */

#include <stdio.h>
#include <string.h>
#include <inttypes.h>
#include <assert.h>

#include "utils/memalloc.h"
#include "utils/string_buffers.h"


/*
 * Initialize: n = initial size
 */
void init_string_buffer(string_buffer_t *s, uint32_t n) {
  s->size = n;
  s->index = 0;
  s->data = NULL;
  if (n > 0) {
    s->data = (char *) safe_malloc(n);
  }
}


/*
 * Expand: make room for at least n extra characters after index.
 */
static void string_buffer_extend(string_buffer_t *s, uint32_t n) {
  uint32_t p;

  n += s->index;
  if (n < s->index) {
    // integer overflow: can't make s large enough
    out_of_memory();
  }

  // try 50% larger. If that's still too small, take n as the new size
  p = s->size;
  if (p < n) {
    p ++;
    p += p>>1;
    if (p < n) p = n;

    s->data = (char *) safe_realloc(s->data, p);
    s->size = p;
  }
}


/*
 * Faster version: make room for one character
 */
static void string_buffer_extend1(string_buffer_t *s) {
  uint32_t p;

  if (s->index == s->size) {
    if (s->size == UINT32_MAX) {
      out_of_memory();
    }
    p = s->size + 1;
    p += p>>1;

    s->data = (char *) safe_realloc(s->data, p);
    s->size = p;
  }
}


/*
 * Delete: free data array
 */
void delete_string_buffer(string_buffer_t *s) {
  safe_free(s->data);
  s->data = NULL;
  s->size = 0;
  s->index = 0;
}


/*
 * Close: append '\0', do not increment the index
 */
void string_buffer_close(string_buffer_t *s) {
  string_buffer_extend1(s);
  s->data[s->index] = '\0';
}


/*
 * Append operations
 */
void string_buffer_append_char(string_buffer_t *s, char c) {
  string_buffer_extend1(s);
  s->data[s->index] = c;
  s->index ++;
}

// s1 must be null-terminated, the '\0' is not copied in s
void string_buffer_append_string(string_buffer_t *s, const char *s1) {
  size_t n;

  n = strlen(s1);
  if (n > UINT32_MAX) {
    out_of_memory();
  }
  string_buffer_extend(s, (uint32_t) n);
  memcpy(s->data + s->index, s1, n);
  s->index += n;
}

void string_buffer_append_buffer(string_buffer_t *s, string_buffer_t *s1) {
  uint32_t n;

  n = string_buffer_length(s1);
  string_buffer_extend(s, n);
  memcpy(s->data + s->index, s1->data, n);
  s->index += n;
}


void string_buffer_append_int32(string_buffer_t *s, int32_t x) {
  int32_t n;
  // max space to print a 32bit number in decimal is
  // 12 character (including sign and trailing zero)
  string_buffer_extend(s, 12);
  n = sprintf(s->data + s->index, "%"PRId32, x);
  assert(n <= 12 && n > 0);
  s->index += n;
}

void string_buffer_append_uint32(string_buffer_t *s, uint32_t x) {
  int32_t n;
  // max space to print a 32bit number in decimal is
  // 12 character (including sign and trailing zero)
  string_buffer_extend(s, 12);
  n = sprintf(s->data + s->index, "%"PRIu32, x);
  assert(n <= 12 && n > 0);
  s->index += n;
}

void string_buffer_append_double(string_buffer_t *s, double x) {
  int32_t n, size;

  size = 0;
  do {
    size += 100;
    string_buffer_extend(s, size);
    n = snprintf(s->data + s->index, size, "%f", x);
    assert(n > 0);
  } while (n >= s->size);

  s->index += n;
}

void string_buffer_append_mpz(string_buffer_t *s, mpz_t z) {
  size_t n;
  char *s0;

  // sizeinbase may overestimate the actual length by one
  n = mpz_sizeinbase(z, 10);
  if (n > UINT32_MAX - 2) {
    out_of_memory();
  }
  string_buffer_extend(s, (uint32_t) (n + 2));
  s0 = s->data + s->index;
  mpz_get_str(s0, 10, z);
  // we can't use n here
  s->index += strlen(s0);
}

void string_buffer_append_mpq(string_buffer_t *s, mpq_t q) {
  size_t n1, n;
  char *s0;

  n1 = mpz_sizeinbase(mpq_numref(q), 10);
  n = n1 + mpz_sizeinbase(mpq_denref(q), 10);
  if (n > UINT32_MAX - 3 || n < n1) {
    // too large or numerical overflow
    out_of_memory();
  }
  string_buffer_extend(s, (uint32_t) (n + 3));
  s0 = s->data + s->index;
  mpq_get_str(s0, 10, q);
  s->index += strlen(s0);
}

void string_buffer_append_rational(string_buffer_t *s, const rational_t *r) {
  if (is_ratgmp(r)) {
    string_buffer_append_mpq(s, get_gmp(r));
  } else {
    string_buffer_append_int32(s, get_num(r));
    if (get_den(r) != 1) {
      string_buffer_append_char(s, '/');
      string_buffer_append_uint32(s, get_den(r));
    }
  }
}

void string_buffer_append_bvconst(string_buffer_t *s, uint32_t *bv, uint32_t n) {
  char *s0;

  assert(n>0);
  string_buffer_extend(s, n);
  s0 = s->data + s->index;
  s->index += n;

  do {
    n --;
    *s0 ++ = bvconst_tst_bit(bv, n) ? '1' : '0';
  } while (n>0);
}


/*
 * Print the full buffer
 */
void string_buffer_print(FILE *f, string_buffer_t *s) {
  string_buffer_close(s);
  fputs(s->data, f);
}


/*
 * Export:
 * - close the string (add '\0') then return it
 * - store the string's size in *len
 * - then reset the buffer.
 */
char *string_buffer_export(string_buffer_t *s, uint32_t *len) {
  char *tmp;

  string_buffer_close(s);
  tmp = s->data;
  *len = s->index;

  // reset to an empty buffer
  s->size = 0;
  s->index = 0;
  s->data = NULL;

  return tmp;
}

