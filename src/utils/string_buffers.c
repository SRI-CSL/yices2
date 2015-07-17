/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
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
static inline void string_buffer_extend1(string_buffer_t *s) {
  uint32_t p;

  if (s->index == s->size) {
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
  //  string_buffer_extend(s, 1);
  string_buffer_extend1(s);
  s->data[s->index] = '\0';
}


/*
 * Append operations
 */
void string_buffer_append_char(string_buffer_t *s, char c) {
  //  string_buffer_extend(s, 1);
  string_buffer_extend1(s);
  s->data[s->index] = c;
  s->index ++;
}

// s1 must be null-terminated, the '\0' is not copied in s
void string_buffer_append_string(string_buffer_t *s, const char *s1) {
  uint32_t n;

  n = strlen(s1);
  string_buffer_extend(s, n);
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
  uint32_t n;
  char *s0;

  // sizeinbase may overestimate the actual length by one
  n = mpz_sizeinbase(z, 10) + 2;
  string_buffer_extend(s, n);
  s0 = s->data + s->index;
  mpz_get_str(s0, 10, z);
  // we can't use n here
  s->index += strlen(s0);
}

void string_buffer_append_mpq(string_buffer_t *s, mpq_t q) {
  uint32_t n;
  char *s0;

  // n may be an overestimate
  n = mpz_sizeinbase(mpq_numref(q), 10) + mpz_sizeinbase(mpq_denref(q), 10) + 3;
  string_buffer_extend(s, n);
  s0 = s->data + s->index;
  mpq_get_str(s0, 10, q);
  s->index += strlen(s0);
}

void string_buffer_append_rational(string_buffer_t *s, rational_t *r) {
  if (r->den == 0) {
    string_buffer_append_mpq(s, get_mpq(r->num));
  } else {
    string_buffer_append_int32(s, r->num);
    if (r->den != 1) {
      string_buffer_append_char(s, '/');
      string_buffer_append_uint32(s, r->den);
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

