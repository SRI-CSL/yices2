/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * UTILITIES TO PARSE STRINGS
 */

#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <errno.h>
#include <assert.h>

#include "utils/string_utils.h"


/*
 * Binary search in a sorted array of strings.
 * - a must be sorted in lexicographic order (i.e.,
 *   strcmp(a[i], a[i+1]) must be non-negative).
 * - n = size of the array. n must be > 0
 * - s = string to search for
 *
 * Return the index i such that a[i] = s if s is in the array.
 * Return -1 otherwise.
 */
int32_t binary_search_string(const char *s, const char * const *a, int32_t n) {
  uint32_t l, h, k;
  int cmp;

  assert(n > 0);

  l = 0;
  h = (uint32_t) n;
  for (;;) {
    k = (l + h)/2;
    assert(l <= k && k < h);
    cmp = strcmp(s, a[k]);
    if (cmp == 0) return k;
    if (k == l) return -1;
    if (cmp < 0) {
      h = k;
    } else {
      assert(cmp > 0);
      l = k;
    }
  }
}


/*
 * Parse s as a keyword:
 * - a must be an array of strings sorted in lexicographic order
 * - b must be an array of integer codes of same size as a
 * - n = size of a and b (n must be positive)
 * - s = string to search for
 * If s is equal to a[i] for some i in 0 .. n-1, then
 * the function returns b[i].
 *
 * Otherwise, return -1.
 */
int32_t parse_as_keyword(const char *s, const char * const *a, const int32_t *b, int32_t n) {
  int32_t i;

  i = binary_search_string(s, a, n);
  if (i >= 0) {
    i = b[i];
  }

  return i;
}


/*
 * Parse s as a boolean: "true" or "TRUE" or "false" or "FALSE"
 * - store the result in *val
 * Return code:
 * - valid_boolean means correct
 * - invalid_boolean means wrong format
 */
boolean_parse_code_t parse_as_boolean(const char *s, bool *val) {
  boolean_parse_code_t r;

  r = invalid_boolean;
  if ((strcmp(s, "true") == 0) || (strcmp(s, "TRUE") == 0)) {
    *val = true;
    r = valid_boolean;
  } else if ((strcmp(s, "false") == 0) || (strcmp(s, "FALSE") == 0)) {
    *val = false;
    r = valid_boolean;
  }

  return r;
}



/*
 * Parse s as a decimal number in the format
 *  <optional_signs><digits>
 * and store the corresponding number into val
 *
 * Return code:
 * - valid_integer means correct format, no overflow
 * - integer_overflow means correct format but overflow
 * - invalid_integer means wrong format
 */
integer_parse_code_t parse_as_integer(const char *s, int32_t *val) {
  long aux;
  char *b;

  while (isspace((int) *s)) s ++;
  errno = 0;
  aux = strtol(s, &b, 10);
  if (errno == ERANGE) {
    return integer_overflow;  //overflow or underflow
  }
  if (errno == EINVAL) {
    return invalid_integer;
  }

  if (aux > (long) INT32_MAX || aux < (long) INT32_MIN) {
    return integer_overflow;
  }

  while (isspace((int) *b)) b++;

  if (*b == '\0' && b != s) {
    *val = (int32_t) aux;
    return valid_integer;
  }

  return invalid_integer;
}


/*
 * Variant: parse s as an unsigned integer
 */
integer_parse_code_t parse_as_uint(const char *s, uint32_t *val) {
  unsigned long aux;
  char *b;

  while (isspace((int) *s)) s ++;
  errno = 0;
  aux = strtoul(s, &b, 0);
  if (errno == ERANGE) {
    return integer_overflow;
  }
  if (errno == EINVAL) {
    return invalid_integer;
  }

  if (aux > (unsigned long) UINT32_MAX) {
    return integer_overflow;
  }

  while (isspace((int) *b)) b++;

  if (*b == '\0' && b != s) {
    *val = (uint32_t) aux;
    return valid_integer;
  }

  return invalid_integer;
}


/*
 * Parse s as a floating point number in the format recognized by
 * strtod, and store the corresponding number into val
 *
 * Return code:
 * - valid_double means correct format, no overflow
 * - double_overflow means correct format but overflow
 * - invalid_double means wrong format
 */
double_parse_code_t parse_as_double(const char *s, double *val) {
  double aux;
  char *b;

  while (isspace((int) *s)) s ++;
  errno = 0;
  aux = strtod(s, &b);
  if (errno == ERANGE) {
    return double_overflow;  //overflow or underflow
  }

  while (isspace((int) *b)) b++;

  if (*b == '\0' && b != s) {
    *val = aux;
    return valid_double;
  }

  return invalid_double;
}

