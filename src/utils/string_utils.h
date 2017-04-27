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
 * UTILITIES TO PARSE STRINGS
 */

#ifndef __STRING_UTILS_H
#define __STRING_UTILS_H

#include <stdbool.h>
#include <stdint.h>


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
extern int32_t binary_search_string(const char *s, const char * const *a, int32_t n);


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
extern int32_t parse_as_keyword(const char *s, const char * const *a, const int32_t *b, int32_t n);


/*
 * Parse s as a boolean: "true" or "TRUE" or "false" or "FALSE"
 * - store the result in *val
 * Return code:
 * - valid_boolean means correct
 * - invalid_boolean means wrong format
 */
typedef enum {
  valid_boolean,
  invalid_boolean,
} boolean_parse_code_t;

extern boolean_parse_code_t parse_as_boolean(const char *s, bool *val);


/*
 * Parse s as a decimal number in the format recognized by strtol
 *  <optional_signs><digits>
 * and store the corresponding number into val
 *
 * Return code:
 * - valid_integer means correct format, no overflow
 * - integer_overflow means correct format but overflow
 * - invalid_integer means wrong format
 */
typedef enum {
  valid_integer,
  integer_overflow,
  invalid_integer,
} integer_parse_code_t;

extern integer_parse_code_t parse_as_integer(const char *s, int32_t *val);


/*
 * Parse s as an unsigned integer
 * - decimal, hexa, octal formats are allowed (as supported by strtoul)
 *
 * Same return codes as the previous function.
 */
extern integer_parse_code_t parse_as_uint(const char *s, uint32_t *val);


/*
 * Parse s as a floating point number in the format recognized by
 * strtod, and store the corresponding number into val
 *
 * Return code:
 * - valid_double means correct format, no overflow
 * - double_overflow means correct format but overflow
 * - invalid_double means wrong format
 */
typedef enum {
  valid_double,
  double_overflow,
  invalid_double,
} double_parse_code_t;

extern double_parse_code_t parse_as_double(const char *s, double *val);



#endif /* __STRING_UTILS_H */
