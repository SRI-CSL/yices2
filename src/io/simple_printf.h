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
 * Crude replacements for printf and fprintf that can be used in
 * signal handlers.  These functions are limited but should be
 * sufficient for printing things like statistics and strings. They
 * are safe to use in signal handlers because they don't use malloc or
 * libc functions such as fprintf.
 *
 * Main limitations:
 * - all functions here rely on a fixed-size buffer (150 characters).
 */

#ifndef __SIMPLE_PRINTF_H
#define __SIMPLE_PRINTF_H

#include <stdint.h>
#include <stdbool.h>

#define PRINT_BUFFER_SIZE 150
#define AUX_PRINT_BUFFER_SIZE 32

/*
 * Buffer: to construct strings to print
 * - data[0 ... idx-1] = string so far,
 * - aux = auxiliary buffer to convert numbers to strings
 * - errcode = error code if write fails
 */
typedef struct print_buffer_s {
  int32_t errcode;
  uint32_t idx;  
  char aux[AUX_PRINT_BUFFER_SIZE];
  char data[PRINT_BUFFER_SIZE];
} print_buffer_t;

/*
 * Initialize/reset the buffer
 */
static inline void reset_print_buffer(print_buffer_t *b) {
  b->idx = 0;
}


/*
 * Append data to the buffer.
 * - if this would cause overflow, the data is truncated.
 */
extern void print_buffer_append_char(print_buffer_t *b, char c);
extern void print_buffer_append_string(print_buffer_t *b, const char *s);
extern void print_buffer_append_int32(print_buffer_t *b, int32_t x);
extern void print_buffer_append_uint32(print_buffer_t *b, uint32_t x);
extern void print_buffer_append_int64(print_buffer_t *b, int64_t x);
extern void print_buffer_append_uint64(print_buffer_t *b, uint64_t x);

/*
 * Append a[0 ... n-1]
 */
extern void print_buffer_append_array(print_buffer_t *b, char a[], uint32_t n);

/*
 * Convert x to a string of the form '<integral part>.<fractional part>"
 * - d = number of digits in the fractional part.
 * - if d is 0, there's no '.' and no fractional is printed.
 *
 * Constraints: d must be between 0 and 4.
 */
extern void print_buffer_append_float(print_buffer_t *b, double x, uint32_t d);

/*
 * Write the current string to a file
 * - f = file descriptor to use.
 *   f must be open and writable.
 * - this function attempts to write b->data[0 ... idx-1] to f
 * - b->idx is reset to 0 (even if the write fails)
 *
 * - return true if the write succeeds, false otherwise
 * - if the write fails, copy errno into b->errcode
 * - otherwise, set b->errcode to 0
 */
extern bool write_buffer(int f, print_buffer_t *b);


#endif /* __SIMPLE_PRINTF_H */
