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

#include <assert.h>
#include <errno.h>
#include <math.h>
#include <string.h>
#include <unistd.h>

#include "io/simple_printf.h"

/*
 * Reverse b[0 ... n-1]
 */
static void reverse(char *b, uint32_t n) {
  uint32_t i, j;
  char c;

  assert(n > 0);

  i = 0;
  j = n-1;
  while (i < j) {
    c =  b[i]; b[i] = b[j]; b[j] = c;
    i ++;
    j --;
  }
}

/*
 * Store digits of x in b, then return the number of digits.
 * - b must be large enough to store all the digits
 *   (2^64 - 1 has 20 digits).
 */
static uint32_t digits_of_uint(char *b, uint64_t x) {
  uint32_t n, d;

  n = 0;
  do {
    d = x % 10;
    x = x/10;
    b[n] = (char) (d + '0');
    n ++;
  } while (x > 0);

  reverse(b, n);

  return n;
}

/*
 * Store nd digits for x in b.
 * - padd with '0' on the left if needed
 * - x must be less than 10^d for this to make sense
 */
static void digits_of_frac(char *b, uint64_t x, uint32_t nd) {
  uint32_t i, d;

  for (i=0; i<nd; i++) {
    d = x % 10;
    x = x/10;
    b[i] = (char) (d + '0');
  }
  reverse(b, nd);
}

static const double scale[5] = { 1.0, 10.0, 100.0, 1000.0, 10000.0 };

/* 
 * for a floating point x, d = number of digits after the '.'
 * d must be between 0 and 4, x must be non-negative.
 */
static uint32_t digits_of_float(char *b, double x, uint32_t d) {
  double f;
  uint64_t p;
  uint32_t n;

  assert(0 <= d && d <= 4);

  p = (uint64_t) x;       // integral part
  f = (x - p) * scale[d]; // fractional part * 10^d

  if (d == 0) {
    if (f > 0.5) p ++;
    n = digits_of_uint(b, p);
  } else {
    n = digits_of_uint(b, p);
    b[n] = '.';
    n ++;
    p = (uint64_t) f;
    if (f - p > 0.5) p ++;
    digits_of_frac(b + n, p, d);
    n += d;
  }

  return n;
}


/*
 * Append data to the buffer.
 * - if this would cause overflow, the data is truncated.
 */
void print_buffer_append_char(print_buffer_t *b, char c) {
  uint32_t i;

  i = b->idx;
  if (i < PRINT_BUFFER_SIZE) {
    b->data[i] = c;
    b->idx = i +1;
  }
}

// this assumes s is a small string.
void print_buffer_append_string(print_buffer_t *b, const char *s) {
  uint32_t i, n, max;

  assert(b->idx <= PRINT_BUFFER_SIZE);

  i = b->idx;
  max = PRINT_BUFFER_SIZE - i;

  n = strlen(s);
  if (n > max) n = max; // truncate
  memcpy(b->data + i, s, n);
  b->idx = i + n;
}

// append a[0 ... n-1]
void print_buffer_append_array(print_buffer_t *b, char a[], uint32_t n) {
  uint32_t i, j, max;

  assert(b->idx <= PRINT_BUFFER_SIZE);

  i = b->idx;
  max = PRINT_BUFFER_SIZE - i;
  if (n > max) n = max;
  for (j=0; j<n; j++) {
    b->data[i + j] = a[j];
  }
  b->idx = i + n;
}

// append c n times
static void print_buffer_append_chars(print_buffer_t *b, char c, uint32_t n) {
  uint32_t i, j, max;

  assert(b->idx <= PRINT_BUFFER_SIZE);

  i = b->idx;
  max = PRINT_BUFFER_SIZE - i;
  if (n > max) n = max;
  for (j=0; j<n; j++) {
    b->data[i + j] = c;
  }
  b->idx = i + n;
}


void print_buffer_append_uint64(print_buffer_t *b, uint64_t x) {
  uint32_t n;

  n = digits_of_uint(b->aux, x);
  print_buffer_append_array(b, b->aux, n);
}

void print_buffer_append_int64(print_buffer_t *b, int64_t x) {
  uint64_t y;

  if (x < 0) {
    print_buffer_append_char(b, '-');
    y = -x; // this works even for x=INT64_MIN
  } else {
    y = x;
  }
  print_buffer_append_uint64(b, y);
}

void print_buffer_append_uint32(print_buffer_t *b, uint32_t x) {
  print_buffer_append_uint64(b, x);
}

void print_buffer_append_int32(print_buffer_t *b, int32_t x) {
  print_buffer_append_int64(b, x);
}


/*
 * Convert x to a string of the form '<integral part>.<fractional part>"
 * - d = number of digits in the fractional part.
 * - if d is 0, there's no '.' and no fractional is printed.
 *
 * Constraints: d must be between 0 and 4.
 */
void print_buffer_append_float(print_buffer_t *b, double x, uint32_t d) {
  uint32_t n;

  switch (fpclassify(x)) {
  case FP_ZERO:
  case FP_SUBNORMAL:
    // ignore the sign and treat subnormals like 0.0
    print_buffer_append_char(b, '0');
    if (d > 0) {
      print_buffer_append_char(b, '.');
      print_buffer_append_chars(b, '0', d);
    }
    break;

  case FP_NORMAL:
    if (signbit(x)) {
      print_buffer_append_char(b, '-');
      x = - x;
    }
    if (x > 1e19) {
      // too big
      print_buffer_append_array(b, ">1e19", 5);
    } else {
      n = digits_of_float(b->aux, x, d);
      print_buffer_append_array(b, b->aux, n);
    }
    break;

  case FP_INFINITE:
    if (signbit(x)) {
      print_buffer_append_array(b, "-inf", 4);
    } else {
      print_buffer_append_array(b, "+inf", 4);
    }
    break;

  case FP_NAN:
    print_buffer_append_array(b, "nan", 3);
    break;
  }
}


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
bool write_buffer(int fd, print_buffer_t *b) {
  uint32_t i, n;
  ssize_t w;

  assert(b->idx <= PRINT_BUFFER_SIZE);

  i = 0;
  n = b->idx;
  b->errcode = 0;
  b->idx = 0;

  while (n > 0) {
    do {
      w = write(fd, b->data + i, n);
    } while (w < 0 && errno == EAGAIN);

    if (w < 0) {
      b->errcode = errno;
      return false;
    }
    i += (uint32_t) w;
    n -= (uint32_t) w;
  }

  return true;
}

