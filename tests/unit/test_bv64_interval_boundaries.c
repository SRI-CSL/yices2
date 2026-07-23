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

#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include "terms/bv64_interval_abstraction.h"


static void check_abstraction(const char *name, const bv64_abs_t *actual,
                              uint32_t nbits, int32_t sign,
                              int64_t low, int64_t high) {
  if (actual->nbits != nbits || actual->sign != sign ||
      actual->low != low || actual->high != high) {
    fprintf(stderr,
            "%s: expected [low=%"PRId64", high=%"PRId64
            ", nbits=%"PRIu32", sign=%"PRId32"]\n"
            "     actual [low=%"PRId64", high=%"PRId64
            ", nbits=%"PRIu32", sign=%"PRId32"]\n",
            name, low, high, nbits, sign,
            actual->low, actual->high, actual->nbits, actual->sign);
    exit(EXIT_FAILURE);
  }
}

static void init_point(bv64_abs_t *a, uint64_t value) {
  bv64_abs_constant(a, value, 64);
}

static void check_top(const char *name, const bv64_abs_t *a) {
  check_abstraction(name, a, 64, sign_undef, INT64_MIN, INT64_MAX);
}


static void test_negate_boundaries(void) {
  bv64_abs_t a;

  init_point(&a, UINT64_C(0x8000000000000000));
  bv64_abs_negate(&a);
  check_top("negate(INT64_MIN)", &a);

  init_point(&a, UINT64_C(0x8000000000000001));
  bv64_abs_negate(&a);
  check_abstraction("negate(INT64_MIN + 1)", &a, 64, sign_zero,
                    INT64_MAX, INT64_MAX);

  init_point(&a, (uint64_t) INT64_MAX);
  bv64_abs_negate(&a);
  check_abstraction("negate(INT64_MAX)", &a, 64, sign_one,
                    -INT64_MAX, -INT64_MAX);
}

static void test_add_boundaries(void) {
  bv64_abs_t a, b;

  init_point(&a, (uint64_t) INT64_MAX);
  init_point(&b, UINT64_C(1));
  bv64_abs_add(&a, &b);
  check_top("INT64_MAX + 1", &a);

  init_point(&a, UINT64_C(0x8000000000000000));
  init_point(&b, UINT64_MAX);
  bv64_abs_add(&a, &b);
  check_top("INT64_MIN + -1", &a);

  init_point(&a, (uint64_t) INT64_MAX);
  init_point(&b, UINT64_MAX);
  bv64_abs_add(&a, &b);
  check_abstraction("INT64_MAX + -1", &a, 64, sign_zero,
                    INT64_MAX - 1, INT64_MAX - 1);

  init_point(&a, UINT64_C(0x8000000000000000));
  init_point(&b, UINT64_C(1));
  bv64_abs_add(&a, &b);
  check_abstraction("INT64_MIN + 1", &a, 64, sign_one,
                    INT64_MIN + 1, INT64_MIN + 1);
}

static void test_sub_boundaries(void) {
  bv64_abs_t a, b;

  init_point(&a, (uint64_t) INT64_MAX);
  init_point(&b, UINT64_MAX);
  bv64_abs_sub(&a, &b);
  check_top("INT64_MAX - -1", &a);

  init_point(&a, UINT64_C(0x8000000000000000));
  init_point(&b, UINT64_C(1));
  bv64_abs_sub(&a, &b);
  check_top("INT64_MIN - 1", &a);

  init_point(&a, (uint64_t) INT64_MAX);
  init_point(&b, UINT64_C(1));
  bv64_abs_sub(&a, &b);
  check_abstraction("INT64_MAX - 1", &a, 64, sign_zero,
                    INT64_MAX - 1, INT64_MAX - 1);

  init_point(&a, UINT64_C(0x8000000000000000));
  init_point(&b, UINT64_MAX);
  bv64_abs_sub(&a, &b);
  check_abstraction("INT64_MIN - -1", &a, 64, sign_one,
                    INT64_MIN + 1, INT64_MIN + 1);
}

static void test_mul_boundaries(void) {
  bv64_abs_t a, b;

  init_point(&a, UINT64_C(0x8000000000000000));
  init_point(&b, UINT64_MAX);
  bv64_abs_mul(&a, &b);
  check_top("INT64_MIN * -1", &a);

  init_point(&a, UINT64_C(0x8000000000000000));
  init_point(&b, UINT64_C(1));
  bv64_abs_mul(&a, &b);
  check_abstraction("INT64_MIN * 1", &a, 64, sign_one,
                    INT64_MIN, INT64_MIN);

  init_point(&a, UINT64_C(1));
  init_point(&b, UINT64_C(0x8000000000000000));
  bv64_abs_mul(&a, &b);
  check_abstraction("1 * INT64_MIN", &a, 64, sign_one,
                    INT64_MIN, INT64_MIN);

  init_point(&a, UINT64_MAX);
  init_point(&b, UINT64_C(0x8000000000000000));
  bv64_abs_mul(&a, &b);
  check_top("-1 * INT64_MIN", &a);

  init_point(&a, (uint64_t) INT64_MAX);
  init_point(&b, UINT64_C(2));
  bv64_abs_mul(&a, &b);
  check_top("INT64_MAX * 2", &a);

  init_point(&a, UINT64_C(0xc000000000000000));
  init_point(&b, UINT64_C(2));
  bv64_abs_mul(&a, &b);
  check_abstraction("-2^62 * 2", &a, 64, sign_one,
                    INT64_MIN, INT64_MIN);
}

static void test_mul_const_boundaries(void) {
  bv64_abs_t a;

  init_point(&a, UINT64_C(0x8000000000000000));
  bv64_abs_mul_const(&a, UINT64_MAX, 64);
  check_top("INT64_MIN * constant -1", &a);

  init_point(&a, UINT64_C(0xc000000000000000));
  bv64_abs_mul_const(&a, UINT64_C(2), 64);
  check_abstraction("-2^62 * constant 2", &a, 64, sign_one,
                    INT64_MIN, INT64_MIN);
}

static void test_power_boundaries(void) {
  bv64_abs_t a;

  init_point(&a, UINT64_C(0x8000000000000000));
  bv64_abs_power(&a, 1);
  check_abstraction("INT64_MIN^1", &a, 64, sign_one,
                    INT64_MIN, INT64_MIN);

  init_point(&a, UINT64_C(0x8000000000000000));
  bv64_abs_power(&a, 2);
  check_top("INT64_MIN^2", &a);

  bv64_abs_default(&a, 64);
  bv64_abs_power(&a, 2);
  check_top("[INT64_MIN, INT64_MAX]^2", &a);

  init_point(&a, UINT64_C(0xfffffffffffffffe));
  bv64_abs_power(&a, 2);
  check_abstraction("-2^2", &a, 4, sign_zero, 4, 4);
}


int main(void) {
  test_negate_boundaries();
  test_add_boundaries();
  test_sub_boundaries();
  test_mul_boundaries();
  test_mul_const_boundaries();
  test_power_boundaries();

  return EXIT_SUCCESS;
}
