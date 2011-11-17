/*
 * TEST INTERVAL CONSTRUCTIONS
 */

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <inttypes.h>
#include <assert.h>


#include "bv64_constants.h"
#include "bv64_intervals.h"

#ifdef MINGW
static inline long int random(void) {
  return rand();
}
#endif



/*
 * Print interval (decimal and binary formats)
 */
static void show_interval_unsigned(FILE *f, bv64_interval_t *intv) {
  uint32_t n;

  n = intv->nbits;
  fprintf(f, "[%"PRIu64", %"PRIu64"  %"PRIu32" bits]", intv->low, intv->high, n);
}

static void show_interval_signed(FILE *f, bv64_interval_t *intv) {
  uint32_t n;
  int64_t low, high;

  n = intv->nbits;
  low = signed_int64(intv->low, n);
  high = signed_int64(intv->high, n);
  fprintf(f, "[%"PRId64", %"PRId64"  %"PRIu32" bits]", low, high, n);
}

static void show_interval_binary(FILE *f, bv64_interval_t *intv) {
  uint32_t n;

  n = intv->nbits;
  fputc('[', f);
  bvconst64_print(f, intv->low, n);
  fputs(", ", f);
  bvconst64_print(f, intv->high, n);
  fputc(']', f);
}



/*
 * All tests below use bitvectors of size 6.
 * A set of such bitvectors is encoded as a 64bit unsigned integers.
 */

/*
 * Display all the elements in set s
 */
static void show_bvset_unsigned(FILE *f, uint64_t s) {
  bool first;
  uint32_t i;

  first = true;
  fputc('{', f);

  for (i=0; i<64; i++) {
    if (tst_bit64(s, i)) {
      if (first) {
	fprintf(f, "%"PRIu32, i);
	first = false;
      } else {
	fprintf(f, " %"PRIu32, i);
      }
    }
  }
  fputc('}', f);
}


static void show_bvset_signed(FILE *f, uint64_t s) {
  bool first;
  int32_t i;

  first = true;
  fputc('{', f);

  for (i=32; i<64; i++) {
    if (tst_bit64(s, i)) {
      if (first) {
	fprintf(f, "%"PRId32, (i-64));
	first = false;
      } else {
	fprintf(f, " %"PRId32, (i-64));
      }
    }
  }

  for (i=0; i<32; i++) {
    if (tst_bit64(s, i)) {
      if (first) {
	fprintf(f, "%"PRId32, i);
	first = false;
      } else {
	fprintf(f, " %"PRId32, i);
      }
    }
  }

  fputc('}', f);
}


/*
 * Get the minimum and maximum of s (s must not be empty)
 */
static uint32_t bvset_min_unsigned(uint64_t s) {
  uint32_t i;

  assert(s != 0);

  for (i=0; i<64; i++) {
    if (tst_bit64(s, i)) break;      
  }

  return i;
}

static uint32_t bvset_max_unsigned(uint64_t s) {
  uint32_t i;

  assert(s != 0);

  i = 64;
  while (i > 0) {
    i--;
    if (tst_bit64(s, i)) break;
  }

  return i;
}


static uint32_t bvset_min_signed(uint64_t s) {
  uint32_t i;

  assert(s != 0);

  for (i=32; i<64; i++) {
    if (tst_bit64(s, i)) goto done;
  }

  for (i=0; i<32; i++) {
    if (tst_bit64(s, i)) goto done;
  }

 done:
  return i;
}


static uint32_t bvset_max_signed(uint64_t s) {
  uint32_t i;

  assert(s != 0);

  i = 32;
  while (i > 0) {
    i --;
    if (tst_bit64(s, i)) goto done;
  }

  i = 64;
  while (i > 32) {
    i --;
    if (tst_bit64(s, i)) goto done;
  }

 done:
  return i;
}



/*
 * Compute the sum of s1 and s2 = { x1 + x2 | x1 in s1 and x2 in s2 }
 */
static uint64_t bvset_sum(uint64_t s1, uint64_t s2) {
  uint64_t sum;
  uint32_t i, j, k;

  sum = 0;
  for (i=0; i<64; i++) {
    if (tst_bit64(s1, i)) {
      for (j=0; j<64; j++) {
	if (tst_bit64(s2, j)) {
	  k = (i + j) & 63; // i+j mod 2^6      
	  sum = set_bit64(sum, k);
	}
      }
    }
  }

  return sum;
}


/*
 * Compute the difference of s1 and s2 = { x1 - x2 | x1 in s1 and x2 in s2 }
 */
static uint64_t bvset_diff(uint64_t s1, uint64_t s2) {
  uint64_t diff;
  uint32_t i, j, k;

  diff = 0;
  for (i=0; i<64; i++) {
    if (tst_bit64(s1, i)) {
      for (j=0; j<64; j++) {
	if (tst_bit64(s2, j)) {
	  k = (i - j) & 63; // i+j mod 2^6      
	  diff = set_bit64(diff, k);
	}
      }
    }
  }
  
  return diff;
}


/*
 * Convert intv to a set
 * - intv->nbits must be 6
 */
static uint64_t unsigned_intv_to_bvset(bv64_interval_t *intv) {
  uint64_t s;
  uint32_t i;

  assert(intv->nbits == 6);
  assert(intv->low <= intv->high && intv->low < 64 && intv->high < 64);

  s = 0;
  for (i=intv->low; i<= intv->high; i++) {
    s = set_bit64(s, i);
  }

  return s;
} 

static uint64_t signed_intv_to_bvset(bv64_interval_t *intv) {
  uint64_t s;
  uint32_t i;

  assert(intv->nbits == 6);
  assert(intv->low < 64 && intv->high < 64 && signed64_le(intv->low, intv->high, 6));

  s = 0;
  if (intv->low <= 31 || intv->high >= 32) {
    // low and high have the same sign (as 2s complement 6bits)
    for (i=intv->low; i<= intv->high; i++) {
      s = set_bit64(s, i);
    }
  } else {
    // low is negative, high is not
    assert(intv->low >= 32 && intv->high <= 31);
    for (i=intv->low; i<64; i++) {
      s = set_bit64(s, i);
    }
    for (i=0; i<= intv->high; i++) {
      s = set_bit64(s, i);
    }
  }

  return s;
} 



/*
 * Test sum interval unsigned
 */
static void test_sum6(bv64_interval_t *a, bv64_interval_t *b) {
  uint64_t sa, sb, sc;

  assert(a->nbits == 6 && b->nbits == 6);
  assert(a->low < 64 && a->high < 64 && a->low <= a->high);
  assert(b->low < 64 && b->high < 64 && b->low <= b->high);

  sa = unsigned_intv_to_bvset(a);
  sb = unsigned_intv_to_bvset(b);
  sc = bvset_sum(sa, sb);

  printf("---- Test sum unsigned ---\n");
  printf("a: ");
  show_interval_unsigned(stdout, a);
  printf("\nelements = ");
  show_bvset_unsigned(stdout, sa);
  printf("\n\n");

  printf("b: ");
  show_interval_unsigned(stdout, b);
  printf("\nelements = ");
  show_bvset_unsigned(stdout, sb);
  printf("\n\n");

  printf("sum set: ");
  show_bvset_unsigned(stdout, sc);
  printf("\n");
  printf("min = %"PRIu32", max = %"PRIu32"\n", bvset_min_unsigned(sc), bvset_max_unsigned(sc));

  bv64_interval_add_u(a, b);
  printf("\nsum interval: ");
  show_interval_unsigned(stdout, a);
  printf("\n\n");

  assert(a->low == bvset_min_unsigned(sc) && a->high == bvset_max_unsigned(sc));
}


/*
 * Test of sum intervals signed
 */
static void test_sum6_signed(bv64_interval_t *a, bv64_interval_t *b) {
  uint64_t sa, sb, sc;
  int32_t min, max;

  assert(a->nbits == 6 && b->nbits == 6);
  assert(a->low < 64 && a->high < 64 && signed64_le(a->low, a->high, 6));
  assert(b->low < 64 && b->high < 64 && signed64_le(b->low, b->high, 6));

  sa = signed_intv_to_bvset(a);
  sb = signed_intv_to_bvset(b);
  sc = bvset_sum(sa, sb);

  printf("---- Test sum signed ---\n");
  printf("a: ");
  show_interval_signed(stdout, a);
  printf("\nelements = ");
  show_bvset_signed(stdout, sa);
  printf("\n\n");

  printf("b: ");
  show_interval_signed(stdout, b);
  printf("\nelements = ");
  show_bvset_signed(stdout, sb);
  printf("\n\n");

  printf("sum set: ");
  show_bvset_signed(stdout, sc);
  printf("\n");
  min = bvset_min_signed(sc);
  if (32 <= min) {
    assert(min < 64);
    min = min - 64;
  }
  max = bvset_max_signed(sc);
  if (32 <= max) {
    assert(max < 64);
    max = max - 64;
  }
  printf("min = %"PRId32", max = %"PRId32"\n", min, max);

  bv64_interval_add_s(a, b);
  printf("sum interval: ");
  show_interval_signed(stdout, a);
  printf("\n\n");  

  assert(a->low == bvset_min_signed(sc) && a->high == bvset_max_signed(sc));
}


/*
 * Test diff interval unsigned
 */
static void test_diff6(bv64_interval_t *a, bv64_interval_t *b) {
  uint64_t sa, sb, sc;

  assert(a->nbits == 6 && b->nbits == 6);
  assert(a->low < 64 && a->high < 64 && a->low <= a->high);
  assert(b->low < 64 && b->high < 64 && b->low <= b->high);

  sa = unsigned_intv_to_bvset(a);
  sb = unsigned_intv_to_bvset(b);
  sc = bvset_diff(sa, sb);

  printf("---- Test diff unsigned ---\n");
  printf("a: ");
  show_interval_unsigned(stdout, a);
  printf("\nelements = ");
  show_bvset_unsigned(stdout, sa);
  printf("\n\n");

  printf("b: ");
  show_interval_unsigned(stdout, b);
  printf("\nelements = ");
  show_bvset_unsigned(stdout, sb);
  printf("\n\n");

  printf("sum set: ");
  show_bvset_unsigned(stdout, sc);
  printf("\n");
  printf("min = %"PRIu32", max = %"PRIu32"\n", bvset_min_unsigned(sc), bvset_max_unsigned(sc));

  bv64_interval_sub_u(a, b);
  printf("difference interval: ");
  show_interval_unsigned(stdout, a);
  printf("\n\n");

  assert(a->low == bvset_min_unsigned(sc) && a->high == bvset_max_unsigned(sc));
}


/*
 * Test of diff intervals signed
 */
static void test_diff6_signed(bv64_interval_t *a, bv64_interval_t *b) {
  uint64_t sa, sb, sc;
  int32_t min, max;

  assert(a->nbits == 6 && b->nbits == 6);
  assert(a->low < 64 && a->high < 64 && signed64_le(a->low, a->high, 6));
  assert(b->low < 64 && b->high < 64 && signed64_le(b->low, b->high, 6));

  sa = signed_intv_to_bvset(a);
  sb = signed_intv_to_bvset(b);
  sc = bvset_diff(sa, sb);

  printf("---- Test diff signed ---\n");
  printf("a: ");
  show_interval_signed(stdout, a);
  printf("\nelements = ");
  show_bvset_signed(stdout, sa);
  printf("\n\n");

  printf("b: ");
  show_interval_signed(stdout, b);
  printf("\nelements = ");
  show_bvset_signed(stdout, sb);
  printf("\n\n");

  printf("sum set: ");
  show_bvset_signed(stdout, sc);
  printf("\n");
  min = bvset_min_signed(sc);
  if (32 <= min) {
    assert(min < 64);
    min = min - 64;
  }
  max = bvset_max_signed(sc);
  if (32 <= max) {
    assert(max < 64);
    max = max - 64;
  }
  printf("min = %"PRId32", max = %"PRId32"\n", min, max);

  bv64_interval_sub_s(a, b);
  printf("difference interval: ");
  show_interval_signed(stdout, a);
  printf("\n\n");  

  assert(a->low == bvset_min_signed(sc) && a->high == bvset_max_signed(sc));
}



/*
 * Tests on bitvectors of size 6 on intervals [x, y] and [s, t]
 */
static void sum_test6u(uint32_t x, uint32_t y, uint32_t s, uint32_t t) {
  bv64_interval_t a;
  bv64_interval_t b;

  assert(0 <= x && x <= y && y < 64);
  assert(0 <= s && s <= t && t < 64);

  a.low = x;
  a.high = y;
  a.nbits = 6;

  b.low = s;
  b.high = t;
  b.nbits = 6;

  test_sum6(&a, &b);
}

static void diff_test6u(uint32_t x, uint32_t y, uint32_t s, uint32_t t) {
  bv64_interval_t a;
  bv64_interval_t b;

  assert(0 <= x && x <= y && y < 64);
  assert(0 <= s && s <= t && t < 64);

  a.low = x;
  a.high = y;
  a.nbits = 6;

  b.low = s;
  b.high = t;
  b.nbits = 6;

  test_diff6(&a, &b);
}


// convert 6bit value x to a 32bit signed integer
static int32_t sign_extend_bv6(uint32_t x) {
  assert(0 <= x && x < 64);
  return (x >= 32) ? (x - 64) : x;
}

static void sum_test6s(uint32_t x, uint32_t y, uint32_t s, uint32_t t) {
  bv64_interval_t a;
  bv64_interval_t b;

  assert(0 <= x && x < 64 && 0 <= y && y < 64);
  assert(0 <= s && s < 64 && 0 <= t && t < 64);
  assert(sign_extend_bv6(x) <= sign_extend_bv6(y));
  assert(sign_extend_bv6(s) <= sign_extend_bv6(t));

  a.low = x;
  a.high = y;
  a.nbits = 6;

  b.low = s;
  b.high = t;
  b.nbits = 6;

  test_sum6_signed(&a, &b);
}

static void diff_test6s(uint32_t x, uint32_t y, uint32_t s, uint32_t t) {
  bv64_interval_t a;
  bv64_interval_t b;

  assert(0 <= x && x < 64 && 0 <= y && y < 64);
  assert(0 <= s && s < 64 && 0 <= t && t < 64);
  assert(sign_extend_bv6(x) <= sign_extend_bv6(y));
  assert(sign_extend_bv6(s) <= sign_extend_bv6(t));

  a.low = x;
  a.high = y;
  a.nbits = 6;

  b.low = s;
  b.high = t;
  b.nbits = 6;

  test_diff6_signed(&a, &b);
}


// random test
static void test6u_random(void) {
  uint32_t x, y, s, t, aux;

  x = (uint32_t) (random() & 63);
  y = (uint32_t) (random() & 63);
  if (x > y) {
    // swap
    aux = x; x = y; y = aux;
  }

  s = (uint32_t) (random() & 63);
  t = (uint32_t) (random() & 63);
  if (s > t) {
    // swap
    aux = s; s = t; t = aux;
  }

  sum_test6u(x, y, s, t);
  diff_test6u(x, y, s, t);
}

static void test6s_random(void) {
  uint32_t x, y, s, t, aux;

  x = (uint32_t) (random() & 63);
  y = (uint32_t) (random() & 63);
  if (sign_extend_bv6(x) > sign_extend_bv6(y)) {
    aux = x; x = y; y = aux;
  }

  s = (uint32_t) (random() & 63);
  t = (uint32_t) (random() & 63);
  if (sign_extend_bv6(s) > sign_extend_bv6(t)) {
    aux = s; s = t; t = aux;
  }

  sum_test6s(x, y, s, t);
  diff_test6s(x, y, s, t);
}


static void tests6(void) { 
  uint32_t n;

  sum_test6u(0, 0, 0, 0);
  sum_test6s(0, 0, 0, 0);
  sum_test6u(1, 1, 0, 0);
  sum_test6s(1, 1, 0, 0);
  sum_test6u(0, 0, 1, 1);
  sum_test6s(0, 0, 1, 1);
  sum_test6u(31, 31, 0, 0);
  sum_test6s(31, 31, 0, 0);
  sum_test6u(32, 32, 0, 0);
  sum_test6s(32, 32, 0, 0);
  sum_test6u(63, 63, 0, 0);
  sum_test6s(63, 63, 0, 0);
  sum_test6u(63, 63, 1, 1);
  sum_test6s(63, 63, 1, 1);
  sum_test6u(63, 63, 31, 31);
  sum_test6s(63, 63, 31, 31);
  
  sum_test6u(0, 31, 0, 31);
  sum_test6s(0, 31, 0, 31);

  sum_test6u(0, 63, 0, 5);
  sum_test6s(63, 0, 0, 5);  
  
  sum_test6u(40, 50, 0, 20);
  sum_test6u(0, 20, 40, 50);

  sum_test6s(40, 10, 0, 25);  
  sum_test6s(0, 25, 40, 10);

  sum_test6s(40, 10, 0, 21);
  sum_test6s(0, 21, 40, 10);

  sum_test6s(34, 57, 0, 21);
  sum_test6s(0, 21, 34, 57);

  sum_test6s(34, 57, 30, 31);
  sum_test6s(30, 31, 34, 57);

  sum_test6s(34, 57, 36, 10);
  sum_test6s(36, 10, 34, 57);

  diff_test6u(0, 0, 0, 0);
  diff_test6s(0, 0, 0, 0);
  diff_test6u(1, 1, 0, 0);
  diff_test6s(1, 1, 0, 0);
  diff_test6u(0, 0, 1, 1);
  diff_test6s(0, 0, 1, 1);
  diff_test6u(31, 31, 0, 0);
  diff_test6s(31, 31, 0, 0);
  diff_test6u(32, 32, 0, 0);
  diff_test6s(32, 32, 0, 0);
  diff_test6u(63, 63, 0, 0);
  diff_test6s(63, 63, 0, 0);
  diff_test6u(63, 63, 1, 1);
  diff_test6s(63, 63, 1, 1);
  diff_test6u(63, 63, 31, 31);
  diff_test6s(63, 63, 31, 31);
  
  diff_test6u(0, 31, 0, 31);
  diff_test6s(0, 31, 0, 31);

  diff_test6u(0, 63, 0, 5);
  diff_test6s(63, 0, 0, 5);  
  
  diff_test6u(40, 50, 0, 20);
  diff_test6u(0, 20, 40, 50);

  diff_test6s(40, 10, 0, 25);  
  diff_test6s(0, 25, 40, 10);

  diff_test6s(40, 10, 0, 21);
  diff_test6s(0, 21, 40, 10);

  diff_test6s(34, 57, 0, 21);
  diff_test6s(0, 21, 34, 57);

  diff_test6s(34, 57, 30, 31);
  diff_test6s(30, 31, 34, 57);

  diff_test6s(34, 57, 36, 10);
  diff_test6s(36, 10, 34, 57);

  n = 20000;
  while (n > 0) {
    test6u_random();
    test6s_random();
    n --;
  }
}


/*
 * Random 64bit unsigned integer
 */
static uint64_t random_uint64(void) {
  return (((uint64_t) (random() & 0xFFFFFF)) << 40) | (((uint64_t) (random() & 0xFFFFFF)) << 16) 
    | (uint64_t) (random() & 0xFFFF);
}

/*
 * Random interval: n = bitsize
 */
static void random_unsigned_intv(bv64_interval_t *a, uint32_t n) {
  uint64_t x, y, aux;

  assert(1 <= n && n <= 64);
  x = norm64(random_uint64(), n);
  y = norm64(random_uint64(), n);
  if (x > y) {
    aux = x; x = y; y = aux;
  }

  a->low = x;
  a->high = y;
  a->nbits = n;  
}

static void random_signed_intv(bv64_interval_t *a, uint32_t n) {
  uint64_t x, y, aux;

  assert(1 <= n && n <= 64);
  x = norm64(random_uint64(), n);
  y = norm64(random_uint64(), n);
  if (signed64_gt(x, y, n)) {
    aux = x; x = y; y = aux;
  }

  a->low = x;
  a->high = y;
  a->nbits = n;  
}


/*
 * Tests of sum
 */
static void test_sum(bv64_interval_t *a, bv64_interval_t *b) {
  printf("\n--- Test sum unsigned ---\n");
  printf("a: ");
  show_interval_unsigned(stdout, a);
  printf("\nb: ");
  show_interval_unsigned(stdout, b);
  printf("\n");
  bv64_interval_add_u(a, b);
  printf("sum: ");
  show_interval_unsigned(stdout, a);
  printf("\n\n");
}


static void test_sum_signed(bv64_interval_t *a, bv64_interval_t *b) {
  printf("\n--- Test sum signed ---\n");
  printf("a: ");
  show_interval_signed(stdout, a);
  printf("\nb: ");
  show_interval_signed(stdout, b);
  printf("\n");
  bv64_interval_add_s(a, b);
  printf("sum: ");
  show_interval_signed(stdout, a);
  printf("\n\n");
}


/*
 * Tests of diff
 */
static void test_diff(bv64_interval_t *a, bv64_interval_t *b) {
  printf("\n--- Test diff unsigned ---\n");
  printf("a: ");
  show_interval_unsigned(stdout, a);
  printf("\nb: ");
  show_interval_unsigned(stdout, b);
  printf("\n");
  bv64_interval_add_u(a, b);
  printf("diff: ");
  show_interval_unsigned(stdout, a);
  printf("\n\n");
}


static void test_diff_signed(bv64_interval_t *a, bv64_interval_t *b) {
  printf("\n--- Test diff signed ---\n");
  printf("a: ");
  show_interval_signed(stdout, a);
  printf("\nb: ");
  show_interval_signed(stdout, b);
  printf("\n");
  bv64_interval_add_s(a, b);
  printf("diff: ");
  show_interval_signed(stdout, a);
  printf("\n\n");
}


/*
 * Random tests for bitvectors of size n
 * - nt = number of tests
 */
static void random_tests_unsigned(uint32_t n, uint32_t nt) {
  bv64_interval_t a;
  bv64_interval_t b;
  uint32_t k;

  k = nt;
  while (k > 0) {
    k --;
    random_unsigned_intv(&a, n);
    random_unsigned_intv(&b, n);    
    test_sum(&a, &b);
  }

  k = nt;
  while (k > 0) {
    k --;
    random_unsigned_intv(&a, n);
    random_unsigned_intv(&b, n);    
    test_diff(&a, &b);
  }
}

static void random_tests_signed(uint32_t n, uint32_t nt) {
  bv64_interval_t a;
  bv64_interval_t b;
  uint32_t k;

  k = nt;
  while (k > 0) {
    k --;
    random_signed_intv(&a, n);
    random_signed_intv(&b, n);    
    test_sum_signed(&a, &b);
  }

  k = nt;
  while (k > 0) {
    k --;
    random_signed_intv(&a, n);
    random_signed_intv(&b, n);    
    test_diff_signed(&a, &b);
  }
}



int main(void) {
  tests6();

  random_tests_unsigned(32, 1000);
  random_tests_signed(32, 1000);

  random_tests_unsigned(33, 1000);
  random_tests_signed(33, 1000);

  random_tests_unsigned(63, 1000);
  random_tests_signed(63, 1000);

  random_tests_unsigned(64, 1000);
  random_tests_signed(64, 1000);

  return 0;
}
