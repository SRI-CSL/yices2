/*
 * TEST INTERVAL CONSTRUCTIONS
 */

#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>
#include <assert.h>

#include "bv64_constants.h"
#include "bv64_intervals.h"



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
	  k = norm64(i + j, 6); // i+j mod 2^6      
	  sum = set_bit64(sum, k);
	}
      }
    }
  }

  return sum;
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
 * Tests on bitvectors of size 6 on intervals [x, y] and [s, t]
 */
static void test6u(uint32_t x, uint32_t y, uint32_t s, uint32_t t) {
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

static void test6s(uint32_t x, uint32_t y, uint32_t s, uint32_t t) {
  bv64_interval_t a;
  bv64_interval_t b;

  assert(0 <= x && x < 64 && 0 <= y && y < 64);
  assert(0 <= s && s < 64 && 0 <= t && t < 64);
  assert(x <= y || (x >= 32 && y <= 31));
  assert(s <= t || (s >= 32 && t <= 31));

  a.low = x;
  a.high = y;
  a.nbits = 6;

  b.low = s;
  b.high = t;
  b.nbits = 6;

  test_sum6_signed(&a, &b);
}

static void tests6(void) {
  test6u(0, 0, 0, 0);
  test6s(0, 0, 0, 0);
  test6u(1, 1, 0, 0);
  test6s(1, 1, 0, 0);
  test6u(0, 0, 1, 1);
  test6s(0, 0, 1, 1);
  test6u(31, 31, 0, 0);
  test6s(31, 31, 0, 0);
  test6u(32, 32, 0, 0);
  test6s(32, 32, 0, 0);
  test6u(63, 63, 0, 0);
  test6s(63, 63, 0, 0);
  test6u(63, 63, 1, 1);
  test6s(63, 63, 1, 1);
  test6u(63, 63, 31, 31);
  test6s(63, 63, 31, 31);
  
  test6u(0, 31, 0, 31);
  test6s(0, 31, 0, 31);

  test6u(0, 63, 0, 5);
  test6s(63, 0, 0, 5);  
  
}


int main(void) {
  tests6();

  return 0;
}
