/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#include <assert.h>

#include "utils/csets.h"
#include "utils/int_array_sort.h"
#include "utils/memalloc.h"

#ifdef MINGW
static inline long int random(void) {
  return rand();
}
#endif



/*
 * Simple sets for checking results
 * - data = list of elements
 * - tag = boolean array of dsize elements
 * - card = number of elements
 * - dsize = domain size
 */
typedef struct bset_s {
  uint32_t *data;
  uint8_t *tag;
  uint32_t dsize;
  uint32_t card;
} bset_t;

#define MAX_BSET_DSIZE 2000

// initialize: n = domain size
static void init_bset(bset_t *s, uint32_t n) {
  uint32_t i;

  assert(0 < n && n <= MAX_BSET_DSIZE);

  s->data = (uint32_t *) safe_malloc(n * sizeof(uint32_t));
  s->tag = (uint8_t *) safe_malloc(n * sizeof(uint8_t));
  s->dsize = n;
  s->card = 0;

  // empty set
  for (i=0; i<n; i++) {
    s->tag[i] = 0;
  }
}

static void delete_bset(bset_t *s) {
  safe_free(s->data);
  safe_free(s->tag);
  s->data = NULL;
  s->tag = NULL;
}

static void bset_add_elem(bset_t *s, uint32_t i) {
  uint32_t k;

  assert(i < s->dsize);
  if (s->tag[i] == 0) {
    s->tag[i] = 1;
    k = s->card;
    s->data[k] = i;
    s->card = k+1;
  }
}

static void bset_remove_elem(bset_t *s, uint32_t i) {
  uint32_t j, n;

  assert(i < s->dsize);
  if (s->tag[i] == 1) {
    s->tag[i] = 0;

    n = s->card;
    assert(n > 0);

    j = 0;
    while (s->data[j] != i) j ++;
    j ++;
    while (j < n) {
      s->data[j-1] = s->data[j];
      j ++;
    }
    s->card = n-1;
  }
}

static bool bset_member(bset_t *s, uint32_t i) {
  assert(i < s->dsize);
  return s->tag[i] != 0;
}

static void bset_add_set(bset_t *s, bset_t *s1) {
  uint32_t i, n;

  assert(s->dsize == s1->dsize);
  n = s1->card;
  for (i=0; i<n; i++) {
    bset_add_elem(s, s1->data[i]);
  }
}

static void bset_remove_set(bset_t *s, bset_t *s1) {
  uint32_t i, n;

  assert(s->dsize == s1->dsize);
  n = s1->card;
  for (i=0; i<n; i++) {
    bset_remove_elem(s, s1->data[i]);
  }
}

static void bset_empty(bset_t *s) {
  uint32_t i, n;

  s->card = 0;
  n = s->dsize;
  for (i=0; i<n; i++) {
    s->tag[i] = 0;
  }
}

static void bset_fill(bset_t *s) {
  uint32_t i, n;

  n = s->dsize;
  s->card = n;
  for (i=0; i<n; i++) {
    s->tag[i] = 1;
    s->data[i] = i;
  }
}

static void bset_sort(bset_t *s) {
  int_array_sort((int32_t*) s->data, s->card);
}

/*
 * Initialize with n random elements
 */
static void random_bset(bset_t *s, uint32_t n) {
  uint32_t i, dsize;

  dsize = s->dsize;
  assert(dsize > 0);
  bset_empty(s);
  while (n > 0) {
    i = random() % dsize;
    bset_add_elem(s, i);
    n --;
  }
}


/*
 * Check inclusion and disjointness
 */
static bool bset_subset(bset_t *s1, bset_t *s2) {
  uint32_t i, n;

  assert(s1->dsize == s2->dsize);
  n = s1->card;
  for (i=0; i<n; i++) {
    if (! bset_member(s2, s1->data[i])) {
      return false;
    }
  }
  return true;
}

static bool bset_disjoint(bset_t *s1, bset_t *s2) {
  uint32_t i, n;

  assert(s1->dsize == s2->dsize);
  n = s1->card;
  for (i=0; i<n; i++) {
    if (bset_member(s2, s1->data[i])) {
      return false;
    }
  }
  return true;
}


/*
 * Copy s into c
 */
static void copy_bset(cset_t *c, bset_t * s) {
  assert(s->dsize == c->dsize);
  cset_empty(c);
  cset_add_array(c, s->data, s->card);
}

/*
 * Display elements
 */
static void show_bset(bset_t *s) {
  uint32_t i, n;

  bset_sort(s);
  printf("{");
  n = s->card;
  for (i=0; i<n; i++) {
    printf(" %"PRIu32, s->data[i]);
  }
  printf(" }");
}

static void show_cset(cset_t *c) {
  ivector_t aux;
  uint32_t i, n;

  init_ivector(&aux, 10);
  cset_extract(c, &aux);
  int_array_sort(aux.data, aux.size);
  printf("{");
  n = aux.size;
  for (i=0; i<n; i++) {
    printf(" %"PRIu32, aux.data[i]);
  }
  printf(" }");
  delete_ivector(&aux);
}

/*
 * Check that s and c are equal
 */
static void check_equal_sets(bset_t *s, cset_t *c) {
  ivector_t aux;
  uint32_t i, n;

  n = s->card;
  for (i=0; i<n; i++) {
    if (! cset_member(c, s->data[i])) {
      goto bug;
    }
  }

  init_ivector(&aux, 10);
  cset_extract(c, &aux);
  n = aux.size;
  for (i=0; i<n; i++) {
    if (! bset_member(s, aux.data[i])) {
      goto bug;
    }
  }
  delete_ivector(&aux);
  return;

 bug:
  printf("*** BUG ***\n");
  printf(" bset: ");
  show_bset(s);
  printf("\n");
  printf(" cset: ");
  show_cset(c);
  printf("\n");
  printf("should be equal\b");
  fflush(stdout);
  exit(1);
}


/*
 * Test basic operations
 */
static void test_empty(cset_t *c, bset_t *s) {
  assert(s->dsize == c->dsize);
  printf("Testing cset_empty: ");
  cset_empty(c);
  bset_empty(s);
  check_equal_sets(s, c);
  printf("OK\n");
}

static void test_fill(cset_t *c, bset_t *s) {
  assert(s->dsize == c->dsize);
  printf("Testing cset_fill: ");
  cset_fill(c);
  bset_fill(s);
  check_equal_sets(s, c);
  printf("OK\n");
}

// copy s into: check equality and cardinal
static void test_copy(cset_t *c, bset_t *s) {
  uint32_t n;

  assert(s->dsize == c->dsize);
  printf("Testing cset_add_array: ");
  copy_bset(c, s);
  check_equal_sets(s, c);
  printf("OK\n");

  n = cset_card(c);
  if (n != s->card) {
    printf("*** BUG ****\n");
    printf(" cset_card returned %"PRIu32"\n", n);
    printf(" expected cardinal is %"PRIu32"\n", s->card);
    fflush(stdout);
    exit(1);
  }
}

// test of cset_add_set
static void test_add_set(cset_t *c1, cset_t *c2, bset_t *s1, bset_t *s2) {
  assert(s1->dsize == s2->dsize && s1->dsize == c1->dsize &&
	 s1->dsize == c2->dsize);

  printf("Testing cset_add_set: ");
  copy_bset(c1, s1);
  copy_bset(c2, s2);
  cset_add_set(c1, c2);
  bset_add_set(s1, s2);
  check_equal_sets(s1, c1);
  printf("OK\n");
  printf("   result: ");
  show_cset(c1);
  printf("\n");
}

// test of cset_remove_set
static void test_remove_set(cset_t *c1, cset_t *c2, bset_t *s1, bset_t *s2) {
  assert(s1->dsize == s2->dsize && s1->dsize == c1->dsize &&
	 s1->dsize == c2->dsize);

  printf("Testing cset_remove_set: ");
  copy_bset(c1, s1);
  copy_bset(c2, s2);
  cset_remove_set(c1, c2);
  bset_remove_set(s1, s2);
  check_equal_sets(s1, c1);
  printf("OK\n");
  printf("   result: ");
  show_cset(c1);
  printf("\n");
}


// test of cset_subset
static void test_subset(cset_t *c1, cset_t *c2, bset_t *s1, bset_t *s2) {
  bool subset, check;

  assert(s1->dsize == s2->dsize && s1->dsize == c1->dsize &&
	 s1->dsize == c2->dsize);

  printf("Testing cset_subset(s1, s2): ");
  copy_bset(c1, s1);
  copy_bset(c2, s2);
  subset = cset_subset(c1, c2);
  check = bset_subset(s1, s2);
  if (subset != check) {
    goto bug;
  }
  printf("OK\n");
  printf("  result: ");
  if (subset) {
    printf("true\n");
  } else {
    printf("false\n");
  }

  printf("Testing cset_subset(s2, s1): ");
  subset = cset_subset(c2, c1);
  check = bset_subset(s2, s1);
  if (subset != check) {
    goto bug;
  }
  printf("OK\n");
  printf("  result: ");
  if (subset) {
    printf("true\n");
  } else {
    printf("false\n");
  }
  return;

 bug:
  printf("*** BUG ****\n");
  printf(" cset_subset returned %d\n", subset);
  printf(" expected result is %d\n", check);
  fflush(stdout);
  exit(1);
}

// test of cset_disjoint
static void test_disjoint(cset_t *c1, cset_t *c2, bset_t *s1, bset_t *s2) {
  bool disjoint, check;

  assert(s1->dsize == s2->dsize && s1->dsize == c1->dsize &&
	 s1->dsize == c2->dsize);

  printf("Testing cset_disjoint: ");
  copy_bset(c1, s1);
  copy_bset(c2, s2);
  disjoint = cset_disjoint(c1, c2);
  check = bset_disjoint(s1, s2);
  if (disjoint != check) {
    goto bug;
  }

  disjoint = cset_disjoint(c2, c1);
  check = bset_disjoint(s2, s1);
  if (disjoint != check) {
    goto bug;
  }
  printf("OK\n");
  printf("  result: ");
  if (disjoint) {
    printf("true\n");
  } else {
    printf("false\n");
  }
  return;
  return;

 bug:
  printf("*** BUG ****\n");
  printf(" cset_disjoint returned %d\n", disjoint);
  printf(" expected result is %d\n", check);
  fflush(stdout);
  exit(1);
}



/*
 * Run tests: for s1 and s2
 * - call test_remove, test_add, test_copy
 * - s is used to make copies of s1 and s2
 */
static void run_tests(cset_t *c1, cset_t *c2, bset_t *s1, bset_t *s2, bset_t *s) {
  printf("\ns1: ");
  show_bset(s1);
  printf("\ns2: ");
  show_bset(s2);
  printf("\n");

  test_copy(c1, s1);
  test_copy(c2, s2);

  bset_empty(s);
  bset_add_set(s, s1);
  test_add_set(c1, c2, s, s2);

  bset_empty(s);
  bset_add_set(s, s2);
  test_add_set(c1, c2, s, s1);

  bset_empty(s);
  bset_add_set(s, s1);
  test_remove_set(c1, c2, s, s2);

  bset_empty(s);
  bset_add_set(s, s2);
  test_remove_set(c1, c2, s, s1);

  test_subset(c1, c2, s1, s2);
  test_disjoint(c1, c2, s1, s2);
}


static void random_test(cset_t *c1, cset_t *c2, bset_t *s1, bset_t *s2, bset_t *s) {
  random_bset(s1, 6);
  bset_empty(s2);
  run_tests(c1, c2, s1, s2, s);
  run_tests(c1, c2, s2, s1, s);

  random_bset(s1, 6);
  bset_fill(s2);
  run_tests(c1, c2, s1, s2, s);
  run_tests(c1, c2, s2, s1, s);

  random_bset(s1, 6);
  random_bset(s2, 6);
  run_tests(c1, c2, s1, s2, s);

  random_bset(s1, 4);
  random_bset(s2, 3);
  bset_add_set(s1, s2);
  run_tests(c1, c2, s1, s2, s);

  random_bset(s1, 4);
  random_bset(s2, 7);
  bset_remove_set(s2, s1);
  run_tests(c1, c2, s1, s2, s);

  random_bset(s1, 10);
  random_bset(s2, 3);
  run_tests(c1, c2, s1, s2, s);

  random_bset(s1, 12);
  random_bset(s2, 12);
  run_tests(c1, c2, s1, s2, s);
}

/*
 * Run tests for dsize = n
 */
static void do_tests(uint32_t n) {
  cset_t c1, c2;
  bset_t b1, b2, b;
  uint32_t i;

  assert(n > 0);
  printf("\n============================"
	 "\n    DOMAIN SIZE = %"PRIu32
	 "\n============================\n\n", n);

  init_cset(&c1);
  cset_init_empty(&c1, n);
  init_cset(&c2);
  cset_init_empty(&c2, n);
  init_bset(&b1, n);
  init_bset(&b2, n);
  init_bset(&b, n);

  test_empty(&c1, &b1);
  test_empty(&c1, &b1);
  test_fill(&c1, &b1);
  test_fill(&c1, &b1);

  for (i=0; i<20; i++) {
    random_test(&c1, &c2, &b1, &b2, &b);
  }

  delete_bset(&b2);
  delete_bset(&b1);
  delete_bset(&b);
  delete_cset(&c2);
  delete_cset(&c1);
}

int main(void) {
  do_tests(14);
  do_tests(31);
  do_tests(32);
  do_tests(33);
  do_tests(60);
  do_tests(160);

  return 0;
}
