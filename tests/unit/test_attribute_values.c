/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <inttypes.h>
#include <assert.h>

#include "frontend/smt2/attribute_values.h"
#include "terms/bv64_constants.h"
#include "terms/bv_constants.h"
#include "terms/rationals.h"
#include "utils/memalloc.h"

#ifdef MINGW
static inline int random(void) {
  return rand();
}
#endif


/*
 * Test constructors
 */
static void test_rational_attr(attr_vtbl_t *table, rational_t *q) {
  aval_t i;

  printf("testing aval_rational: ");
  q_print(stdout, q);
  printf("\n");
  fflush(stdout);

  i = attr_vtbl_rational(table, q);
  aval_incref(table, i);

  if (aval_tag(table, i) != ATTR_RATIONAL) {
    fprintf(stderr, "BUG in rational constructor (wrong tag)\n");
    exit(1);
  }

  if (! q_eq(&table->desc[i].rational, q)) {
    fprintf(stderr, "BUG in rational constructor (wrong value)\n");
    exit(1);
  }
}

static void test_bv64_attr(attr_vtbl_t *table, uint32_t nbits, uint64_t c) {
  bvconst_attr_t *d;
  aval_t i;

  printf("test aval_bv64: ");
  bvconst64_print(stdout, c, nbits);
  printf("\n");
  fflush(stdout);

  i = attr_vtbl_bv64(table, nbits, c);
  aval_incref(table, i);

  if (aval_tag(table, i) != ATTR_BV) {
    fprintf(stderr, "BUG in bv64 constructor (wrong tag)\n");
    exit(1);
  }

  d = table->desc[i].ptr;
  if (d->nbits != nbits || d->data[0] != (uint32_t) c ||
      (nbits> 32 && d->data[1] != (uint32_t) (c >> 32))) {
    fprintf(stderr, "BUG in bv64 constructor (wrong value)\n");
    exit(1);
  }
}

static void test_bv_attr(attr_vtbl_t *table, uint32_t nbits, uint32_t *c) {
  bvconst_attr_t *d;
  aval_t i;
  uint32_t w;

  printf("test aval_bv: ");
  bvconst_print(stdout, c, nbits);
  printf("\n");
  fflush(stdout);

  i = attr_vtbl_bv(table, nbits, c);
  aval_incref(table, i);

  if (aval_tag(table, i) != ATTR_BV) {
    fprintf(stderr, "BUG in bv constructor (wrong tag)\n");
    exit(1);
  }

  d = table->desc[i].ptr;
  w = (nbits + 31) >> 5;
  if (d->nbits != nbits || bvconst_neq(d->data, c, w)) {
    fprintf(stderr, "BUG in bv constructor (wrong value)\n");
    exit(1);
  }
}

static void test_string_attr(attr_vtbl_t *table, const char *s) {
  aval_t i;

  printf("test aval_string: \"%s\"\n", s);
  fflush(stdout);

  i = attr_vtbl_string(table, s);
  aval_incref(table, i);

  if (aval_tag(table, i) != ATTR_STRING) {
    fprintf(stderr, "BUG in string constructor (wrong tag)\n");
    exit(1);
  }

  if (strcmp(s, table->desc[i].ptr) != 0) {
    fprintf(stderr, "BUG in string constructor (wrong value)\n");
    exit(1);
  }
}

static void test_symbol_attr(attr_vtbl_t *table, const char *s) {
  aval_t i;

  printf("test aval_string: \"%s\"\n", s);
  fflush(stdout);

  i = attr_vtbl_symbol(table, s);
  aval_incref(table, i);

  if (aval_tag(table, i) != ATTR_SYMBOL) {
    fprintf(stderr, "BUG in symbol constructor (wrong tag)\n");
    exit(1);
  }

  if (strcmp(s, table->desc[i].ptr) != 0) {
    fprintf(stderr, "BUG in symbol constructor (wrong value)\n");
    exit(1);
  }
}

static void print_list(uint32_t n, aval_t *a) {
  uint32_t i;

  if (n == 0) {
    printf("()");
  } else {
    printf("(a!%"PRId32, a[0]);
    for (i=1; i<n; i++) {
      printf(" a!%"PRId32, a[i]);
    }
    printf(")");
  }
}

static bool equal_lists(aval_t *a, aval_t *b, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (a[i] != b[i]) {
      return false;
    }
  }
  return true;
}

static void test_list_attr(attr_vtbl_t *table, uint32_t n, aval_t *a) {
  attr_list_t *d;
  aval_t i;

  printf("test aval_list: ");
  print_list(n, a);
  printf("\n");

  i = attr_vtbl_list(table, n, a);
  aval_incref(table, i);

  if (aval_tag(table, i) != ATTR_LIST) {
    fprintf(stderr, "BUG in list constructor (wrong tag)\n");
    exit(1);
  }

  d = table->desc[i].ptr;
  if (d->nelems != n || ! equal_lists(a, d->data, n)) {
    fprintf(stderr, "BUG in list constructor (wrong value)\n");
    exit(1);
  }
}

/*
 * Test of decref
 */
static void test_decref(attr_vtbl_t *table, aval_t i) {
  uint32_t c1, c2;

  printf("testing decref on a!%"PRId32"\n", i);
  fflush(stdout);

  c1 = aval_refcount(table, i);
  aval_decref(table, i);
  c2 = aval_refcount(table, i);
  if (c1 != c2 +1) {
    printf("BUG in decref: bad refcount\n");
    exit(1);
  }
  if (c2 == 0 && table->tag[i] != ATTR_DELETED) {
    printf("BUG in decref: a!%"PRId32" should be deleted\n", i);
    exit(1);
  }
}

static void test_rationals(attr_vtbl_t *table) {
  rational_t q;

  q_init(&q);
  q_set_one(&q);
  test_rational_attr(table, &q);
  q_clear(&q);
  test_rational_attr(table, &q);
  q_set32(&q, 100);
  test_rational_attr(table, &q);
  q_set_int32(&q, -1, 6);
  test_rational_attr(table, &q);
  q_clear(&q);
}

static void test_bvs(attr_vtbl_t *table) {
  uint32_t aux[4];

  test_bv64_attr(table, 32, 0);
  test_bv64_attr(table, 31, 0x40000000);
  test_bv64_attr(table, 16, 0xFF00);

  aux[0] = 0x55555555;
  aux[1] = 0x55555555;
  aux[2] = 0x55555555;
  aux[3] = 0;
  test_bv_attr(table, 96, aux);
  aux[3] = 0xFFFFFFFF;
  test_bv_attr(table, 128, aux);
  aux[0] = 0;
  aux[1] = 0;
  aux[2] = 0;
  aux[3] = 0x4000000;
  test_bv_attr(table, 127, aux);
}

static void test_strings(attr_vtbl_t *table) {
  test_string_attr(table, "alpha");
  test_string_attr(table, "beta");
  test_string_attr(table, "gamma");

  test_symbol_attr(table, "north");
  test_symbol_attr(table, "south");
  test_symbol_attr(table, "east");
  test_symbol_attr(table, "west");
}

static void test_random_list(attr_vtbl_t *table) {
  aval_t aux[20];
  uint32_t i, j, n, p;
  int32_t x;

  p = table->nelems;
  if (p == 0) return;

  n = 5 + random() % 16;
  assert(n <= 20);
  j = 0;
  for (i=0; i<n; i++) {
    x = random() % p;
    if (table->tag[x] != ATTR_DELETED) {
      aux[j] = x;
      j ++;
    }
  }
  test_list_attr(table, j, aux);
}

static void test_lists(attr_vtbl_t *table) {
  uint32_t n;

  n = 12;
  while (n > 0) {
    test_random_list(table);
    n --;
  }
}

/*
 * Test of decref:
 * - n = number of tests
 */
static void test_decrefs(attr_vtbl_t *table, uint32_t n) {
  uint8_t *a;
  uint32_t p;
  int32_t i;

  p = table->nelems;
  if (p == 0) {
    printf("test decref: not possible, table is empty");
    return;
  }

  a = (uint8_t *) safe_malloc(p * sizeof(uint8_t));
  for (i=0; i<p; i++) {
    a[i] = 0;
  }

  while (n > 0) {
    n --;
    i = random() % p;
    if (a[i] == 0 && table->tag[i] != ATTR_DELETED) {
      test_decref(table, i);
      a[i] = 1;
    }
  }

  safe_free(a);
}


/*
 * Show attribute i
 */
static void print_array(attr_list_t *a) {
  uint32_t i, n;

  n = a->nelems;
  if (n == 0) {
    printf("()");
  } else {
    printf("(a!%"PRId32, a->data[0]);
    for (i=1; i<n; i++) {
      printf(" a!%"PRId32, a->data[i]);
    }
    printf(")");
  }
}

static void print_aval(attr_vtbl_t *table, int32_t i) {
  bvconst_attr_t *b;

  assert(valid_aval(table, i));

  printf("   attr[%"PRId32"]: ", i);
  switch (aval_tag(table, i)) {
  case ATTR_DELETED:
    printf("deleted (next = %"PRId32")", table->desc[i].next);
    break;

  case ATTR_RATIONAL:
    q_print(stdout, &table->desc[i].rational);
    break;

  case ATTR_BV:
    b = table->desc[i].ptr;
    bvconst_print(stdout, b->data, b->nbits);
    break;

  case ATTR_STRING:
    printf("\"%s\"", (char *) table->desc[i].ptr);
    break;

  case ATTR_SYMBOL:
    fputs((char *) table->desc[i].ptr, stdout);
    break;

  case ATTR_LIST:
    print_array(table->desc[i].ptr);
    break;
  }
  printf("\n");
}

/*
 * Show table
 */
static void print_attr_vtbl(attr_vtbl_t *table) {
  uint32_t i, n;

  printf("table %p\n", table);
  printf("  size = %"PRIu32"\n", table->size);
  printf("  nelems = %"PRIu32"\n", table->nelems);
  printf("  free_idx = %"PRId32"\n", table->free_idx);

  n = table->nelems;
  for (i=0; i<n; i++) {
    print_aval(table, i);
  }
  printf("\n");
}

static attr_vtbl_t table;

int main(void) {
  init_rationals();

  init_attr_vtbl(&table);
  printf("=== INITIAL CONTENT ====\n");
  print_attr_vtbl(&table);

  test_rationals(&table);
  test_bvs(&table);
  test_strings(&table);
  test_lists(&table);
  printf("\n=== AFTER TESTS ====\n");
  print_attr_vtbl(&table);

  reset_attr_vtbl(&table);
  printf("=== AFTER RESET ====\n");
  print_attr_vtbl(&table);

  test_rationals(&table);
  test_bvs(&table);
  test_strings(&table);
  test_lists(&table);
  printf("\n=== AFTER TESTS ====\n");
  print_attr_vtbl(&table);

  test_decrefs(&table, 100);
  printf("\n=== AFTER DECREFS ====\n");
  print_attr_vtbl(&table);

  delete_attr_vtbl(&table);
  cleanup_rationals();

  return 0;
}
