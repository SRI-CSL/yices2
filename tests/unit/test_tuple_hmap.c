/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Force assert to work even if compiled with debug disabled
 */
#ifdef NDEBUG
# undef NDEBUG
#endif

#include <assert.h>
#include <stdio.h>
#include <stdbool.h>
#include <inttypes.h>

#include "utils/tuple_hash_map.h"


static void print_tuple(uint32_t n, int32_t *a) {
  uint32_t i;

  if (n == 0) {
    printf("[]");
  } else {
    printf("[%"PRId32, a[0]);
    for (i=1; i<n; i++) {
      printf(" %"PRId32, a[i]);
    }
    printf("]");
  }
}

static void print_tuple_record(tuple_hmap_rec_t *r) {
  uint32_t i, n;

  n = r->arity;
  if (n == 0) {
    printf("[]: %"PRId32, r->value);
  } else {
    printf("[%"PRId32, r->key[0]);
    for (i=1; i<n; i++) {
      printf(" %"PRId32, r->key[i]);
    }
    printf("]: %"PRId32, r->value);
  }
}


static void print_tuple_hmap(tuple_hmap_t *table) {
  uint32_t i;
  tuple_hmap_rec_t *d;

  printf("table %p\n", table);
  printf("  size = %"PRIu32"\n", table->size);
  printf("  nelems = %"PRIu32"\n", table->nelems);
  printf("  ndeleted = %"PRIu32"\n", table->ndeleted);
  printf("  content:\n");

  for (i=0; i<table->size; i++) {
    d = table->data[i];
    if (d != NULL && d != TUPLE_HMAP_DELETED) {
      printf("    ");
      print_tuple_record(d);
      printf("\n");
    }
  }
  printf("\n");
}


/*
 * Add a record
 */
static void test_get(tuple_hmap_t *table, uint32_t n, int32_t *a) {
  tuple_hmap_rec_t *r, *d;
  bool new;

  printf("Test get ");
  print_tuple(n, a);
  printf("\n");

  // find before
  d = tuple_hmap_find(table, n, a);

  r = tuple_hmap_get(table, n, a, &new);
  if (new) {
    // assign a value (otherwise valgrind will complain)
    r->value = 93;
  }

  printf("result: %p = ", r);
  print_tuple_record(r);
  if (new) {
    printf(" (new)\n");
    assert(d == NULL);
  } else {
    printf(" (not new)\n");
    assert(d == r);
  }

  // find after
  d = tuple_hmap_find(table, n, a);
  assert(d == r);
}


/*
 * Search for a record
 */
static void test_find(tuple_hmap_t *table, uint32_t n, int32_t *a) {
  tuple_hmap_rec_t *d;

  printf("Test find ");
  print_tuple(n, a);
  printf("\n");

  d = tuple_hmap_find(table, n, a);
  if (d != NULL) {
    printf("result: %p = ", d);
    print_tuple_record(d);
  } else {
    printf("result: NULL");
  }
  printf("\n");
}


/*
 * Add a record
 */
static void test_add(tuple_hmap_t *table, uint32_t n, int32_t *a, int32_t val) {
  tuple_hmap_rec_t *d;

  printf("Test add ");
  print_tuple(n, a);
  printf(": %"PRId32"\n", val);

  // find before
  d = tuple_hmap_find(table, n, a);
  if (d != NULL) {
    printf("result: not feasible, already present\n");
  } else {
    tuple_hmap_add(table, n, a, val);
    d = tuple_hmap_find(table, n, a);
    assert(d != NULL);
    printf("after addition: found %p = ", d);
    print_tuple_record(d);
    printf("\n");
  }

}


/*
 * Remove a record
 */
static void test_remove(tuple_hmap_t *table, uint32_t n, int32_t *a) {
  tuple_hmap_rec_t *d;

  printf("Test remove ");
  print_tuple(n, a);
  printf("\n");

  d = tuple_hmap_find(table, n, a);
  if (d == NULL) {
    printf("not present\n");
  }
  tuple_hmap_remove(table, n, a);
  if (d != NULL) {
    // check that it's been removed
    d = tuple_hmap_find(table, n, a);
    assert(d == NULL);
    printf("removed\n");
  }
}


/*
 * Erase
 */
static void test_erase(tuple_hmap_t *table, uint32_t n, int32_t *a) {
  tuple_hmap_rec_t *d;

  printf("Test erase ");
  print_tuple(n, a);
  printf("\n");

  d = tuple_hmap_find(table, n, a);
  if (d == NULL) {
    printf("not present\n");
  } else {
    printf("found %p = ", d);
    print_tuple_record(d);
    printf("\n");
    tuple_hmap_erase(table, d);
    d = tuple_hmap_find(table, n, a);
    assert(d == NULL);
    printf("erased\n");
  }
}



#define N 20
static tuple_hmap_t table;
static int32_t aux[20];

int main(void) {
  uint32_t i, j;

  init_tuple_hmap(&table, 2);
  printf("\n*** After initialization ***\n");
  print_tuple_hmap(&table);

  for (j=0; j<20; j++) {
    aux[j] = j;
  }

  for (i=0; i<9; i++) {
    test_add(&table, i, aux, 100+i);
    test_get(&table, i, aux);
    test_find(&table, i, aux);
    printf("\n");
  }

  printf("\n*** After additions ***\n");
  print_tuple_hmap(&table);

  test_find(&table, 10, aux);
  printf("\n");
  test_find(&table, 15, aux);
  printf("\n");

  reset_tuple_hmap(&table);
  printf("\n*** After reset ***\n");
  print_tuple_hmap(&table);

  for (i=0; i<14; i += 2) {
    test_get(&table, i, aux);
    printf("\n");
  }

  printf("\n*** After additions ***\n");
  print_tuple_hmap(&table);

  for (i=0; i<20; i++) {
    test_find(&table, i, aux);
    printf("\n");
  }

  for (i=0; i<10; i++) {
    test_remove(&table, i, aux);
    printf("\n");
  }

  printf("\n*** After removals ***\n");
  print_tuple_hmap(&table);

  for (i=0; i<20; i++) {
    test_find(&table, i, aux);
    printf("\n");
  }

  for (i=0; i<20; i++) {
    test_erase(&table, i, aux);
    printf("\n");
  }

  printf("\n*** After erasures ***\n");
  print_tuple_hmap(&table);

  delete_tuple_hmap(&table);

  return 0;
}
