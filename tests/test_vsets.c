#include <stdio.h>
#include <inttypes.h>

#include "vsets.h"


static void print_array(uint32_t n, int32_t *a) {
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

static void print_vset(vset_t *set) {
  uint32_t i, n;

  n = set->nelems;
  if (n == 0) {
    printf("{}");
  } else {
    printf("{%"PRId32, set->data[0]);
    for (i=1; i<n; i++) {
      printf(" %"PRId32, set->data[i]);
    }
    printf("}");
  }
}


static void print_vsets(vset_htbl_t *table) {
  uint32_t i;
  vset_t *d;

  printf("table %p\n", table);
  printf("  size = %"PRIu32"\n", table->size);
  printf("  nelems = %"PRIu32"\n", table->nelems);
  printf("  ndeleted = %"PRIu32"\n", table->ndeleted);
  printf("  content:\n");
 
  for (i=0; i<table->size; i++) {
    d = table->data[i];
    if (d != NULL && d != DELETED_VSET) {
      printf("    ");
      print_vset(d);
      printf("\n");
    }
  }
  printf("\n");
}


/*
 * Add a record
 */
static void test_get(vset_htbl_t *table, uint32_t n, int32_t *a) {
  vset_t *d;

  printf("Test get ");
  print_array(n, a);
  printf("\n");

  d = vset_htbl_get(table, n, a);
  printf("result: %p = ", d);
  print_vset(d);
  printf("\n");
}


/*
 * Search for a record
 */
static void test_find(vset_htbl_t *table, uint32_t n, int32_t *a) {
  vset_t *d;

  printf("Test find ");
  print_array(n, a);
  printf("\n");

  d = vset_htbl_find(table, n, a);
  if (d != NULL) {
    printf("result: %p = ", d);
    print_vset(d);
  } else {
    printf("result: NULL");
  }
  printf("\n");
}


/*
 * Remove a record
 */
static void test_remove(vset_htbl_t *table, uint32_t n, int32_t *a) {
  printf("Test remove ");
  print_array(n, a);
  printf("\n");
  vset_htbl_remove(table, n, a);
}


#define N 20
static vset_htbl_t table;
static int32_t aux[20];

int main(void) {
  uint32_t i, j;

  init_vset_htbl(&table, 4);
  printf("\n*** Initial table ***\n");
  print_vsets(&table);

  for (j=0; j<20; j++) {
    aux[j] = j;
  }
  
  for (i=0; i<9; i++) {
    test_get(&table, i, aux);
    test_find(&table, i, aux);
  }

  printf("\n*** After additions ***\n");
  print_vsets(&table);

  test_find(&table, 10, aux);
  test_find(&table, 15, aux);

  reset_vset_htbl(&table);
  printf("\n*** After reset ***\n");
  print_vsets(&table);

  for (i=0; i<14; i += 2) {
    test_get(&table, i, aux);
  }

  printf("\n*** After additions ***\n");
  print_vsets(&table);

  for (i=0; i<20; i++) {
    test_find(&table, i, aux);
  }

  for (i=0; i<10; i++) {
    test_remove(&table, i, aux);
  }

  printf("\n*** After removals ***\n");
  print_vsets(&table);

  for (i=0; i<20; i++) {
    test_find(&table, i, aux);
  }


  delete_vset_htbl(&table);

  return 0;
}
