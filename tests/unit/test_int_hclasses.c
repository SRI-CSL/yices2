/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <inttypes.h>
#include <assert.h>

#include "utils/hash_functions.h"
#include "utils/int_hash_classes.h"



/*
 * Hash code for an integer x
 */
static uint32_t hash(void *aux, int32_t x) {
  return jenkins_hash_int32(x % 61);
}


/*
 * Equality test
 */
static bool match(void *aux, int32_t x, int32_t y) {
  return x % 61 == y % 61;
}


/*
 * Print the hash table
 */
static void print_iclass(int_hclass_t *table) {
  uint32_t i, n;

  printf("iclass: %p\n", table);
  printf("  size = %"PRIu32"\n", table->size);
  printf("  nelems = %"PRIu32"\n", table->nelems);

  if (table->nelems > 0) {
    printf("  Content\n");
    n = table->size;
    for (i=0; i<n; i++) {
      if (table->data[i] != null_index) {
	printf("   data[%"PRIu32"]: %"PRId32"\n", i, table->data[i]);
      }
    }
  }
}



/*
 * Global table
 */
static int_hclass_t iclass;

int main(void) {
  int32_t i, x, y, z;

  init_int_hclass(&iclass, 16, NULL, (iclass_hash_fun_t) hash, (iclass_match_fun_t) match);
  printf("=== Init ===\n");
  print_iclass(&iclass);
  printf("\n\n");

  for (i=0; i<100; i++) {
    x = int_hclass_find_rep(&iclass, i);
    y = int_hclass_get_rep(&iclass, i);
    printf("find %"PRId32" = %"PRId32"\n", i, x);
    printf("get  %"PRId32" = %"PRId32"\n\n", i, y);
    fflush(stdout);
    assert((x >= 0 && x == y) || (x < 0 && y == i));
  }

  printf("=== Final table ===\n");
  print_iclass(&iclass);
  printf("\n\n");


  reset_int_hclass(&iclass);
  printf("=== After reset ===\n");
  print_iclass(&iclass);
  printf("\n\n");

  for (i=0; i<140; i++) {
    z = 200 - i;
    x = int_hclass_find_rep(&iclass, z);
    y = int_hclass_get_rep(&iclass, z);
    printf("find %"PRId32" = %"PRId32"\n", z, x);
    printf("get  %"PRId32" = %"PRId32"\n\n", z, y);
    fflush(stdout);
    assert((x >= 0 && x == y) || (x < 0 && y == z));
  }

  printf("=== Final table ===\n");
  print_iclass(&iclass);
  printf("\n\n");

  delete_int_hclass(&iclass);

  return 0;
}
