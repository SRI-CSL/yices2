/*
 * Test of internalization tables
 */

#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>

#include "internalization_map.h"


/*
 * Print the content of a table
 */
static void display_itable(itable_t *table) {
  uint32_t i, n, m;

  printf("Table %p\n", table);
  printf("  level = %"PRIu32"\n", table->level);
  printf("  size  = %"PRIu32"\n", table->size);
  m = 0;
  n = table->size;
  for (i=0; i<n; i++) {
    if (table->data[i] != nil) {
      printf("  %"PRIu32" --> %"PRId32"\n", i, table->data[i]);
      m ++;
    }
  }

  if (m == 0) {
    printf("  empty\n");
  }
}

int main() {
  itable_t table;
  int32_t x, k;

  init_itable(&table, 5);
  printf("\n*** INITIAL TABLE ***\n");
  display_itable(&table);

  printf("\n*** Adding mapping (x --> x) for x=1 to 7 ***\n");
  for (x=1; x<=7; x++) {
    itable_map(&table, x, x);
  }
  display_itable(&table);

  printf("\n*** Checking mapping ***\n");
  for (x=0; x<15; x++) {
    k = itable_get(&table, x);
    printf("  %2"PRId32" mapped to %2"PRId32"\n", x, k);
  }

  printf("\n*** Push ***\n");
  itable_push(&table);

  printf("\n*** Adding mapping (x --> 3 * x) for x=8 to 15 ***\n");
  for (x=8; x <= 15; x++) {
    itable_map(&table, x, 3 * x);
  }
  display_itable(&table);

  printf("\n*** Checking mapping ***\n");
  for (x=0; x<15; x++) {
    k = itable_get(&table, x);
    printf("  %2"PRId32" mapped to %2"PRId32"\n", x, k);
  }

  // empty push
  printf("\n*** Push ***\n");
  itable_push(&table);
  
  printf("\n*** Push ***\n");
  itable_push(&table);
  printf("\n*** Overwritting mapping (x --> 2 * x) for x = 4 to 9 ***\n");
  for (x=4; x<=9; x++) {
    itable_remap(&table, x, 2 * x);
  }
  printf("*** Adding mapping (x ---> 10 * x) for x = 0, 50, 100 ***\n");
  itable_map(&table, 0, 0);
  itable_map(&table, 50, 500);
  itable_map(&table, 100, 1000);
  display_itable(&table);

  printf("\n*** Checking mapping ***\n");
  for (x=0; x<15; x++) {
    k = itable_get(&table, x);
    printf("  %2"PRId32" mapped to %2"PRId32"\n", x, k);
  }

  while (table.level > 0) {
    // repeat pop until we're at level 0
    printf("\n*** Pop ***\n");
    itable_pop(&table);
    display_itable(&table);
  
    printf("\n*** Checking mapping ***\n");
    for (x=0; x<15; x++) {
      k = itable_get(&table, x);
      printf("  %2"PRId32" mapped to %2"PRId32"\n", x, k);
    }
  }
  
  printf("\n*** Reset ***\n");
  reset_itable(&table);
  display_itable(&table);

  delete_itable(&table);
  
  return 0;
}
