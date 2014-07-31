/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <inttypes.h>

#include "utils/ptr_hash_map.h"

static ptr_hmap_t map;

/*
 * Array of strings for testing
 */
static char *test[26] = {
  "alpha", "bravo", "charlie", "echo", "foxtrot", "golf",
  "hotel", "india", "juliet", "kilo", "lima", "mike", "november"
  "oscar", "papa", "quebec", "romeo", "sierra", "tango", "uniform",
  "victor", "whiskey", "x-ray", "yankee", "zulu",
};


static void print_map(ptr_hmap_t *map) {
  uint32_t i;
  ptr_hmap_pair_t *d;

  printf("map %p\n", map);
  printf("  size = %"PRIu32"\n", map->size);
  printf("  nelems = %"PRIu32"\n", map->nelems);
  printf("  ndeleted = %"PRIu32"\n", map->ndeleted);
  printf("  content:\n");

  d = map->data;
  for (i=0; i<map->size; i++) {
    if (d->key >= 0) {
      printf("    [key = %"PRId32", val = %s]\n", d->key, (char*) d->val);
    }
    d ++;
  }
  printf("\n");
}


int main() {
  ptr_hmap_pair_t *d;
  int32_t i;

  init_ptr_hmap(&map, 4);
  printf("\n*** Initial map ***\n");
  print_map(&map);

  // add 9 records
  for (i=0; i<9; i++) {
    d = ptr_hmap_get(&map, i);
    if (d->val == NULL) {
      d->val = test[i];
      printf("added new record %p: [key = %"PRId32", val = %s]\n", d, i, (char*) d->val);
    } else {
      printf("found record %p: [key = %"PRId32", val = %s]\n", d, i, (char *) d->val);
    }
  }

  printf("\n*** Map ***\n");
  print_map(&map);

  // search
  for (i=0; i<20; i++) {
    printf("searching: key = %"PRId32": ", i);
    fflush(stdout);
    d = ptr_hmap_find(&map, i);
    if (d == NULL) {
      printf("not found\n");
    } else {
      printf("found: val = %s\n", (char*) d->val);
    }
  }

  // erase some records;
  for (i=0; i<9; i+=3) {
    d = ptr_hmap_find(&map, i);
    if (d != NULL) {
      printf("erasing record %p: key = %"PRId32", val = %s\n", d, i, (char*) d->val);
      ptr_hmap_erase(&map, d);
    } else {
      printf("*** BUG ***\n");
    }
  }

  printf("\n*** Map after deletion ***\n");
  print_map(&map);

  // search
  for (i=0; i<9; i++) {
    printf("searching: key = %"PRId32": ", i);
    fflush(stdout);
    d = ptr_hmap_find(&map, i);
    if (d == NULL) {
      printf("not found\n");
    } else {
      printf("found: val = %s\n", (char*) d->val);
    }
  }

  ptr_hmap_reset(&map);

  printf("\n*** Map after reset ***\n");
  print_map(&map);

  delete_ptr_hmap(&map);

  return 0;
}
