/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <inttypes.h>

#include "utils/pair_hash_map.h"

static pmap_t map;

static void print_map(pmap_t *map) {
  uint32_t i;
  pmap_rec_t *d;

  printf("map %p\n", map);
  printf("  size = %"PRIu32"\n", map->size);
  printf("  nelems = %"PRIu32"\n", map->nelems);
  printf("  ndeleted = %"PRIu32"\n", map->ndeleted);
  printf("  content:\n");

  d = map->data;
  for (i=0; i<map->size; i++) {
    if (d->val != NULL && d->val != DELETED_PTR) {
      printf("    [k0 = %"PRId32", k1 = %"PRId32", val = %p]\n", d->k0, d->k1, d->val);
    }
    d ++;
  }
  printf("\n");
}


int main() {
  pmap_rec_t *d;
  char *fake;
  int32_t i;
  int32_t k0, k1;

  init_pmap(&map, 4);
  printf("\n*** Initial map ***\n");
  print_map(&map);

  // add 9 records
  fake = (char *) 0xabc00000;
  for (i=0; i<9; i++) {
    k0 = i+1;
    k1 = 10-i;
    d = pmap_get(&map, k0, k1);
    if (d->val == DEFAULT_PTR) {
      d->val = fake;
      printf("added new record %p: [k0 = %"PRId32", k1 = %"PRId32", val = %p]\n", d, k0, k1, d->val);
    } else {
      printf("found record %p: [k0 = %"PRId32", k1 = %"PRId32", val = %p]\n", d, k0, k1, d->val);
    }
    fake += 0x20;
  }

  printf("\n*** Map ***\n");
  print_map(&map);

  // search
  for (i=0; i<20; i++) {
    k0 = i + 1;
    k1 = 10 - i;
    printf("searching: [k0 = %"PRId32", k1 = %"PRId32"]: ", k0, k1);
    fflush(stdout);
    d = pmap_find(&map, k0, k1);
    if (d == NULL) {
      printf("not found\n");
    } else {
      printf("found: val = %p\n", d->val);
    }
  }

  // erase some records;
  for (i=0; i<9; i+=3) {
    k0 = i+1;
    k1 = 10-i;
    d = pmap_find(&map, k0, k1);
    if (d != NULL) {
      printf("erasing record %p: [k0 = %"PRId32", k1 = %"PRId32"]\n", d, k0, k1);
      pmap_erase(&map, d);
    } else {
      printf("*** BUG ***\n");
    }
  }

  printf("\n*** Map after deletion ***\n");
  print_map(&map);

  // search
  for (i=0; i<9; i++) {
    k0 = i + 1;
    k1 = 10 - i;
    printf("searching: [k0 = %"PRId32", k1 = %"PRId32"]: ", k0, k1);
    fflush(stdout);
    d = pmap_find(&map, k0, k1);
    if (d == NULL) {
      printf("not found\n");
    } else {
      printf("found: val = %p\n", d->val);
    }
  }

  pmap_reset(&map);

  printf("\n*** Map after reset ***\n");
  print_map(&map);

  delete_pmap(&map);

  return 0;
}
