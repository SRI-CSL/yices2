/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */

#include <stdio.h>
#include <inttypes.h>

#include "utils/int_hash_map.h"

static int_hmap_t map;

static void print_map(int_hmap_t *map) {
  uint32_t i;
  int_hmap_pair_t *d;

  printf("map %p\n", map);
  printf("  size = %"PRIu32"\n", map->size);
  printf("  nelems = %"PRIu32"\n", map->nelems);
  printf("  ndeleted = %"PRIu32"\n", map->ndeleted);
  printf("  content:\n");

  d = map->data;
  for (i=0; i<map->size; i++) {
    if (d->key >= 0) {
      printf("    [key = %"PRId32", val = %"PRId32"]\n", d->key, d->val);
    }
    d ++;
  }
  printf("\n");
}


int main(void) {
  int_hmap_pair_t *d;
  int32_t i;

  init_int_hmap(&map, 4);
  printf("\n*** Initial map ***\n");
  print_map(&map);

  // add 9 records
  for (i=0; i<9; i++) {
    d = int_hmap_get(&map, i);
    if (d->val == -1) {
      d->val = 3 * i;
      printf("added new record %p: [key = %"PRId32", val = %"PRId32"]\n", d, i, d->val);
    } else {
      printf("found record %p: [key = %"PRId32", val = %"PRId32"]\n", d, i, d->val);
    }
  }

  printf("\n*** Map ***\n");
  print_map(&map);

  // search
  for (i=0; i<20; i++) {
    printf("searching: key = %"PRId32": ", i);
    fflush(stdout);
    d = int_hmap_find(&map, i);
    if (d == NULL) {
      printf("not found\n");
    } else {
      printf("found: val = %"PRId32"\n", d->val);
    }
  }

  // erase some records;
  for (i=0; i<9; i+=3) {
    d = int_hmap_find(&map, i);
    if (d != NULL) {
      printf("erasing record %p: key = %"PRId32"\n", d, i);
      int_hmap_erase(&map, d);
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
    d = int_hmap_find(&map, i);
    if (d == NULL) {
      printf("not found\n");
    } else {
      printf("found: val = %"PRId32"\n", d->val);
    }
  }

  int_hmap_reset(&map);

  printf("\n*** Map after reset ***\n");
  print_map(&map);

  delete_int_hmap(&map);

  return 0;
}
