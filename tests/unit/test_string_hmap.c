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
#include <string.h>
#include <stdlib.h>
#include <inttypes.h>
#include <assert.h>

#include "utils/string_hash_map.h"


// Copied from string_hash_map.c
#define DELETED_KEY ((char *) 1)


static void print_map(strmap_t *hmap) {
  strmap_rec_t *d;
  uint32_t i;

  printf("map %p\n", hmap);
  printf("  size = %"PRIu32"\n", hmap->size);
  printf("  nelems = %"PRIu32"\n", hmap->nelems);
  printf("  ndeleted = %"PRIu32"\n", hmap->ndeleted);

  d = hmap->data;
  for (i=0; i<hmap->size; i++) {
    if (d->key != NULL && d->key != DELETED_KEY) {
      printf("    [key = %s, hash = %"PRIu32", val = %"PRId32"]\n", d->key, d->hash, d->val);
    }
    d ++;
  }
  printf("\n");
}

static strmap_t map;

#define NKEYS 10

static const char * const test_key[NKEYS] = {
  "one", "two", "three", "four", "five",
  "six", "seven", "eight", "nine", "ten",
};

int main(void) {
  strmap_rec_t *d, *r;
  uint32_t i;
  bool new;

  init_strmap(&map, 4);
  printf("\n*** Initial map ***\n");
  print_map(&map);

  printf("\n*** Testing find (should all fail) ***\n");
  for (i=0; i<NKEYS; i++) {
    printf("find key %s\n", test_key[i]);
    d = strmap_find(&map, test_key[i]);
    if (d != NULL) {
      printf("BUG: find returned a record\n");
      fflush(stdout);
      exit(1);
    }
  }

  printf("\n*** Adding %"PRIu32" records ***\n", NKEYS);
  for (i=0; i<NKEYS; i++) {
    printf("add key %s\n", test_key[i]);
    d = strmap_get(&map, test_key[i], &new);
    if (! new) {
      printf("BUG: record not returned as new\n");
      fflush(stdout);
      exit(1);
    }
    if (strcmp(d->key, test_key[i]) != 0) {
      printf("BUG: record has the wrong key\n");
      fflush(stdout);
      exit(1);
    }
    r = strmap_get(&map, test_key[i], &new);
    if (new || r != d) {
      printf("BUG: in second call to get\n");
      fflush(stdout);
      exit(1);
    }
  }

  printf("\n*** After additions ***\n");
  print_map(&map);

  printf("\n*** Testing find (should all succeed) ***\n");
  for (i=0; i<NKEYS; i++) {
    printf("find key %s\n", test_key[i]);
    d = strmap_find(&map, test_key[i]);
    if (d == NULL) {
      printf("BUG: find failed\n");
      fflush(stdout);
      exit(1);
    }
    if (strcmp(d->key, test_key[i]) != 0) {
      printf("BUG: find returned a wrong record\n");
      fflush(stdout);
      exit(1);
    }
  }

  printf("\n*** Testing find (should all fail) ***\n");
  printf("test find empty key\n");
  d = strmap_find(&map, "");
  if (d != NULL) {
    printf("BUG: find returned a record\n");
    fflush(stdout);
    exit(1);
  }
  printf("test find key twenty\n");
  d = strmap_find(&map, "twenty");
  if (d != NULL) {
    printf("BUG: find returned a record\n");
    fflush(stdout);
    exit(1);
  }

  printf("\n*** Testing erase ***\n");
  for (i=0; i<NKEYS; i += 2) {
    printf("removing key %s\n", test_key[i]);
    d = strmap_find(&map, test_key[i]);
    assert(d != NULL && strcmp(d->key, test_key[i]) == 0);
    strmap_erase(&map, d);
    r = strmap_find(&map, test_key[i]);
    assert(r == NULL);
  }

  printf("\n*** After removals ***\n");
  print_map(&map);

  printf("\n*** Testing find ***\n");
  for (i=0; i<NKEYS; i++) {
    printf("find key %s: ", test_key[i]);
    d = strmap_find(&map, test_key[i]);
    if (d == NULL) {
      printf("not found\n");
      if ((i & 1) != 0) {
	printf("BUG: should be present\n");
	fflush(stdout);
	exit(1);
      }
    } else {
      printf("found\n");
      if ((i & 1) == 0) {
	printf("BUG: should be absent\n");
	fflush(stdout);
	exit(1);
      }
    }
  }

  reset_strmap(&map);
  printf("\n*** After reset ***\n");
  print_map(&map);

  delete_strmap(&map);
  return 0;
}
