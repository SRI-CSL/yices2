/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2018 SRI International.
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

#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

#include "utils/backtrack_int_hash_map.h"


static void show_mapping(FILE *f, back_hmap_t *map) {
  back_hmap_data_t *d;
  uint32_t i, n;

  fprintf(f, "hmap %p\n", map);
  fprintf(f, "  size = %"PRIu32"\n", map->size);
  fprintf(f, "  nelems = %"PRIu32"\n", map->nelems);
  fprintf(f, "  ndeleted = %"PRIu32"\n", map->ndeleted);
  fprintf(f, "  resize threshold = %"PRIu32"\n", map->resize_threshold);
  fprintf(f, "  cleanup threshold = %"PRIu32"\n", map->cleanup_threshold);
  fprintf(f, "  level = %"PRIu32"\n", map->level);
  fprintf(f, "  content:\n");

  n = map->size;
  d = &map->data;
  for (i=0; i<n; i++) {
    if (d->pair[i].key >= 0) {
      fprintf(f, "   entry[%"PRIu32"]: %"PRId32" --> %"PRId32" (level = %"PRIu32")\n",
	      i, d->pair[i].key, d->pair[i].val, d->level[i]);
    }
  }
  fprintf(f, "\n");
}


/*
 * Some consistency checks
 */
static void check_map(back_hmap_t *map) {
  back_hmap_data_t *d;
  uint32_t i, n, count, deleted;

  n = map->size;
  d = &map->data;
  count = 0;
  deleted = 0;

  for (i=0; i<n; i++) {
    if (d->pair[i].key >= 0) {
      count ++;
      if (d->level[i] > map->level) {
	fprintf(stderr, "*** BUG: inconsistent map: level[%"PRIu32"] = %"PRIu32" but map->level is %"PRIu32" ***\n",
		i, d->level[i], map->level);
	exit(1);
      }
    } else if (d->pair[i].key == BACK_HMAP_DELETED_KEY) {
      deleted ++;
    }
  }

  if (count != map->nelems) {
    fprintf(stderr, "*** BUG: inconsistent map: nelems is wrong ***\n");
    exit(1);
  }

  if (deleted != map->ndeleted) {
    fprintf(stderr, "*** BUG: inconsistent map: ndeleted is wrong ***\n");
    exit(1);
  }
}

static inline bool is_power_of_two(uint32_t n) {
  return (n & (n - 1)) == 0;
}

/*
 * For testing: at level n,
 * - the map should assign i to (i % 5) for i=0 ... 2^k < n
 */
static void check_map_content(back_hmap_t *map, uint32_t n) {
  back_hmap_elem_t *b;
  uint32_t i;

  while (!is_power_of_two(n)) {
    n &= n-1;
  }

  for (i=0; i<n; i++) {
    b = back_hmap_find(map, i);
    if (b == NULL) {
      fprintf(stderr, "*** BUG: expected entry for key %"PRId32", got NULL ***\n", i);
      exit(1);
    }
    if (b->val != (i % 5)) {
      fprintf(stderr, "*** BUG: bad value for key %"PRId32", got %"PRId32" instead of %"PRId32" ***\n",
	      i, b->val, i % 5);
      exit(1);
    }    
  }

  // check a few more
  for (i=n; i<n+10; i++) {
    b = back_hmap_find(map, n);
    if (b != NULL) {
      fprintf(stderr, "*** BUG: got an entry for key %"PRId32", expected none ***\n", i);
      exit(1);
    }
  }

  printf("content looks correct\n");  
}




/*
 * Store data for level n:
 * - if n is a power of two, add n/2 elements from i=n/2 to n-1
 * - otherwise add nothing
 */
static void add_level(back_hmap_t *map, uint32_t n) {
  back_hmap_elem_t *d;
  uint32_t i;

  if (is_power_of_two(n)) {
    for (i=n/2; i<n; i++) {
      d = back_hmap_find(map, i);
      if (d != NULL) {
	fprintf(stderr, "*** BUG in add_level: key %"PRId32" is already present ***\n", i);
	exit(1);
      }
      d = back_hmap_get(map, i);
      assert(d->key == i && d->val == -1);
      d->val = (i % 5);
    }
  }
}


static back_hmap_t hmap;


int main(void) {
  uint32_t n;
  
  printf("--- Initial map ---\n");
  init_back_hmap(&hmap, 16);
  check_map(&hmap);
  show_mapping(stdout, &hmap);

  for (n=0; n<20; n++) {
    printf("--- After level %"PRIu32" ---\n", n);
    add_level(&hmap, n);
    show_mapping(stdout, &hmap);
    check_map_content(&hmap, n);
    check_map(&hmap);
    back_hmap_push(&hmap);
  }

  printf("--- At level %"PRIu32" ---\n", n);
  show_mapping(stdout, &hmap);
  check_map_content(&hmap, n);

  while (n > 4) {
    n --;
    printf("--- Backtracking to level %"PRIu32" ---\n", n);
    back_hmap_pop(&hmap);
    show_mapping(stdout, &hmap);
    check_map_content(&hmap, n);
    check_map(&hmap);
  }

  while (n < 100) {
    n ++;
    printf("---- Adding level %"PRIu32" ---\n", n);
    back_hmap_push(&hmap);
    add_level(&hmap, n);
    show_mapping(stdout, &hmap);
    check_map_content(&hmap, n);
    check_map(&hmap);
  }
  
  printf("--- After reset ---\n");
  reset_back_hmap(&hmap);
  show_mapping(stdout, &hmap);
  check_map(&hmap);

  delete_back_hmap(&hmap);

  return 0;
}
