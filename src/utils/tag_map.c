/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Vector that stores a map from 32bit indices to 8bit values
 * - this is a variant of mark_vectors.h intended to be more
 *   efficient (to be used by the sat solver)
 * - the default value is map[x] = 0 for all x
 */

#include <string.h>

#include "utils/memalloc.h"
#include "utils/tag_map.h"


/*
 * Initialize: n = initial size.
 * - if n == 0, use the default
 */
void init_tag_map(tag_map_t *map, uint32_t n) {
  if (n == 0) {
    n = DEF_TAG_MAP_SIZE;
  }
  map->map = (uint8_t *) safe_malloc(n * sizeof(uint8_t));
  memset(map->map, 0, n);
  init_ivector(&map->marked, 20);
  map->size = n;
}


void delete_tag_map(tag_map_t *map) {
  safe_free(map->map);
  delete_ivector(&map->marked);
  map->map = NULL;
}


/*
 * Increase size so that we can store map->map[x]
 */
static void resize_tag_map(tag_map_t *map, uint32_t x) {
  uint32_t n;

  assert(x >= map->size);

  if (x == UINT32_MAX) {
    out_of_memory();
  }

  // try about 50% larger, if that's not enough use x+1
  n = map->size + 1;
  n += (n >> 1);
  if (x >= n) {
    n = x+1;
  }
  assert(x < n);

  map->map = (uint8_t *) safe_realloc(map->map, n * sizeof(uint8_t));
  memset(map->map + map->size, 0, n - map->size);
  map->size = n;
}


/*
 * Set map[x] := v
 * - v must be positive
 */
void tag_map_write(tag_map_t *map, uint32_t x, uint8_t v) {
  assert(v > 0);
  if (x >= map->size) {
    resize_tag_map(map, x);
    map->map[x] = v;
    ivector_push(&map->marked, x);
  } else {
    if (map->map[x] == 0) {
      ivector_push(&map->marked, x);
    }
    map->map[x] = v;
  }
}


/*
 * Clear: reset all to 0
 */
void clear_tag_map(tag_map_t *map) {
  uint32_t i, n, x;

  n = map->marked.size;
  for (i=0; i<n; i++) {
    x = map->marked.data[i];
    assert(x < map->size && map->map[x] > 0);
    map->map[x] = 0;
  }
  ivector_reset(&map->marked);
}

