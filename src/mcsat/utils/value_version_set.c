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

#include <stdbool.h>

#include "mcsat/value.h"
#include "mcsat/utils/value_version_set.h"
#include "mcsat/utils/value_hash_map.h"


struct value_version_set_struct {
  value_version_set_type_t type;
  /** current level (0 means all elements, and set is ignored) */
  uint32_t timestamp;
  /** Values stored in the map [value -> ts]. Every map[value] <= timestamp.
   * Union Sets: When the element was added.
   * Intersection Sets: When map[value] = timestamp then element is in the set, otherwise value was in the set previously */
  value_hmap_t map;
  /** Count to perform efficient is_empty checks for intersections */
  uint32_t count;
};

value_version_set_t* value_version_set_new(value_version_set_type_t type) {
  value_version_set_t *set = safe_malloc(sizeof(value_version_set_t));
  set->type = type;
  set->timestamp = 0;
  set->count = 0;
  init_value_hmap(&set->map, 0);
  return set;
}

void value_version_set_delete(value_version_set_t *set) {
  delete_value_hmap(&set->map);
  safe_free(set);
}

uint32_t value_version_set_count(const value_version_set_t *set) {
  if (set->type == VALUE_SET_INTERSECTION && set->timestamp == 0) {
    // set containing "all"
    assert(set->count == 0);
    return UINT32_MAX;
  }
  assert(set->type != VALUE_SET_UNION || set->map.nelems == set->count);
  return set->count;
}

void value_version_set_reset(value_version_set_t *set) {
  set->timestamp = 0;
  set->count = 0;
  value_hmap_reset(&set->map);
}

static
bool value_version_set_push_union(value_version_set_t *set, mcsat_value_t *new_set, size_t new_set_size, void *aux, value_version_set_filter_t f) {
  bool update = false;
  set->timestamp++;
  for (size_t i = 0; i < new_set_size; ++i) {
    mcsat_value_t *new = &new_set[i];
    if (f != NULL && !f(aux, new)) {
      continue;
    }
    value_hmap_pair_t *pair = value_hmap_get(&set->map, new);
    if (pair->val == -1) {
      set->count++;
      update = true;
      pair->val = set->timestamp;
    }
  }
  return update;
}

static
bool value_version_set_push_intersect(value_version_set_t *set, mcsat_value_t *new_set, size_t new_set_size, void *aux, value_version_set_filter_t f) {
  size_t remaining = 0;
  for (size_t i = 0; i < new_set_size; ++i) {
    mcsat_value_t *new = &new_set[i];
    if (f != NULL && !f(aux, new)) {
      continue;
    }
    value_hmap_pair_t *pair = value_hmap_find(&set->map, new);
    if (pair != NULL && pair->val == set->timestamp) {
      pair->val++;
      remaining++;
    }
  }

  set->timestamp++;
  bool update = (remaining != set->count);
  set->count = remaining;
  return update;
}

bool value_version_set_push(value_version_set_t *set, mcsat_value_t *new_set, size_t new_set_size) {
  return value_version_set_push_filter(set, new_set, new_set_size, NULL, NULL);
}

bool value_version_set_push_filter(value_version_set_t *set, mcsat_value_t *new_set, size_t new_set_size, void *aux, value_version_set_filter_t f) {
  if (set->type == VALUE_SET_UNION || (set->type == VALUE_SET_INTERSECTION && set->timestamp == 0)) {
    return value_version_set_push_union(set, new_set, new_set_size, aux, f);
  } else if (set->type == VALUE_SET_INTERSECTION) {
    return value_version_set_push_intersect(set, new_set, new_set_size, aux, f);
  } else {
    assert(false);
    return false;
  }
}

static
uint32_t feasibility_int_set_push_current(void *set, const value_hmap_pair_t *p) {
  uint32_t ts = ((value_version_set_t *) set)->timestamp;
  return p->val == ts ? p->val + 1 : p->val;
}

/** specific push function that requires an not-empty intersection set. Updates all that are not in new_set */
bool value_version_set_push_intersect_inverted(value_version_set_t *set, mcsat_value_t *new_set, size_t new_set_size) {
  assert(set->type == VALUE_SET_INTERSECTION);
  assert(set->timestamp > 0);

  // update all current by one
  value_hmap_update_records(&set->map, set, feasibility_int_set_push_current);
  set->timestamp++;

  // decrement the timestamp of all current that are in new_set to exclude them
  bool update = false;
  for (size_t i = 0; i < new_set_size; ++i) {
    value_hmap_pair_t *pair = value_hmap_find(&set->map, &new_set[i]);
    if (pair != NULL && pair->val == set->timestamp) {
      pair->val--;
      set->count--;
      update = true;
    }
  }

  return update;
}

static
bool feasibility_int_set_pop_is_future_ts(void *set, const value_hmap_pair_t *p) {
  uint32_t ts = ((value_version_set_t *) set)->timestamp;
  return p->val > ts;
}

static
uint32_t feasibility_int_set_pop_map_min(void *set, const value_hmap_pair_t *p) {
  uint32_t ts = ((value_version_set_t *) set)->timestamp;
  return p->val > ts ? ts : p->val;
}

void value_version_set_pop(value_version_set_t *set, size_t count) {
  if (count >= set->timestamp) {
    value_version_set_reset(set);
  } else {
    set->timestamp -= count;
    switch(set->type) {
    case VALUE_SET_UNION:
      value_hmap_remove_records(&set->map, set, feasibility_int_set_pop_is_future_ts);
      break;
    case VALUE_SET_INTERSECTION:
      value_hmap_update_records(&set->map, set, feasibility_int_set_pop_map_min);
      break;
    default:
      assert(false);
    }
  }
}

bool value_version_set_contains(const value_version_set_t *set, const mcsat_value_t *k) {
  value_hmap_pair_t *pair = value_hmap_find(&set->map, k);
  if (pair == NULL) {
    return false;
  } else if (set->type == VALUE_SET_UNION) {
    return true;
  } else {
    return pair->val == set->timestamp;
  }
}

const mcsat_value_t* value_version_set_any(const value_version_set_t *set) {
  value_hmap_pair_t *it;

  if (set->count == 0) {
    return NULL;
  }

  switch(set->type) {
  case VALUE_SET_UNION:
    it = value_hmap_first_record(&set->map);
    return it == NULL ? NULL : it->key;
  case VALUE_SET_INTERSECTION:
    for (it = value_hmap_first_record(&set->map); it != NULL; it = value_hmap_next_record(&set->map, it)) {
      if (it->val == set->timestamp) {
        return it->key;
      }
    }
    assert(false);
    return NULL;
  default:
    assert(false);
    return NULL;
  }
}

uint32_t value_version_set_get_timestamp(const value_version_set_t *set) {
  return set->timestamp;
}

void value_version_set_print(const value_version_set_t *set, FILE *out) {
  value_version_set_print_at(set, set->timestamp, out);
}

void value_version_set_print_at(const value_version_set_t *set, uint32_t timestamp, FILE *out) {
  fprintf(out, "{");
  bool first = true;
  for (value_hmap_pair_t *it = value_hmap_first_record(&set->map); it != NULL; it = value_hmap_next_record(&set->map, it)) {
    if (set->type == VALUE_SET_UNION && it->val > timestamp) {
      continue;
    }
    if (set->type == VALUE_SET_INTERSECTION && it->val < timestamp) {
      continue;
    }
    if (!first) {
      fprintf(out, ", ");
    }
    first = false;
    mcsat_value_print(it->key, out);
  }
  fprintf(out, "}");
}
