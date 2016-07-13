/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */
 
#include "mcsat/utils/int_mset.h"

#include <stdbool.h>
#include <stddef.h>
#include <assert.h>

void int_mset_construct(int_mset_t* set, uint32_t null_element) {
  init_int_hmap(&set->count_map, 0);
  init_int_hmap(&set->element_list_position, 0);
  init_ivector(&set->element_list, 0);
  set->is_compact = true;
  set->size = 0;
  set->null_element = null_element;
}

void int_mset_destruct(int_mset_t* set) {
  delete_int_hmap(&set->count_map);
  delete_int_hmap(&set->element_list_position);
  delete_ivector(&set->element_list);
}

void int_mset_add(int_mset_t* set, int32_t x) {
  int_hmap_pair_t* find_x;

  assert(x != set->null_element);

  find_x = int_hmap_find(&set->count_map, x);
  if (find_x == NULL) {
    int_hmap_add(&set->count_map, x, 1);
    int_hmap_add(&set->element_list_position, x, set->element_list.size);
    ivector_push(&set->element_list, x);
  } else {
    find_x->val ++;
  }

  set->size ++;
}

uint32_t int_mset_contains(const int_mset_t* set, int32_t x) {
  int_hmap_pair_t* find_x;
  int_hmap_t* set_nonconst;

  set_nonconst = (int_hmap_t*) &set->count_map;
  find_x = int_hmap_find(set_nonconst, x);
  if (find_x == NULL) return 0;
  else return find_x->val;
}

void int_mset_remove_all(int_mset_t* set, int32_t x) {
  int_hmap_pair_t* find_x;

  assert(int_mset_contains(set, x) > 0);

  // Remove from the count_map
  find_x = int_hmap_find(&set->count_map, x);
  set->size -= find_x->val;
  int_hmap_erase(&set->count_map, find_x);

  // Remove from the position map
  find_x = int_hmap_find(&set->element_list_position, x);
  set->element_list.data[find_x->val] = set->null_element;
  int_hmap_erase(&set->element_list_position, find_x);

  // Not compact anymore
  set->is_compact = false;
}

void int_mset_remove_one(int_mset_t* set, int32_t x) {
  int_hmap_pair_t* find_x;

  assert(int_mset_contains(set, x) > 0);

  // Remove from the count_map
  find_x = int_hmap_find(&set->count_map, x);
  set->size --;
  find_x->val --;

  // Remove from the position map
  if (find_x->val == 0) {
    int_hmap_erase(&set->count_map, find_x);
    find_x = int_hmap_find(&set->element_list_position, x);
    set->element_list.data[find_x->val] = set->null_element;
    int_hmap_erase(&set->element_list_position, find_x);
  }

  // Not compact anymore
  set->is_compact = false;
}

void int_mset_clear(int_mset_t* set) {
  int_hmap_reset(&set->count_map);
  int_hmap_reset(&set->element_list_position);
  ivector_reset(&set->element_list);
  set->is_compact = true;
  set->size = 0;
}

void int_mset_compact(int_mset_t* set) {
  uint32_t keep, i;
  int32_t x;
  for (keep = 0, i = 0; i < set->element_list.size; ++ i) {
    x = set->element_list.data[i];
    if (x != set->null_element && int_mset_contains(set, x)) {
      set->element_list.data[keep ++] = x;
    }
  }
  ivector_shrink(&set->element_list, keep);
  set->is_compact = true;
}

ivector_t* int_mset_get_list(int_mset_t* set) {
  if (!set->is_compact) {
    int_mset_compact(set);
  }
  return &set->element_list;
}
