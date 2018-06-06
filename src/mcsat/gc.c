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
 
#include "mcsat/gc.h"

#include <stddef.h>
#include <assert.h>
#include <stdio.h>

void gc_info_construct(gc_info_t* gc, int32_t null_value, bool is_id) {
  init_int_hmap(&gc->old2new_map, 0);
  init_ivector(&gc->marked, 0);
  gc->is_id = is_id;
  gc->is_relocated = false;
  gc->null_value = null_value;
  gc->relocated = 0;
  gc->level = 0;
  gc->marked_first = 0;
}

void gc_info_destruct(gc_info_t* gc) {
  delete_int_hmap(&gc->old2new_map);
  delete_ivector(&gc->marked);
}

void gc_info_mark(gc_info_t* gc, int32_t obj) {
  int_hmap_pair_t* find;

  assert(obj != gc->null_value);
  assert(!gc_info_is_relocated(gc));

  find = int_hmap_find(&gc->old2new_map, obj);
  if (find != NULL) {
    assert(find->val == gc->null_value);
  } else {
    int_hmap_add(&gc->old2new_map, obj, gc->null_value);
    ivector_push(&gc->marked, obj);
  }
}

bool gc_info_is_marked(const gc_info_t* gc, int32_t obj) {
  int_hmap_pair_t* find;

  find = int_hmap_find((int_hmap_t*)&gc->old2new_map, obj);
  return (find != NULL);
}

void gc_info_set_reloc(gc_info_t* gc, int32_t obj, int32_t obj_new) {
  int_hmap_pair_t* find;

  assert(obj_new != gc->null_value);
  assert(!gc_info_is_relocated(gc));

  find = int_hmap_find((int_hmap_t*) &gc->old2new_map, obj);

  assert(find != NULL);
  assert(find->val == gc->null_value);
  assert(!gc->is_id);

  find->val = obj_new;

  gc->relocated ++;
}

int32_t gc_info_get_reloc(const gc_info_t* gc, int32_t obj) {
  int_hmap_pair_t* find;

  find = int_hmap_find((int_hmap_t*)&gc->old2new_map, obj);
  if (find != NULL) {
    if (gc->is_id) {
      return obj;
    } else {
      assert(find->val != gc->null_value);
      return find->val;
    }
  } else {
    return gc->null_value;
  }
}

void gc_info_sweep_ivector(const gc_info_t* gc, ivector_t* objs) {
  uint32_t i, to_keep;
  int32_t obj, obj_reloc;

  assert(gc_info_is_relocated(gc));

  for (i = 0, to_keep = 0; i < objs->size; ++ i) {
    obj = objs->data[i];
    obj_reloc = gc_info_get_reloc(gc, obj);
    assert(obj >= 0);
    assert(obj_reloc >= 0);
    if (obj_reloc != gc->null_value) {
      objs->data[to_keep ++] = obj_reloc;
    }
  }

  ivector_shrink(objs, to_keep);
}

void gc_info_sweep_ptr_hmap_keys(const gc_info_t* gc, ptr_hmap_t* objs, ptr_hmap_ptr_delete ptr_delete) {
  // New map
  ptr_hmap_t new_objs;
  init_ptr_hmap(&new_objs, 0);

  // Relocate
  ptr_hmap_pair_t* it = ptr_hmap_first_record(objs);
  for (; it != NULL; it = ptr_hmap_next_record(objs, it)) {
    int32_t old_key = it->key;
    int32_t new_key = gc_info_get_reloc(gc, old_key);
    if (new_key != gc->null_value) {
      ptr_hmap_pair_t* new_item = ptr_hmap_get(&new_objs, new_key);
      new_item->val = it->val;
    } else {
      (*ptr_delete)(it->val);
    }
  }

  // Destroy and swap in
  delete_ptr_hmap(objs);
  *objs = new_objs;
}

void gc_info_sweep_int_hmap_keys(const gc_info_t* gc, int_hmap_t* objs) {
  // New map
  int_hmap_t new_objs;
  init_int_hmap(&new_objs, 0);

  // Relocate
  int_hmap_pair_t* it = int_hmap_first_record(objs);
  for (; it != NULL; it = int_hmap_next_record(objs, it)) {
    int32_t old_key = it->key;
    int32_t new_key = gc_info_get_reloc(gc, old_key);
    if (new_key != gc->null_value) {
      int_hmap_add(&new_objs, new_key, it->val);
    }
  }

  // Destroy and swap in
  delete_int_hmap(objs);
  *objs = new_objs;
}

void gc_info_sweep_int_hmap_values(const gc_info_t* gc, int_hmap_t* objs) {
  // New map
  int_hmap_t new_objs;
  init_int_hmap(&new_objs, 0);

  // Relocate
  int_hmap_pair_t* it = int_hmap_first_record(objs);
  for (; it != NULL; it = int_hmap_next_record(objs, it)) {
    int32_t old_val = it->val;
    int32_t new_val = gc_info_get_reloc(gc, old_val);
    if (new_val != gc->null_value) {
      int_hmap_add(&new_objs, it->key, new_val);
    }
  }

  // Destroy and swap in
  delete_int_hmap(objs);
  *objs = new_objs;
}

void gc_info_set_relocated(gc_info_t* gc) {
  assert(gc->is_relocated == false);
  gc->is_relocated = true;
  if (gc->is_id) {
    gc->relocated = gc->marked.size;
  }
}

bool gc_info_is_relocated(const gc_info_t* gc) {
  assert (!gc->is_relocated || gc->relocated == gc->marked.size);
  return gc->is_relocated;
}

void gc_info_new_level(gc_info_t* gc) {
  gc->level ++;
  gc->marked_first = gc->marked.size;
}

uint32_t gc_info_get_level_size(const gc_info_t* gc) {
  return gc->marked.size - gc->marked_first;
}
