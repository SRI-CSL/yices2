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
 
#include "mcsat/watch_list_manager.h"

void watch_list_manager_construct(watch_list_manager_t* wlm, variable_db_t* var_db) {
  init_ivector(&wlm->vlist_memory, 0);
  init_pvector(&wlm->wlist_memory, 0);
  init_ivector(&wlm->all_watchers, 0);
  init_ivector(&wlm->all_lists, 0);
  init_int_hmap(&wlm->list_to_constraint_map, 0);
  init_int_hmap(&wlm->constraint_to_list_map, 0);
  wlm->var_db = var_db;
}

void watch_list_manager_destruct(watch_list_manager_t* wlm) {
  uint32_t i;
  delete_int_hmap(&wlm->list_to_constraint_map);
  delete_int_hmap(&wlm->constraint_to_list_map);
  for (i = 0; i < wlm->wlist_memory.size; ++ i) {
    ivector_t* list_vector = wlm->wlist_memory.data[i];
    if (list_vector != NULL) {
      delete_ivector(list_vector);
      safe_free(list_vector);
    }
  }
  delete_pvector(&wlm->wlist_memory);
  delete_ivector(&wlm->vlist_memory);
  delete_ivector(&wlm->all_watchers);
  delete_ivector(&wlm->all_lists);
}

static
ivector_t* watch_list_manager_get_list_of_lists(watch_list_manager_t* wlm, variable_t watcher) {
  if (watcher >= wlm->wlist_memory.size) {
    return NULL;
  } else {
    return wlm->wlist_memory.data[watcher];
  }
}

variable_list_ref_t watch_list_manager_new_list(watch_list_manager_t* wlm, const variable_t* list, uint32_t size, variable_t constraint) {
  uint32_t i;
  variable_list_ref_t ref;

  // Reference of the constraint
  ref = wlm->vlist_memory.size;

  // Copy the elements and null-terminate
  for (i = 0; i < size; ++ i) {
    ivector_push(&wlm->vlist_memory, list[i]);
  }
  ivector_push(&wlm->vlist_memory, variable_null);

  // Remember the association with the constraint
  int_hmap_add(&wlm->list_to_constraint_map, ref, constraint);
  int_hmap_add(&wlm->constraint_to_list_map, constraint, ref);

  // Remember the list
  ivector_push(&wlm->all_lists, ref);

  return ref;
}

void watch_list_manager_gc_mark(watch_list_manager_t* wlm, gc_info_t* gc_vars) {
  // Look for any lists at the current GC level
  uint32_t marked_i = 0;
  for (marked_i = gc_vars->marked_first; marked_i < gc_vars->marked.size; marked_i ++) {
    variable_t constraint_var = gc_vars->marked.data[marked_i];
    if (watch_list_manager_has_constraint(wlm, constraint_var)) {
      variable_list_ref_t list_ref = watch_list_manager_get_list_of(wlm, constraint_var);
      variable_t* vars = watch_list_manager_get_list(wlm, list_ref);
      while (*vars != variable_null) {
        gc_info_mark(gc_vars, *vars);
        vars ++;
      }
    }
  }
}

void watch_list_manager_gc_sweep_lists(watch_list_manager_t* wlm, const gc_info_t* gc_vars) {

  gc_info_t gc_lists;
  int_hmap_t new_list_to_constraint_map;
  int_hmap_t new_constraint_to_list_map;
  variable_list_ref_t new_vlist_top = 0;

  init_int_hmap(&new_list_to_constraint_map, 0);
  init_int_hmap(&new_constraint_to_list_map, 0);

  // Relocation of lists
  gc_info_construct(&gc_lists, variable_list_ref_null, false);

  // Reallocate the variable list memory:
  // - scan from bottom (using all_lists), keep list that are not collected
  // - keep map from old lists to new lists (gc_info)
  uint32_t ref_i = 0, ref_keep;
  for (ref_i = 0, ref_keep = 0; ref_i < wlm->all_lists.size; ++ ref_i) {
    // Old reference
    variable_list_ref_t old_vlist_ref = wlm->all_lists.data[ref_i];
    // Get the constraint
    variable_t old_constraint = watch_list_manager_get_constraint(wlm, old_vlist_ref);
    variable_t new_constraint = gc_info_get_reloc(gc_vars, old_constraint);
    if (new_constraint != gc_vars->null_value) {
      // Add to map list -> constraint
      int_hmap_add(&new_list_to_constraint_map, new_vlist_top, new_constraint);
      int_hmap_add(&new_constraint_to_list_map, new_constraint, new_vlist_top);
      // We keep this one
      wlm->all_lists.data[ref_keep ++] = new_vlist_top;
      gc_info_mark(&gc_lists, old_vlist_ref);
      gc_info_set_reloc(&gc_lists, old_vlist_ref, new_vlist_top);
      // Copy over the list
      variable_t list_element;
      do {
        list_element = wlm->vlist_memory.data[old_vlist_ref ++];
        assert(list_element == variable_null || gc_info_get_reloc(gc_vars, list_element) != variable_null);
        wlm->vlist_memory.data[new_vlist_top ++] = list_element;
      } while (list_element != variable_null);
    }
  }
  ivector_shrink(&wlm->all_lists, ref_keep);

  // Go through the watchers and update their watchlists using the gc_lists map
  uint32_t watch_i;
  for (watch_i = 0; watch_i < wlm->all_watchers.size; ++ watch_i) {
    variable_t watcher = wlm->all_watchers.data[watch_i];
    assert(watcher < wlm->wlist_memory.size);
    ivector_t* wlist = wlm->wlist_memory.data[watcher];
    assert(wlist != 0);
    uint32_t wlist_i, wlist_keep;
    for (wlist_i = 0, wlist_keep = 0; wlist_i < wlist->size; wlist_i ++) {
      variable_list_ref_t old_list = wlist->data[wlist_i];
      variable_list_ref_t new_list = gc_info_get_reloc(&gc_lists, old_list);
      if (new_list != variable_list_ref_null) {
        // Keep this entry
        wlist->data[wlist_keep ++] = new_list;
      }
    }
    ivector_shrink(wlist, wlist_keep);
  }

  // Swap in the map from lists to constraints
  delete_int_hmap(&wlm->list_to_constraint_map);
  wlm->list_to_constraint_map = new_list_to_constraint_map;
  delete_int_hmap(&wlm->constraint_to_list_map);
  wlm->constraint_to_list_map = new_constraint_to_list_map;

  gc_info_destruct(&gc_lists);
}

variable_t watch_list_manager_get_constraint(watch_list_manager_t* wlm, variable_list_ref_t var_list) {
  int_hmap_pair_t* find;
  find = int_hmap_find(&wlm->list_to_constraint_map, var_list);
  assert(find != NULL);
  return find->val;
}

bool watch_list_manager_has_constraint(watch_list_manager_t* wlm, variable_t constraint) {
  return int_hmap_find(&wlm->constraint_to_list_map, constraint) != NULL;
}

variable_list_ref_t watch_list_manager_get_list_of(watch_list_manager_t* wlm, variable_t constraint) {
  int_hmap_pair_t* find;
  find = int_hmap_find(&wlm->constraint_to_list_map, constraint);
  assert(find != NULL);
  return find->val;
}

variable_t* watch_list_manager_get_list(watch_list_manager_t* wlm, variable_list_ref_t var_list) {
  return wlm->vlist_memory.data + var_list;
}

void watch_list_manager_add_to_watch(watch_list_manager_t* wlm, variable_list_ref_t var_list, variable_t watcher) {
  assert(watcher != variable_null);
  if (watcher >= wlm->wlist_memory.size) {
    // Extend the vector if necessary (fill with NULL)
    size_t new_size = wlm->wlist_memory.size;
    while (watcher >= new_size) {
      new_size = new_size + new_size / 2 + 1;
    }
    resize_pvector(&wlm->wlist_memory, new_size);
    while (watcher >= wlm->wlist_memory.size) {
      pvector_push(&wlm->wlist_memory, NULL);
    }
  }

  // Create the new vector if not there
  if (wlm->wlist_memory.data[watcher] == NULL) {
    wlm->wlist_memory.data[watcher] = safe_malloc(sizeof(ivector_t));
    init_ivector(wlm->wlist_memory.data[watcher], 0);
    ivector_push(&wlm->all_watchers, watcher);
  }

  // Add the variable list to the watch-list for the watcher
  ivector_push(wlm->wlist_memory.data[watcher], var_list);
}

void remove_iterator_construct(remove_iterator_t* it, watch_list_manager_t* wlm, variable_t watcher) {
  it->wlm = wlm;
  it->watcher = watcher;
  it->keep = 0;
  it->current = 0;
}

void remove_iterator_destruct(remove_iterator_t* it) {
  while (!remove_iterator_done(it)) {
    remove_iterator_next_and_keep(it);
  }
  ivector_t* current_list = watch_list_manager_get_list_of_lists(it->wlm, it->watcher);
  if (current_list != NULL) {
    ivector_shrink(it->wlm->wlist_memory.data[it->watcher], it->keep);
  }
}

variable_list_ref_t remove_iterator_get_list_ref(const remove_iterator_t* it) {
  const ivector_t* current_list;
  current_list = watch_list_manager_get_list_of_lists(it->wlm, it->watcher);
  assert(current_list);
  return current_list->data[it->current];
}

variable_t remove_iterator_get_constraint(const remove_iterator_t* it) {
  return watch_list_manager_get_constraint(it->wlm, remove_iterator_get_list_ref(it));
}

const variable_t* remove_iterator_get_list(const remove_iterator_t* it) {
  variable_list_ref_t list_ref = remove_iterator_get_list_ref(it);
  assert(list_ref < it->wlm->vlist_memory.size);
  return it->wlm->vlist_memory.data + list_ref;
}

bool remove_iterator_done(const remove_iterator_t* it) {
  const ivector_t* current_list;
  current_list = watch_list_manager_get_list_of_lists(it->wlm, it->watcher);
  return current_list == NULL || it->current >= current_list->size;
}

void remove_iterator_next_and_keep(remove_iterator_t* it) {
  const ivector_t* current_list;
  current_list = watch_list_manager_get_list_of_lists(it->wlm, it->watcher);
  assert(current_list);
  current_list->data[it->keep ++] = current_list->data[it->current ++];
}

void remove_iterator_next_and_remove(remove_iterator_t* it) {
  it->current ++;
}

void watch_list_manager_print(watch_list_manager_t* wlm, FILE* out) {

  variable_t x;
  uint32_t i;

  for (x = 0; x < wlm->wlist_memory.size; ++ x) {
    ivector_t* list_of_lists = wlm->wlist_memory.data[x];
    if (list_of_lists) {
      fprintf(out, "lists of ");
      variable_db_print_variable(wlm->var_db, x, out);
      fprintf(out, "\n");
      for (i = 0; i < list_of_lists->size; ++ i) {
        fprintf(out, "\t");
        variable_list_ref_t list_ref = list_of_lists->data[i];
        variable_t* list = watch_list_manager_get_list(wlm, list_ref);
        while (*list != variable_null) {
          variable_db_print_variable(wlm->var_db, x, out);
          fprintf(out, " ");
          list ++;
        }
        fprintf(out, "\n");
        fprintf(out, "\tfrom ");
        variable_t cstr = watch_list_manager_get_constraint(wlm, list_ref);
        variable_db_print_variable(wlm->var_db, cstr, out);
        fprintf(out, "\n");
      }
    }
  }

}

uint32_t watch_list_manager_size(const watch_list_manager_t* wlm) {
  return wlm->all_lists.size;
}
