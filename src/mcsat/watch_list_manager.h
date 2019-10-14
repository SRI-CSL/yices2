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
 
#ifndef ASSIGNED_WATCHER_H_
#define ASSIGNED_WATCHER_H_

#include "mcsat/variable_db.h"

#include <stdio.h>

/** Type of reference to the list */
typedef int32_t variable_list_ref_t;

#define variable_list_ref_null (-1)

/**
 * Manager to store lists of variables that appear in a constraint. Lists of
 * variables can be added to the manager and are given an id (ref).
 *
 * For example given a constraint C = (x + y + z > 0), we can associate the
 * variable list [x, y, z] to C, by adding it to the manager, obtaining an
 * internal reference C_ref. We can then add the list to the watch-list of a
 * variable, for example x, so that when x gets assigned we can check if the
 * constraint C became univariate.
 *
 * For the purposes of such checks there is a remove iterator below, that can
 * be used to remove C_ref from the watch-list of x.
 */
typedef struct {

  /** Memory where the variable lists are stored (null terminated) */
  ivector_t vlist_memory;

  /**
   * Memory of where all the watch-lists are stored (indexed by variable).
   * Each variable maps to a ivector of references into vlist_memory.
   */
  pvector_t wlist_memory;

  /** List of all watchers ever added */
  ivector_t all_watchers;

  /** List of all lists ever created */
  ivector_t all_lists;

  /** Map from variable lists to constraints */
  int_hmap_t list_to_constraint_map;

  /** Map from variable constraints to variable lists */
  int_hmap_t constraint_to_list_map;

  /** The variable database */
  variable_db_t* var_db;

} watch_list_manager_t;

/** Construct a watch-list manager */
void watch_list_manager_construct(watch_list_manager_t* wlm, variable_db_t* var_db);

/** Destruct the watch-list manager */
void watch_list_manager_destruct(watch_list_manager_t* wlm);

/** Returns the size of the manage (number of lists) */
uint32_t watch_list_manager_size(const watch_list_manager_t* wlm);

/** Print the manager */
void watch_list_manager_print(watch_list_manager_t* wlm, FILE* out);

/**
 * Add a new list of variables to the manager and associate it with the
 * given constraint.
 */
variable_list_ref_t watch_list_manager_new_list(watch_list_manager_t* wlm, const variable_t* list, uint32_t size, variable_t constraint);

/** Returns the constraint associated with the variable list. */
variable_t watch_list_manager_get_constraint(watch_list_manager_t* wlm, variable_list_ref_t var_list);

/** Check if the constraint is managed by this manager */
bool watch_list_manager_has_constraint(watch_list_manager_t* wlm, variable_t constraint);

/** Returns the variable list associated with the constraint. */
variable_list_ref_t watch_list_manager_get_list_of(watch_list_manager_t* wlm, variable_t constraint);

/** Get the actual list */
variable_t* watch_list_manager_get_list(watch_list_manager_t* wlm, variable_list_ref_t var_list);

/**
 * Add the given variable list to the watch-list of the given watcher variable.
 */
void watch_list_manager_add_to_watch(watch_list_manager_t* wlm, variable_list_ref_t var_list, variable_t watcher);

/** Mark the variables in the lists */
void watch_list_manager_gc_mark(watch_list_manager_t* wlm, gc_info_t* gc_vars);

/** Sweep the variables in the lists */
void watch_list_manager_gc_sweep_lists(watch_list_manager_t* wlm, const gc_info_t* gc_vars);

typedef struct {

  /** The watch-list manager */
  watch_list_manager_t* wlm;

  /** Index of the watch-list we're iterating */
  variable_t watcher;

  /** Element after the last element to keep in the watch-list */
  uint32_t keep;

  /** The current element */
  uint32_t current;

} remove_iterator_t;

/** Constructs a remove iterator for the given watcher. */
void remove_iterator_construct(remove_iterator_t* it, watch_list_manager_t* wlm, variable_t watcher);

/** Destruct a remove iterator for the given watcher and removes any elements marked to remove */
void remove_iterator_destruct(remove_iterator_t* it);

/** Returns the current list reference */
variable_list_ref_t remove_iterator_get_list_ref(const remove_iterator_t* it);

/** Returns the current list (null terminated, internal memory) */
const variable_t* remove_iterator_get_list(const remove_iterator_t* it);

/** Returns the constrains of the iterator */
variable_t remove_iterator_get_constraint(const remove_iterator_t* it);

/** Returns true if the iterator is finished */
bool remove_iterator_done(const remove_iterator_t* it);

/** Move the iterator to the next list and keep the current list */
void remove_iterator_next_and_keep(remove_iterator_t* it);

/** Move the iterator to the next list and remove the current lits */
void remove_iterator_next_and_remove(remove_iterator_t* it);

#endif /* ASSIGNED_WATCHER_H_ */
