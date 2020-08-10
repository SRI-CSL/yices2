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
 
#ifndef MCSAT_INT_MSET_H_
#define MCSAT_INT_MSET_H_

#include "utils/int_vectors.h"
#include "utils/int_hash_map.h"

/**
 * A collection (multiset) of elements (multiples of the same counts twice).
 */
typedef struct {
  /** Map from elements to the number of times they appear */
  int_hmap_t count_map;
  /** Map from elements to their index in the element list */
  int_hmap_t element_list_position;
  /** List of all elements that appear in the collection. */
  ivector_t element_list;
  /** Null element to use in the list for removed elements */
  uint32_t null_element;
  /** Is the list of elements compact (no non-existants elements)? */
  bool is_compact;
  /** Size of the set (total number with repeats) */
  uint32_t size;
} int_mset_t;

/** Construct the set */
void int_mset_construct(int_mset_t* set, uint32_t null_element);

/** Add an element */
void int_mset_add(int_mset_t* set, int32_t x);

/** Add an element n times */
void int_mset_add_n(int_mset_t* set, int32_t x, uint32_t n);

/** Remove an element (all occurrences) */
void int_mset_remove_all(int_mset_t* set, int32_t x);

/** Remove an element (one occurrence) */
void int_mset_remove_one(int_mset_t* set, int32_t x);

/** Returns the number of occurrences */
uint32_t int_mset_contains(const int_mset_t* set, int32_t x);

/** Clear the collection */
void int_mset_clear(int_mset_t* set);

/** Destruct the set */
void int_mset_destruct(int_mset_t* set);

/* Make it compact, i.e. remove non-existent variables from the element list */
void int_mset_compact(int_mset_t* set);

/** Get the list of elements (no duplicates) */
ivector_t* int_mset_get_list(int_mset_t* set);

#endif /* INT_MSET_H_ */
