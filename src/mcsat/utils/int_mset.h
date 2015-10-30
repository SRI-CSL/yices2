/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
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

/** Remove an element (all occurances) */
void int_mset_remove_all(int_mset_t* set, int32_t x);

/** Remove an element (one occurance) */
void int_mset_remove_one(int_mset_t* set, int32_t x);

/** Returns the number of occurances */
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
