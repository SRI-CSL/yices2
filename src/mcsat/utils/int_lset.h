/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */
 
#ifndef INT_LSET_H_
#define INT_LSET_H_

#include "utils/int_vectors.h"
#include "mcsat/gc.h"

/** Reference for the list elements */
typedef int32_t int_lset_element_ref_t;

#define int_lset_element_ref_null (-1)
#define int_lset_element_ref_null_and_never_used (-2)

typedef struct {
  /** List element */
  int32_t value;
  /** The next one */
  int_lset_element_ref_t next;
} int_lset_element_t;

/** Map from integers to lists of integers. */
typedef struct {

  /** Memory for elements */
  int_lset_element_t* memory;

  /** Size of the used cells */
  uint32_t size;

  /** Capacity of the memory */
  uint32_t capacity;

  /** Free list */
  ivector_t free_list;

  /** Map from keys to lists */
  ivector_t key_to_list_map;

  /** List of used slots */
  ivector_t slot_list;

} int_lset_t;

/** Construct the list set */
void int_lset_construct(int_lset_t* lset);

/** Destruct the list manager */
void int_lset_destruct(int_lset_t* lset);

/** Add the value to the list of the key */
void int_lset_add(int_lset_t* lset, int32_t key, int32_t value);

/** Remove the list */
void int_lset_remove(int_lset_t* lset, int32_t key);

/** Check whether the list exists */
bool int_lset_has_list(const int_lset_t* lset, int32_t key);

/** Relocate the elements of the lists */
void int_lset_reloc_elements(int_lset_t* lset, const gc_info_t* gc_info);

typedef struct {

  /** The trigger literal */
  int32_t key;

  /** The watch-list manager */
  int_lset_t* lset;

  /** The current and previous element */
  int_lset_element_ref_t current, prev;

} int_lset_iterator_t;

/** Constructs a iterator for the key. */
void int_lset_iterator_construct(int_lset_iterator_t* it, int_lset_t* lset, int32_t key);

/** Destruct the iterator and remove any elements marked to remove */
void int_lset_iterator_destruct(int_lset_iterator_t* it);

/** Returns the current value */
int32_t* int_lset_iterator_get(const int_lset_iterator_t* it);

/** Returns true if the iterator is finished */
bool int_lset_iterator_done(const int_lset_iterator_t* it);

/** Move the iterator to the next list and keep the current list */
void int_lset_iterator_next_and_keep(int_lset_iterator_t* it);

/** Move the iterator to the next list and remove the current lits */
void int_lset_iterator_next_and_remove(int_lset_iterator_t* it);

#endif /* INT_int_lset_H_ */
