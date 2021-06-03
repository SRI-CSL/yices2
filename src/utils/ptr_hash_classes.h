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

/*
 * HASH TABLE FOR MAINTAINING EQUIVALENCE CLASSES
 *
 * Objects are represented by void* pointers and
 * an equivalence relation is defined by a match predicate.
 * The table stores one representative per class and allows
 * one to quickly find it.
 *
 * This module is similar to int_hash_classes, except that is uses pointers.
 */

#ifndef __PTR_HASH_CLASSES_H
#define __PTR_HASH_CLASSES_H

#include <stdint.h>
#include <stdbool.h>

/*
 * The behavior is customized via two functions that must be provided
 * when the table is initialized.
 * - hash = hash function
 * - match = equivalence predicate
 * These two function take an auxiliary pointer as first argument:
 * - hash(aux, ptr) must return the hash code for ptr
 * - match(aux, ptr1, ptr2) must return true if ptr1 and ptr2 are in
 *   the same class
 */
typedef uint32_t (*pclass_hash_fun_t)(const void *aux, const void *ptr);
typedef bool (*pclass_match_fun_t)(const void *aux, const void *ptr1, const void *ptr2);

/*
 * Hash table
 */
typedef struct ptr_hclass_s {
  void **data;       // hash-table
  uint32_t size;     // size of the data array, always a power of 2
  uint32_t nelems;   // number of non-NULL elements in the table
  uint32_t resize_threshold; // controls when resizing occurs

  // customization: function pointers
  void *aux;
  pclass_hash_fun_t hash;
  pclass_match_fun_t match;
} ptr_hclass_t;


// default + maximal size
#define DEF_PCLASS_SIZE 64
#define MAX_PCLASS_SIZE (UINT32_MAX/sizeof(void *))

// resize ratio
#define PCLASS_RESIZE_RATIO 0.6



/*
 * Initialize table
 * - n = initial table size
 *   n must be a power of 2. If n=0, the default size is used.
 * - hash_fn, match_fn, aux: customization
 */
extern void init_ptr_hclass(ptr_hclass_t *table, uint32_t n, void *aux,
                            pclass_hash_fun_t hash_fn, pclass_match_fun_t match_fn);


/*
 * Delete table
 * - free all memory
 */
extern void delete_ptr_hclass(ptr_hclass_t *table);


/*
 * Reset table: empty it
 */
extern void reset_ptr_hclass(ptr_hclass_t *table);


/*
 * Search for the representative in p's equivalence class
 * - return NULL is there's none
 */
extern void *ptr_hclass_find_rep(const ptr_hclass_t *table, void *p);


/*
 * Search for the representative in p's equivalence class
 * If there's no existing representative, add p to the table
 * and return p.
 */
extern void *ptr_hclass_get_rep(ptr_hclass_t *table, void *p);



#endif /* __PTR_HASH_CLASSES_H */
