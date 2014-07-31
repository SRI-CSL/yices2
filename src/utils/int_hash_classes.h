/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Hash table for maintaining equivalence classes.
 * Objects are represented by non-negative integers and
 * an equivalence relation is defined by a match predicate.
 * The table stores one representative per class and allows
 * one to quickly find it.
 */

#ifndef __INT_HASH_CLASSES_H
#define __INT_HASH_CLASSES_H

#include <stdint.h>
#include <stdbool.h>

/*
 * The behavior is customized via two functions that must be provided
 * when the table structure is initialized.
 * - hash = hash function
 * - match = equivalence predicate
 * These two function take an auxiliary pointer as first argument:
 * - hash(aux, i) must return the hash code for object i
 * - match(aux, i1, i2) must return true if i1 and i2 are in
 *   the same class
 * Requirement: elements in the same class must have the same
 * hash code.
 */
typedef uint32_t (*iclass_hash_fun_t)(void *aux, int32_t i);
typedef bool (*iclass_match_fun_t)(void *aux, int32_t i1, int32_t i2);


/*
 * Hash table
 */
typedef struct int_hclass_s {
  int32_t *data;     // hash-table
  uint32_t size;     // size of the records array, always a power of 2
  uint32_t nelems;   // number of used records
  uint32_t resize_threshold; // controls when resizing occurs

  // customization: function pointers
  void *aux;
  iclass_hash_fun_t hash;
  iclass_match_fun_t match;
} int_hclass_t;


/*
 * Marker: null_index (to mark empty records in the hash table).
 */
enum {
  null_index = -1,
};


/*
 * Default and maximal sizes
 */
// for the hash table
#define DEF_ICLASS_SIZE  64
#define MAX_ICLASS_SIZE  (UINT32_MAX/sizeof(int32_t))

// resize ratio
#define ICLASS_RESIZE_RATIO 0.6



/*
 * Initialize table
 * - n = initial table size
 *   n must be a power of 2. If n=0, the default size is used.
 * - hash_fn, match_fn, aux: customization
 */
extern void init_int_hclass(int_hclass_t *table, uint32_t n, void *aux,
                            iclass_hash_fun_t hash_fn, iclass_match_fun_t match_fn);


/*
 * Delete table
 * - free all memory
 */
extern void delete_int_hclass(int_hclass_t *table);


/*
 * Reset table: empty it
 */
extern void reset_int_hclass(int_hclass_t *table);


/*
 * Search for the representative in i's equivalence class
 * - return null_idx (-1) is there's none
 */
extern int32_t int_hclass_find_rep(int_hclass_t *table, int32_t i);


/*
 * Search for the representative in i's equivalence class
 * If there's no existing representative, add i to the table
 * and return i.
 */
extern int32_t int_hclass_get_rep(int_hclass_t *table, int32_t i);



#endif /* __INT_HASH_CLASSES_H */
