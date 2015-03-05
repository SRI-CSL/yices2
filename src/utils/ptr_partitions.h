/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Data structure to collect classes of objects. This is intended
 * to be used to construct the classes that contain at least two objects.
 * Objects are stored abstractly as (void*) pointers.
 * - equivalence classes are defined by a match predicates
 * - a hash function must map two objects of the same class to
 *   the same hash code.
 */

#ifndef __PTR_PARTITIONS_H
#define __PTR_PARTITIONS_H

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>


/*
 * Records stored in the hash table
 * - each record includes <hash, class id, ptr>
 * - class id is an integer (either -1 or an integer between 0 and nclasses)
 */
typedef struct ppart_rec_s {
  uint32_t hash;
  int32_t cid;
  void *data;
} ppart_rec_t;


/*
 * Vectors to store the classes (use a hidden header)
 */
typedef struct ppart_vector_s {
  uint32_t capacity;
  uint32_t size;   // number of elements stored
  void *data[0];   // real size = capacity
} ppart_vector_t;



/*
 * The behavior is customized via two functions that must be provided
 * when the ppart structure is initialized.
 * - hash = hash function
 * - match = equivalence predicate
 * These two function take an auxiliary pointer as first argument:
 * - hash(aux, ptr) must return the hash code for ptr
 * - match(aux, ptr1, ptr2) must return true if ptr1 and ptr2 are in
 *   the same class
 */
typedef uint32_t (*ppart_hash_fun_t)(void *aux, void *ptr);
typedef bool (*ppart_match_fun_t)(void *aux, void *ptr1, void *ptr2);


/*
 * Hash table + array of classes.
 */
typedef struct ppart_s {
  ppart_rec_t *records;  // hash-table
  void ***classes;       // class[i] is an array of (void*) pointers
  uint32_t size;         // size of the records array, always a power of 2
  uint32_t nelems;       // number of used records
  uint32_t resize_threshold; // controls when resizing occurs
  uint32_t csize;        // size of the array classes
  uint32_t nclasses;     // number of classes

  // customization: function pointers
  void *aux;
  ppart_hash_fun_t hash;
  ppart_match_fun_t match;
} ppart_t;



/*
 * Default and maximal sizes
 */
// for the hash table
#define DEF_PPART_SIZE  64
#define MAX_PPART_SIZE  (UINT32_MAX/sizeof(ppart_rec_t))

// for ppart_vector
#define DEF_PPART_VSIZE 10
#define MAX_PPART_VSIZE (((uint32_t)(UINT32_MAX-sizeof(ppart_vector_t)))/sizeof(void*))

// for the classes array
#define DEF_PPART_CSIZE 10
#define MAX_PPART_CSIZE (UINT32_MAX/sizeof(void **))

// resize ratio
#define PPART_RESIZE_RATIO 0.6



/*
 * Initialize pp
 * - n = hash table size:
 *   n must be a power of 2. If n=0, the default size is used.
 * - hash_fn, match_fn, aux: customization
 * - the table is empty, classes is not allocated yet (NULL).
 */
extern void init_ptr_partition(ppart_t *pp, uint32_t n, void *aux,
                               ppart_hash_fun_t hash_fn, ppart_match_fun_t match_fn);


/*
 * Delete pp
 * - free all memory
 */
extern void delete_ptr_partition(ppart_t *pp);


/*
 * Reset pp: empty its content
 */
extern void reset_ptr_partition(ppart_t *pp);


/*
 * Add ptr to the table:
 * - if there's a pointer p in the table that matches ptr
 *   then ptr is added to p's class. If p has no class attached
 *   yet, then a new class vector is allocated and both p and
 *   ptr are added to that class.
 */
extern void ptr_partition_add(ppart_t *pp, void *ptr);


/*
 * Return the index of the partition vector that contains ptr
 * - return -1 if there's no such vector
 */
extern int32_t ptr_partition_get_index(ppart_t *pp, void *ptr);


/*
 * Check whether pp is empty
 */
static inline bool ptr_partition_is_empty(ppart_t *pp) {
  return pp->nelems == 0;
}



/***************************
 *  ACCESS TO THE CLASSES  *
 **************************/

/*
 * Number of classes
 */
static inline uint32_t ptr_partition_nclasses(ppart_t *pp) {
  return pp->nclasses;
}

/*
 * Size of a class vector v
 */
static inline ppart_vector_t *ppv_header(void **v) {
  return (ppart_vector_t *) (((char *) v) - offsetof(ppart_vector_t, data));
}

static inline uint32_t ppv_size(void **v) {
  return ppv_header(v)->size;
}

static inline uint32_t ppv_capacity(void **v) {
  return ppv_header(v)->capacity;
}



#endif /* __PTR_PARTITIONS_H */
