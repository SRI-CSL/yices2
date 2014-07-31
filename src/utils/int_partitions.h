/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Data structure to collect classes of objects. This is parameterized
 * by an equivalence relation and it's intended to construct the
 * classes that contain at least two objects.  Objects are identified
 * by a non-negative integer id.
 * - equivalence classes are defined by a match predicates
 * - a hash function must map two objects of the same class to
 *   the same hash code.
 */

#ifndef __INT_PARTITIONS_H
#define __INT_PARTITIONS_H

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>


/*
 * Records stored in the hash table
 * - each record includes <hash, class id, data>
 * - class id is an integer (either -1 or an integer between 0 and nclasses)
 */
typedef struct ipart_rec_s {
  uint32_t hash;
  int32_t cid;
  int32_t data;
} ipart_rec_t;


/*
 * The behavior is customized via two functions that must be provided
 * when the ipart structure is initialized.
 * - hash = hash function
 * - match = equivalence predicate
 * These two functions take an auxiliary pointer as first argument:
 * - hash(aux, i) must return the hash code for object i
 * - match(aux, i1, i2) must return true if i1 and i2 are in
 *   the same class
 */
typedef uint32_t (*ipart_hash_fun_t)(void *aux, int32_t i);
typedef bool (*ipart_match_fun_t)(void *aux, int32_t i1, int32_t i2);


/*
 * Each class is a vector stored in pp->classes that
 * contains at least two objects.
 *
 * To scan the classes, use something like this:
 *
 *   n = int_partition_nclasses(pp);
 *   for (i=0; i<n; i++) {
 *     v = pp->classes[i];
 *     // then the functions from index_vectors.h can be used
 *     // iv_size(v): number of elements in the class
 *     ...
 *   }
 */


/*
 * Hash table + array of classes.
 *
 * Each class is stored as an integer array, with a hidden header
 * (cf. index_vector.h).
 */
typedef struct ipart_s {
  ipart_rec_t *records;  // hash-table
  int32_t **classes;     // classes[i] is an array of integers
  uint32_t size;         // size of the records array, always a power of 2
  uint32_t nelems;       // number of used records
  uint32_t resize_threshold; // controls when resizing occurs
  uint32_t csize;        // size of the arrray classes
  uint32_t nclasses;     // number of classes

  // customization: function pointers
  void *aux;
  ipart_hash_fun_t hash;
  ipart_match_fun_t match;
} ipart_t;


/*
 * Marker: not_an_index (to mark empty records in the hash table).
 */
enum {
  not_an_index = -1,
};


/*
 * Default and maximal sizes
 */
// for the hash table
#define DEF_IPART_SIZE  64
#define MAX_IPART_SIZE  (UINT32_MAX/sizeof(ipart_rec_t))

// for the classes array
#define DEF_IPART_CSIZE 10
#define MAX_IPART_CSIZE (UINT32_MAX/sizeof(int32_t))

// resize ratio
#define IPART_RESIZE_RATIO 0.6



/*
 * Initialize pp
 * - n = hash table size:
 *   n must be a power of 2. If n=0, the default size is used.
 * - hash_fn, match_fn, aux: customization
 * - the table is empty, classes is not allocated yet (NULL).
 */
extern void init_int_partition(ipart_t *pp, uint32_t n, void *aux,
                               ipart_hash_fun_t hash_fn, ipart_match_fun_t match_fn);


/*
 * Delete pp
 * - free all memory
 */
extern void delete_int_partition(ipart_t *pp);


/*
 * Reset pp: empty its content
 */
extern void reset_int_partition(ipart_t *pp);


/*
 * Add i to the table:
 * - if there's a index j in the table that matches i
 *   then j is added to i's class. If i has no class attached
 *   yet, then a new class vector is allocated and both i and
 *   j are added to that class.
 */
extern void int_partition_add(ipart_t *pp, int32_t i);



/*
 * Number of classes
 */
static inline uint32_t int_partition_nclasses(ipart_t *pp) {
  return pp->nclasses;
}



#endif /* __INT_PARTITIONS_H */
