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
 * Vectors to store the classes (use a hidden header)
 */
typedef struct ipart_vector_s {
  uint32_t capacity;
  uint32_t size;   // number of elements stored
  int32_t data[0];   // real size = capacity
} ipart_vector_t;



/*
 * The behavior is customized via two functions that must be provided
 * when the ipart structure is initialized.
 * - hash = hash function
 * - match = equivalence predicate
 * These two function take an auxiliary pointer as first argument:
 * - hash(aux, i) must return the hash code for object i
 * - match(aux, i1, i2) must return true if i1 and i2 are in 
 *   the same class
 */
typedef uint32_t (*ipart_hash_fun_t)(void *aux, int32_t i);
typedef bool (*ipart_match_fun_t)(void *aux, int32_t i1, int32_t i2);


/*
 * Hash table + array of classes.
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
 * Marker: null_index (to mark empty records in the hash table).
 */
enum {
  null_index = -1,
};


/*
 * Default and maximal sizes
 */
// for the hash table
#define DEF_IPART_SIZE  64
#define MAX_IPART_SIZE  (UINT32_MAX/sizeof(ipart_rec_t))

// for ipart_vector
#define DEF_IPART_VSIZE 10
#define MAX_IPART_VSIZE (((uint32_t)(UINT32_MAX-sizeof(ipart_vector_t)))/sizeof(int32_t))

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





/***************************
 *  ACCESS TO THE CLASSES  *
 **************************/

/*
 * Each class is a vector stored in pp->classes that
 * contains at least two objects. 
 *
 * The functions below can be used to scan the classes,
 * using something like:
 *
 *   n = int_partition_nclasses(pp);
 *   for (i=0; i<n; i++) {
 *     v = pp->classes[i];
 *     // ipv_size(v) gives the number of elements in v
 *     ...
 *   }
 */


/*
 * Number of classes
 */
static inline uint32_t int_partition_nclasses(ipart_t *pp) {
  return pp->nclasses;
}

/*
 * Size of a class vector v
 */
static inline ipart_vector_t *ipv_header(int32_t *v) {
  return (ipart_vector_t *) (((char *) v) - offsetof(ipart_vector_t, data));
}

static inline uint32_t ipv_size(int32_t *v) {
  return ipv_header(v)->size;
}

static inline uint32_t ipv_capacity(int32_t *v) {
  return ipv_header(v)->capacity;
}



#endif /* __INT_PARTITIONS_H */
