/*
 * Lists of integers
 */

#ifndef __ILISTS_H
#define __ILISTS_H

#include <stdint.h>

#include "object_stores.h"
#include "int_vectors.h"

/*
 * Elements in a list
 * NULL is the empty list
 */
typedef struct ilist_s ilist_t;

struct ilist_s {
  ilist_t *next;
  int32_t elem;
};


/*
 * Initialize an object store for these elements
 * - the store must be passed to all list operations
 */
extern void init_ilist_store(object_store_t *store);


/*
 * Delete and reset the store: just call the object_store functions
 */
static inline void delete_ilist_store(object_store_t *store) {
  delete_objstore(store);
}

static inline void reset_ilist_store(object_store_t *store) {
  reset_objstore(store);
}


/*
 * LIST CONSTRUCTORS
 */

/*
 * Add x to l: x is added as head of the list
 */
extern ilist_t *ilist_cons(object_store_t *store, int32_t x, ilist_t *l);


/*
 * Add a[0 ... n-1] to list l:
 * - same as (cons a[0] (cons a[1] .... (cons a[n-1] l) ... ))
 */
extern ilist_t *ilist_cons_array(object_store_t *store, uint32_t n, int32_t *a, ilist_t *l);


/*
 * Create a singleton list that contains just x
 */
static inline ilist_t *ilist_singleton(object_store_t *store, int32_t x) {
  return ilist_cons(store, x, NULL);
}


/*
 * Convert a[0 ... n-1] to a list
 */
static inline ilist_t *ilist_of_array(object_store_t *store, uint32_t n, int32_t *a) {
  return ilist_cons_array(store, n, a, NULL);
}


/*
 * Append l1 and l2: l1 is first
 */
extern ilist_t *ilist_append(object_store_t *store, ilist_t *l1, ilist_t *l2);



/*
 * QUERIES
 */

/*
 * Length of list l
 */
extern uint32_t ilist_length(const ilist_t *l);


/*
 * Collect the elements of l into vector v
 * - this adds all elements of l in order, at the end of v
 * - v is not reset 
 */
extern void ilist_collect(const ilist_t *l, ivector_t *v);



#endif /* __ILISTS_H */
