/*
 * Term and Type Stores for testing
 */

#ifndef __STORES_H
#define __STORES_H

#include <stdio.h>
#include <inttypes.h>

#include "int_vectors.h"
#include "bitvectors.h"

#include "yices.h"

#ifdef MINGW
static inline long int random(void) {
  return rand();
}
#endif

extern void show_types(FILE* output);
extern void show_terms(FILE* output);

/*
 * TYPE STORE
 */

/*
 * Type store:
 * - size = its size
 * - ntypes = number of types
 * - type = array where the types are stored
 * - terms[i] = all the terms of type type[i]
 */
typedef struct type_store_s {
  uint32_t size;
  uint32_t ntypes;
  type_t *type;
  ivector_t *terms;
} type_store_t;


#define TYPE_STORE_DEF_SIZE 100
#define TYPE_STORE_MAX_SIZE (UINT32_MAX/sizeof(ivector_t))


/*
 * Initialization
 */
extern void init_type_store(type_store_t *store);

/*
 * Make the store 50% larger
 */
extern void extend_type_store(type_store_t *store);


/*
 * Allocate a new index i and initialize terms[i]
 */
extern uint32_t type_store_alloc_index(type_store_t *store);


/*
 * Get the index of type tau:
 * - if tau is not in the store, add it
 */
extern uint32_t type_store_get_type(type_store_t *store, type_t tau);

/*
 * Add term t to the store:
 * - t is added as last element of store->terms[i] where i = index for type of t
 */
extern void type_store_add_term(type_store_t *store, term_t t);

/*
 * Get the index of type tau.
 * - return store->ntypes is tau is not present in the store.
 */
extern uint32_t type_store_type_index(type_store_t *store, type_t tau);

/*
 * Delete the store
 */
extern void delete_type_store(type_store_t *store);

/*
 * TERM STORE
 */

/*
 * Term store:
 * - term = array of all terms
 * - mark = bitvectore: mark[t] = 1 if t is present in terms
 */
typedef struct term_store_s {
  uint32_t size;
  uint32_t nterms;
  term_t *term;
  uint32_t max_term;  // size of mark bitvector
  byte_t *mark;
} term_store_t;

#define TERM_STORE_DEF_SIZE 1000
#define TERM_STORE_MAX_SIZE (UINT32_MAX/sizeof(term_t))

#define TERM_STORE_DEF_MSIZE 100

/*
 * Initialize store
 */
extern void init_term_store(term_store_t *store);

/*
 * Extend: make the term array 50% larger
 */
extern void extend_term_store(term_store_t *store);

/*
 * Get a new index i to store a term
 */
extern uint32_t term_store_alloc_index(term_store_t *store);



/*
 * Mark term t
 */
extern void term_store_mark_term(term_store_t *store, term_t t);

/*
 * Check whether t is present in store
 */
extern bool term_store_contains_term(term_store_t *store, term_t t);


/*
 * Add term t to the store (t should not be present)
 */
extern void term_store_add_term(term_store_t *store, term_t t);

/*
 * Delete store
 */
extern void delete_term_store(term_store_t *store);


/*
 * SUPPORT FOR RANDOM TESTING
 */

/*
 * Sampling: select one type in store that satifies predicate p
 */
typedef bool (*predicate_t)(type_t tau);

extern type_t type_store_sample(type_store_t *store, predicate_t p);

/*
 * Sampling: select one of the terms of type tau
 * - return NULL_TERM if there's nothing of type tau in the store.
 */
extern term_t type_store_sample_terms(type_store_t *store, type_t tau);

/*
 * Term sampling: get a term that satisfies the predicate P(tau, t).
 * Give priority to small terms (i.e., those created early).
 */
typedef bool (*term_pred_t)(type_t tau, term_t t);

extern term_t term_array_sample(term_t *a, uint32_t n, type_t tau, term_pred_t p);

extern term_t term_store_sample(term_store_t *store, type_t tau, term_pred_t p);

  
#endif /* __STORES_H */

