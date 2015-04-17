/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Abstract objects used by the array solver to construct models.
 * - an array variable is modeled as a mapping from [tau1 ... tau_n -> sigma]
 * - tau_1 ... tau_n and sigma are types defined in the global type table
 *
 * An array A is specified via a finite number of mappings
 *        [x_11 ... x_1n -> y_1]
 *           ...
 *        [x_m1 ... x_mn -> y_m]
 *   + a default value y_0
 * The tuples (x_i1, ..., x_in) are pairwise distinct.
 * This means
 *     A[x_i1 ... x_in] = y_i for (i=1, ..., m)
 *     A[i_1, ..., i_n] = y_0 for all other input
 *
 * This module provides support for building the objects x_ij and y_k,
 * and for representing the arrays and mappings.
 * - Each atomic element x_ij or y_k is either an egraph label
 *   or a fresh constant of some type tau created by the solver.
 * - The egraph can later convert the abstract values into concrete objects.
 */

#ifndef __ABSTRACT_VALUES_H
#define __ABSTRACT_VALUES_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "model/concrete_values.h"
#include "solvers/egraph/egraph_base_types.h"
#include "terms/types.h"
#include "utils/bitvectors.h"
#include "utils/int_hash_tables.h"


/*
 * Abstract values are called particles. They are identified by an
 * integer index in a global table. We use hash consing. There are
 * three kinds of abstract values:
 *  LABEL (egraph label)
 *  FRESH (fresh constant)
 *  TUPLE
 *
 * We use TUPLE to represent n-ary maps. Rather than writing
 *  [x_i1, ..., x_in -> y_i]
 * we construct t = [x_i1, ..., x_in] and store [t -> y_i] in the
 * array descriptor.
 */

/*
 * Indices
 */
typedef int32_t particle_t;

/*
 * null value
 */
enum {
  null_particle = -1,
};

/*
 * Particle types
 */
typedef enum {
  LABEL_PARTICLE,
  FRESH_PARTICLE,
  TUPLE_PARTICLE,
} particle_kind_t;


/*
 * Descriptors: either an integer or a pointer
 */
typedef union particle_desc_u {
  int32_t integer;
  void *ptr;
} particle_desc_t;


/*
 * Tuple descriptor
 */
typedef struct particle_tuple_s {
  uint32_t nelems;
  particle_t elem[0]; // real size = nelems
} particle_tuple_t;


#define MAX_PARTICLE_TUPLE_ARITY (UINT32_MAX/8)


/*
 * Particle table
 * - valid objects have indices between 0 and nobjects - 1
 * - for each object i:
 *     kind[i] = its kind
 *     desc[i] = its descriptor
 *     concrete[i] = its concretization
 *     mark[i] = general purpose mark bit
 * - other components:
 *     htbl = hash table for hash consing
 */
typedef struct particle_table_s {
  uint32_t size;
  uint32_t nobjects;
  uint8_t *kind;
  particle_desc_t *desc;
  value_t *concrete;
  byte_t *mark;

  int_htbl_t htbl;
} particle_table_t;


#define DEF_PARTICLE_TABLE_SIZE 200
#define MAX_PARTICLE_TABLE_SIZE (UINT32_MAX/sizeof(particle_desc_t))



/*
 * Descriptor for a set of particles of a tuple of types [tau_0,..., tau_n-1]
 * - arity = number of types
 * - type[0,.,,n-1] = tau_0 to tau_n-1
 * For a simple type tau, we use n=1 and type[0] = tau
 * - data = vector that contains all particles of that type
 * - size = size of array data
 * - nelems = number of elements in the array
 */
typedef struct particle_set_s {
  uint32_t size;
  uint32_t nelems;
  particle_t *data;
  uint32_t arity;
  type_t type[0];   // real size = arity
} particle_set_t;


#define DEF_PSET_SIZE 20
#define MAX_PSET_SIZE ((UINT32_MAX - sizeof(particle_set_t))/sizeof(type_t))


/*
 * Table of these descriptors
 * - pset[0 ... n-1] = all sets
 * - size = size of the set array
 * - nsets = n
 * - there shouldn't be too many different types so we just use
 *   sequential search to find the pset for a given type
 *   (or tuple of types).
 */
typedef struct pset_table_s {
  uint32_t size;
  uint32_t nsets;
  particle_set_t **set;
} pset_table_t;


#define DEF_PSET_TABLE_SIZE 10
#define MAX_PSET_TABLE_SIZE (UINT32_MAX/sizeof(particle_set_t *))



/*
 * Global store:
 * - store particles and particle_sets
 * + pointer to the global type table
 *
 * Auxiliary buffers and arrays for constructing fresh tuples
 * of types tau[0] ... tau[n-1]
 * - rank array: for a particle x of type tau, rank[x] = i
 *   iff set[tau]->data[i] = x
 * - rank_size = size of the rank array
 * - card array: card[k] = number of elements in tau[k]
 * - aux array: must have size n
 */
typedef struct pstore_s {
  type_table_t *types;
  particle_table_t ptbl;
  pset_table_t psets;
  // buffers
  uint32_t rank_size;
  uint32_t card_size;
  int32_t *rank;
  uint32_t *card;
  int32_t *aux;
} pstore_t;




/*
 * Initialize a store:
 * - use default sizes for both ptbl and psets
 * - ttbl = the type table
 */
extern void init_pstore(pstore_t *store, type_table_t *ttbl);


/*
 * Delete a store
 */
extern void delete_pstore(pstore_t *store);


/*
 * Get a particle for an egraph label l
 * - tau = the particle type
 * If that particle already exists it's returned.
 * Otherwise it's created and added to the particle_set for tau
 */
extern particle_t pstore_labeled_particle(pstore_t *store, elabel_t l, type_t tau);


/*
 * Create a fresh particle of type tau
 * - the particle is added to the set for tau
 */
extern particle_t pstore_fresh_particle(pstore_t *store, type_t tau);


/*
 * Create a tuple particle:
 * - a[0] ... a[n-1] = components
 * - tau[0] ... tau[n-1] = types of each component
 */
extern particle_t pstore_tuple_particle(pstore_t *store, uint32_t n, particle_t *a, type_t *tau);


/*
 * Map particle i to a concrete value v
 * - i must be a valid particle index
 * - until this function is called, concrete[i] is equal to null_value
 */
static inline void pstore_make_concrete(pstore_t *store, particle_t i, value_t v) {
  assert(0 <= i && i < store->ptbl.nobjects);
  store->ptbl.concrete[i] = v;
}



/*
 * Get the particle set for type tau
 * - return NULL if there are no particles of that type
 */
extern particle_set_t *pstore_find_set_for_type(pstore_t *store, type_t tau);


/*
 * Get the particle set for the tuple type (tau[0], ..., tau[n-1])
 * - return NULL if there are no particles of that type.
 */
extern particle_set_t *pstore_find_set_for_types(pstore_t *store, uint32_t n, type_t *tau);



/*
 * Return a particle of type tau that's distinct from all elements
 * of array a.
 * - p = size of array a
 * - return null_particle if that's not possible (i.e., tau is finite
 *   and all its members occur in a).
 */
extern particle_t get_distinct_particle(pstore_t *store, type_t tau, uint32_t p, particle_t *a);


/*
 * Return a (fresh) particle of that tau that's distinct from all
 * other particles of that type.
 * - return null_particle if that's not possible.
 */
extern particle_t get_new_particle(pstore_t *store, type_t tau);


/*
 * Variant 1: get any particle of type tau
 */
static inline particle_t get_some_particle(pstore_t *store, type_t tau) {
  return get_distinct_particle(store, tau, 0, NULL);
}


/*
 * Variant 2: get a particle distinct from x
 */
static inline particle_t get_another_particle(pstore_t *store, type_t tau, particle_t x) {
  return get_distinct_particle(store, tau, 1, &x);
}



/*
 * Return a particle of type (tau[0], ..., tau[n-1]) that's distinct
 * from all particles in array a.
 * - n must be a least 2
 * - p = size of the array a
 * - return null_particle if that's not possible
 */
extern particle_t get_distinct_tuple(pstore_t *store, uint32_t n, type_t *tau,
                                     uint32_t p, particle_t *a);



/*
 * Return a particle of type (tau[0], ..., tau[n-1]) that's distinct
 * from all other particles of that type in the store.
 * - n must be at least 2
 * - return null_particle if that's not possible.
 */
extern particle_t get_new_tuple(pstore_t *store, uint32_t n, type_t *tau);



/*
 * Number of particles in the store
 */
static inline uint32_t pstore_num_particles(pstore_t *store) {
  return store->ptbl.nobjects;
}


/*
 * Get kind and descriptor of a particle
 */
static inline bool valid_particle(pstore_t *store, particle_t i) {
  return 0 <= i && i < store->ptbl.nobjects;
}

static inline particle_kind_t particle_kind(pstore_t *store, particle_t i) {
  assert(valid_particle(store, i));
  return (particle_kind_t) store->ptbl.kind[i];
}

static inline bool is_labeled_particle(pstore_t *store, particle_t i) {
  return particle_kind(store, i) == LABEL_PARTICLE;
}

static inline bool is_fresh_particle(pstore_t *store, particle_t i) {
  return particle_kind(store, i) == FRESH_PARTICLE;
}

static inline bool is_tuple_particle(pstore_t *store, particle_t i) {
  return particle_kind(store, i) == TUPLE_PARTICLE;
}


// label of a labeled particle
static inline elabel_t particle_label(pstore_t *store, particle_t i) {
  assert(is_labeled_particle(store, i));
  return (elabel_t) store->ptbl.desc[i].integer;
}

// type of a fresh particle
static inline type_t fresh_particle_type(pstore_t *store, particle_t i) {
  assert(is_fresh_particle(store, i));
  return (type_t) store->ptbl.desc[i].integer;
}

// descriptor of a tuple particle
static inline particle_tuple_t *tuple_particle_desc(pstore_t *store, particle_t i) {
  assert(is_tuple_particle(store, i));
  return (particle_tuple_t *) store->ptbl.desc[i].ptr;
}

// number of components of a tuple
static inline uint32_t tuple_particle_nelems(pstore_t *store, particle_t i) {
  return tuple_particle_desc(store, i)->nelems;
}

// component k of the tuple
static inline uint32_t tuple_particle_elem(pstore_t *store, particle_t i, uint32_t k) {
  assert(k < tuple_particle_nelems(store, i));
  return tuple_particle_desc(store, i)->elem[k];
}


// concrete value of a particle i
static inline value_t particle_concrete_value(pstore_t *store, particle_t i) {
  assert(valid_particle(store, i));
  return store->ptbl.concrete[i];
}



#endif /* __ABSTRACT_VALUES_H */
