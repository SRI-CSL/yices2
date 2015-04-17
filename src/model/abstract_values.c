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
 * and for representing the arrays and mappings. Each atomic element
 * - x_ij or y_k is either an egraph class or a fresh constant of some type tau
 *   created by the solver.
 * - the egraph can later convert the abstract values into concrete objects.
 */

#include <stdbool.h>

#include "model/abstract_values.h"
#include "utils/hash_functions.h"
#include "utils/memalloc.h"
#include "utils/prng.h"




/********************
 *  PARTICLE TABLE  *
 *******************/

/*
 * Initialization: use default size
 */
static void init_particle_table(particle_table_t *table) {
  uint32_t n;

  n = DEF_PARTICLE_TABLE_SIZE;
  assert(n < MAX_PARTICLE_TABLE_SIZE);

  table->size = n;
  table->nobjects = 0;
  table->kind = (uint8_t *) safe_malloc(n * sizeof(uint8_t));
  table->desc = (particle_desc_t *) safe_malloc(n * sizeof(particle_desc_t));
  table->concrete = (value_t *) safe_malloc(n * sizeof(value_t));
  table->mark = allocate_bitvector(n);

  init_int_htbl(&table->htbl, 0);
}


/*
 * Make the table larger
 */
static void extend_particle_table(particle_table_t *table) {
  uint32_t n;

  n = table->size + 1;
  n += n>>1;
  if (n >= MAX_PARTICLE_TABLE_SIZE) {
    out_of_memory();
  }

  table->size = n;
  table->kind = (uint8_t *) safe_realloc(table->kind, n * sizeof(uint8_t));
  table->desc = (particle_desc_t *) safe_realloc(table->desc, n * sizeof(particle_desc_t));
  table->concrete = (value_t *) safe_realloc(table->concrete, n * sizeof(value_t));
  table->mark = extend_bitvector(table->mark, n);
}


/*
 * Allocate a new index
 */
static particle_t allocate_particle(particle_table_t *table) {
  particle_t i;

  i = table->nobjects;
  if (i == table->size) {
    extend_particle_table(table);
  }
  assert(i < table->size);
  table->nobjects = i+1;

  return i;
}


/*
 * Delete all descriptors
 */
static void particle_table_delete_descriptors(particle_table_t *table) {
  uint32_t i, n;

  n = table->nobjects;
  for (i=0; i<n; i++) {
    if (table->kind[i] == TUPLE_PARTICLE) {
      safe_free(table->desc[i].ptr);
    }
  }
}


/*
 * Delete the table
 */
static void delete_particle_table(particle_table_t *table) {
  particle_table_delete_descriptors(table);
  safe_free(table->kind);
  safe_free(table->desc);
  safe_free(table->concrete);
  delete_bitvector(table->mark);
  delete_int_htbl(&table->htbl);

  table->kind = NULL;
  table->desc = NULL;
  table->concrete = NULL;
  table->mark = NULL;
}



/*
 * PARTICLE CONSTRUCTORS
 */

/*
 * Create a fresh particle of type tau
 */
static particle_t mk_fresh_particle(particle_table_t *table, type_t tau) {
  particle_t i;

  i = allocate_particle(table);
  table->kind[i] = FRESH_PARTICLE;
  table->desc[i].integer = tau;
  table->concrete[i] = null_value;
  clr_bit(table->mark, i);

  return i;
}


/*
 * Create particle for label l
 */
static particle_t mk_label_particle(particle_table_t *table, elabel_t l) {
  particle_t i;

  i = allocate_particle(table);
  table->kind[i] = LABEL_PARTICLE;
  table->desc[i].integer = l;
  table->concrete[i] = null_value;
  clr_bit(table->mark, i);

  return i;
}


/*
 * Create particle for tuple a[0 ... n-1]
 */
static particle_t mk_tuple_particle(particle_table_t *table, uint32_t n, particle_t *a) {
  particle_tuple_t *d;
  particle_t i;
  uint32_t j;

  assert(n < MAX_PARTICLE_TUPLE_ARITY);

  d = (particle_tuple_t *) safe_malloc(sizeof(particle_tuple_t) + n * sizeof(particle_t));
  d->nelems = n;
  for (j=0; j<n; j++) {
    d->elem[j] = a[j];
  }

  i = allocate_particle(table);
  table->kind[i] = TUPLE_PARTICLE;
  table->desc[i].ptr = d;
  table->concrete[i] = null_value;
  clr_bit(table->mark, i);

  return i;
}


/*
 * HASH CONSING
 */

/*
 * Hash consing is used for tuples and labels
 */
typedef struct label_hobj_s {
  int_hobj_t m;
  particle_table_t *table;
  elabel_t label;
} label_hobj_t;

typedef struct tuple_hobj_s {
  int_hobj_t m;
  particle_table_t *table;
  uint32_t nelems;
  particle_t *elem;
} tuple_hobj_t;


/*
 * Hash functions
 */
static uint32_t hash_label(label_hobj_t *o) {
  return jenkins_hash_int32(o->label);
}

static uint32_t hash_tuple(tuple_hobj_t *o) {
  return jenkins_hash_intarray(o->elem, o->nelems);
}


/*
 * Test equality
 */
static bool equal_label_particle(label_hobj_t *o, particle_t i) {
  particle_table_t *table;

  table = o->table;
  return table->kind[i] == LABEL_PARTICLE && table->desc[i].integer == o->label;
}

static bool equal_tuple_particle(tuple_hobj_t *o, particle_t i) {
  particle_table_t *table;
  particle_tuple_t *d;
  uint32_t j, n;

  table = o->table;
  if (table->kind[i] != TUPLE_PARTICLE) {
    return false;
  }

  d = (particle_tuple_t *) table->desc[i].ptr;
  n = d->nelems;
  if (n != o->nelems) {
    return false;
  }

  for (j=0; j<n; j++) {
    if (d->elem[j] != o->elem[j]) {
      return false;
    }
  }

  return true;
}


/*
 * Constructors
 */
static particle_t build_label_particle(label_hobj_t *o) {
  return mk_label_particle(o->table, o->label);
}

static particle_t build_tuple_particle(tuple_hobj_t *o) {
  return mk_tuple_particle(o->table, o->nelems, o->elem);
}



/*
 * Hash consing objects
 */
static label_hobj_t label_hobj = {
  { (hobj_hash_t) hash_label, (hobj_eq_t) equal_label_particle, (hobj_build_t) build_label_particle },
  NULL,
  0,
};

static tuple_hobj_t tuple_hobj = {
  { (hobj_hash_t) hash_tuple, (hobj_eq_t) equal_tuple_particle, (hobj_build_t) build_tuple_particle },
  NULL,
  0,
  NULL,
};



/*
 * Hash consing
 */
static particle_t get_label_particle(particle_table_t *table, elabel_t l) {
  label_hobj.table = table;
  label_hobj.label = l;

  return int_htbl_get_obj(&table->htbl, (int_hobj_t *) &label_hobj);
}

static particle_t get_tuple_particle(particle_table_t *table, uint32_t n, particle_t *a) {
  tuple_hobj.table = table;
  tuple_hobj.nelems = n;
  tuple_hobj.elem = a;

  return int_htbl_get_obj(&table->htbl, (int_hobj_t*) &tuple_hobj);
}







/***********************
 *  SETS OF PARTICLES  *
 **********************/

/*
 * Allocate and initialize a set (use default size)
 * - n = arity
 * - tau[0, ..., n-1] = types for that set
 */
static particle_set_t *new_particle_set(uint32_t n, type_t *tau) {
  particle_set_t *set;
  uint32_t i;

  assert(DEF_PSET_SIZE < MAX_PSET_SIZE && n < MAX_PARTICLE_TUPLE_ARITY && n > 0);

  set = (particle_set_t *) safe_malloc(sizeof(particle_set_t) + n * sizeof(type_t));
  set->size = DEF_PSET_SIZE;
  set->nelems = 0;
  set->data = (particle_t *) safe_malloc(DEF_PSET_SIZE * sizeof(particle_t));
  set->arity = n;

  for (i=0; i<n; i++) {
    set->type[i] = tau[i];
  }

  return set;
}


/*
 * Special case: arity 1
 */
static inline particle_set_t *new_particle_set1(type_t tau) {
  return new_particle_set(1, &tau);
}


/*
 * Delete set
 */
static void free_particle_set(particle_set_t *set) {
  safe_free(set->data);
  safe_free(set);
}


/*
 * Make the data vector larger
 */
static void extend_particle_set(particle_set_t *set) {
  uint32_t n;

  n = set->size + 1;
  n += n>>1;
  if (n >= MAX_PSET_SIZE) {
    out_of_memory();
  }
  set->data = (particle_t *) safe_realloc(set->data, n * sizeof(particle_t));
  set->size = n;
}


/*
 * Add particle x at the end of set
 */
static void add_particle_to_set(particle_set_t *set, particle_t x) {
  uint32_t i;

  i = set->nelems;
  if (i == set->size) {
    extend_particle_set(set);
  }
  assert(i < set->size);
  set->data[i] = x;
  set->nelems = i+1;
}



/*
 * Check whether set matches types tau[0 ... n-1]
 */
static bool particle_set_matches_types(particle_set_t *set, uint32_t n, type_t *tau) {
  uint32_t i;

  if (set->arity != n) {
    return false;
  }

  for (i=0; i<n; i++) {
    if (set->type[i] != tau[i]) {
      return false;
    }
  }
  return true;
}


/*
 * Special case: arity = 1
 */
static inline bool particle_set_matches_type(particle_set_t *set, type_t tau) {
  return set->arity == 1 && set->type[0] == tau;
}








/*
 * Initialize set table: use default size
 */
static void init_pset_table(pset_table_t *table) {
  uint32_t n;

  n = DEF_PSET_TABLE_SIZE;
  assert(n < MAX_PSET_TABLE_SIZE);
  table->size = n;
  table->nsets = 0;
  table->set = (particle_set_t **) safe_malloc(n * sizeof(particle_set_t *));
}


/*
 * Make the table larger
 */
static void extend_pset_table(pset_table_t *table) {
  uint32_t n;

  n = table->size + 1;
  n += n >> 1;
  if (n >= MAX_PSET_TABLE_SIZE) {
    out_of_memory();
  }

  table->size = n;
  table->set = (particle_set_t **) safe_realloc(table->set, n * sizeof(particle_set_t *));
}


/*
 * Allocate a new element in the table
 */
static uint32_t allocate_pset(pset_table_t *table) {
  uint32_t i;

  i = table->nsets;
  if (i == table->size) {
    extend_pset_table(table);
  }
  assert(i < table->size);
  table->nsets = i + 1;

  return i;
}




/*
 * Delete the table
 */
static void delete_pset_table(pset_table_t *table) {
  uint32_t i, n;

  n = table->nsets;
  for (i=0; i<n; i++) {
    free_particle_set(table->set[i]);
  }
  safe_free(table->set);
  table->set = NULL;
}


/*
 * Search for a set that matches tau[0 .. n-1] in the table
 * - return NULL if there's none
 */
static particle_set_t *find_pset_for_types(pset_table_t *table, uint32_t n, type_t *tau) {
  particle_set_t *set;
  uint32_t i, m;

  m = table->nsets;
  for (i=0; i<m; i++) {
    set = table->set[i];
    assert(set != NULL);
    if (particle_set_matches_types(set, n, tau)) {
      return set;
    }
  }

  return NULL;
}


/*
 * Special case: arity 1
 */
static particle_set_t *find_pset_for_type(pset_table_t *table, type_t tau) {
  particle_set_t *set;
  uint32_t i, m;

  m = table->nsets;
  for (i=0; i<m; i++) {
    set = table->set[i];
    assert(set != NULL);
    if (particle_set_matches_type(set, tau)) {
      return set;
    }
  }

  return NULL;
}


/*
 * Search for a set that matches tau[0 ... n-1]
 * - create a new empty set if there's no match
 */
static particle_set_t *get_pset_for_types(pset_table_t *table, uint32_t n, type_t *tau) {
  particle_set_t *set;
  uint32_t i, m;

  m = table->nsets;
  for (i=0; i<m; i++) {
    set = table->set[i];
    assert(set != NULL);
    if (particle_set_matches_types(set, n, tau)) {
      return set;
    }
  }

  i = allocate_pset(table);
  set = new_particle_set(n, tau);
  table->set[i] = set;

  return set;
}


/*
 * Special case: arity 1
 */
static particle_set_t *get_pset_for_type(pset_table_t *table, type_t tau) {
  particle_set_t *set;
  uint32_t i, m;

  m = table->nsets;
  for (i=0; i<m; i++) {
    set = table->set[i];
    assert(set != NULL);
    if (particle_set_matches_type(set, tau)) {
      return set;
    }
  }

  i = allocate_pset(table);
  set = new_particle_set1(tau);
  table->set[i] = set;

  return set;
}



/*
 * Add particle i to the set for types tau[0 ... n-1]
 * - create a new set if necessary
 */
static void add_particle_to_types(pset_table_t *table, uint32_t n, type_t *tau, particle_t i) {
  particle_set_t *set;

  set = get_pset_for_types(table, n, tau);
  add_particle_to_set(set, i);
}


// arity 1
static void add_particle_to_type(pset_table_t *table, type_t tau, particle_t i) {
  particle_set_t *set;

  set = get_pset_for_type(table, tau);
  add_particle_to_set(set, i);
}





/******************
 *  GLOBAL STORE  *
 *****************/

/*
 * Initialization
 */
void init_pstore(pstore_t *store, type_table_t *ttbl) {
  store->types = ttbl;
  init_particle_table(&store->ptbl);
  init_pset_table(&store->psets);
  store->rank_size = 0;
  store->card_size = 0;
  store->rank = NULL;
  store->card = NULL;
  store->aux = NULL;
}


/*
 * Deletion
 */
void delete_pstore(pstore_t *store) {
  delete_particle_table(&store->ptbl);
  delete_pset_table(&store->psets);
  safe_free(store->rank);
  safe_free(store->card);
  safe_free(store->aux);
  store->rank = NULL;
}



/*
 * Particle labeled by l of type tau
 */
particle_t pstore_labeled_particle(pstore_t *store, elabel_t l, type_t tau) {
  particle_t i;
  uint32_t n;

  n = store->ptbl.nobjects;
  i = get_label_particle(&store->ptbl, l);
  if (store->ptbl.nobjects > n) {
    // i is a new particle
    assert(store->ptbl.nobjects == n+1);
    add_particle_to_type(&store->psets, tau, i);
  }

  return i;
}


/*
 * Fresh particle of type tau
 */
particle_t pstore_fresh_particle(pstore_t *store, type_t tau) {
  particle_t i;

  i = mk_fresh_particle(&store->ptbl, tau);
  add_particle_to_type(&store->psets, tau, i);

  return i;
}


/*
 * Tuple particle
 */
particle_t pstore_tuple_particle(pstore_t *store, uint32_t n, particle_t *a, type_t *tau) {
  particle_t i;
  uint32_t m;

  m = store->ptbl.nobjects;
  i = get_tuple_particle(&store->ptbl, n, a);
  if (store->ptbl.nobjects > m) {
    // i is a new particle
    assert(store->ptbl.nobjects == m+1);
    add_particle_to_types(&store->psets, n, tau, i);
  }

  return i;
}


/*
 * Get the particle set for type tau
 * - return NULL if there are no particles of that type
 */
particle_set_t *pstore_find_set_for_type(pstore_t *store, type_t tau) {
  return find_pset_for_type(&store->psets, tau);
}



/*
 * Get the particle set for the tuple type (tau[0], ..., tau[n-1])
 * - return NULL if there are no particles of that type.
 */
particle_set_t *pstore_find_set_for_types(pstore_t *store, uint32_t n, type_t *tau) {
  return find_pset_for_types(&store->psets, n, tau);
}






/*
 * SET OPERATIONS
 */

/*
 * Mark all the particles in array a[0, ..., p-1]
 */
static void set_particle_marks(pstore_t *store, uint32_t p, particle_t *a) {
  uint32_t i;

  for (i=0; i<p; i++) {
    set_bit(store->ptbl.mark, a[i]);
  }
}

/*
 * Clear the mark of all particles in array a[0...p-1]
 */
static void clear_particle_marks(pstore_t *store, uint32_t p, particle_t *a) {
  uint32_t i;

  for (i=0; i<p; i++) {
    clr_bit(store->ptbl.mark, a[i]);
  }
}


/*
 * Find an element in set that's not marked
 * - return null_particle if all elements are marked
 */
static particle_t get_unmarked_particle(pstore_t *store, particle_set_t *set) {
  uint32_t i, n;
  particle_t k;

  if (set != NULL) {
    n = set->nelems;
    for (i=0; i<n; i++) {
      k = set->data[i];
      if (! tst_bit(store->ptbl.mark, k)) {
        return k;
      }
    }
  }

  return null_particle;
}



/*
 * Return a particle of type tau that's distinct from all elements
 * of array a.
 * - p = size of array a
 * - create a fresh particle of type tau
 * - return null_particle if that's not possible (i.e., tau is finite
 *   and all its members occur in a).
 */
particle_t get_distinct_particle(pstore_t *store, type_t tau, uint32_t p, particle_t *a) {
  particle_set_t *set;
  particle_t k;
  uint32_t card;

  // search for an existing particle first
  set_particle_marks(store, p, a);
  set = get_pset_for_type(&store->psets, tau);
  k = get_unmarked_particle(store, set);
  clear_particle_marks(store, p, a);

  if (k == null_particle) {
    // create a fresh particle if the type isn't saturated
    card = type_card(store->types, tau);
    if (set->nelems < card) {
      k = pstore_fresh_particle(store, tau);
    }
  }

  return k;
}


/*
 * Return a (fresh) particle of that tau that's distinct from all
 * other particles of that type.
 * - return null_particle if that's not possible.
 */
particle_t get_new_particle(pstore_t *store, type_t tau) {
  particle_set_t *set;
  uint32_t card;
  particle_t k;

  set = get_pset_for_type(&store->psets, tau);
  card = type_card(store->types, tau);
  k = null_particle;
  if (set->nelems < card) {
    k = pstore_fresh_particle(store, tau);
  }

  return k;
}



/*
 * SUPPORT FOR BUILDING DISTINCT TUPLES
 *
 * Given an array a[0 ... p-1] of p particles, all of the same type
 * tau[0] x ... x tau[n-1], we want to construct a particle k distinct
 * from a[0] ... a[p-1]. To do this, we sort elements of a in
 * lexicographic order. Because all types have finitely many particles,
 * we can define the successor and predecessor (succ(a), pre(a)) of any
 * element a of type tau[0] x ... x tau[n-1] in the lexicographic order
 * (except the first and last elements). To find an element not in
 *  a[0 ... p-1], we search for a[i] such that a' = succ(a[i]) or pre(a[i])
 * is not in the array then we return a'
 *
 * Lexicographic order: for all elements in set[tau], we assign
 * a rank defined by rank[x] = i iff set[tau]->data[i] = x.
 * By construction, we have rank[x] < rank[y] iff x < y (as integers).
 * Then we use the lexicographic order (x_1, ..., x_n) < (y_1, ..., y_n)
 * if for some k we have x_1 = y1, ..., x_{k-1} = y_{k-1} and x_k < y_k.
 * The successor of (x_1,..., x_n) is obtained by increasing rank[x_n] by 1,
 * if that's overflows, we set y_n = element of rank[0] in tau[n-1], then
 * increase rank[x_{n-1}] by 1 and so forth.
 */

/*
 * Allocate or resize the rank array
 * - initialize all ranks to -1
 */
static void pstore_prepare_rank(pstore_t *store) {
  uint32_t i, n;

  n = store->ptbl.nobjects;
  if (store->rank_size < n) {
    store->rank = safe_realloc(store->rank, n * sizeof(int32_t));
    store->rank_size = n;
  }

  for (i=0; i<n; i++) {
    store->rank[i] = -1;
  }
}

#ifndef NDEBUG
/*
 * For debugging: check that set is in increasing order
 */
static bool pset_is_sorted(particle_set_t *set) {
  uint32_t i, n;

  n = set->nelems;
  if (n > 1) {
    n --;
    for (i=0; i<n; i++) {
      if (set->data[i] >= set->data[i+1]) {
        return false;
      }
    }
  }

  return true;
}

#endif

/*
 * Set the rank of all elements of type tau
 */
static void pstore_ranks_for_type(pstore_t *store, type_t tau) {
  particle_set_t *set;
  uint32_t i, n;
  particle_t x;

  set = find_pset_for_type(&store->psets, tau);
  if (set != NULL) {
    assert(pset_is_sorted(set));
    n = set->nelems;
    for (i=0; i<n; i++) {
      x = set->data[i];
      store->rank[x] = i;
    }
  }
}


/*
 * Size of set for the type tau
 * - 0 if there's no particle of that type
 */
static uint32_t pstore_size_for_type(pstore_t *store, type_t tau) {
  particle_set_t *set;

  set = pstore_find_set_for_type(store, tau);
  if (set != NULL) {
    return set->nelems;
  } else {
    return 0;
  }
}


/*
 * Allocate or resize card and aux arrays, and ranks
 * - tau[0 .. n-1] = tuple types
 * - return true if card[0, ..., n-1] are all positive
 * - return false otherwise
 */
static bool pstore_prepare_for_tuple(pstore_t *store, uint32_t n, type_t *tau) {
  uint32_t i, s;

  s = store->card_size;
  if (s < n) {
    store->card = (uint32_t *) safe_realloc(store->card, n * sizeof(uint32_t));
    store->aux = (int32_t *) safe_realloc(store->aux, n * sizeof(int32_t));
    store->card_size = n;
  }

  for (i=0; i<n; i++) {
    pstore_ranks_for_type(store, tau[i]);
    store->card[i] = pstore_size_for_type(store, tau[i]);
    if (store->card[i] == 0) {
      return false;
    }
  }

  return true;
}



/*
 * Check whether x < y in the lexicographic ordering
 * - both x and y must be tuple particles of the same types
 */
static bool lexico_precedes(particle_table_t *table, particle_t x, particle_t y) {
  particle_tuple_t *tx, *ty;
  particle_t a, b;
  uint32_t i, n;

  assert(0 <= x && x < table->nobjects && 0 <= y && y < table->nobjects &&
         table->kind[x] == TUPLE_PARTICLE && table->kind[y] == TUPLE_PARTICLE);

  tx = (particle_tuple_t *) table->desc[x].ptr;
  ty = (particle_tuple_t *) table->desc[y].ptr;
  n = tx->nelems;
  assert(n == ty->nelems);

  for (i=0; i<n; i++) {
    a = tx->elem[i];
    b = ty->elem[i];
    if (a < b) {
      return true;
    } else if (a > b) {
      return false;
    }
  }

  return false;
}


/*
 * Sort array a[0 ... n-1] in lexicographic order
 */
static void lexico_qsort(particle_table_t *table, particle_t *a, uint32_t n);

// insertion sort
static void lexico_isort(particle_table_t *table, particle_t *a, uint32_t n) {
  uint32_t i, j;
  particle_t x, y;

  for (i=1; i<n; i++) {
    x = a[i];
    j = 0;
    while (lexico_precedes(table, a[j], x)) {
      j ++;
    }
    while (j < i) {
      y = a[j]; a[j] = x; x = y;
      j ++;
    }
    a[j] = x;
  }
}

// sort: either insertion sort or quick sort
static void lexico_sort(particle_table_t *table, particle_t *a, uint32_t n) {
  if (n < 10) {
    lexico_isort(table, a, n);
  } else {
    lexico_qsort(table, a, n);
  }
}


// quick sort: n must be at least 2
static void lexico_qsort(particle_table_t *table, particle_t *a, uint32_t n) {
  uint32_t i, j;
  particle_t x, y;

  // x = random pivot
  i = random_uint(n);
  x = a[i];

  // swap x and a[0]
  a[i] = a[0];
  a[0] = x;

  i = 0;
  j = n;

  do { j--; } while (lexico_precedes(table, x, a[j]));
  do { i++; } while (i <= j && lexico_precedes(table, a[i], x));

  while (i < j) {
    // we have a[i] >= x and a[j] <= x: swap a[i] and a[j]
    y = a[i]; a[i] = a[j]; a[j] = y;

    do { j--; } while (lexico_precedes(table, x, a[j]));
    do { i++; } while (lexico_precedes(table, a[i], x));
  }

  // swap pivot and a[j]
  a[0] = a[j];
  a[j] = x;

  // recursion
  lexico_sort(table, a, j);
  j ++;
  lexico_sort(table, a + j, n - j);
}



/*
 * Check whether x has a predecessor in lexico ordering
 * - x must be a tuple
 */
static bool has_predecessor(pstore_t *store, particle_t x) {
  particle_tuple_t *tx;
  particle_t y;
  uint32_t i, n;

  tx = tuple_particle_desc(store, x);
  n = tx->nelems;
  assert(n <= store->card_size);
  for (i=0; i<n; i++) {
    y = tx->elem[i];
    assert(store->rank[y] >= 0 && store->rank[y] < store->card[i] );
    if (store->rank[y] > 0) {
      return true;
    }
  }

  // all components have rank 0
  return false;
}


/*
 * Check whether x has a successor in the lexicographic ordering
 */
static bool has_successor(pstore_t *store, particle_t x) {
  particle_tuple_t *tx;
  particle_t y;
  uint32_t i, n;

  tx = tuple_particle_desc(store, x);
  n = tx->nelems;
  assert(n <= store->card_size);
  for (i=0; i<n; i++) {
    y = tx->elem[i];
    assert(store->rank[y] >= 0 && store->rank[y] < store->card[i] );
    if (store->rank[y] < store->card[i] - 1) {
      return true;
    }
  }

  // all components have maximal rank
  return false;
}


/*
 * Compute the predecessor of rank(x) as an array of n ranks
 * - the result is stored in aux[0] ... aux[n-1]
 */
static void rank_predecessor(pstore_t *store, particle_t x) {
  particle_tuple_t *tx;
  particle_t y;
  uint32_t i, n;
  int32_t k;

  tx = tuple_particle_desc(store, x);
  n = tx->nelems;
  assert(n <= store->card_size);
  for (i=0; i<n; i++) {
    y = tx->elem[i];
    store->aux[i] = store->rank[y];
    assert(0 <= store->aux[i] && store->aux[i] < store->card[i]);
  }

  // decrement the ranks from right to left
  while (i > 0) {
    i --;
    k = store->aux[i];
    assert(k < store->card[i]);
    if (k == 0) {
      store->aux[i] = store->card[i] - 1;
    } else {
      store->aux[i] = k - 1;
      break;
    }
  }
}



/*
 * Compute the successor of rank(x) as an array of n ranks
 * - the result is stored in aux[0] ... aux[n-1]
 */
static void rank_successor(pstore_t *store, particle_t x) {
  particle_tuple_t *tx;
  particle_t y;
  uint32_t i, n;
  int32_t k;

  tx = tuple_particle_desc(store, x);
  n = tx->nelems;
  assert(n <= store->card_size);
  for (i=0; i<n; i++) {
    y = tx->elem[i];
    store->aux[i] = store->rank[y];
    assert(0 <= store->aux[i] && store->aux[i] < store->card[i]);
  }

  // increment the ranks from right to left
  while (i > 0) {
    i --;
    k = store->aux[i] + 1;
    if (k == store->card[i]) {
      store->aux[i] = 0;
    } else {
      assert(k < store->card[i]);
      store->aux[i] = k;
      break;
    }
  }
}


/*
 * Check whether (aux[0], ..., aux[n-1]) < (rank[x_1], ... , rank[x_n]) in lex order
 */
static bool rank_lex_precedes(pstore_t *store, particle_t x) {
  particle_tuple_t *tx;
  particle_t y;
  uint32_t i, n;
  int32_t r, s;

  tx = tuple_particle_desc(store, x);
  n = tx->nelems;
  assert(n <= store->card_size);
  for (i=0; i<n; i++) {
    y = tx->elem[i];
    s = store->rank[y];
    r = store->aux[i];
    if (r < s) {
      return true;
    } else if (r > s) {
      return false;
    }
  }

  return false;
}




/*
 * Build the tuple defined by the ranks aux[0 ... n-1]
 */
static particle_t pstore_tuple_from_ranks(pstore_t *store, uint32_t n, type_t *tau) {
  particle_set_t *set;
  particle_t y;
  int32_t k;
  uint32_t i;

  // replace aux[i] by the variable of type tau[i] and rank aux[i]
  assert(n <= store->card_size);
  for (i=0; i<n; i++) {
    set = pstore_find_set_for_type(store, tau[i]);
    assert(set != NULL);
    k = store->aux[i];
    assert(0 <= k && k < store->card[i] && store->card[i] == set->nelems);
    y = set->data[k];
    assert(store->rank[y] == k);
    store->aux[i] = y;
  }

  // build the tuple
  return pstore_tuple_particle(store, n, store->aux, tau);
}


/*
 * Build a new tuple distinct from all elements in array a
 * - a must be sorted in lexicographic order
 * - return null_particle if all possible tuples are already in a
 */
static particle_t new_distinct_tuple(pstore_t *store, uint32_t n, type_t *tau, uint32_t p, particle_t *a) {
  uint32_t i;
  particle_t x, y;

  if (p == 0) {
    // make the element of rank 0, ..., 0
    for (i=0; i<n; i++) {
      store->aux[i] = 0;
    }
    goto build;
  }

  x = a[0];
  if (has_predecessor(store, x)) {
    rank_predecessor(store, x);
    goto build;
  }

  p --;
  for (i=0; i<p; i++) {
    x = a[i];
    y = a[i+1];
    if (x != y) {
      assert(lexico_precedes(&store->ptbl, x, y) && has_successor(store, x));
      rank_successor(store, x);
      if (rank_lex_precedes(store, y)) goto build;
    }
  }

  x = a[p];
  if (has_successor(store, x)) {
    rank_successor(store, x);
    goto build;
  }

  return null_particle;

 build:
  return pstore_tuple_from_ranks(store, n, tau);
}




/*
 * Try to construct a new tuple particle distinct from a[0] ... a[p-1]
 * - tau[0] ... tau[n-1] = type of the tuple to create
 *   (that must be the type of a[0] ... a[p-1] too).
 */
static particle_t make_distinct_tuple(pstore_t *store, uint32_t n, type_t *tau, uint32_t p, particle_t *a) {
  particle_t k;

  pstore_prepare_rank(store);
  k = null_particle;
  if (pstore_prepare_for_tuple(store, n, tau)) {
    lexico_sort(&store->ptbl, a, p);
    k = new_distinct_tuple(store, n, tau, p, a);
  }
  return k;
}


/*
 * Create fresh elements in all of the types tau[0] ... tau[n-1]
 * then build a tuple from that.
 */
static particle_t add_fresh_particles_and_build_tuple(pstore_t *store, uint32_t n, type_t *tau) {
  particle_set_t *set;
  bool fresh_elem;
  uint32_t i, card, s;

  // make sure aux is allocated
  s = store->card_size;
  if (s < n) {
    store->card = (uint32_t *) safe_realloc(store->card, n * sizeof(uint32_t));
    store->aux = (int32_t *) safe_realloc(store->aux, n * sizeof(int32_t));
    store->card_size = n;
  }

  fresh_elem = false;
  i = n;
  while (i > 0) {
    i --;
    set = get_pset_for_type(&store->psets, tau[i]);
    card = type_card(store->types, tau[i]);
    if (set->nelems == 0 || (!fresh_elem && set->nelems< card)) {
      // create a fresh particle of type tau[i]
      store->aux[i] = pstore_fresh_particle(store, tau[i]);
      fresh_elem = true;
    } else {
      // use an existing particle (the first one)
      assert(set->nelems > 0);
      store->aux[i] = set->data[0];
    }
  }

  if (fresh_elem) {
    return pstore_tuple_particle(store, n, store->aux, tau);
  } else {
    return null_particle;
  }
}



/*
 * Get a particle of type (tau[0] x ... x tau[n-1]) that's distinct from
 * all elements of array a
 * - n must be at least 2 (for n=1 get_distinct_particle should be used)
 * - p = size of the array a
 */
particle_t get_distinct_tuple(pstore_t *store, uint32_t n, type_t *tau, uint32_t p, particle_t *a) {
  particle_set_t *set;
  particle_t k;

  // try an existing particle (in set)
  set_particle_marks(store, p, a);
  set = get_pset_for_types(&store->psets, n, tau);
  k = get_unmarked_particle(store, set);
  clear_particle_marks(store, p, a);
  if (k != null_particle) {
    goto done;
  }

  // try to construct a new tuple
  k = make_distinct_tuple(store, n, tau, p, a);
  if (k != null_particle) {
    goto done;
  }

  // try to create a new tuple by adding an element in tau[0] or ... or tau[n-1]
  k = add_fresh_particles_and_build_tuple(store, n, tau);

 done:
  return k;
}


/*
 * Return a particle of type (tau[0], ..., tau[n-1]) that's distinct
 * from all other particles of that type in the store.
 * - n must be at least 2
 * - return null_particle if that's not possible.
 */
particle_t get_new_tuple(pstore_t *store, uint32_t n, type_t *tau) {
  particle_set_t *set;
  particle_t *a;
  particle_t k;
  uint32_t i, s;

  set = get_pset_for_types(&store->psets, n, tau);

  // copy all elements of set in array a
  s = set->nelems;
  a = (particle_t *) safe_malloc(s * sizeof(particle_t));
  for (i=0; i<s; i++) {
    a[i] = set->data[i];
  }

  // try to construct a new tuple
  k = make_distinct_tuple(store, n, tau, s, a);
  safe_free(a);

  if (k == null_particle) {
    // try to create a new tuple by adding an element in tau[0] or ... or tau[n-1]
    k = add_fresh_particles_and_build_tuple(store, n, tau);
  }

  return k;
}

