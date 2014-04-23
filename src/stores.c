/*
 * Term and Type Stores for testing
 */

#if defined(CYGWIN) || defined(MINGW)
#ifndef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__ __declspec(dllexport)
#endif
#endif

#include "stores.h"
#include "yices_globals.h"
#include "type_printer.h"
#include "term_printer.h"

#include "yices.h"

/*
 * Print the type table
 */
void show_types(FILE* output) {
  fprintf(output, "\n---- Type table ----\n");
  pp_type_table(output, __yices_globals.types);
}


/*
 * Print the term table
 */
void show_terms(FILE* output) {
  fprintf(output, "\n---- Term table -----\n");
  pp_term_table(output, __yices_globals.terms);
}

/*
 * Print location + error message
 */
void show_error(FILE* output) {
  error_report_t *error;

  error = yices_error_report();
  fprintf(output, "parser error: line %"PRIu32", column %"PRIu32"\n", error->line, error->column);
  yices_print_error(output);
  fflush(output);
}


/*
 * Initialization
 */
void init_type_store(type_store_t *store) {
  uint32_t n;

  n = TYPE_STORE_DEF_SIZE;
  assert(n < TYPE_STORE_MAX_SIZE);

  store->size = n;
  store->ntypes = 0;
  store->type = (type_t *) safe_malloc(n * sizeof(type_t));
  store->terms = (ivector_t *) safe_malloc(n * sizeof(ivector_t));
}


/*
 * Make the store 50% larger
 */
void extend_type_store(type_store_t *store) {
  uint32_t n;

  n = store->size + 1;
  n += n >> 1;

  if (n >= TYPE_STORE_MAX_SIZE) {
    out_of_memory();
  }

  store->size = n;
  store->type = (type_t *) safe_realloc(store->type, n * sizeof(type_t));
  store->terms = (ivector_t *) safe_realloc(store->terms, n * sizeof(ivector_t));
}


/*
 * Allocate a new index i and initialize terms[i]
 */
uint32_t type_store_alloc_index(type_store_t *store) {
  uint32_t i;

  i = store->ntypes;
  if (i == store->size) {
    extend_type_store(store);
  }
  assert(i < store->size);

  init_ivector(store->terms + i, 10);
  store->ntypes ++;

  return i;
}


/*
 * Get the index of type tau:
 * - if tau is not in the store, add it
 */
uint32_t type_store_get_type(type_store_t *store, type_t tau) {
  uint32_t i, n;

  n = store->ntypes;
  for (i=0; i<n; i++) {
    if (store->type[i] == tau) {
      return i;
    }
  }

  i = type_store_alloc_index(store);
  store->type[i] = tau;

  return i;
}


/*
 * Add term t to the store:
 * - t is added as last element of store->terms[i] where i = index for type of t
 */
void type_store_add_term(type_store_t *store, term_t t) {
  uint32_t i;
  type_t tau;

  assert(good_term(__yices_globals.terms, t));

  tau = term_type(__yices_globals.terms, t);
  i = type_store_get_type(store, tau);
  ivector_push(store->terms + i, t);
}



/*
 * Get the index of type tau.
 * - return store->ntypes is tau is not present in the store.
 */
uint32_t type_store_type_index(type_store_t *store, type_t tau) {
  uint32_t i, n;

  n = store->ntypes;
  for (i=0; i<n; i++) {
    if (store->type[i] == tau) break;
  }
  return i;
}




/*
 * Delete the store
 */
void delete_type_store(type_store_t *store) {
  uint32_t i, n;

  n = store->ntypes;
  for (i=0; i<n; i++) {
    delete_ivector(store->terms + i);
  }
  safe_free(store->type);
  safe_free(store->terms);

  store->type = NULL;
  store->terms = NULL;
}




/*
 * TERM STORE
 */

/*
 * Initialize store
 */
void init_term_store(term_store_t *store) {
  uint32_t n;

  n = TERM_STORE_DEF_SIZE;
  assert(n < TERM_STORE_MAX_SIZE);

  store->size = n;
  store->nterms = 0;
  store->term = (term_t *) safe_malloc(n * sizeof(term_t));

  n = TERM_STORE_DEF_MSIZE;
  store->max_term = n;
  store->mark = allocate_bitvector0(n);
}


/*
 * Extend: make the term array 50% larger
 */
void extend_term_store(term_store_t *store) {
  uint32_t n;

  n = store->size + 1;
  n += n>>1;

  if (n >= TERM_STORE_MAX_SIZE) {
    out_of_memory();
  }

  store->size = n;
  store->term = (term_t *) safe_realloc(store->term, n * sizeof(term_t));
}


/*
 * Get a new index i to store a term
 */
uint32_t term_store_alloc_index(term_store_t *store) {
  uint32_t i;

  i = store->nterms;
  if (i == store->size) {
    extend_term_store(store);
  }
  assert(i < store->size);
  store->nterms ++;

  return i;
}



/*
 * Mark term t
 */
void term_store_mark_term(term_store_t *store, term_t t) {
  uint32_t n;

  assert(t >= 0);

  n = store->max_term;
  if (t >= n) {
    // make the mark vector large enough to mark t: try to double its size
    // if that's not enough allocate a vector of size
    n += n;
    if (t >= n) {
      n = (t + 8) >> 3; // ceil((t+1)/8)
    }
    store->mark = extend_bitvector0(store->mark, n, store->max_term);
    store->max_term = n;
    assert(t < n);
  }
  set_bit(store->mark, t);
}



/*
 * Check whether t is present in store
 */
bool term_store_contains_term(term_store_t *store, term_t t) {
  return t < store->max_term && tst_bit(store->mark, t);
}


/*
 * Add term t to the store (t should not be present)
 */
void term_store_add_term(term_store_t *store, term_t t) {
  uint32_t i;

  assert(! term_store_contains_term(store, t));

  i = term_store_alloc_index(store);
  store->term[i] = t;
  term_store_mark_term(store, t);
}


/*
 * Delete store
 */
void delete_term_store(term_store_t *store) {
  safe_free(store->term);
  delete_bitvector(store->mark);
  store->term = NULL;
  store->mark = NULL;
}





/*
 * SUPPORT FOR RANDOM TESTING
 */

/*
 * Sampling: select one type in store that satifies predicate p
 */
type_t type_store_sample(type_store_t *store, predicate_t p) {
  uint32_t i, n, m;
  type_t tau, sigma;

  n = store->ntypes;
  m = 0;
  sigma = NULL_TYPE;
  for (i=0; i<n; i++) {
    tau = store->type[i];
    if (p(tau)) {
      m ++;
      // replace sigma by tau with probability 1/m
      // keep sigma with probablity (m-1)/m
      if ((((uint32_t)random()) % m) == 0) {
	sigma = tau;
      }
    }
  }

  return sigma;
}



/*
 * Sampling: select one of the terms of type tau
 * - return NULL_TERM if there's nothing of type tau in the store.
 */
term_t type_store_sample_terms(type_store_t *store, type_t tau) {
  uint32_t i, j, n;
  term_t t;

  t = NULL_TERM;
  i = type_store_type_index(store, tau);
  if (i < store->ntypes) {
    n = store->terms[i].size;
    if (n > 0) {
      j = ((uint32_t) random()) % n;
      t = store->terms[i].data[j];
    }
  }

  return t;
}



/*
 * Term sampling: get a term that satisfies the predicate P(tau, t).
 * Give priority to small terms (i.e., those created early).
 */
term_t term_array_sample(term_t *a, uint32_t n, type_t tau, term_pred_t p) {
  uint32_t i, m;
  term_t t, s;

  m = 0;
  s = NULL_TERM;
  for (i=0; i<n; i++) {
    t = a[i];
    if (p(tau, t)) {
      m ++;
      if ((((uint32_t)random()) % m) == 0) {
	s = t;
      }
    }
  }

  return s;
}

term_t term_store_sample(term_store_t *store, type_t tau, term_pred_t p) {
  uint32_t n;
  term_t t, s;

  n = store->nterms;
  if (n > 150) {
    s = term_array_sample(store->term, 150, tau, p); // small terms
    if (s == NULL_TERM || (random() % 10) == 0) {
      t = term_array_sample(store->term + 150, n - 150, tau, p); // large terms
      if (t != NULL_TERM) {
	s = t;
      }
    }
  } else {
    s = term_array_sample(store->term, n, tau, p); // all terms are small
  }

  return s;
}



