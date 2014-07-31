/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Computation of the free variables of a term.
 */

#include <assert.h>

#include "utils/int_array_sort.h"
#include "utils/ptr_array_sort.h"
#include "terms/free_var_collector.h"


/*
 * Initialization
 */
void init_fvar_collector(fvar_collector_t *collect, term_table_t *ttbl) {
  collect->terms = ttbl;
  init_ptr_hmap(&collect->map, 0);         // default size
  init_int_array_hset(&collect->store, 0); // default size
  init_pstack(&collect->stack);
  init_ivector(&collect->buffer, 20);      // initial size = 20
  init_int_hset(&collect->aux, 0);         // default size
}


/*
 * Delete the whole thing
 */
void delete_fvar_collector(fvar_collector_t *collect) {
  delete_ptr_hmap(&collect->map);
  delete_int_array_hset(&collect->store);
  delete_pstack(&collect->stack);
  delete_ivector(&collect->buffer);
  delete_int_hset(&collect->aux);
}


/*
 * Reset: empty everything
 */
void reset_fvar_collector(fvar_collector_t *collect) {
  ptr_hmap_reset(&collect->map);
  reset_int_array_hset(&collect->store);
  reset_pstack(&collect->stack);
  ivector_reset(&collect->buffer);
  int_hset_reset(&collect->aux);
}



/*
 * For debugging: check that a is sorted and does not contain duplicates
 * and that all elements of a are variables.
 */
#ifndef NDEBUG
static bool good_var_set(term_table_t *terms, harray_t *a) {
  uint32_t i, n;
  term_t x;

  n = a->nelems;
  x = NULL_TERM; // -1
  for (i = 0; i<n; i++) {
    if (a->data[i] <= x) return false; // not sorted or duplicate
    x = a->data[i];
    if (term_kind(terms, x) != VARIABLE) return false;
  }

  return true;
}

#endif


/*
 * Empty set of variables
 */
static inline harray_t *empty_fvar_set(fvar_collector_t *collect) {
  return int_array_hset_get(&collect->store, 0, NULL);
}


/*
 * Singleton set: x = unique element
 */
static inline harray_t *singleton_fvar_set(fvar_collector_t *collect, term_t x) {
  return int_array_hset_get(&collect->store, 1, &x);
}


/*
 * Add all elements of a to vector v and to hset
 * - skip the elements of a that are already in hset
 */
static void fvar_merge(ivector_t *v, int_hset_t *hset, harray_t *a) {
  uint32_t i, n;
  term_t x;

  n = a->nelems;
  for (i=0; i<n; i++) {
    x = a->data[i];
    if (int_hset_add(hset, x)) { // new variable
      ivector_push(v, x);
    }
  }
}


/*
 * Compute the union of a and b
 */
static harray_t *merge_two_fvar_sets(fvar_collector_t *collect, harray_t *a, harray_t *b) {
  ivector_t *v;
  int_hset_t *aux;

  if (a != b) {
    v = &collect->buffer;
    aux = &collect->aux;
    assert(v->size == 0 && int_hset_is_empty(aux));

    fvar_merge(v, aux, a);
    fvar_merge(v, aux, b);
    int_array_sort(v->data, v->size);
    a = int_array_hset_get(&collect->store, v->size, v->data);
    assert(good_var_set(collect->terms, a));

    ivector_reset(v);
    int_hset_reset(aux);
  }

  return a;
}

/*
 * Compute the union of a[0 ... n-1]
 * - n must be positive
 */
static harray_t *merge_fvar_sets(fvar_collector_t *collect, harray_t **a, uint32_t n) {
  harray_t *b, *c;
  ivector_t *v;
  int_hset_t *aux;
  uint32_t i;

  assert(n > 0);

  if (n == 1) {
    b = a[0];
  } else if (n == 2) {
    b = merge_two_fvar_sets(collect, a[0], a[1]);
  } else {
    v = &collect->buffer;
    aux = &collect->aux;
    assert(v->size == 0 && int_hset_is_empty(aux));

    /*
     * Collect all elements of a[0] ... a[n-1] in v
     */
    ptr_array_sort((void **) a, n);
    b = a[0];
    for (i=1; i<n; i++) {
      c = a[i];
      if (c != b) {
        fvar_merge(v, aux, b);
        b = c;
      }
    }

    /*
     * b is a[i], for some i and elements of b have not been
     * processed yet. If i = 0, then all elements of a are
     * equal to b so the result is b.
     */
    if (b != a[0]) {
      fvar_merge(v, aux, b);

      assert(v->size > 0 && int_hset_is_nonempty(aux));
      int_array_sort(v->data, v->size);
      b = int_array_hset_get(&collect->store, v->size, v->data);
      assert(good_var_set(collect->terms, b));

      ivector_reset(v);
      int_hset_reset(aux);
    }
  }

  return b;
}


/*
 * Remove variables x[0] to x[n-1] from set a then build a harray.
 */
static harray_t *fvar_set_remove(fvar_collector_t *collect, harray_t *a, uint32_t n, term_t *x) {
  ivector_t *v;
  int_hset_t *aux;
  uint32_t i;
  term_t y;

  v = &collect->buffer;
  aux = &collect->aux;
  assert(v->size == 0 && int_hset_is_empty(aux));

  // store x[0] ... x[n-1] in aux
  for (i=0; i<n; i++) {
    (void) int_hset_add(aux, x[i]);
  }

  /*
   * collect elements of a - aux into v.
   * the elements are sorted in v.
   */
  n = a->nelems;
  for (i=0; i<n; i++) {
    y = a->data[i];
    if (! int_hset_member(aux, y)) {
      ivector_push(v, y);
    }
  }
  a = int_array_hset_get(&collect->store, v->size, v->data);
  assert(good_var_set(collect->terms, a));

  ivector_reset(v);
  int_hset_reset(aux);

  return a;
}


/*
 * Check whether the free var set for term index i is in the hash map
 * - return NULL if it's not
 */
static harray_t *lookup_free_vars(fvar_collector_t *collect, int32_t i) {
  ptr_hmap_pair_t *p;
  harray_t *a;

  a = NULL;
  p = ptr_hmap_find(&collect->map, i);
  if (p != NULL) {
    a = p->val;
    assert(a != NULL && good_var_set(collect->terms, a));
  }
  return a;
}


/*
 * Store the free var set of i into the hash map
 * - i: term index
 * - a: set of variables of i
 * There must not be anything mapped to i the the map yet.
 */
static void cache_free_vars(fvar_collector_t *collect, int32_t i, harray_t *a) {
  ptr_hmap_pair_t *p;

  p = ptr_hmap_get(&collect->map, i);
  assert(p->val == NULL);
  p->val = a;
}


/*
 * Free variables in composite terms (other than forall)
 */
static harray_t *free_vars_of_composite(fvar_collector_t *collect, composite_term_t *c) {
  harray_t **a;
  harray_t *result;
  uint32_t i, n;

  n = c->arity;
  a = (harray_t **) alloc_pstack_array(&collect->stack, n);
  for (i=0; i<n; i++) {
    a[i] = get_free_vars_of_term(collect, c->arg[i]);
  }
  result = merge_fvar_sets(collect, a, n);
  free_pstack_array(&collect->stack, (void **) a);

  return result;
}

static harray_t *free_vars_of_pprod(fvar_collector_t *collect, pprod_t *p) {
  harray_t **a;
  harray_t *result;
  uint32_t i, n;

  n = p->len;
  a = (harray_t **) alloc_pstack_array(&collect->stack, n);
  for (i=0; i<n; i++) {
    a[i] = get_free_vars_of_term(collect, p->prod[i].var);
  }
  result = merge_fvar_sets(collect, a, n);
  free_pstack_array(&collect->stack, (void **) a);

  return result;
}

static harray_t *free_vars_of_poly(fvar_collector_t *collect, polynomial_t *p) {
  harray_t **a;
  harray_t *result;
  monomial_t *mono;
  uint32_t i, n;

  n = p->nterms;
  mono = p->mono;
  // skip the constant term if any
  if (mono[0].var == const_idx) {
    n --;
    mono ++;
  }

  a = (harray_t **) alloc_pstack_array(&collect->stack, n);
  for (i=0; i<n; i++) {
    a[i] = get_free_vars_of_term(collect, mono[i].var);
  }
  result = merge_fvar_sets(collect, a, n);
  free_pstack_array(&collect->stack, (void **) a);

  return result;
}

static harray_t *free_vars_of_bvpoly64(fvar_collector_t *collect, bvpoly64_t *p) {
  harray_t **a;
  harray_t *result;
  bvmono64_t *mono;
  uint32_t i, n;

  n = p->nterms;
  mono = p->mono;
  if (mono[0].var == const_idx) {
    n--;
    mono ++;
  }
  a = (harray_t **) alloc_pstack_array(&collect->stack, n);
  for (i=0; i<n; i++) {
    a[i] = get_free_vars_of_term(collect, mono[i].var);
  }
  result = merge_fvar_sets(collect, a, n);
  free_pstack_array(&collect->stack, (void **) a);

  return result;
}

static harray_t *free_vars_of_bvpoly(fvar_collector_t *collect, bvpoly_t *p) {
  harray_t **a;
  harray_t *result;
  bvmono_t *mono;
  uint32_t i, n;

  n = p->nterms;
  mono = p->mono;
  if (mono[0].var == const_idx) {
    n--;
    mono ++;
  }

  a = (harray_t **) alloc_pstack_array(&collect->stack, n);
  for (i=0; i<n; i++) {
    a[i] = get_free_vars_of_term(collect, mono[i].var);
  }
  result = merge_fvar_sets(collect, a, n);
  free_pstack_array(&collect->stack, (void **) a);

  return result;
}


/*
 * Free variables in (FORALL x1, ..., xn: P) and (LAMBDA x1 ... x_n : t)
 */
static harray_t *free_vars_of_binding(fvar_collector_t *collect, composite_term_t *p) {
  harray_t *a;
  uint32_t n;

  n = p->arity;
  /*
   * The bound variables are p->arg[0] to p->arg[n-2]
   * The body is p->arg[n-1]
   */
  assert(n >= 2);
  a = get_free_vars_of_term(collect, p->arg[n-1]);
  a = fvar_set_remove(collect, a, n-1, p->arg);

  return a;
}


/*
 * Compute the set of free variables in term t:
 * - t must be defined in collect->terms
 * - the set is returned as a harray structure a (cf. int_array_hsets)
 *   a->nelems = size of the set = n
 *   a->data[0 ... n-1] = variables of t listed in increasing order
 */
harray_t *get_free_vars_of_term(fvar_collector_t *collect, term_t t) {
  term_table_t *terms;
  harray_t *result;
  int32_t i;

  terms = collect->terms;
  i = index_of(t);
  switch (kind_for_idx(terms, i)) {
  case CONSTANT_TERM:
  case ARITH_CONSTANT:
  case BV64_CONSTANT:
  case BV_CONSTANT:
  case UNINTERPRETED_TERM:
    result = empty_fvar_set(collect);
    break;

  case VARIABLE:
    // we use pos_term(i) rather than t since t could be a negative term
    // (i.e., neg_term(i) that represents (not v) for some Boolean variable v)
    result = singleton_fvar_set(collect, pos_term(i));
    break;

  case ARITH_EQ_ATOM:
  case ARITH_GE_ATOM:
    result = get_free_vars_of_term(collect, integer_value_for_idx(terms, i));
    break;

  case ITE_TERM:
  case ITE_SPECIAL:
  case APP_TERM:
  case UPDATE_TERM:
  case TUPLE_TERM:
  case EQ_TERM:
  case DISTINCT_TERM:
  case OR_TERM:
  case XOR_TERM:
  case ARITH_BINEQ_ATOM:
  case BV_ARRAY:
  case BV_DIV:
  case BV_REM:
  case BV_SDIV:
  case BV_SREM:
  case BV_SMOD:
  case BV_SHL:
  case BV_LSHR:
  case BV_ASHR:
  case BV_EQ_ATOM:
  case BV_GE_ATOM:
  case BV_SGE_ATOM:
    result = lookup_free_vars(collect, i);
    if (result == NULL) {
      result = free_vars_of_composite(collect, composite_for_idx(terms, i));
      cache_free_vars(collect, i, result);
    }
    break;

  case FORALL_TERM:
  case LAMBDA_TERM:
    result = lookup_free_vars(collect, i);
    if (result == NULL) {
      result = free_vars_of_binding(collect, composite_for_idx(terms, i));
      cache_free_vars(collect, i, result);
    }
    break;

  case SELECT_TERM:
  case BIT_TERM:
    result = get_free_vars_of_term(collect, select_for_idx(terms, i)->arg);
    break;

  case POWER_PRODUCT:
    result = lookup_free_vars(collect, i);
    if (result == NULL) {
      result = free_vars_of_pprod(collect, pprod_for_idx(terms, i));
      cache_free_vars(collect, i, result);
    }
    break;

  case ARITH_POLY:
    result = lookup_free_vars(collect, i);
    if (result == NULL) {
      result = free_vars_of_poly(collect, polynomial_for_idx(terms, i));
      cache_free_vars(collect, i, result);
    }
    break;

  case BV64_POLY:
    result = lookup_free_vars(collect, i);
    if (result == NULL) {
      result = free_vars_of_bvpoly64(collect, bvpoly64_for_idx(terms, i));
      cache_free_vars(collect, i, result);
    }
    break;

  case BV_POLY:
    result = lookup_free_vars(collect, i);
    if (result == NULL) {
      result = free_vars_of_bvpoly(collect, bvpoly_for_idx(terms, i));
      cache_free_vars(collect, i, result);
    }
    break;

  default:
    assert(false);
    result = NULL;
    break;
  }

  return result;
}




/*
 * Check whether t is a ground term:
 * - side effect: this computes the set of free variables of t
 */
bool term_is_ground(fvar_collector_t *collect, term_t t) {
  harray_t *a;

  a = get_free_vars_of_term(collect, t);
  return a->nelems == 0;
}



/*
 * Filter for ptr_hmap: r is a pair <term, ptr>
 * - r must be deleted if the term is dead
 * - aux is a pointer to the term table
 */
static bool fvar_dead_hmap_pair(void *aux, const ptr_hmap_pair_t *r) {
  return !live_term(aux, r->key);
}


/*
 * Filter for the store:
 * - a is a harray structure
 * - aux is a pointer to the term table
 * - a must be deleted if it contains a dead term
 */
static bool fvar_dead_harray(void *aux, const harray_t *a) {
  uint32_t i, n;

  n = a->nelems;
  for (i=0; i<n; i++) {
    if (!live_term(aux, a->data[i])) {
      return true;
    }
  }

  return false;
}



/*
 * Cleanup: remove any references to deleted terms
 * - this must be called after terms are removed from collect->terms
 */
void cleanup_fvar_collector(fvar_collector_t *collect) {
  // must delete records in the map first
  ptr_hmap_remove_records(&collect->map, collect->terms, fvar_dead_hmap_pair);
  int_array_hset_remove_arrays(&collect->store, collect->terms, fvar_dead_harray);
}
