/*
 * ATTEMPT TO LEARN CONSTRAINTS ON VARIABLES FROM CONDITIONAL DEFINITIONS
 */

#include <assert.h>

#include "memalloc.h"
#include "ptr_array_sort2.h"
#include "term_utils.h"

#include "conditional_definitions.h"


#if 1

#include <stdio.h>
#include <inttypes.h>

#include "term_printer.h"

#endif


/*
 * SET OF TERMS (BOOLEAN VARIABLES)
 */

/*
 * We store sets of variables using harray_t.
 * A set if represented as a sorted array of terms.
 */
/*
 * Check that array a of n term is sorted and has no duplicates
 */
#ifndef NDEBUG
static bool array_is_sorted(term_t *a, uint32_t n) {
  uint32_t i;

  for (i=0; i+1<n; i++) {
    if (a[i] >= a[i+1]) return false;
  }
  return true;
}

static bool vector_is_sorted(ivector_t *v) {
  return array_is_sorted(v->data, v->size);
}

static bool harray_is_sorted(harray_t *a) {
  return array_is_sorted(a->data, a->nelems);
}

#endif


/*
 * Insert t into vector v
 * - v is assumed sorted in increasing order
 * - do nothing if t is already in v
 */
static void add_var_to_vector(ivector_t *v, term_t t) {
  uint32_t i, j, k;

  assert(vector_is_sorted(v));

  // binary search
  i = 0;
  j = v->size;
  while (i < j) {
    k = (i+j) >> 1; // (i+j) can't overflow since v->size <= MAX_IVECTOR_SIZE
    assert(i <= k && k < j);
    if (v->data[k] < t) {
      i = k+1;
    } else {
      j = k;
    }
  }

  j = v->size;
  if (i == j) {
    // all elements are smaller than t
    ivector_push(v, t);
  } else {
    assert(i < v->size && v->data[i] >= t);
    if (v->data[i] > t) {
      // insert t in v->data[i] and shift everything
      ivector_push(v, 0); // make room
      while (j > i) {
	v->data[j] = v->data[j-1];
	j --;
      }
      v->data[j] = t;
    }
  }

  assert(vector_is_sorted(v) && i < v->size && v->data[i] == t);
}


/*
 * Add all elements of a to vector v:
 * - we could use a merge here?
 */
static void add_vars_to_vector(ivector_t *v, harray_t *a) {
  uint32_t i, n;

  assert(vector_is_sorted(v) && harray_is_sorted(a));

  n = a->nelems;
  for (i=0; i<n; i++) {
    add_var_to_vector(v, a->data[i]);
  }
}




/*
 * BOOLEAN CONDITIONS
 */

/*
 * Initialize collect:
 * - ctx = relevant context
 * - store = hash_array structure
 */
static void init_bool_var_collector(bool_var_collector_t *collect, context_t *ctx, int_array_hset_t *store) {
  collect->ctx = ctx;
  collect->terms = ctx->terms;
  collect->store = store;
  init_simple_cache(&collect->cache, 0);
  init_pstack(&collect->stack);
  init_ivector(&collect->buffer, 10);
}

/*
 * Free memory
 */
static void delete_bool_var_collector(bool_var_collector_t *collect) {
  delete_simple_cache(&collect->cache);
  delete_pstack(&collect->stack);
  delete_ivector(&collect->buffer);
}


/*
 * Build sets
 */
static harray_t *empty_set(bool_var_collector_t *collect) {
  return int_array_hset_get(collect->store, 0, NULL); // this returns a non-NULL harray
}

static harray_t *singleton(bool_var_collector_t *collect, term_t t) {
  return int_array_hset_get(collect->store, 1, &t);
}

static harray_t *vector_to_set(bool_var_collector_t *collect, ivector_t *v) {
  assert(vector_is_sorted(v));
  return int_array_hset_get(collect->store, v->size, v->data);
}



/*
 * Cache for bool_var_collector:
 * - the value for a term index i is a pointer (to harray_t)
 * - the value is NULL if i is not a pure Boolean term
 * - otherwise the value is the set of Boolean variables occurring in i
 */
static void cache_bool_var_set(bool_var_collector_t *collect, int32_t i, harray_t *a) {
  assert(good_term_idx(collect->terms, i));
  simple_cache_store_ptr(&collect->cache, i, 0, a); // tag = 0 (not used)
}


/*
 * Check whether term t is purely Boolean and compute the set of variables
 * - return NULL if t is not purely Boolean
 * - return the set of variables of t otherwise
 */
static harray_t *bool_vars_of_term(bool_var_collector_t *collect, term_t t);

// recursively explore a composite term d
static harray_t *bool_vars_of_composite(bool_var_collector_t *collect, composite_term_t *d) {
  void **a;
  harray_t *set;
  ivector_t *v;
  uint32_t i, n;

  set = NULL;

  n = d->arity;
  a = alloc_pstack_array(&collect->stack, n);
  for (i=0; i<n; i++) {
    a[i] = bool_vars_of_term(collect, d->arg[i]);
    if (a[i] == NULL) goto done;
  }

  // compute the union of a[0 ... n-1]
  v = &collect->buffer;
  assert(v->size == 0);
  for (i=0; i<n; i++) {
    add_vars_to_vector(v, a[i]);
  }
  set = vector_to_set(collect, v);
  ivector_reset(v);

 done:
  free_pstack_array(&collect->stack, a);
  return set;
}


static harray_t *bool_vars_of_term(bool_var_collector_t *collect, term_t t) {
  context_t *ctx;
  term_table_t *terms;
  simple_cache_entry_t *e;
  harray_t *set;
  composite_term_t *eq;
  term_t r;
  int32_t i;

  assert(is_boolean_term(collect->terms, t));

  set = NULL;

  ctx = collect->ctx;
  r = intern_tbl_get_root(&ctx->intern, t);
  if (term_is_true(ctx, r) || term_is_false(ctx, r)) {
    set = empty_set(collect);

  } else {

    i = index_of(r);
    assert(good_term_idx(collect->terms, i));

    terms = collect->terms;
    switch (kind_for_idx(terms, i)) {
    case UNINTERPRETED_TERM:
      set = singleton(collect, pos_occ(i));
      break;

    case ITE_TERM:
    case ITE_SPECIAL:
    case OR_TERM:
    case XOR_TERM:
      e = simple_cache_find(&collect->cache, i);
      if (e != NULL) {
	assert(e->key == i && e->tag == 0);
	set =  e->val.ptr;
      } else {
	set = bool_vars_of_composite(collect, composite_for_idx(terms, i));
	cache_bool_var_set(collect, i, set);
      }
      break;

    case EQ_TERM:
      eq = composite_for_idx(terms, i);
      if (is_boolean_term(terms, eq->arg[0])) {
	// treat i as (IFF t1 t2)
	e = simple_cache_find(&collect->cache, i);
	if (e != NULL) {
	  assert(e->key == i && e->tag == 0);
	  set =  e->val.ptr;
	} else {
	  set = bool_vars_of_composite(collect, eq);
	  cache_bool_var_set(collect, i, set);
	}
      }
      break;

    default:
      // not a pure Boolean term
      break;
    }
  }

  return set;
}


/*
 * Check whether t is purely Boolean
 */
static bool bool_term_is_pure(bool_var_collector_t *collect, term_t t) {
  return bool_vars_of_term(collect, t) != NULL;
}



/*
 * CONDITIONAL DEFINITIONS
 */

/*
 * Create a conditional definition descriptor:
 * - t = term
 * - v = value
 * - vset = set of variables
 * - n = number of conditions
 * - a[0 ... n-1] = conditions
 */
static cond_def_t *new_cond_def(term_t t, term_t v, harray_t *vset, uint32_t n, term_t *a) {
  cond_def_t *tmp;
  uint32_t i;

  assert(n <= MAX_COND_DEF_CONJUNCTS);
  tmp = (cond_def_t *) safe_malloc(sizeof(cond_def_t) + n * sizeof(term_t));
  tmp->term = t;
  tmp->value = v;
  tmp->vset = vset;
  tmp->nconds = n;
  for (i=0; i<n; i++) {
    tmp->cond[i] = a[i];
  }
  return tmp;
}



/*
 * Initialize a collector
 * - ctx = relevant context
 */
void init_cond_def_collector(cond_def_collector_t *c, context_t *ctx) {
  c->ctx = ctx;
  c->terms = ctx->terms;
  init_pvector(&c->cdefs, 0);
  init_int_array_hset(&c->store, 0);
  init_bool_var_collector(&c->collect, ctx, &c->store);
  init_ivector(&c->assumptions, 10);
  init_ivector(&c->aux, 10);
}


/*
 * Delete: free all memory
 */
void delete_cond_def_collector(cond_def_collector_t *c) {
  uint32_t i, n;

  n = c->cdefs.size;
  for (i=0; i<n; i++) {
    safe_free(c->cdefs.data[i]);
  }
  delete_pvector(&c->cdefs);
  delete_bool_var_collector(&c->collect);
  delete_int_array_hset(&c->store);
  delete_ivector(&c->assumptions);
  delete_ivector(&c->aux);
}


/*
 * Add a conditional definition to c
 */
static inline void add_cond_def(cond_def_collector_t *c, cond_def_t *def) {
  assert(def != NULL);
  pvector_push(&c->cdefs, def);
}


/*
 * For testing: print def
 */
static void print_cond_def(cond_def_collector_t *c, cond_def_t *def) {
  yices_pp_t pp;
  pp_area_t area;
  uint32_t i, n;

  area.width = 400;
  area.height = 300;
  area.offset = 0;
  area.stretch = false;
  area.truncate = true;
  init_default_yices_pp(&pp, stdout, &area);

  pp_open_block(&pp, PP_OPEN);
  pp_open_block(&pp, PP_OPEN_IMPLIES);
  n = def->nconds;
  if (n > 1) pp_open_block(&pp, PP_OPEN_AND);
  for (i=0; i<n; i++) {
    pp_term_full(&pp, c->terms, def->cond[i]);
  }
  if (n > 1) pp_close_block(&pp, true); // close and
  pp_open_block(&pp, PP_OPEN_EQ);
  pp_term_full(&pp, c->terms, def->term);
  pp_term_full(&pp, c->terms, def->value);
  pp_close_block(&pp, true); // close eq
  pp_close_block(&pp, true); // close implies
  pp_close_block(&pp, false);

  delete_yices_pp(&pp, true);
}




/*
 * CONVERSION OF ASSERTIONS TO CONDITIONAL DEFINITIONS
 */

/*
 * Add t as an assumption: follow the internalization table
 */
static void push_assumption(cond_def_collector_t *c, term_t t) {
  context_t *ctx;

  ctx = c->ctx;
  t = intern_tbl_get_root(&ctx->intern, t);
  if (term_is_true(ctx, t)) {
    t = true_term;
  } else if (term_is_false(ctx, t)) {
    t = false_term;
  }
  ivector_push(&c->assumptions, t);
}


/*
 * Compute the set of variables occurring in a[0 ... n-1]
 * - a[0 ... n-1] must all be pure Boolean terms
 */
static harray_t *bool_vars_of_array(cond_def_collector_t *c, uint32_t n, term_t *a) {
  ivector_t *v;
  harray_t *s;
  uint32_t i;

  if (n == 0) {
    s = int_array_hset_get(&c->store, 0, NULL); // empty set
  } else if (n == 1) {
    s = bool_vars_of_term(&c->collect, a[0]);
  } else {
    v = &c->aux;
    assert(v->size == 0);
    for (i=0; i<n; i++) {
      s = bool_vars_of_term(&c->collect, a[i]);
      add_vars_to_vector(v, s);
    }
    assert(vector_is_sorted(v));
    s = int_array_hset_get(&c->store, v->size, v->data);
    ivector_reset(v);
  }

  return s;
}


/*
 * Attempts to convert a formula of the form (assumptions => f) to
 * conditional definitions.
 * - the assumptions are stored in c->assumption vector
 * - f = term to explore
 */
static void cond_def_explore(cond_def_collector_t *c, term_t f);


/*
 * Explore (or t1 ... tn)
 * - if polarity is true, this is processed as (or t1 ... tn)
 * - if polarity is false, this is processed (and (not t1) ... (not t_n))
 */
static void cond_def_explore_or(cond_def_collector_t *c, composite_term_t *or, bool polarity) {
  uint32_t i, n, num_assumptions;
  term_t t, u;

  n = or->arity;
  if (polarity) {
    num_assumptions = c->assumptions.size;

    /*
     * Check whether all t_i's but one are pure Boolean.
     */
    u = NULL_TERM;
    for (i=0; i<n; i++) {
      t = or->arg[i];
      if (bool_term_is_pure(&c->collect, t)) {
	// add t as an assumption
	push_assumption(c, t);
      } else {
	if (u != NULL_TERM){
	  // we can't convert the or to a conditional definition
	  goto abort;
	}
	u = t;
      }
    }

    /*
     * u is the unique sub-term that's not purely Boolean
     * the other subterms are in the assumption vector
     * we recursively process u.
     */
    if (u != NULL_TERM) {
      cond_def_explore(c, u);
    }

  abort:
    // restore the assumption stack
    ivector_shrink(&c->assumptions, num_assumptions);


  } else {
    /*
     * Assumptions => (and (not t1) ... (not t_n))
     */
    for (i=0; i<n; i++) {
      cond_def_explore(c, opposite_term(or->arg[i]));
    }
  }
}


/*
 * Explore (ite c t1 2)
 * - if polarity is true, this is processed as (c => t1) AND (not(c) => t2)
 * - otherwise, it's processed as (c => not(t1)) AND (not c => not(t2))
 */
static void cond_def_explore_ite(cond_def_collector_t *c, composite_term_t *ite, bool polarity) {
  term_t cond;

  assert(ite->arity == 3);
  cond = ite->arg[0];
  if (bool_term_is_pure(&c->collect, cond)) {
    push_assumption(c, cond);
    cond_def_explore(c, signed_term(ite->arg[1], polarity));
    ivector_pop(&c->assumptions);

    push_assumption(c, opposite_term(cond));
    cond_def_explore(c, signed_term(ite->arg[2], polarity));
    ivector_pop(&c->assumptions);
  }
}


static void cond_def_explore(cond_def_collector_t *c, term_t f) {
  term_table_t *terms;
  cond_def_t *def;
  harray_t *set;
  term_t x, a;

  terms = c->terms;
  switch (term_kind(terms, f)) {
  case OR_TERM:
    cond_def_explore_or(c, or_term_desc(terms, f), is_pos_term(f));
    break;

  case ITE_TERM:
  case ITE_SPECIAL:
    cond_def_explore_ite(c, ite_term_desc(terms, f), is_pos_term(f));
    break;

  default:
    //    if (is_term_eq_const(terms, f, &x, &a)) {
    if (is_unint_eq_const(terms, f, &x, &a)) {
      if (c->assumptions.size <= MAX_COND_DEF_CONJUNCTS) {
	set = bool_vars_of_array(c, c->assumptions.size, c->assumptions.data);
	/*
	 * If set is empty, we ignore this definition: either the assumptions
	 * are all true or all false. In either case, normal internalization
	 * will process (x == a) or ignore it.
	 */
	if (set->nelems > 0) {
	  def = new_cond_def(x, a, set, c->assumptions.size, c->assumptions.data);
	  add_cond_def(c, def);
	}
      }
    }
    break;
  }
}



/*
 * Attempt to convert f to a conjunction of conditional definitions
 * - id = index to identify f
 * - add the defintions to c->cdefs
 */
void extract_conditional_definitions(cond_def_collector_t *c, term_t f) {
  ivector_reset(&c->assumptions);
  cond_def_explore(c, f);
}


/*
 * Process all conditional definitions for the same term x
 * - the definitions are stored in a[0 ... n-1]
 */
static void analyze_term_cond_def(cond_def_collector_t *c, term_t x, cond_def_t **a, uint32_t n) {
  cond_def_t *d;
  uint32_t i;

  printf("\nDefinitions for term ");
  print_term_name(stdout, c->terms, x);
  printf("\n");
  for (i=0; i<n; i++) {
    d = a[i];
    assert(d->term == x);
    print_cond_def(c, d);
  }
  printf("---\n");
}

/*
 * Sort the conditional definitions:
 * - we want all defintions with the same variable to be adjacent in c->cdefs
 */
// comparison function: return true if d1 < d2 in this ordering
static bool cdef_lt(void *data, void *d1, void *d2) {
  return ((cond_def_t *) d1)->term  < ((cond_def_t *) d2)-> term;
}

/*
 * Process all conditional definitions in c->cdefs
 */
void analyze_conditional_definitions(cond_def_collector_t *c) {
  uint32_t i, j, n;
  cond_def_t **a;
  term_t x;

  n = c->cdefs.size;
  if (n > 0) {
    ptr_array_sort2(c->cdefs.data, n, NULL, cdef_lt);

    a = (cond_def_t **) c->cdefs.data;
    i = 0;
    j = 0;
    while (i < n) {
      assert(i == j);

      /*
       * find segment: [i ... j-1]: that containts all defs with the
       * same variable x
       */
      x = a[i]->term;
      do { j ++; } while (j < n && a[j]->term == x);
      assert(i < j);
      analyze_term_cond_def(c, x, a + i, j - i);
      i = j;
    }
  }
}
