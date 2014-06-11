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
 * Build sets
 */
static harray_t *empty_set(int_array_hset_t *store) {
  return int_array_hset_get(store, 0, NULL); // this returns a non-NULL harray
}

static harray_t *singleton(int_array_hset_t *store, term_t t) {
  assert(is_pos_term(t));
  return int_array_hset_get(store, 1, &t);
}

static harray_t *vector_to_set(int_array_hset_t *store, ivector_t *v) {
  assert(vector_is_sorted(v));
  return int_array_hset_get(store, v->size, v->data);
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
  collect->budget = 0;
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
  set = vector_to_set(collect->store, v);
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

  if (collect->budget > 0) {
    collect->budget --;

    ctx = collect->ctx;
    r = intern_tbl_get_root(&ctx->intern, t);
    if (term_is_true(ctx, r) || term_is_false(ctx, r)) {
      set = empty_set(collect->store);

    } else {

      i = index_of(r);
      assert(good_term_idx(collect->terms, i));

      terms = collect->terms;
      switch (kind_for_idx(terms, i)) {
      case UNINTERPRETED_TERM:
	set = singleton(collect->store, pos_occ(i));
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
  }

  return set;
}


/*
 * Check whether t is purely Boolean
 * - set a budget of 100 = max number of recursive calls to bool_vars_of_term
 */
static bool bool_term_is_pure(bool_var_collector_t *collect, term_t t) {
  collect->budget = 100;
  return bool_vars_of_term(collect, t) != NULL;
}


/*
 * Collect the variables of t when t is known to be small and pure Boolean
 */
static harray_t *get_bool_vars_of_term(bool_var_collector_t *collect, term_t t) {
  collect->budget = UINT32_MAX;
  return bool_vars_of_term(collect, t);
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
  init_simple_cache(&c->cache, 0);
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
  delete_simple_cache(&c->cache);
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
 * For testing: print the variables in s
 */
static void print_vset(cond_def_collector_t *c, harray_t *s) {
  uint32_t i, n;

  n = s->nelems;
  for (i=0; i<n; i++) {
    if (i > 0) printf(" ");
    print_term_full(stdout, c->terms, s->data[i]);
  }
}


/*
 * For testing: print a truth table
 * - ttbl = 64bit encoding for the table
 * - x[0 ... n-1] = Boolean variables in increasing order
 */
static void print_truth_tbl(cond_def_collector_t *c, uint64_t ttbl, term_t *x, uint32_t n) {
  uint32_t i, k, max_k;
  uint64_t mask, bit;

  assert(array_is_sorted(x, n) && n <= 6);

  for (i=0; i<n; i++) {
    assert(is_boolean_term(c->terms, x[i]) &&
	   is_pos_term(x[i]) &&
	   term_kind(c->terms, x[i]) == UNINTERPRETED_TERM);

    printf("  %6s", term_name(c->terms, x[i]));
  }
  printf("\n");

  max_k = (1 << n); // 2^n
  assert(max_k <= 64);
  mask = 1;  // select bit 0 of ttbl

  for (k=0; k<max_k; k++) {
    for (i=0; i<n; i++) {
      bit = (k & (1 << i));
      assert(bit == 0 || bit == (1 << i));
      if (bit == 0) {
	printf("  %6s", "0");
      } else {
	printf("  %6s", "1");
      }
    }
    bit = (ttbl & mask);
    assert(bit == 0 || bit == mask);
    if (bit == 0) {
      printf("  |    0\n");
    } else {
      printf("  |    1\n");
    }
    mask <<= 1;
  }

  printf("\n");
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
    s = empty_set(&c->store);
  } else if (n == 1) {
    s = get_bool_vars_of_term(&c->collect, a[0]);
  } else {
    v = &c->aux;
    assert(v->size == 0);
    for (i=0; i<n; i++) {
      s = get_bool_vars_of_term(&c->collect, a[i]);
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
	// add (not t) as an assumption
	push_assumption(c, opposite_term(t));
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
 * TRUTH TABLES
 */

/*
 * Given a term t that's a Boolean combination of n variables x[0] ... x[n-1],
 * we can encode the truth table for t as a bit-vector of 2^n elements.
 * We limit this to n <= 6, then we can represent the truth table as an unsigned
 * 64 bit integer.
 *
 * For example, if n=3 the truth table for t will look like
 *
 *     x[2]   x[1]   x[0]   |  t
 *   ------------------------------
 *       0      0      0    |  t_0
 *       0      0      1    |  t_1
 *       0      1      0    |  t_2
 *       0      1      1    |  t_3
 *       1      0      0    |  t_4
 *       1      0      1    |  t_5
 *       1      1      0    |  t_6
 *       1      1      1    |  t_7
 *
 * The truth table for t is then 8 word [t_7 t_6 ... t_0] (from high-order
 * to low-order). We extend it to 64 bit by repeating this pattern 8 times.
 *
 * All functions below compute the truth-table for a term t, assuming a fixed
 * set of Boolean variables x[0 ... n-1] (with n <= 6). The variables are
 * sorted in increasing order and are all distinct.
 */


/*
 * Constant arrays: truth tables for variables x[0 ... 5]
 */
static const uint64_t truth_tbl_var[6] = {
  0xAAAAAAAAAAAAAAAAu,  // 1010 1010 1010 1010 1010 1010 1010 1010 ...
  0xCCCCCCCCCCCCCCCCu,  // 1100 1100 1100 1100 1100 1100 1100 1100 ...
  0xF0F0F0F0F0F0F0F0u,  // 1111 0000 1111 0000 1111 0000 1111 0000 ...
  0xFF00FF00FF00FF00u,  // 1111 1111 0000 0000 1111 1111 0000 0000 ...
  0xFFFF0000FFFF0000u,  // 1111 1111 1111 1111 0000 0000 0000 0000 ..
  0xFFFFFFFF00000000u,
};


/*
 * Main procedure: recursively compute the truth table of t
 * - t must be a pure Boolean term
 * - the variables of t must be included in { x[0] ... x[n-1] }
 * - n must be no more than 6
 */
static uint64_t truth_tbl_of_term(cond_def_collector_t *c, term_t t, term_t *x, uint32_t n);

/*
 * Truth table for a variable t
 * - t must be present in x[0 ... n-1]
 */
static uint64_t truth_tbl_of_var(term_t t, term_t *x, uint32_t n) {
  uint32_t i;

  assert(is_pos_term(t) && array_is_sorted(x, n) && n <= 6);

  for (i=0; i<n; i++) {
    if (t == x[i]) break;
  }
  assert(i < n);

  return truth_tbl_var[i];
}


/*
 * Store truth table of idx in c->cache
 */
static void cache_truth_tbl(cond_def_collector_t *c, int32_t idx, uint64_t ttbl) {
  assert(good_term_idx(c->terms, idx));
  simple_cache_store_u64(&c->cache, idx, 0x1a, ttbl); // tag = 0x1a (could be anything)
}

/*
 * Recursive computation for composite terms:
 * - idx is a valid term index in the term table
 * - we use c->cache to avoid blowing up
 */
static uint64_t truth_tbl_of_ite(cond_def_collector_t *c, int32_t idx, term_t *x, uint32_t n) {
  simple_cache_entry_t *e;
  composite_term_t *ite;
  uint64_t tc, ta, tb, r;

  assert(kind_for_idx(c->terms, idx) == ITE_TERM ||
	 kind_for_idx(c->terms, idx) == ITE_SPECIAL);

  e = simple_cache_find(&c->cache, idx);
  if (e != NULL) {
    assert(e->key == idx && e->tag == 0x1a);
    return e->val.u64;
  }

  ite = composite_for_idx(c->terms, idx);
  assert(ite->arity == 3);

  tc = truth_tbl_of_term(c, ite->arg[0], x, n); // condition
  ta = truth_tbl_of_term(c, ite->arg[1], x, n); // then part
  tb = truth_tbl_of_term(c, ite->arg[2], x, n); // else part
  r = (tc & ta) | (~tc & tb);

  cache_truth_tbl(c, idx, r);

  return r;
}

static uint64_t truth_tbl_of_or(cond_def_collector_t *c, int32_t idx, term_t *x, uint32_t n) {
  simple_cache_entry_t *e;
  composite_term_t *or;
  uint64_t r;
  uint32_t i, m;

  assert(kind_for_idx(c->terms, idx) == OR_TERM);

  e = simple_cache_find(&c->cache, idx);
  if (e != NULL) {
    assert(e->key == idx && e->tag == 0x1a);
    return e->val.u64;
  }

  r = 0;
  or = composite_for_idx(c->terms, idx);
  m = or->arity;
  for (i=0; i<m; i++) {
    r |= truth_tbl_of_term(c, or->arg[i], x, n);
  }

  cache_truth_tbl(c, idx, r);

  return r;
}

static uint64_t truth_tbl_of_xor(cond_def_collector_t *c, int32_t idx, term_t *x, uint32_t n) {
  simple_cache_entry_t *e;
  composite_term_t *xor;
  uint64_t r;
  uint32_t i, m;

  assert(kind_for_idx(c->terms, idx) == XOR_TERM);

  e = simple_cache_find(&c->cache, idx);
  if (e != NULL) {
    assert(e->key == idx && e->tag == 0x1a);
    return e->val.u64;
  }

  r = 0;
  xor = composite_for_idx(c->terms, idx);
  m = xor->arity;
  for (i=0; i<m; i++) {
    r ^= truth_tbl_of_term(c, xor->arg[i], x, n);
  }

  cache_truth_tbl(c, idx, r);

  return r;
}

static uint64_t truth_tbl_of_iff(cond_def_collector_t *c, int32_t idx, term_t *x, uint32_t n) {
  simple_cache_entry_t *e;
  composite_term_t *iff;
  uint64_t ta, tb, r;

  assert(kind_for_idx(c->terms, idx) == EQ_TERM);

  e = simple_cache_find(&c->cache, idx);
  if (e != NULL) {
    assert(e->key == idx && e->tag == 0x1a);
    return e->val.u64;
  }

  iff = composite_for_idx(c->terms, idx);
  assert(iff->arity == 2);

  ta = truth_tbl_of_term(c, iff->arg[0], x, n);
  tb = truth_tbl_of_term(c, iff->arg[1], x, n);
  r = ~(ta ^ tb); // not xor

  cache_truth_tbl(c, idx, r);

  return r;
}

static uint64_t truth_tbl_of_term(cond_def_collector_t *c, term_t t, term_t *x, uint32_t n) {
  context_t *ctx;
  term_table_t *terms;
  uint64_t ttbl;
  term_t r;
  int32_t i;

  assert(is_boolean_term(c->terms, t));

  ctx = c->ctx;
  r = intern_tbl_get_root(&ctx->intern, t);
  if (term_is_true(ctx, r)) {
    return 0xFFFFFFFFFFFFFFFFu; // all true
  }

  if (term_is_false(ctx, r)) {
    return 0x0000000000000000u; // all false
  }

  i = index_of(r);
  terms = c->terms;

  assert(good_term_idx(c->terms, i));

  switch (kind_for_idx(terms, i)) {
  case UNINTERPRETED_TERM:
    ttbl = truth_tbl_of_var(pos_occ(i), x, n);
    break;

  case ITE_TERM:
  case ITE_SPECIAL:
    ttbl = truth_tbl_of_ite(c, i, x, n);
    break;

  case OR_TERM:
    ttbl = truth_tbl_of_or(c, i, x, n);
    break;

  case XOR_TERM:
    ttbl = truth_tbl_of_xor(c, i, x, n);
    break;

  case EQ_TERM:
    // this must be an equality between Boolean terms
    ttbl = truth_tbl_of_iff(c, i, x, n);
    break;

  default:
    // this should not happen. t is a pure Boolean term
    assert(false);
    ttbl = 0; // prevent a GCC warning
    break;
  }

  /*
   * ttbl is the truth table for i.
   * if  r is not(i), we flip all bits
   */
  if (is_neg_term(r)) {
    ttbl = ~ttbl;
  }

  return ttbl;
}


/*
 * Truth table for the conjunction (a[0] /\ ... /\ a[m-1])
 */
static uint64_t truth_tbl_of_array(cond_def_collector_t *c, uint32_t m, term_t *a, term_t *x, uint32_t n) {
  uint64_t r;
  uint32_t i;

  r = 0xFFFFFFFFFFFFFFFFu;
  for (i=0; i<m; i++) {
    r &= truth_tbl_of_term(c, a[i], x, n);
  }

  return r;
}


/*
 * ANALYSIS OF CONDITIONAL DEFINITIONS
 */

/*
 * Compute the union of all vsets in a[0] ... a[n-1]
 * - n must be positive
 * - return NULL if the union has more than 6 elements
 */
static harray_t *merge_vsets(cond_def_collector_t *c, cond_def_t **a, uint32_t n) {
  harray_t *s, *r;
  ivector_t *v;
  uint32_t i;

  assert(n > 0);

  r = NULL;
  s = a[0]->vset;
  if (s->nelems <= 6) {
    // it's common for all sets to be equal.
    for (i=1; i<n; i++) {
      if (s != a[i]->vset) break;
    }

    if (i == n) {
      // a[0 ... n-1] all have the set same vset
      r = s;
    } else {
      assert(i < n);

      // merge s with a[i] ... a[n-1];
      v = &c->aux;
      assert(v->size == 0);
      add_vars_to_vector(v, s);
      do {
	add_vars_to_vector(v, a[i]->vset);
	i ++;
      } while (v->size <= 6 && i < n);

      if (v->size <= 6) {
	r = vector_to_set(&c->store, v);
      }
      ivector_reset(v);
    }
  }

  return r;
}


/*
 * Process all conditional definitions for the same term x
 * - the definitions are stored in a[0 ... n-1]
 */
static void analyze_term_cond_def(cond_def_collector_t *c, term_t x, cond_def_t **a, uint32_t n) {
  cond_def_t *d;
  harray_t *s;
  uint64_t ttbl;
  uint32_t i;

  printf("\nDefinitions for term ");
  print_term_name(stdout, c->terms, x);
  printf("\n");
  for (i=0; i<n; i++) {
    d = a[i];
    assert(d->term == x);
    print_cond_def(c, d);
    s = d->vset;
    if (s->nelems <= 6) {
      ttbl = truth_tbl_of_array(c, d->nconds, d->cond, s->data, s->nelems);
      print_truth_tbl(c, ttbl, s->data, s->nelems);
    }
  }

  s = merge_vsets(c, a, n);
  if (s != NULL) {
    printf("Merged var set: ");
    print_vset(c, s);
    printf("\n");
  } else {
    printf("More than six variables\n");
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
