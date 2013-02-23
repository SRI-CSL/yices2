/*
 * SUPPORT FOR BREAKING SYMMETRIES IN UF FORMULAS
 */

#include <stdbool.h>
#include <assert.h>

#include "int_array_sort.h"
#include "memalloc.h"
#include "symmetry_breaking.h"



/*
 * RANGE-CONSTRAINT RECORDS
 */

/*
 * Initialize r for the set of constants a[0 ... n-1]
 * - a must be sorted
 * - arrays r->trm/r->idx are allocated with default initial size
 */
static void init_rng_record(rng_record_t *r, term_t *a, uint32_t n) {  
  term_t *tmp;
  uint32_t i, nt;

  assert(n <= UINT32_MAX/sizeof(term_t));

  tmp = (term_t *) safe_malloc(n * sizeof(term_t));
  for (i=0; i<n; i++) {
    tmp[i] = a[i];
  }

  nt = DEF_RNG_RECORD_SIZE;
  assert(nt <= MAX_RNG_RECORD_SIZE);

  r->cst = tmp;
  r->trm = (term_t *) safe_malloc(nt * sizeof(term_t));
  r->idx = (uint32_t *) safe_malloc(nt * sizeof(uint32_t));
  r->num_constants = n;
  r->num_terms = 0;
  r->size = nt;
}


/*
 * Make arrays trm and idx 50% larger
 */
static void extend_rng_record(rng_record_t *r) {
  uint32_t n;

  n = r->size;
  n += n >> 1;
  assert(n > r->size);

  if (n > MAX_RNG_RECORD_SIZE) {
    out_of_memory();
  }
  r->trm = (term_t *) safe_realloc(r->trm, n * sizeof(term_t));
  r->idx = (uint32_t *) safe_realloc(r->idx, n * sizeof(uint32_t));
  r->size = n;
}


/*
 * Add pair (t, id) to the record
 */
static void rng_record_add(rng_record_t *r, term_t t, uint32_t id) {
  uint32_t i;

  i = r->num_terms;
  if (i == r->size) {
    extend_rng_record(r);
  }
  assert(i < r->size);
  r->trm[i] = t;
  r->idx[i] = id;
  r->num_terms = i+1;
}


/*
 * Delete the whole thing
 */
static void delete_rng_record(rng_record_t *r) {
  safe_free(r->cst);
  safe_free(r->trm);
  safe_free(r->idx);
}


/*
 * Check whether r->cst is equal to a[0 ... n-1]
 * - a must be sorted
 */
static bool equal_arrays(term_t *a, term_t *b, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (a[i] != b[i]) {
      return false;
    }
  }

  return true;
}

static bool rng_record_match(rng_record_t *r, term_t *a, uint32_t n) {
  return r->num_constants == n && equal_arrays(r->cst, a, n);
}





/*
 * ARRAY OF RANGE-CONSTRAINT RECORDS
 */

static void init_rng_vector(rng_vector_t *v) {
  v->data = NULL;
  v->nelems = 0;
  v->size = 0;
}

static void extend_rng_vector(rng_vector_t *v) {
  uint32_t n;

  n = v->size;
  if (n == 0) {
    /*
     *  initial allocation: use DEF_RNG_VECTOR_SIZE
     */
    n = DEF_RNG_VECTOR_SIZE;
    assert(v->data == NULL && n <= MAX_RNG_VECTOR_SIZE);

    v->data = (rng_record_t *) safe_malloc(n * sizeof(rng_record_t));
    v->size = n;
  } else {
    /*
     * Make it 50% larger
     */
    n += (n>>1) + 1;
    assert(n > v->size);

    if (n > MAX_RNG_VECTOR_SIZE) {
      out_of_memory();
    }

    v->data = (rng_record_t *) safe_realloc(v->data, n * sizeof(rng_record_t));
    v->size = n;
  }
}


static void delete_rng_vector(rng_vector_t *rng) {
  uint32_t i, n;

  n = rng->nelems;
  for (i=0; i<n; i++) {
    delete_rng_record(rng->data + i);
  }
  safe_free(rng->data);
  rng->data = NULL;
}



/*
 * Add a range constraint to v:
 * - a[0 ... n-1] = the constant for this constraint
 * - t = term, id = index 
 * - a must be sorted.
 */
static void add_range_constraint(rng_vector_t *v, term_t *a, uint32_t n, term_t t, uint32_t id) {
  uint32_t i, p;
  
  p = v->nelems;
  for (i=0; i<p; i++) {
    if (rng_record_match(v->data + i, a, n)) {
      rng_record_add(v->data + i, t, id);
      return;
    }
  }

  // create a new record
  if (i == v->size) {
    extend_rng_vector(v);
  }
  assert(i < v->size);
  init_rng_record(v->data + i, a, n);
  rng_record_add(v->data + i, t, id);
  v->nelems = i+1;
}



/*
 * FORMULA PROCESSING
 */

/*
 * For breadth-first term exploration we use a queue + cache
 * - terms to be processed are in the queue 
 * - terms already processeed or already in the queue are in cache
 */

/*
 * Add t to queue and cache if it's not already in the cache
 */
static void push_term(int_queue_t *queue, int_hset_t *cache, term_t t) {
  if (int_hset_add(cache, t)) {
    int_queue_push(queue, t);
  }
}

/*
 * Add all children of composite c to the queue/cache
 */
static void push_children(int_queue_t *queue, int_hset_t *cache, composite_term_t *c) {
  uint32_t i, n;

  n = c->arity;
  for (i=0; i<n; i++) {
    push_term(queue, cache, c->arg[i]);
  }
}


/*
 * Check whether t is a constant
 * - t must have positive polarity
 */
static bool term_is_constant(term_table_t *table, term_t t) {
  term_kind_t kind;

  assert(is_pos_term(t));
  kind = term_kind(table, t);
  return kind == CONSTANT_TERM || kind == UNINTERPRETED_TERM;
}

static bool term_is_uconst(term_table_t *table, term_t t) {
  assert(is_pos_term(t));
  return term_kind(table, t) == UNINTERPRETED_TERM;
}


/*
 * Check for equality that trivially reduce to false
 */
static bool false_eq(term_table_t *table, term_t t1, term_t t2) {
  return t1 != t2 && term_kind(table, t1) == CONSTANT_TERM && term_kind(table, t2) == CONSTANT_TERM;
}

/*
 * Check whether t is of the following formsL
 * - false term
 * - disjuction: (or t1 ... tn_
 * - equality (x == constant) or (constant == x)
 * 
 * The function retuns one of the following codes:
 * - MATCH_FALSE
 * - MATCH_OR
 * - MATCH_EQ
 * - MATCH_OTHER
 *
 * And in case of MATCH_EQ it stores the constant in *a and the other
 * term in *x. Warning: *x may be uninterpreted.
 */
typedef enum match_code {
  MATCH_FALSE,
  MATCH_OR,
  MATCH_EQ,
  MATCH_OTHER,
} match_code_t;

static match_code_t match_term(context_t *ctx, term_t t, term_t *a, term_t *x) {
  composite_term_t *eq;
  term_table_t *terms;
  match_code_t code;
  term_t t1, t2;
  
  if (term_is_false(ctx, t)) {
    code = MATCH_FALSE;
  } else {
    code = MATCH_OTHER;
    if (is_pos_term(t)) {
      terms = ctx->terms;
      if (term_kind(terms, t) == OR_TERM) {
	code = MATCH_OR;
      } else if (term_kind(terms, t) == EQ_TERM) {
	eq = eq_term_desc(terms, t);
	t1 = intern_tbl_get_root(&ctx->intern, eq->arg[0]);
	t2 = intern_tbl_get_root(&ctx->intern, eq->arg[1]);
	if (false_eq(terms, t1, t2)) {
	  code = MATCH_FALSE;
	} else if (term_is_constant(terms, t1)) {
	  *a = t1;
	  *x = t2;
	  code = MATCH_EQ;
	} else if (term_is_constant(terms, t2)) {
	  *a = t2;
	  *x = t1;
	  code = MATCH_EQ;
	}
      }
    }
  }

  return code;
}


/*
 * Check whether f is a range constraint
 * - if so return a term t and fill in vector v with the formula's constants
 * - otherwise, return NULL_TERM
 *
 * Side effect: use queue and cache.
 * v may be modified even if the function returns NULL_TERM.
 */
static term_t formula_is_range_constraint(sym_breaker_t *breaker, term_t f, ivector_t *v) {
  int_queue_t *queue;
  int_hset_t *cache;
  term_table_t *terms;
  intern_tbl_t *intern;
  term_t r, t;
  term_t x, a, y, b;
  uint32_t neqs;

  queue = &breaker->queue;
  cache = &breaker->cache;
  terms = breaker->terms;
  intern = &breaker->ctx->intern;

  assert(int_queue_is_empty(queue) && int_hset_is_empty(cache));
  push_term(queue, cache, f);

  neqs = 0;
  t = NULL_TERM;

  y = NULL_TERM; // prevent GCC warning
  b = NULL_TERM; // prevent GCC warning

  /*
   * Invariants:
   * - neqs = number of equality atoms seen so far
   * - if neq == 1, then the first equality is stored as (y == b) where b is a constant
   * - if neq >= 2, then all equalities seen so far were of the form (x == constant)
   */
  do {
    // r := root of the first term in the queue
    r = intern_tbl_get_root(intern, int_queue_pop(queue));

    switch (match_term(breaker->ctx, r, &a, &x)) {
    case MATCH_FALSE: // skip false terms
      break;

    case MATCH_OR:
      push_children(queue, cache, or_term_desc(terms, r));
      break;

    case MATCH_EQ:
      assert(term_is_constant(terms, a));
      if (neqs == 0) {
	y = x; b = a;
      } else if (neqs == 1) {
	/*
	 * First equality: (y == b). Second equality: (x == a)
	 */
	if (y == x) { 
	  // y is the common term, a and b are constant	  
	  ivector_push(v, b);
	  ivector_push(v, a);
	} else if (y == a && term_is_uconst(terms, x)) {
	  // y is the common term, b and x are constant
	  ivector_push(v, b);
	  ivector_push(v, a);	  
	} else if (x == b && term_is_uconst(terms, y)) {
	  // b is the common term, y and a are constant
	  ivector_push(v, y);
	  ivector_push(v, a);
	  y = b;
	} else if (a == b && term_is_uconst(terms, y) && term_is_uconst(terms, x)) {
	  // b is the common term, y and x are constant
	  ivector_push(v, y);
	  ivector_push(v, x);
	  y = b;
	} else {
	  // abort
	  goto done;
	}

      } else {
	/*
	 * All equalities so far have the form (y == constant)
	 * - the current equality is (x == a)
	 */
	if (y == x) {
	  ivector_push(v, a); // match
	} else if (y == a && term_is_constant(terms, x)) {
	  ivector_push(v, x); // swap a and x
	} else {
	  // no match
	  goto done;
	}	
      }
      neqs ++;
      break;

    default:
      // abort
      goto done;
    }
  } while (! int_queue_is_empty(queue));

  assert(y != NULL_TERM);
  t = y;

 done:
  int_queue_reset(queue);
  int_hset_reset(cache);

  return t;
}



/*
 * SYMMETRY BREAKER
 */

/*
 * Initialize sym_breaker
 * - ctx = relevant context
 */
void init_sym_breaker(sym_breaker_t *breaker, context_t *ctx) {
  breaker->ctx = ctx;
  breaker->terms = ctx->terms;
  init_rng_vector(&breaker->range_constraints);
  init_int_queue(&breaker->queue, 0);
  init_int_hset(&breaker->cache, 0);
  init_ivector(&breaker->aux, 10);
}


/*
 * Delete it: free all memory it uses
 */
void delete_sym_breaker(sym_breaker_t *breaker) {
  delete_rng_vector(&breaker->range_constraints);
  delete_int_queue(&breaker->queue);
  delete_int_hset(&breaker->cache);
  delete_ivector(&breaker->aux);
}


/*
 * Collect all domain constraints from ctx->top_formulas
 * - all constraints found are added the range_constraint record
 */
void collect_range_constraints(sym_breaker_t *breaker) {
  ivector_t *formulas;
  ivector_t *v;
  uint32_t i, n;
  term_t t;
  
  v = &breaker->aux;
  formulas = &breaker->ctx->top_formulas;
  n = formulas->size;
  for (i=0; i<n; i++) {
    ivector_reset(v);
    t = formula_is_range_constraint(breaker, formulas->data[i], v);
    if (t != NULL_TERM) {
      int_array_sort(v->data, v->size); // sort the constants
      add_range_constraint(&breaker->range_constraints, v->data, v->size, t, i);
    }
  }
}

