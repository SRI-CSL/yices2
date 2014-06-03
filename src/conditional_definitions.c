/*
 * ATTEMPT TO LEARN CONSTRAINTS ON VARIABLES FROM CONDITIONAL DEFINITIONS
 */

#include <assert.h>

#include "memalloc.h"
#include "term_utils.h"
#include "conditional_definitions.h"


#if 1

#include <stdio.h>
#include <inttypes.h>

#include "term_printer.h"

#endif


/*
 * Create a conditional definition descriptor:
 * - t = term
 * - v = value
 * - n = number of conditions
 * - a[0 ... n-1] = conditions
 */
static cond_def_t *new_cond_def(term_t t, term_t v, uint32_t n, term_t *a) {
  cond_def_t *tmp;
  uint32_t i;

  assert(n <= MAX_COND_DEF_CONJUNCTS);
  tmp = (cond_def_t *) safe_malloc(sizeof(cond_def_t) + n * sizeof(term_t));
  tmp->term = t;
  tmp->value = v;
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
  init_ivector(&c->assumptions, 10);
  init_int_queue(&c->queue, 0);
  init_int_hset(&c->cache, 0);
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
  delete_ivector(&c->assumptions);
  delete_int_queue(&c->queue);
  delete_int_hset(&c->cache);
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
  pp_string(&pp, "Conditional def:");
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
 * ASSUMPTIONS/CONDITIONS
 */

/*
 * Add term t to c->queue and c->cache it t isn't in the cache
 */
static void cond_def_enqueue(cond_def_collector_t *c, term_t t) {
  if (int_hset_add(&c->cache, t)) {
    int_queue_push(&c->queue, t);
  }
}

// or is (or t1 ... t_n): enqueue not(t1) ... not(tn)
static void cond_def_enqueue_conjuncts(cond_def_collector_t *c, composite_term_t *or) {
  uint32_t i, n;

  n = or->arity;
  for (i=0; i<n; i++) {
    cond_def_enqueue(c, opposite_term(or->arg[i]));
  }
}


/*
 * When processing formulas, we store conditions into vector c->assumptions
 * - we also flatten assumptions of the form (not (or a[0] ... a[k])) into
 *   their conjuncts.
 * - for this flattening, we use c->queue and c->cache.
 */
static void cond_def_push_assumption(cond_def_collector_t *c, term_t t) {
  term_table_t *terms;
  intern_tbl_t *intern;
  term_t r;

  assert(int_queue_is_empty(&c->queue) && int_hset_is_empty(&c->cache));

  terms = c->terms;
  intern = &c->ctx->intern;

  cond_def_enqueue(c, t);
  do {
    // r := root of the first term in the queue
    r = intern_tbl_get_root(intern, int_queue_pop(&c->queue));
    if (term_is_false(c->ctx, r)) {
      // add false_term as the last assumption
      ivector_push(&c->assumptions, false_term);
      goto done;
    }
    if (!term_is_true(c->ctx, r)) {
      if (is_neg_term(r) && term_kind(terms, r) == OR_TERM) {
	cond_def_enqueue_conjuncts(c, or_term_desc(terms, r));
      } else {
	// add r as an assumption
	ivector_push(&c->assumptions, r);
      }
    }
  } while (! int_queue_is_empty(&c->queue));

 done:
  int_queue_reset(&c->queue);
  int_hset_reset(&c->cache);
}



/*
 * CONVERSION OF ASSERTIONS TO CONDITIONAL DEFINITIONS
 */

/*
 * Attempts to convert a formula of the form (assumptions => f) to
 * conditional definitions.
 * - the assumptions are stored in c->assumption vector
 * - f = term to explore
 * - the numebr of assumptions must be not more than MAX_COND_DEF_CONJUNCTS
 */
static void cond_def_explore(cond_def_collector_t *c, term_t f);


/*
 * - or is (or t[0] ... t[n-1])
 * - i is an index between 0 and n-1
 * Add (not t[j]) for j /= i as assumptions then explore t[i]
 */
static void cond_def_explore_disjunct(cond_def_collector_t *c, composite_term_t *or, uint32_t i) {
  uint32_t num_assumptions;
  uint32_t j, n;

  assert(0 <= i && i < or->arity);

  num_assumptions = c->assumptions.size;

  n = or->arity;
  for (j=0; j<n; j++) {
    if (j != i) {
      cond_def_push_assumption(c, opposite_term(or->arg[j]));
    }
  }

  if (c->assumptions.size <= MAX_COND_DEF_CONJUNCTS) {
    cond_def_explore(c, or->arg[i]);
  }

  // restore the assumption stack
  ivector_shrink(&c->assumptions, num_assumptions);
}


/*
 * Explore (or t1 ... tn)
 * - if polary is true, this is processed as (or t1 ... tn)
 * - if polarity is false, this is processed (and (not t1) ... (not t_n))
 */
static void cond_def_explore_or(cond_def_collector_t *c, composite_term_t *or, bool polarity) {
  uint32_t i, n;

  n = or->arity;
  if (polarity) {
    /*
     * To avoid blowing up, we stop exploring if n + num_assumptions is too large
     */
    for (i=0; i<n; i++) {
      cond_def_explore_disjunct(c, or, i);
    }
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
  uint32_t num_assumptions;

  assert(ite->arity == 3);

  num_assumptions = c->assumptions.size;

  cond_def_push_assumption(c, ite->arg[0]);
  if (c->assumptions.size <= MAX_COND_DEF_CONJUNCTS) {
    cond_def_explore(c, signed_term(ite->arg[1], polarity));
  }
  ivector_shrink(&c->assumptions, num_assumptions);

  cond_def_push_assumption(c, opposite_term(ite->arg[0]));
  if (c->assumptions.size <= MAX_COND_DEF_CONJUNCTS) {
    cond_def_explore(c, signed_term(ite->arg[2], polarity));
  }
  ivector_shrink(&c->assumptions, num_assumptions);
}


static void cond_def_explore(cond_def_collector_t *c, term_t f) {
  term_table_t *terms;
  cond_def_t *def;
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
    if (is_term_eq_const(terms, f, &x, &a)) {
      assert(c->assumptions.size <= MAX_COND_DEF_CONJUNCTS);
      def = new_cond_def(x, a, c->assumptions.size, c->assumptions.data);
      add_cond_def(c, def);
      print_cond_def(c, def);
    }
    break;
  }
}




/*
 * Attempt to convert f to a conjunction of conditional definitions
 * - add the defintions to c->cdefs
 */
void extract_conditional_definitions(cond_def_collector_t *c, term_t f) {
  ivector_reset(&c->assumptions);
  cond_def_explore(c, f);
}
