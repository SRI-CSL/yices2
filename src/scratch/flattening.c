/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Support for flattening formulas to conjuncts and to disjuncts
 */

#include <assert.h>

#include "scratch/flattening.h"


/*
 * Initialization
 */
void init_flattener(flattener_t *flat, term_manager_t *mngr) {
  flat->terms = term_manager_get_terms(mngr);
  flat->manager = mngr;
  init_int_queue(&flat->queue, 0);
  init_int_hset(&flat->cache, 128);
  init_ivector(&flat->resu, 64);
}


/*
 * Reset queue/cache and vector
 */
void reset_flattener(flattener_t *flat) {
  int_queue_reset(&flat->queue);
  int_hset_reset(&flat->cache);
  ivector_reset(&flat->resu);
}


/*
 * Delete
 */
void delete_flattener(flattener_t *flat) {
  delete_int_queue(&flat->queue);
  delete_int_hset(&flat->cache);
  delete_ivector(&flat->resu);
}



/*
 * Check whether t is in the cache.
 * If not, add t to the cache and to the end of the queue
 */
static void flattener_push_term(flattener_t *flat, term_t t) {
  if (int_hset_add(&flat->cache, t)) {
    int_queue_push(&flat->queue, t);
  }
}


/*
 * Flatten all terms in flat->queue to conjuncts
 * - all terms in the queue must also be in the cache
 * - f_ite: if true, flatten (ite c a b)
 * - f_iff: if true, flatten (iff a b)
 */
static void flattener_build_conjuncts(flattener_t *flat, bool f_ite, bool f_iff) {
  term_table_t *terms;
  int_queue_t *queue;
  composite_term_t *d;
  term_t t, u, v;
  uint32_t i, n;

  queue = &flat->queue;
  terms = flat->terms;

  while (! int_queue_is_empty(queue)) {
    t = int_queue_pop(queue);

    switch (term_kind(terms, t)) {
    case ITE_TERM:
    case ITE_SPECIAL:
      d = ite_term_desc(terms, t);
      assert(d->arity == 3);
      if (f_ite && is_boolean_term(terms, d->arg[1])) {
        assert(is_boolean_term(terms, d->arg[2]));
        /*
         * If t is (ite C A B)
         *    u := (C => A)
         *    v := (not C => B)
         * Otherwise, t is (not (ite C A B))
         *    u := (C => not A)
         *    v := (not C => not B)
         */
        u = d->arg[1];  // A
        v = d->arg[2];  // B
        if (is_neg_term(t)) {
          u = opposite_term(u);
          v = opposite_term(v);
        }
        u = mk_implies(flat->manager, d->arg[0], u); // (C => u)
        v = mk_implies(flat->manager, opposite_term(d->arg[0]), v); // (not C) => v
        flattener_push_term(flat, u);
        flattener_push_term(flat, v);
        continue;
      }
      break;

    case EQ_TERM:
      d = eq_term_desc(terms, t);
      assert(d->arity == 2);
      if (f_iff && is_boolean_term(terms, d->arg[0])) {
        assert(is_boolean_term(terms, d->arg[1]));
        /*
         * t is either (iff A B) or (not (iff A B)):
         */
        u = d->arg[0]; // A
        v = d->arg[1]; // B
        if (is_neg_term(t)) {
          u = opposite_term(u);
        }
        // flatten to (u => v) and (v => u)
        t = mk_implies(flat->manager, u, v); // (u => v)
        u = mk_implies(flat->manager, v, u); // (v => u);
        flattener_push_term(flat, t);
        flattener_push_term(flat, u);
        continue;
      }
      break;

    case OR_TERM:
      if (is_neg_term(t)) {
        /*
         * t is (not (or a[0] ... a[n-1]))
         * it flattens to (and (not a[0]) ... (not a[n-1]))
         */
        d = or_term_desc(terms, t);
        n = d->arity;
        for (i=0; i<n; i++) {
          flattener_push_term(flat, opposite_term(d->arg[i]));
        }
        continue;
      }
      break;

    default:
      break;
    }
    ivector_push(&flat->resu, t);
  }

  // clean up the cache
  assert(int_queue_is_empty(queue));
  int_hset_reset(&flat->cache);
}


/*
 * Flatten all terms in flat->queue to disjuncts
 * - all terms in the queue must also be in the cache
 * - f_ite: if true, flatten (ite c a b)
 * - f_iff: if true, flatten (iff a b)
 */
static void flattener_build_disjuncts(flattener_t *flat, bool f_ite, bool f_iff) {
  term_table_t *terms;
  int_queue_t *queue;
  composite_term_t *d;
  term_t t, u, v;
  uint32_t i, n;

  queue = &flat->queue;
  terms = flat->terms;

  while (! int_queue_is_empty(queue)) {
    t = int_queue_pop(queue);

    switch (term_kind(terms, t)) {
    case ITE_TERM:
    case ITE_SPECIAL:
      d = ite_term_desc(terms, t);
      assert(d->arity == 3);
      if (f_ite && is_boolean_term(terms, d->arg[1])) {
        assert(is_boolean_term(terms, d->arg[2]));
        /*
         * If t is (ite C A B)
         *    u := (C AND A)
         *    v := (not C AND B)
         * Otherwise, t is (not (ite C A B))
         *    u := (C AND not A)
         *    v := (not C AND not B)
         */
        u = d->arg[1];  // A
        v = d->arg[2];  // B
        if (is_neg_term(t)) {
          u = opposite_term(u); // NOT A
          v = opposite_term(v); // NOT B
        }
        u = mk_binary_and(flat->manager, d->arg[0], u); // (C AND u)
        v = mk_binary_and(flat->manager, opposite_term(d->arg[0]), v); // (not C) AND v
        flattener_push_term(flat, u);
        flattener_push_term(flat, v);
        continue;
      }
      break;

    case EQ_TERM:
      d = eq_term_desc(terms, t);
      assert(d->arity == 2);
      if (f_iff && is_boolean_term(terms, d->arg[0])) {
        assert(is_boolean_term(terms, d->arg[1]));
        /*
         * t is either (iff A B) or (not (iff A B)):
         */
        u = d->arg[0]; // A
        v = d->arg[1]; // B
        if (is_neg_term(t)) {
          u = opposite_term(u);
        }
        // flatten to (u AND v) or ((not u) AND (not v))
        t = mk_binary_and(flat->manager, u, v); // (u AND v)
        u = mk_binary_and(flat->manager, opposite_term(u), opposite_term(v)); // (not u AND not v);
        flattener_push_term(flat, t);
        flattener_push_term(flat, u);
        continue;
      }
      break;

    case OR_TERM:
      if (is_pos_term(t)) {
        /*
         * t is (or a[0] ... a[n-1])
         */
        d = or_term_desc(terms, t);
        n = d->arity;
        for (i=0; i<n; i++) {
          flattener_push_term(flat, d->arg[i]);
        }
        continue;
      }
      break;

    default:
      break;
    }

    ivector_push(&flat->resu, t);
  }

  // clean up the cache
  assert(int_queue_is_empty(queue));
  int_hset_reset(&flat->cache);
}



/*
 * Process conjuncts and universal quantifiers
 * - input formulas are stored in flat->queue
 */
static void flattener_forall_conjuncts(flattener_t *flat, bool f_ite, bool f_iff) {
  term_table_t *terms;
  int_queue_t *queue;
  composite_term_t *d;
  term_t t, u, v;
  uint32_t i, n;

  queue = &flat->queue;
  terms = flat->terms;

  while (! int_queue_is_empty(queue)) {
    t = int_queue_pop(queue);

    switch (term_kind(terms, t)) {
    case ITE_TERM:
    case ITE_SPECIAL:
      d = ite_term_desc(terms, t);
      assert(d->arity == 3);
      if (f_ite && is_boolean_term(terms, d->arg[1])) {
        assert(is_boolean_term(terms, d->arg[2]));
        /*
         * If t is (ite C A B)
         *    u := (C => A)
         *    v := (not C => B)
         * Otherwise, t is (not (ite C A B))
         *    u := (C => not A)
         *    v := (not C => not B)
         */
        u = d->arg[1];  // A
        v = d->arg[2];  // B
        if (is_neg_term(t)) {
          u = opposite_term(u);
          v = opposite_term(v);
        }
        u = mk_implies(flat->manager, d->arg[0], u); // (C => u)
        v = mk_implies(flat->manager, opposite_term(d->arg[0]), v); // (not C) => v
        flattener_push_term(flat, u);
        flattener_push_term(flat, v);
        continue;
      }
      break;

    case EQ_TERM:
      d = eq_term_desc(terms, t);
      assert(d->arity == 2);
      if (f_iff && is_boolean_term(terms, d->arg[0])) {
        assert(is_boolean_term(terms, d->arg[1]));
        /*
         * t is either (iff A B) or (not (iff A B)):
         */
        u = d->arg[0]; // A
        v = d->arg[1]; // B
        if (is_neg_term(t)) {
          u = opposite_term(u);
        }
        // flatten to (u => v) and (v => u)
        t = mk_implies(flat->manager, u, v); // (u => v)
        u = mk_implies(flat->manager, v, u); // (v => u);
        flattener_push_term(flat, t);
        flattener_push_term(flat, u);
        continue;
      }
      break;

    case OR_TERM:
      if (is_neg_term(t)) {
        /*
         * t is (not (or a[0] ... a[n-1]))
         * it flattens to (and (not a[0]) ... (not a[n-1]))
         */
        d = or_term_desc(terms, t);
        n = d->arity;
        for (i=0; i<n; i++) {
          flattener_push_term(flat, opposite_term(d->arg[i]));
        }
        continue;
      }
      break;

    case FORALL_TERM:
      if (is_pos_term(t)) {
        d = forall_term_desc(terms, t);
        n = d->arity;
        assert(n >= 2);
        /*
         * t is (FORALL x_0 ... x_k : body)
         * body is the last argument in the term descriptor
         */
        flattener_push_term(flat, d->arg[n-1]);
        continue;
      }
      break;

    default:
      break;
    }
    ivector_push(&flat->resu, t);
  }

  // clean up the cache
  assert(int_queue_is_empty(queue));
  int_hset_reset(&flat->cache);
}


/*
 * Process disjuncts and universal quantifiers
 * - input = all terms in the queue
 * - f_ite: if true, flatten (ite c a b)
 * - f_iff: if true, flatten (iff a b)
 */
static void flattener_forall_disjuncts(flattener_t *flat, bool f_ite, bool f_iff) {
  term_table_t *terms;
  int_queue_t *queue;
  composite_term_t *d;
  term_t t, u, v;
  uint32_t i, n;

  queue = &flat->queue;
  terms = flat->terms;

  while (! int_queue_is_empty(queue)) {
    t = int_queue_pop(queue);

    switch (term_kind(terms, t)) {
    case ITE_TERM:
    case ITE_SPECIAL:
      d = ite_term_desc(terms, t);
      assert(d->arity == 3);
      if (f_ite && is_boolean_term(terms, d->arg[1])) {
        assert(is_boolean_term(terms, d->arg[2]));
        /*
         * If t is (ite C A B)
         *    u := (C AND A)
         *    v := (not C AND B)
         * Otherwise, t is (not (ite C A B))
         *    u := (C AND not A)
         *    v := (not C AND not B)
         */
        u = d->arg[1];  // A
        v = d->arg[2];  // B
        if (is_neg_term(t)) {
          u = opposite_term(u); // NOT A
          v = opposite_term(v); // NOT B
        }
        u = mk_binary_and(flat->manager, d->arg[0], u); // (C AND u)
        v = mk_binary_and(flat->manager, opposite_term(d->arg[0]), v); // (not C) AND v
        flattener_push_term(flat, u);
        flattener_push_term(flat, v);
        continue;
      }
      break;

    case EQ_TERM:
      d = eq_term_desc(terms, t);
      assert(d->arity == 2);
      if (f_iff && is_boolean_term(terms, d->arg[0])) {
        assert(is_boolean_term(terms, d->arg[1]));
        /*
         * t is either (iff A B) or (not (iff A B)):
         */
        u = d->arg[0]; // A
        v = d->arg[1]; // B
        if (is_neg_term(t)) {
          u = opposite_term(u);
        }
        // flatten to (u AND v) or ((not u) AND (not v))
        t = mk_binary_and(flat->manager, u, v); // (u AND v)
        u = mk_binary_and(flat->manager, opposite_term(u), opposite_term(v)); // (not u AND not v);
        flattener_push_term(flat, t);
        flattener_push_term(flat, u);
        continue;
      }
      break;

    case OR_TERM:
      if (is_pos_term(t)) {
        /*
         * t is (or a[0] ... a[n-1])
         */
        d = or_term_desc(terms, t);
        n = d->arity;
        for (i=0; i<n; i++) {
          flattener_push_term(flat, d->arg[i]);
        }
        continue;
      }
      break;

    case FORALL_TERM:
      if (is_pos_term(t)) {
        d = forall_term_desc(terms, t);
        n = d->arity;
        assert(n >= 2);
        /*
         * t is (FORALL x_0 ... x_k : body)
         * body is the last argument in the term descriptor
         */
        flattener_push_term(flat, d->arg[n-1]);
        continue;
      }
      break;

    default:
      break;
    }

    ivector_push(&flat->resu, t);
  }

  // clean up the cache
  assert(int_queue_is_empty(queue));
  int_hset_reset(&flat->cache);
}




/*
 * Flatten formula f to conjuncts
 * - f must be defined in flat->terms
 * - flags f_ite and f_iff control optional flattening:
 *
 *   if f_ite is true, then (ite C A B) is converted to
 *       (and (=> C A)(=> (not C) B))
 *   (otherwise, (ite C A B) is kept as is)
 *
 *   if f_iff is true, then (iff A B) is converted to
 *       (and (=> A B)(=> B A))
 *   (otherwise, (iff A B) is kept)
 *
 * - the result is stored in flat->resu:
 *   flat->resu.size = number of conjuncts
 *   flat->resu.data = array of conjuncts
 */
void flatten_to_conjuncts(flattener_t *flat, term_t f, bool f_ite, bool f_iff) {
  assert(int_queue_is_empty(&flat->queue) && int_hset_is_empty(&flat->cache));

  ivector_reset(&flat->resu);
  flattener_push_term(flat, f);
  flattener_build_conjuncts(flat, f_ite, f_iff);
}


/*
 * Flatten formula f to disjuncts
 * - f must be defined in flat->terms
 * - flags f_ite and f_iff control optional flattening:
 *
 *   if f_ite is true, then (ite C A B) is converted to
 *       (OR (C AND A) ((not C) AND B))
 *   (otherwise, (ite C A B) is kept as is)
 *
 *   if f_iff is true, then (iff A B) is converted to
 *       (OR (A AND B) ((not A) AND (not B))
 *   (otherwise, (iff A B) is kept)
 *
 * - the result is stored in flat->resu:
 *   flat->resu.size = number of conjuncts
 *   flat->resu.data = array of conjuncts
 */
void flatten_to_disjuncts(flattener_t *flat, term_t f, bool f_ite, bool f_iff) {
  assert(int_queue_is_empty(&flat->queue) && int_hset_is_empty(&flat->cache));

  ivector_reset(&flat->resu);
  flattener_push_term(flat, f);
  flattener_build_disjuncts(flat, f_ite, f_iff);
}



/*
 * Flattening of conjuncts and universal quantifiers + optionally ite and iff terms
 */
void flatten_forall_conjuncts(flattener_t *flat, term_t f, bool f_ite, bool f_iff) {
  assert(int_queue_is_empty(&flat->queue) && int_hset_is_empty(&flat->cache));

  ivector_reset(&flat->resu);
  flattener_push_term(flat, f);
  flattener_forall_conjuncts(flat, f_ite, f_iff);
}


/*
 * Flattening of disjuncts and universal quantifiers + optionally ite and iff terms
 */
void flatten_forall_disjuncts(flattener_t *flat, term_t f, bool f_ite, bool f_iff) {
  assert(int_queue_is_empty(&flat->queue) && int_hset_is_empty(&flat->cache));

  ivector_reset(&flat->resu);
  flattener_push_term(flat, f);
  flattener_forall_disjuncts(flat, f_ite, f_iff);
}



/*
 * Flatten array f[0 ... n-1]:
 * - this builds an array of conjuncts equivalent to (and f[0] ... f[n-1])
 */
void flatten_array_to_conjuncts(flattener_t *flat, uint32_t n, term_t *f, bool f_ite, bool f_iff) {
  uint32_t i;

  assert(int_queue_is_empty(&flat->queue) && int_hset_is_empty(&flat->cache));

  ivector_reset(&flat->resu);
  for (i=0; i<n; i++) {
    flattener_push_term(flat, f[i]);
  }
  flattener_build_conjuncts(flat, f_ite, f_iff);
}


/*
 * Flatten array f[0 ... n-1]:
 * - this builds an array of disjuncts equivalent to (or  f[0] ... f[n-1])
 */
void flatten_array_to_disjuncts(flattener_t *flat, uint32_t n, term_t *f, bool f_ite, bool f_iff) {
  uint32_t i;

  assert(int_queue_is_empty(&flat->queue) && int_hset_is_empty(&flat->cache));

  ivector_reset(&flat->resu);
  for (i=0; i<n; i++) {
    flattener_push_term(flat, f[i]);
  }
  flattener_build_disjuncts(flat, f_ite, f_iff);
}



/*
 * Flatten array f[0 .... n-1]: universal quantifiers + conjuncts
 */
void flatten_array_forall_conjuncts(flattener_t *flat, uint32_t n, term_t *f, bool f_ite, bool f_iff) {
  uint32_t i;

  assert(int_queue_is_empty(&flat->queue) && int_hset_is_empty(&flat->cache));

  ivector_reset(&flat->resu);
  for (i=0; i<n; i++) {
    flattener_push_term(flat, f[i]);
  }
  flattener_forall_conjuncts(flat, f_ite, f_iff);
}


/*
 * Flatten array f[0 .... n-1]: universal quantifiers + disjuncts
 */
void flatten_array_forall_disjuncts(flattener_t *flat, uint32_t n, term_t *f, bool f_ite, bool f_iff) {
  uint32_t i;

  assert(int_queue_is_empty(&flat->queue) && int_hset_is_empty(&flat->cache));

  ivector_reset(&flat->resu);
  for (i=0; i<n; i++) {
    flattener_push_term(flat, f[i]);
  }
  flattener_forall_disjuncts(flat, f_ite, f_iff);
}

