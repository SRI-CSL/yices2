/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * CONDITIONALS
 */

#include <assert.h>
#include <stdbool.h>

#include "utils/memalloc.h"
#include "terms/term_utils.h"
#include "terms/conditionals.h"

/*
 * Initialize:
 * - empty pair array
 * - defval = NULL_TERM
 */
void init_conditional(conditional_t *d, term_table_t *terms) {
  d->terms = terms;
  d->pair = NULL;
  d->defval = NULL_TERM;
  d->nconds = 0;
  d->size = 0;
}

/*
 * Increase the size of d->pairs
 */
static void extend_conditional(conditional_t *d) {
  uint32_t n;

  n = d->size;
  if (n == 0) {
    // first allocation
    n = DEF_CONDITIONAL_SIZE;
    assert(2 <= n && n <= MAX_CONDITIONAL_SIZE);
    d->pair = (cond_pair_t *) safe_malloc(n * sizeof(cond_pair_t));
    d->size = n;
  } else {
    // increase by 50%
    n += n>>1;
    if (n > MAX_CONDITIONAL_SIZE) {
      out_of_memory();
    }
    d->pair = (cond_pair_t *) safe_realloc(d->pair, n * sizeof(cond_pair_t));
    d->size = n;
  }
}


/*
 * Add pair [c, v] at the end of the pair array
 */
static void conditional_add_pair(conditional_t *d, term_t c, term_t v) {
  uint32_t i;

  i = d->nconds;
  if (i == d->size) {
    extend_conditional(d);
  }
  assert(i < d->size);
  d->pair[i].cond = c;
  d->pair[i].val = v;
  d->nconds = i+1;
}


/*
 * Delete: free the array
 */
void delete_conditional(conditional_t *d) {
  safe_free(d->pair);
  d->pair = NULL;
}

/*
 * Reset: reset defval to NULL_TERM and nconds to 0, but don't
 * delete the array
 */
void reset_conditional(conditional_t *d) {
  d->nconds = 0;
  d->defval = NULL_TERM;
}


/*
 * Check whether c is disjoint with all the current conditions
 */
static bool disjoint_condition(conditional_t *d, term_t c) {
  uint32_t i, n;

  n = d->nconds;
  for (i=0; i<n; i++) {
    if (!incompatible_boolean_terms(d->terms, c, d->pair[i].cond)) {
      return false;
    }
  }

  return true;
}



/*
 * Convert (if c a b) to a conditional
 */
void convert_ite_to_conditional(conditional_t *d, term_t c, term_t a, term_t b) {
  composite_term_t *ite;
  term_t t, c1, t1, t2;

  reset_conditional(d);

  if (is_ite_term(d->terms, b)) {
    /*
     * b is either (ite c1 ...) or (not (ite c1  ...).
     *
     * we normalize to (ite c1 t1 t2):
     * - if b is (ite c1 t1 t2) we're done
     * - if b is (not (ite c1 u1 u2)) we push the negation inside:
     *   so t1 := (not u1) and t2 := (not u2)
     */
    ite = ite_term_desc(d->terms, b);
    assert(ite->arity == 3);

    c1 = ite->arg[0];
    t1 = ite->arg[1];
    t2 = ite->arg[2];
    if (is_neg_term(b)) {
      t1 = opposite_term(t1);
      t2 = opposite_term(t2);
    }

    /*
     * we try to build the conditional
     *    [c --> a,     c1 --> t1, else --> t2] if c and c1 are disjoint
     * or [c --> a, not c1 --> t2, else --> t1] if c and not c1 are disjoint
     */
    if (incompatible_boolean_terms(d->terms, c, c1)) {
      conditional_add_pair(d, c, a);
      conditional_add_pair(d, c1, t1);
      t = t2;
      goto loop;
    }

    if (incompatible_boolean_terms(d->terms, c, opposite_term(c1))) {
      conditional_add_pair(d, c, a);
      conditional_add_pair(d, opposite_term(c1), t2);
      t = t1;
      goto loop;
    }
  }

  if (is_ite_term(d->terms, a)) {
    /*
     * a is either (ite c1 ...) or (not (ite c1 ...))
     * we normalize as above to (ite c1 t1 t2)
     */
    ite = ite_term_desc(d->terms, a);
    assert(ite->arity == 3);

    c1 = ite->arg[0];
    t1 = ite->arg[1];
    t2 = ite->arg[2];
    if (is_neg_term(a)) {
      t1 = opposite_term(t1);
      t2 = opposite_term(t2);
    }

    /*
     * we try
     *    [not c --> b,     c1 --> t1, else --> t2]
     * or [not c --> b, not c1 --> t2, else --> t1]
     */
    if (incompatible_boolean_terms(d->terms, opposite_term(c), c1)) {
      conditional_add_pair(d, opposite_term(c), b);
      conditional_add_pair(d, c1, t1);
      t = t2;
      goto loop;
    }

    if (incompatible_boolean_terms(d->terms, opposite_term(c), opposite_term(c1))) {
      conditional_add_pair(d, opposite_term(c), b);
      conditional_add_pair(d, opposite_term(c1), t2);
      t = t1;
      goto loop;
    }
  }

  // Default: found no disjoint conditions
  conditional_add_pair(d, c, a);
  d->defval = b;
  return;

  // t is the 'else part'
 loop:
  while (is_ite_term(d->terms, t)) {
    // t is (ite c1 t1 t2)
    ite = ite_term_desc(d->terms, t);
    assert(ite->arity == 3);

    c1 = ite->arg[0];
    t1 = ite->arg[1];
    t2 = ite->arg[2];
    if (is_neg_term(t)) {
      t1 = opposite_term(t1);
      t2 = opposite_term(t2);
    }

    if (disjoint_condition(d, c1)) {
      conditional_add_pair(d, c1, t1);
      t = t2;
    } else if (disjoint_condition(d, opposite_term(c1))) {
      conditional_add_pair(d, opposite_term(c1), t2);
      t = t1;
    } else {
      break;
    }
  }

  d->defval = t;
}


/*
 * Convert term t to a conditional; store the result in d
 * - d is reset first
 * - t must be a valid term defined in d->terms
 * - if t is not an if-then-else term, the result is
 *     d->nconds = 0
 *     d->defval = t
 * - if t is (ite c a b) then the conversion depends on whether
 *   a or b is an if-then-else term.
 */
void convert_term_to_conditional(conditional_t *d, term_t t) {
  composite_term_t *ite;
  term_t a, b;

  if (is_ite_term(d->terms, t)) {
    ite = ite_term_desc(d->terms, t);
    assert(ite->arity == 3);

    a = ite->arg[1];
    b = ite->arg[2];
    if (is_neg_term(t)) {
      a = opposite_term(a);
      b = opposite_term(b);
    }
    convert_ite_to_conditional(d, ite->arg[0], ite->arg[1], ite->arg[2]);
  } else {
    reset_conditional(d);
    d->defval = t;
  }
}
