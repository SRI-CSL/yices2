/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Analyze a UF formula F to learn global equalities implied by F
 * The result is stored as an epartition.
 */

#include <stdint.h>

#include "context/eq_learner.h"

#define TRACE 0

#if TRACE

#include <stdio.h>

#include "io/term_printer.h"


/*
 * Print a term partition
 */
void print_epartition(FILE *f, term_table_t *terms, epartition_t *p) {
  term_t *q, t;
  uint32_t i, n;

  n = p->nclasses;
  if (n == 0) {
    fprintf(f, "empty");
  } else {
    q = p->data;
    for (i=0; i<n; i++) {
      fprintf(f, " {");
      t = *q ++;
      while (t >= 0) {
        fputc(' ', f);
        print_term_name(f, terms, t);
        t = *q ++;
      }
      fprintf(f, " }");
    }
  }
}


#endif


/*
 * Initialize a learner structure
 * - the cache has default size
 */
void init_eq_learner(eq_learner_t *learner, term_table_t *tbl) {
  learner->terms = tbl;
  init_epartition_manager(&learner->manager);
  init_ptr_hmap(&learner->cache, 0);
}


/*
 * Delete the learner structure and all epartition objects
 */
void delete_eq_learner(eq_learner_t *learner) {
  ptr_hmap_pair_t *p;
  ptr_hmap_t *cache;
  epartition_manager_t *m;

  cache = &learner->cache;
  m = &learner->manager;
  for (p = ptr_hmap_first_record(cache);
       p != NULL;
       p = ptr_hmap_next_record(cache, p)) {
    delete_epartition(m, p->val);
  }
  delete_ptr_hmap(cache);
  delete_epartition_manager(m);
}


/*
 * Find record for formula f in the cache.
 * If the record is not present, return NULL
 */
static epartition_t *find_cached_abstraction(eq_learner_t *learner, term_t f) {
  ptr_hmap_pair_t *p;

  assert(good_term(learner->terms, f) && is_boolean_term(learner->terms, f));

  p = ptr_hmap_find(&learner->cache, f);
  if (p != NULL) {
    assert(p->val != NULL);
    return p->val;
  } else {
    return NULL;
  }
}

/*
 * Store that f is abstracted to p
 * - there must not be a record for f in the cache
 */
static void cache_abstraction(eq_learner_t *learner, term_t f, epartition_t *p) {
  ptr_hmap_pair_t *r;

  assert(good_term(learner->terms, f) && is_boolean_term(learner->terms, f) && p != NULL);
  r = ptr_hmap_get(&learner->cache, f);
  assert(r->val == NULL);
  r->val = p;
}


/*
 * Get abstraction for f in the cache
 * - this works only if the corresponding record exists
 */
static epartition_t *get_cached_abstraction(eq_learner_t *learner, term_t f) {
  ptr_hmap_pair_t *p;

  assert(good_term(learner->terms, f) && is_boolean_term(learner->terms, f));
  p = ptr_hmap_find(&learner->cache, f);
  assert(p != NULL);

  return p->val;
}


/*
 * Compute the abstraction of formula f or (not f)
 * - if polarity is true: abstract f
 * - if polarity is false: abstract (not f)
 */
static epartition_t *eq_abstract(eq_learner_t *learner, term_t f, bool polarity);


/*
 * Build the abstraction for an (OR ...) formula or its negation
 * - if polarity is true: abstraction of (OR t1 ... tn)
 * - if polarity is false: abstraction of not (OR t1 ... tn)
 *   (i.e., abstraction of (AND (not t1) ... (not tn)))
 */
static epartition_t *eq_abstract_or(eq_learner_t *learner, composite_term_t *or, bool polarity) {
  uint32_t i, n;
  epartition_manager_t *m;
  epartition_t *p;

  assert(or->arity > 1);

  // abstract the arguments
  n = or->arity;
  for (i=0; i<n; i++) {
    (void) eq_abstract(learner, or->arg[i], polarity);
  }

  /*
   * for (OR t1 ... t_n): construct the join of abs(t1) ... abs(t_n)
   * for not (OR t1 ... t_n) <=> (and (not t1) ... (not t_n)):
   *  construct meet(abs (not t1) ... abs(not t_n))
   */
  m = &learner->manager;
  if (polarity) {
    // (OR t1 ... t_n)
    p = get_cached_abstraction(learner, or->arg[0]);
    epartition_init_for_join(m, p);
    for (i=1; i<n; i++) {
      p = get_cached_abstraction(learner, or->arg[i]);
      epartition_join(m, p);
    }
    return epartition_get_join(m);

  } else {
    // (AND (not t1) ... (not t_n))
    p = get_cached_abstraction(learner, opposite_term(or->arg[0]));
    epartition_init_for_meet(m, p);
    for (i=1; i<n; i++) {
      p = get_cached_abstraction(learner, opposite_term(or->arg[i]));
      epartition_meet(m, p);
    }
    return epartition_get_meet(m);
  }
}


/*
 * Compute meet p1 p2 and join p1 p2
 */
static epartition_t *eq_abstract_meet(epartition_manager_t *m, epartition_t *p1, epartition_t *p2) {
  epartition_init_for_meet(m, p1);
  epartition_meet(m, p2);
  return epartition_get_meet(m);
}

static epartition_t *eq_abstract_join(epartition_manager_t *m, epartition_t *p1, epartition_t *p2) {
  epartition_init_for_join(m, p1);
  epartition_join(m, p2);
  return epartition_get_join(m);
}




/*
 * Abstraction of (eq t1 t2):
 * - if t1 and t2 are boolean, we rewrite the formula as (t1 ==> t2) AND (t2 ==> t1)
 * - if t1 and t2 are non boolean build a basic partition
 */
static epartition_t *eq_abstract_eq(eq_learner_t *learner, composite_term_t *eq, bool polarity) {
  term_t t1, t2;
  epartition_t *p1, *q1, *p2, *q2;
  epartition_manager_t *m;

  assert(eq->arity == 2);

  m = &learner->manager;
  t1 = eq->arg[0];
  t2 = eq->arg[1];

  assert(t1 != t2);

  if (is_boolean_term(learner->terms, t1)) {
    assert(is_boolean_term(learner->terms, t2));
    /*
     * - for positive polarity,
     *   let u2 = t2, then (t1 <==> t2) is (t1 <==> u2)
     * - for negative polarity
     *   let u2 = (not t2), then (not (t1 <==> t2)) is equivalent to (t1 <==> u2)
     * - in both cases we compute
     *     abs(t1 <==> u2)
     *   = abs((t1 ==> u2) and (u2 ==> t1))
     *   = abs((not t1 or u2) and (not u2 or t1))
     *   = meet(join(abs(not t1), abs(u2)), join(abs(not t2), abs(t1)))
     */
    p1 = eq_abstract(learner, t1, true);      // abs(t1)
    q1 = eq_abstract(learner, t1, false);     // abs(not t1)
    p2 = eq_abstract(learner, t2, polarity);  // abs(u2)
    q2 = eq_abstract(learner, t2, !polarity); // abs(not u2)

    q1 = eq_abstract_join(m, q1, p2);   // join(abs(not t1), abs(u2))
    p1 = eq_abstract_join(m, q2, p1);   // join(abs(not u2), abs(t1))
    p2 = eq_abstract_meet(m, p1, q1);   // meet ..

    // prevent memory leak
    delete_epartition(m, p1);
    delete_epartition(m, q1);

    return p2;

  } else {
    if (polarity) {
      return basic_epartition(t1, t2);
    } else {
      return empty_epartition(m);
    }
  }
}


/*
 * Abstraction of (ite c t1 t2)
 */
static epartition_t *eq_abstract_ite(eq_learner_t *learner, composite_term_t *ite, bool polarity) {
  term_t c, t1, t2;
  epartition_t *p, *q, *p1, *p2;
  epartition_manager_t *m;

  assert(ite->arity == 3);

  m = &learner->manager;
  c = ite->arg[0];
  t1 = ite->arg[1];
  t2 = ite->arg[2];

  /*
   * - for positive polarity: let u1=t1 and u2=t2, then
   *     (ite c t1 t2) is (ite c u1 u2)
   * - for negative polarity: let u1=not t1 and u2=not t2, then
   *     not (ite c t1 t2) is (ite c u1 u2)
   * - in both cases, we compute
   *     abs(ite c u1 u2)
   *   = abs((c ==> u1) and (not c ==> u2))
   *   = abs((not c or u1) and (c or u2))
   *   = meet(join(abs(not c), abs(u1)), join(abs(c), abs(u2)))
   */
  p = eq_abstract(learner, c, true);    // abs(c)
  q = eq_abstract(learner, c, false);   // abs(not c)
  p1 = eq_abstract(learner, t1, polarity); // abs(u1)
  p2 = eq_abstract(learner, t2, polarity); // abs(u2)

  p1 = eq_abstract_join(m, q, p1);  // join(abs(not c), abs(u1))
  p2 = eq_abstract_join(m, p, p2);  // join(abs(c), abs(u2))
  p = eq_abstract_meet(m, p1, p2);  // result

  delete_epartition(m, p1);
  delete_epartition(m, p2);

  return p;
}



/*
 * Main abstraction function
 */
static epartition_t *eq_abstract(eq_learner_t *learner, term_t f, bool polarity) {
  term_table_t *terms;
  epartition_t *a;

  assert(is_boolean_term(learner->terms, f));

  a = find_cached_abstraction(learner, signed_term(f, polarity));
  if (a == NULL) {
    // not in the cache

    // remove top-level negation
    if (is_neg_term(f)) {
      f = opposite_term(f);
      polarity = !polarity;
    }

    // explore f
    terms = learner->terms;
    switch (term_kind(terms, f)) {
    case EQ_TERM:
      a = eq_abstract_eq(learner, eq_term_desc(terms, f), polarity);
      break;
    case ITE_TERM:
    case ITE_SPECIAL:
      a = eq_abstract_ite(learner, ite_term_desc(terms, f), polarity);
      break;
    case OR_TERM:
      a = eq_abstract_or(learner, or_term_desc(terms, f), polarity);
      break;
    default:
      a = empty_epartition(&learner->manager);
      break;
    }
    cache_abstraction(learner, signed_term(f, polarity), a);
  }

  return a;
}


/*
 * Exported version
 */
epartition_t *eq_learner_process(eq_learner_t *learner, term_t f) {
  epartition_t *p;

  p = eq_abstract(learner, f, true);

#if TRACE
  printf("---> ABS: ");
  print_term_def(stdout, learner->terms, f);
  printf("\n---> result = ");
  print_epartition(stdout, learner->terms, p);
  printf("\n");
#endif

  return p;
}
