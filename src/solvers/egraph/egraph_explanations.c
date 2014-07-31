/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*************************
 *  EGRAPH EXPLANATIONS  *
 ************************/

/*
 * There are two phases to generating explanations:
 * - when an equality (t1 == t2) is implied, an edge is added and an
 *   antecedent attached to that edge in the propagation queue
 * - the antecedent encodes the reason for the implication.
 * When explanations need to be communicated to the DPLL solver, the antecedents
 * are visited and expanded into a vector of literals.
 *
 * Expansion is done in build_explanation_vector using a set of edges + a
 * vector of literals:
 * - to explain an edge i = (t1 == t2), we start with
 *    set = { i } , vector = empty vector
 * - each processing step replaces an edge i in the set by other edges
 *   based on the explanation for i, or remove i from the set and add
 *   a literal to v
 * - we do this until the set is empty: the resulting explanation is
 *   the vector
 *
 * Modification: the set is now a queue and all the edges in the queue
 * are marked.
 *
 * It's important to ensure causality: the information stored as
 * antecedent to edge i when an equality is implied must allow the
 * same explanation to be reconstructed when edge i is expanded later.
 * In particular, the expansion should not introduce any equalities
 * asserted after i.
 */


#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "utils/bit_tricks.h"
#include "utils/int_vectors.h"
#include "utils/memalloc.h"

#include "solvers/egraph/egraph_types.h"
#include "solvers/egraph/egraph_utils.h"
#include "solvers/egraph/egraph.h"
#include "solvers/egraph/composites.h"
#include "solvers/egraph/theory_explanations.h"


#if 0

#include <stdio.h>
#include <inttypes.h>

#include "smt_core_printer.h"
#include "egraph_printer.h"

#endif


/**********************************
 *  CONSTRUCTION OF ANTECEDENTS   *
 *********************************/

/*
 * Antecedent for (distinct t_1 ... t_n) == false
 * The antecedent is EXPL_EQ(t_i, t_j) where t_i and t_j have label x
 * - c = composite term (distinct t_1 ... t_n)
 * - x = label (via which the simplification was detected)
 * - k = index where the explanation must be stored in egraph->stack
 */
void gen_distinct_simpl_antecedent(egraph_t *egraph, composite_t *c, elabel_t x, int32_t k) {
  uint32_t i;
  occ_t t1, t2;

  assert(composite_kind(c) == COMPOSITE_DISTINCT);

  i = 0;
  do {
    assert(i < composite_arity(c));
    t1 = c->child[i];
    i ++;
  } while (egraph_label(egraph, t1) != x);

  do {
    assert(i < composite_arity(c));
    t2 = c->child[i];
    i ++;
  } while (egraph_label(egraph, t2) != x);

  egraph->stack.etag[k] = EXPL_EQ;
  egraph->stack.edata[k].t[0] = t1;
  egraph->stack.edata[k].t[1] = t2;
}


/*
 * Antecedent for (distinct t_1 ... t_n) == (distinct u_1 ... u_n)
 * - build a permutation v[1 ... n] of u_1 ... u_n such that t_i == u_{v[j]}
 * - k = index where the explanation must be stored
 */
void gen_distinct_congruence_antecedent(egraph_t *egraph, composite_t *c1, composite_t *c2, int32_t k) {
  occ_t *aux, *ch;
  uint32_t i, n;
  int_hmap_t *imap;
  int_hmap_pair_t *p;
  elabel_t l;

  assert(c1->tag == c2->tag && composite_kind(c1) == COMPOSITE_DISTINCT);

  // store map [label(u_i) --> u_i] into imap
  n = composite_arity(c1);
  ch = c2->child;
  imap = egraph_get_imap(egraph);
  for (i=0; i<n; i++) {
    l = egraph_label(egraph, ch[i]);
    assert(l >= 0);
    p = int_hmap_get(imap, l);
    assert(p->val < 0); // otherwise (distinct u_1 ... u_n) == false
    p->val = ch[i];
  }

  // for every t_i, find which u_j is mapped to label(t_i)
  // store that u_j in aux[i]
  aux = (occ_t *) arena_alloc(&egraph->arena, n * sizeof(occ_t));
  ch = c1->child;
  for (i=0; i<n; i++) {
    l = egraph_label(egraph, ch[i]);
    assert(l >= 0);
    p = int_hmap_find(imap, l);
    assert(p != NULL);
    aux[i] = p->val;
  }

  egraph->stack.etag[k] = EXPL_DISTINCT_CONGRUENCE;
  egraph->stack.edata[k].ptr = aux;

  // cleanup
  int_hmap_reset(imap);
}


/*
 * Scan the path from t to its root
 * - for every term x on this path, add the mapping [x -> t] or [x -> neg(t)]
 *   to imap (unless x is already mapped to some other term t')
 */
static void map_path(egraph_t *egraph, int_hmap_t *imap, occ_t t) {
  eterm_t x;
  occ_t u, v;
  int_hmap_pair_t *p;
  equeue_elem_t *eq;
  int32_t *edge;
  int32_t i;

  edge = egraph->terms.edge;
  eq = egraph->stack.eq;

  t &= ~0x1; // clear sign bit: start with t positive
  u = t;
  for (;;) {
    x = term_of_occ(u);

    p = int_hmap_get(imap, x);
    if (p->val >= 0) break;;
    p->val = t;

    i = edge[x];
    if (i < 0) break;
    v = edge_next_occ(eq + i, u);
    // flip sign of t if u and v have opposite signs
    t ^= (u ^ v) & 0x1;
    u = v;
  }
}

/*
 * Add mapping [true_term -> false] to the imap (i.e. root(false) is mapped to false)
 * if there's nothing mapped to true_term yet.
 */
static void map_false_node(int_hmap_t *imap) {
  int_hmap_pair_t *p;

  p = int_hmap_get(imap, term_of_occ(false_occ));
  if (p->val < 0) {
    p->val = false_occ;
  }
}

/*
 * Scan the path from t to its root until a term x is found in imap
 * - return whatever is mapped to x with adjusted polarities
 */
static occ_t find_in_path(egraph_t *egraph, int_hmap_t *imap, occ_t t) {
  int_hmap_pair_t *p;
  equeue_elem_t *eq;
  int32_t *edge;
  int32_t i;
  occ_t u, sgn;
  eterm_t x;

  edge = egraph->terms.edge;
  eq = egraph->stack.eq;

  sgn = polarity_of_occ(t);

  for (;;) {
    x = term_of_occ(t);

    p = int_hmap_find(imap, x);
    if (p != NULL) break;

    i = edge[x];
    assert(i >= 0); // i is not null_edge
    u = edge_next_occ(eq + i, t);

    // flip sign if t and u have opposite polarities
    sgn ^= (u ^ t) & 0x1;
    t = u;
  }

  // x is mapped to p->val (this encodes pos_occ(x) == p->val)
  // we have t == pos_occ(x) ^ sign.

  return p->val ^ sgn;
}



/*
 * For every i in 0 ... n-1, choose u among { d[0] ... d[m-1] false }
 * such that (c[i] == u) holds in the egraph. Store that term u into a[i].
 */
static void half_or_congruence_antecedent(egraph_t *egraph, occ_t *c, uint32_t n, occ_t *d, uint32_t m, occ_t *a) {
  int_hmap_t *imap;
  uint32_t i;

  imap = egraph_get_imap(egraph);
  for (i=0; i<m; i++) {
    map_path(egraph, imap, d[i]);
  }

  // if false node is not in imap then add it, mapped to itself
  map_false_node(imap);

  for (i=0; i<n; i++) {
    a[i] = find_in_path(egraph, imap, c[i]);
  }
  int_hmap_reset(imap);
}



/*
 * Antecedent for or-congruence (could be used for any AC operator)
 * - c1 and c2 must be two composites of the form (or t_1 ... t_n) and (or u_1 ... u_m)
 * - k = index where the explanation must be stored in egraph->stack
 */
void gen_or_congruence_antecedent(egraph_t *egraph, composite_t *c1, composite_t *c2, int32_t k) {
  occ_t *aux, *ch1, *ch2;
  uint32_t n1, n2;

  assert(composite_kind(c1) == COMPOSITE_OR && composite_kind(c2) == COMPOSITE_OR);

  n1 = composite_arity(c1);
  n2 = composite_arity(c2);
  aux = (occ_t *) arena_alloc(&egraph->arena, (n1 + n2) * sizeof(occ_t));
  ch1 = c1->child;
  ch2 = c2->child;

  half_or_congruence_antecedent(egraph, ch1, n1, ch2, n2, aux);
  half_or_congruence_antecedent(egraph, ch2, n2, ch1, n1, aux + n1);

  egraph->stack.etag[k] = EXPL_OR_CONGRUENCE;
  egraph->stack.edata[k].ptr = aux;
}





/************************************
 *  EXPANSION INTO LITERAL VECTORS  *
 ***********************************/

/*
 * Add edge i to the explanation queue if it's not marked and mark it.
 */
static inline void enqueue_edge(ivector_t *eq, byte_t *mark, int32_t i) {
  if (!tst_bit(mark, i)) {
    set_bit(mark, i);
    ivector_push(eq, i);
  }
}

/*
 * Mark all unmarked edges on the path from t1 to t and add them to the explanation queue.
 */
static void mark_path(egraph_t *egraph, eterm_t t1, eterm_t t) {
  equeue_elem_t *eq;
  int32_t *edge;
  byte_t *mark;
  ivector_t *q;
  int32_t i;

  edge = egraph->terms.edge;
  eq = egraph->stack.eq;
  mark = egraph->stack.mark;
  q = &egraph->expl_queue;

  while (t1 != t) {
    i = edge[t1];
    assert(i >= 0);
    enqueue_edge(q, mark, i);
    t1 = edge_next(eq + i, t1);
  }
}

/*
 * Find common ancestor to t1 and t2 in the explanation tree
 * - both must be in the same class
 */
static eterm_t common_ancestor(egraph_t *egraph, eterm_t t1, eterm_t t2) {
  equeue_elem_t *eq;
  int32_t *edge;
  byte_t *mark;
  int32_t i;
  eterm_t t;

  assert(egraph_term_class(egraph, t1) == egraph_term_class(egraph, t2));

  edge = egraph->terms.edge;
  mark = egraph->terms.mark;
  eq = egraph->stack.eq;

  // mark all nodes on the path from t1 to its root
  t = t1;
  for (;;) {
    set_bit(mark, t);
    i = edge[t];
    if (i == null_edge) break;
    t = edge_next(eq + i, t);
  }

  // find first marked ancestor of t2
  while (! tst_bit(mark, t2)) {
    i = edge[t2];
    assert(i >= 0);
    t2 = edge_next(eq + i, t2);
  }

  // clear all marks
  for (;;) {
    clr_bit(mark, t1);
    i = edge[t1];
    if (i == null_edge) break;
    t1 = edge_next(eq + i, t1);
  }

  return t2;
}


/*
 * SHORT CUTS FOR EQUALITY EXPLANATION
 */

/*
 * Rather than processing the egraph merge trees to construct explanation.
 * we can look for short cuts. A short cut for explaining (t1 == t2)
 * is a literal l such that
 * 1) l is equivalent to (t1 == t2)
 * 2) l is true in the smt_core
 * 3) l does not cause a circularity in the explanation
 *
 * To check condition 3: we keep track of the edge index that triggers
 * a theory propagation from the egraph to the core: that's an egde
 * that causes merging of a class c with the Boolean constant class.
 * This causes all terms in c's class to be mapped to true or false,
 * and corresponding literals to be propagated in the smt_core.
 * If l is such a literal, then the antecedent for l in the core
 * stores the index k of the edge that triggered the propagation.
 *
 * When building an explanation for an egraph conflict, the index k
 * does not matter. When building an explanation for something else
 * (i.e., an equality (u1 == u2), then we can take l as a short cut
 * if i < k.
 */

/*
 * Literal equivalent to a Boolean term occurrence x.
 *
 * NOTE: Some Boolean terms don't have a theory variable. They come
 * from axioms of the form (not (eq t1 t2))
 * (cf. egraph_assert_diseq_axiom)
 */
static literal_t literal_for_eterm(egraph_t *egraph, occ_t x) {
  eterm_t tx;
  bvar_t v;
  literal_t l;

  tx = term_of_occ(x);
  assert(egraph_term_is_bool(egraph, tx));
  v = egraph_term_base_thvar(egraph, tx);
  l = null_literal;
  if (v != null_thvar) {
    l = mk_signed_lit(v, is_pos_occ(x));
  }

  return l;
}

/*
 * Search for a literal equivalent to (x == y)
 * - return a negative integer if no literal is found:
 *   either null_literal (i.e., -1) or -2 (i.e., null_literal ^ 1)
 */
static literal_t literal_for_eq(egraph_t *egraph, occ_t x, occ_t y) {
  if (term_of_occ(x) == true_eterm) {
    /*
     * x is either true_occ or false_occ
     * - if x is true_occ, we return the literal for y
     * - if x is false_occ, we return the opposite of the literal for y
     * we do this by flipping the low order bit if x is false, that is if
     * polarity of x is 1.
     */
    return literal_for_eterm(egraph, y) ^ polarity_of_occ(x);
  }

  if (term_of_occ(y) == true_eterm) {
    // y is either true_occ or false_occ
    return literal_for_eterm(egraph, x) ^ polarity_of_occ(y);
  }

  // otherwise: search for (eq x y)
  return egraph_find_eq(egraph, x, y);
}



/*
 * Explanation for (x == y) or (x == (not y)) when x and y are in the same class.
 * - if short_cuts are enabled, search for a literal l that's equivalent to (x == y)
 *   and add it to vector v
 * - it short_cuts are disabled, or no l is found, use symmatry/transitivity:
 *   find a path between x and y, mark all unmarked edges on that path
 */
static void explain_eq(egraph_t *egraph, occ_t x, occ_t y, ivector_t *v) {
  eterm_t tx, ty, w;
  literal_t l;
  antecedent_t a;
  int32_t id;

  assert(egraph_same_class(egraph, x, y));

  tx = term_of_occ(x);
  ty = term_of_occ(y);

  if (tx == ty) return;

  if (egraph->short_cuts) {
    assert(v != NULL);

    l = literal_for_eq(egraph, x, y);
    if (l >= 0) {
      if (egraph_opposite_occ(egraph, x, y)) {
	l = not(l);
      }

      if (l == true_literal) {
#if 0
	printf("---> possible short cut: ");
	print_literal(stdout, l);
	printf("\n");
#endif
	return;
      }

      if (literal_value(egraph->core, l) == VAL_TRUE) {
	a = get_bvar_antecedent(egraph->core, var_of(l));
	if (antecedent_tag(a) == generic_tag) {
	  // i.e., l was propagated by the Egraph
	  id = i32_of_expl(generic_antecedent(a));
	  if (id < egraph->top_id) {
#if 0
	    printf("---> short cut: ");
	    print_literal(stdout, l);
	    printf(" := ");
	    print_egraph_atom_of_literal(stdout, egraph, l);
	    printf("\n");
#endif
	    ivector_push(v, l);
	    return;
	  }
	}
      }
    }
  }

  w = common_ancestor(egraph, tx, ty);
  mark_path(egraph, tx, w);
  mark_path(egraph, ty, w);
}



/*
 * SUPPORT FOR CAUSAL EXPLANATIONS
 */

/*
 * Check whether all edges on the path from t1 to t precede k
 * (i.e., whether t1 == t was true when edge k was added).
 * - t must be an ancestor of t1
 */
static bool path_precedes_edge(egraph_t *egraph, eterm_t t1, eterm_t t, int32_t k) {
  equeue_elem_t *eq;
  int32_t *edge;
  int32_t i;

  edge = egraph->terms.edge;
  eq = egraph->stack.eq;

  while (t1 != t) {
    i = edge[t1];
    assert(i >= 0);
    if (i >= k) return false;
    t1 = edge_next(eq + i, t1);
  }

  return true;
}


/*
 * Check whether (x == y) or (x == (not y)) was true when edge k was added
 * - x and y must be in the same class
 */
static bool causally_equal(egraph_t *egraph, occ_t x, occ_t y, int32_t k) {
  eterm_t tx, ty, w;

  assert(egraph_same_class(egraph, x, y));

  tx = term_of_occ(x);
  ty = term_of_occ(y);

  if (tx == ty) return true;

  w = common_ancestor(egraph, tx, ty);
  return path_precedes_edge(egraph, tx, w, k) && path_precedes_edge(egraph, ty, w, k);
}



/*
 * DISEQUALITY EXPLANATIONS
 */

/*
 * Check whether term t is constant
 */
static bool eterm_is_constant(egraph_t *egraph, eterm_t t) {
  thvar_t x;
  etype_t tau;

  if (constant_body(egraph_term_body(egraph, t))) {
    return true;
  }

  x = egraph_term_base_thvar(egraph, t);
  if (x != null_thvar) {
    tau = egraph_term_type(egraph, t);
    switch (tau) {
    case ETYPE_INT:
    case ETYPE_REAL:
    case ETYPE_BV:
      return egraph->eg[tau]->is_constant(egraph->th[tau], x);

    default:
      break;
    }
  }

  return false;
}



/*
 * Find a constant t in the class of x then return t+
 * Warning: make sure there's a constant in the class before calling this.
 */
static occ_t constant_in_class(egraph_t *egraph, occ_t x) {
  eterm_t t;

  t = term_of_occ(x);
  while (! eterm_is_constant(egraph, t)) {
  //  while (! constant_body(egraph_term_body(egraph, t))) {
    t = term_of_occ(egraph->terms.next[t]);
    assert(t != term_of_occ(x));
  }

  return pos_occ(t);
}

/*
 * Explanation for (x != y) via bit 0 of dmasks:
 * - find two constants a and b such that x == a and y == b
 */
static void explain_diseq_via_constants(egraph_t *egraph, occ_t x, occ_t y, ivector_t *v) {
  explain_eq(egraph, x, constant_in_class(egraph, x), v);
  explain_eq(egraph, y, constant_in_class(egraph, y), v);
}


/*
 * Explanation for (x != y) from (distinct u_1 ... u_n)
 * - we must have (distinct u_1 ... u_n) == true, x == u_i, y == u_j for i/=j
 * - the explanation is built using edges that precede k
 */
static void explain_diseq_via_distinct(egraph_t *egraph, occ_t x, occ_t y, composite_t *d, int32_t k, ivector_t *v) {
  class_t cx, cy;
  occ_t t, tx, ty;
  uint32_t i;

  assert(composite_kind(d) == COMPOSITE_DISTINCT);

  t = pos_occ(d->id);
  assert(egraph_label(egraph, t) == true_label);
  explain_eq(egraph, t, true_occ, v);

  cx = egraph_class(egraph, x);
  cy = egraph_class(egraph, y);
  assert(cx != cy);

  // find terms tx of class cx and ty of class cy in d
  i = 0;
  tx = null_occurrence;
  ty = null_occurrence;
  for (;;) {
    assert(i < composite_arity(d));
    t = d->child[i];

    if (egraph_class(egraph, t) == cx && causally_equal(egraph, t, x, k)) {
      assert(tx == null_occurrence);
      tx = t;
      if (ty != null_occurrence) break;

    } else if (egraph_class(egraph, t) == cy && causally_equal(egraph, t, y, k)) {
      assert(ty == null_occurrence);
      ty = t;
      if (tx != null_occurrence) break;
    }

    i ++;
  }

  explain_eq(egraph, x, tx, v);
  explain_eq(egraph, y, ty, v);
}



/*
 * Explanation for (x != y) via the dmasks
 * - i = index of the distinct term that implied (x != y)
 * - i must be between 1 and 31
 * - k = index of the edge that uses (x != y) as antecedent
 */
static void explain_diseq_via_dmasks(egraph_t *egraph, occ_t x, occ_t y, uint32_t i, int32_t k, ivector_t *v) {
  composite_t *dpred;

  assert(1 <= i && i < egraph->dtable.npreds);

  dpred = egraph->dtable.distinct[i];
  assert(dpred != NULL && composite_kind(dpred) == COMPOSITE_DISTINCT);

  explain_diseq_via_distinct(egraph, x, y, dpred, k, v);
}




/*
 * SIMPLIFICATION AND CONGRUENCE
 */

/*
 * Explanation for (or t1 ... tn) == false
 * - t_i == false for all i
 */
static void explain_simp_or_false(egraph_t *egraph, composite_t *c, ivector_t *v) {
  uint32_t i, m;

  assert(composite_kind(c) == COMPOSITE_OR);
  m = composite_arity(c);
  for (i=0; i<m; i++) {
    explain_eq(egraph, c->child[i], false_occ, v);
  }
}


/*
 * Explanation for (or t1 ... tn) == u
 * - either t_i == false or t_i == v for all i
 */
static void explain_simp_or(egraph_t *egraph, composite_t *c, occ_t u, ivector_t *v) {
  uint32_t i, m;
  occ_t t;

  assert(composite_kind(c) == COMPOSITE_OR);

  m = composite_arity(c);
  for (i=0; i<m; i++) {
    t = c->child[i];
    if (egraph_occ_is_false(egraph, t)) {
      explain_eq(egraph, t, false_occ, v);
    } else {
      explain_eq(egraph, t, u, v);
    }
  }
}



/*
 * Explanation for "c1 and c2 are congruent" when c1 and c2 are apply, update, or tuple terms
 */
static void explain_congruence(egraph_t *egraph, composite_t *c1, composite_t *c2, ivector_t *v) {
  uint32_t i, m;

  assert(c1->tag == c2->tag);

  m = composite_arity(c1);
  for (i=0; i<m; i++) {
    explain_eq(egraph, c1->child[i], c2->child[i], v);
  }
}

/*
 * (eq t1 t2) congruent to (eq u1 u2): two variants
 */
static void explain_eq_congruence1(egraph_t *egraph, composite_t *c1, composite_t *c2, ivector_t *v) {
  explain_eq(egraph, c1->child[0], c2->child[0], v);
  explain_eq(egraph, c1->child[1], c2->child[1], v);
}

static void explain_eq_congruence2(egraph_t *egraph, composite_t *c1, composite_t *c2, ivector_t *v) {
  explain_eq(egraph, c1->child[0], c2->child[1], v);
  explain_eq(egraph, c1->child[1], c2->child[0], v);
}


/*
 * (ite t1 t2 t3) congruent to (ite u1 u2 u3): two variants
 */
static void explain_ite_congruence1(egraph_t *egraph, composite_t *c1, composite_t *c2, ivector_t *v) {
  explain_eq(egraph, c1->child[0], c2->child[0], v);
  explain_eq(egraph, c1->child[1], c2->child[1], v);
  explain_eq(egraph, c1->child[2], c2->child[2], v);
}

static void explain_ite_congruence2(egraph_t *egraph, composite_t *c1, composite_t *c2, ivector_t *v) {
  // the first call to explain_eq is for c1->child[0] == (not c2->child[0])
  explain_eq(egraph, c1->child[0], c2->child[0], v);
  explain_eq(egraph, c1->child[1], c2->child[2], v);
  explain_eq(egraph, c1->child[2], c2->child[1], v);
}


/*
 * Explanation for "c1 and c2 are congruent" when
 * c1 is (or t_1 ... t_n)
 * c2 is (or u_1 ... u_m)
 * p is an array of n+m term occurrences
 * the explanation if the conjunction
 *  (t_1 == p[0] and ... and t_n == p[n-1]) and (u_1 == p[n] and ... and u_m == p[n+m-1])
 */
static void explain_or_congruence(egraph_t *egraph, composite_t *c1, composite_t *c2, occ_t *p, ivector_t *v) {
  uint32_t i, k;

  k = composite_arity(c1);
  for (i=0; i<k; i++) {
    explain_eq(egraph, c1->child[i], *p, v);
    p ++;
  }

  k = composite_arity(c2);
  for (i=0; i<k; i++) {
    explain_eq(egraph, c2->child[i], *p, v);
    p ++;
  }
}

/*
 * Explanation for (distinct t_1 ... t_n) == (distinct u_1 ... u_n)
 * p is a permutation of u_1 ... u_n
 * the explanation is the conjunction
 * (t_1 == p[0] ... t_n == p[n-1])
 */
static void explain_distinct_congruence(egraph_t *egraph, composite_t *c1, composite_t *c2, occ_t *p, ivector_t *v) {
  uint32_t i, k;

  k = composite_arity(c1);
  for (i=0; i<k; i++) {
    explain_eq(egraph, c1->child[i], p[i], v);
  }
}



/*
 * Convert the explanation tag for a theory equality to the corresponding theory type
 */
static inline etype_t etag2theory(expl_tag_t id) {
  int32_t tau;

  assert(EXPL_ARITH_PROPAGATION <= id && id <= EXPL_FUN_PROPAGATION);
  tau = ETYPE_REAL + id - EXPL_ARITH_PROPAGATION;
  assert(ETYPE_REAL <= tau && tau <= ETYPE_FUNCTION);
  return (etype_t) tau;
}


/*
 * Explanation for equality (t1 == t2) propagated from a theory solver
 * - id = one of EXPL_ARITH_PROPAGATION, EXPL_BV_PROPAGATION, EXPL_FUN_PROPAGATION
 * - expl = whatever the solver gave as explanation when it called egraph_propagate_equality
 * - v = vector of literals (partial explanation under construction)
 */
static void explain_theory_equality(egraph_t *egraph, expl_tag_t id, eterm_t t1, eterm_t t2,
                                    void *expl, ivector_t *v) {
  th_explanation_t *e;
  etype_t tau;
  thvar_t x1, x2;
  uint32_t i, n;
  literal_t *atoms;
  th_eq_t *eqs;
  diseq_pre_expl_t *diseqs;
  composite_t *cmp;
  occ_t t;

  e = &egraph->th_expl;
  tau = etag2theory(id);
  x1 = egraph_term_base_thvar(egraph, t1);
  x2 = egraph_term_base_thvar(egraph, t2);

  assert(x1 != null_thvar && x2 != null_thvar);

  // get explanation from the satellite solver
  reset_th_explanation(e);
  egraph->eg[tau]->expand_th_explanation(egraph->th[tau], x1, x2, expl, e);

  /*
   * e->atoms = list of literals (attached to theory specific atoms)
   */
  atoms = e->atoms;
  if (atoms != NULL) {
    n = get_av_size(atoms);
    for (i=0; i<n; i++) {
      ivector_push(v, atoms[i]);
    }
  }

  /*
   * e->eqs = list of equalities
   */
  eqs = e->eqs;
  if (eqs != NULL) {
    n = get_eqv_size(eqs);
    for (i=0; i<n; i++) {
      explain_eq(egraph, pos_occ(eqs[i].lhs), pos_occ(eqs[i].rhs), v);
    }
  }

  /*
   * e->diseqs = list of disequalities + hint
   */
  diseqs = e->diseqs;
  if (diseqs != NULL) {
    n = get_diseqv_size(diseqs);
    for (i=0; i<n; i++) {
      cmp = diseqs[i].hint;
      t = pos_occ(cmp->id);
      if (composite_kind(cmp) == COMPOSITE_EQ) {
	assert(egraph_label(egraph, t) == false_label);
	explain_eq(egraph, t, false_occ, v);
      } else {
	assert(composite_kind(cmp) == COMPOSITE_DISTINCT && egraph_label(egraph, t) == true_label);
	explain_eq(egraph, t, true_occ, v);
      }
      explain_eq(egraph, pos_occ(diseqs[i].t1), pos_occ(diseqs[i].u1), v);
      explain_eq(egraph, pos_occ(diseqs[i].t2), pos_occ(diseqs[i].u2), v);
    }
  }
}






/*
 * EXPLANATION VECTOR
 */

/*
 * Expand the marked edges into a vector of literals
 * - v = result vector: literals are added to it (v is not reset)
 */
static void build_explanation_vector(egraph_t *egraph, ivector_t *v) {
  equeue_elem_t *eq;
  byte_t *mark;
  ivector_t *queue;
  unsigned char *etag;
  expl_data_t *edata;
  composite_t **body;
  eterm_t t1, t2;
  uint32_t k;
  int32_t i;

  eq = egraph->stack.eq;
  mark = egraph->stack.mark;
  etag = egraph->stack.etag;
  edata = egraph->stack.edata;
  body = egraph->terms.body;
  queue = &egraph->expl_queue;

  for (k = 0; k < queue->size; k++) {
    i = queue->data[k];
    assert(i >= 0 && tst_bit(mark, i));
    switch (etag[i]) {
    case EXPL_AXIOM:
      break;

    case EXPL_ASSERT:
      ivector_push(v, edata[i].lit);
      break;

    case EXPL_EQ:
      explain_eq(egraph, edata[i].t[0], edata[i].t[1], v);
      break;

    case EXPL_DISTINCT0:
      explain_diseq_via_constants(egraph, edata[i].t[0], edata[i].t[1], v);
      break;

    case EXPL_DISTINCT1:
    case EXPL_DISTINCT2:
    case EXPL_DISTINCT3:
    case EXPL_DISTINCT4:
    case EXPL_DISTINCT5:
    case EXPL_DISTINCT6:
    case EXPL_DISTINCT7:
    case EXPL_DISTINCT8:
    case EXPL_DISTINCT9:
    case EXPL_DISTINCT10:
    case EXPL_DISTINCT11:
    case EXPL_DISTINCT12:
    case EXPL_DISTINCT13:
    case EXPL_DISTINCT14:
    case EXPL_DISTINCT15:
    case EXPL_DISTINCT16:
    case EXPL_DISTINCT17:
    case EXPL_DISTINCT18:
    case EXPL_DISTINCT19:
    case EXPL_DISTINCT20:
    case EXPL_DISTINCT21:
    case EXPL_DISTINCT22:
    case EXPL_DISTINCT23:
    case EXPL_DISTINCT24:
    case EXPL_DISTINCT25:
    case EXPL_DISTINCT26:
    case EXPL_DISTINCT27:
    case EXPL_DISTINCT28:
    case EXPL_DISTINCT29:
    case EXPL_DISTINCT30:
    case EXPL_DISTINCT31:
      explain_diseq_via_dmasks(egraph, edata[i].t[0], edata[i].t[1], (uint32_t) (etag[i] - EXPL_DISTINCT0), i, v);
      break;

    case EXPL_SIMP_OR:
      // eq[i].lhs = (or ...), rhs == false or term occurrence
      t1 = term_of_occ(eq[i].lhs);
      assert(composite_body(body[t1]));
      if (eq[i].rhs == false_occ) {
        explain_simp_or_false(egraph, body[t1], v);
      } else {
        explain_simp_or(egraph, body[t1], eq[i].rhs, v);
      }
      break;

    case EXPL_BASIC_CONGRUENCE:
      t1 = term_of_occ(eq[i].lhs);
      t2 = term_of_occ(eq[i].rhs);
      explain_congruence(egraph, body[t1], body[t2], v);
      break;

    case EXPL_EQ_CONGRUENCE1:
      t1 = term_of_occ(eq[i].lhs);
      t2 = term_of_occ(eq[i].rhs);
      explain_eq_congruence1(egraph, body[t1], body[t2], v);
      break;

    case EXPL_EQ_CONGRUENCE2:
      t1 = term_of_occ(eq[i].lhs);
      t2 = term_of_occ(eq[i].rhs);
      explain_eq_congruence2(egraph, body[t1], body[t2], v);
      break;

    case EXPL_ITE_CONGRUENCE1:
      t1 = term_of_occ(eq[i].lhs);
      t2 = term_of_occ(eq[i].rhs);
      explain_ite_congruence1(egraph, body[t1], body[t2], v);
      break;

    case EXPL_ITE_CONGRUENCE2:
      t1 = term_of_occ(eq[i].lhs);
      t2 = term_of_occ(eq[i].rhs);
      explain_ite_congruence2(egraph, body[t1], body[t2], v);
      break;

    case EXPL_OR_CONGRUENCE:
      t1 = term_of_occ(eq[i].lhs);
      t2 = term_of_occ(eq[i].rhs);
      explain_or_congruence(egraph, body[t1], body[t2], edata[i].ptr, v);
      break;

    case EXPL_DISTINCT_CONGRUENCE:
      t1 = term_of_occ(eq[i].lhs);
      t2 = term_of_occ(eq[i].rhs);
      explain_distinct_congruence(egraph, body[t1], body[t2], edata[i].ptr, v);
      break;

    case EXPL_ARITH_PROPAGATION:
    case EXPL_BV_PROPAGATION:
    case EXPL_FUN_PROPAGATION:
      t1 = term_of_occ(eq[i].lhs);
      t2 = term_of_occ(eq[i].rhs);
      explain_theory_equality(egraph, etag[i], t1, t2, edata[i].ptr, v);
      break;

    case EXPL_RECONCILE:
      assert(false);
      break;
    }
  }

  // clear all the marks
  for (k=0; k<queue->size; k++) {
    i = queue->data[k];
    assert(i >= 0 && tst_bit(mark, i));
    clr_bit(mark, i);
  }
  ivector_reset(queue);

  // remove duplicates
  ivector_remove_duplicates(v);
}




/*
 * Build explanation for (t1 == t2): requires class[t1] == class[t2]
 * - id = edge index: all egdes used in building the explanation must have index < id
 */
void egraph_explain_equality(egraph_t *egraph, occ_t t1, occ_t t2, int32_t id, ivector_t *v) {
  assert(egraph_equal_occ(egraph, t1, t2));
  assert(egraph->expl_queue.size == 0);
  egraph->top_id = id;
  explain_eq(egraph, t1, t2, v);
  build_explanation_vector(egraph, v);
}



/*
 * Explanation for (t1 != t2) either via dmasks or via an atom (eq u v) == false
 * with t1 == u and t2 == v.
 */
static void explain_diseq(egraph_t *egraph, occ_t t1, occ_t t2, ivector_t *v) {
  composite_t *eq;
  class_t c1, c2;
  occ_t aux;
  uint32_t msk;
  int32_t k;

  c1 = egraph_class(egraph, t1);
  c2 = egraph_class(egraph, t2);

  assert(c1 != c2);

  msk = egraph->classes.dmask[c1] & egraph->classes.dmask[c2];
  if ((msk & 1) != 0) {
    explain_diseq_via_constants(egraph, t1, t2, v);
    return;
  } else if (msk != 0){
    assert(1 <= ctz(msk) && ctz(msk) < egraph->dtable.npreds);
    k = egraph->stack.top;
    explain_diseq_via_dmasks(egraph, t1, t2, ctz(msk), k, v);
    return;
  }

  // search for a composite (eq u v) such that (eq u v) == false
  // u == t1, and v == t2
  eq = congruence_table_find_eq(&egraph->ctable, t1, t2, egraph->terms.label);

  if (eq != NULL_COMPOSITE && egraph_occ_is_false(egraph, pos_occ(eq->id))) {

    explain_eq(egraph, pos_occ(eq->id), false_occ, v);

    if (c1 != egraph_class(egraph, eq->child[0])) {
      assert(c2 == egraph_class(egraph, eq->child[0]));
      aux = t1; t1 = t2; t2 = aux;
    }

    explain_eq(egraph, t1, eq->child[0], v);
    explain_eq(egraph, t2, eq->child[1], v);

  } else {
    // they don't look disequal
    assert(false);
    abort();
  }
}






/*
 * Disequality pre-explanation objects.  These must be used if the
 * egraph propagates (x1 != x2) to a satellite solver and the solver
 * uses this disequality as antecedent in further propagation. The
 * explanation for (x1 != x2) can be constructed in two steps:
 *
 * 1) eager step: call egraph_store_diseq_pre_expl
 *    This must be done when (x1 != x2) is received from the egraph
 *    to store sufficnet data into a diseq_pre_expl_t object.
 *
 * 2) lazy step: expand the pre-expl data into a set of literals.
 *    Can be done lazily, only when the explanation is needed.
 */


/*
 * Auxiliary function: find a child of cmp that's equal to t
 * in the egraph. Return null_occurrence if there's none.
 */
static occ_t find_equal_child(egraph_t *egraph, composite_t *cmp, occ_t t) {
  uint32_t i, n;
  occ_t x;
  elabel_t l;

  n = composite_arity(cmp);
  l = egraph_label(egraph, t);
  for (i=0; i<n; i++) {
    x = cmp->child[i];
    if (egraph_label(egraph, x) == l) {
      return x;
    }
  }

  return null_occurrence;
}


/*
 * Eager step: build a pre-explanation for (x1 != x2)
 * - t1 must be the egraph term attached to theory variable x1
 * - t2 must be the egraph term attached to theory variable x2
 * - hint must be the composite passed by the egraph in the call
 *   to assert_disequality or assert_distinct
 * - p: pointer to a pre-explanation structure to fill in
 */
void egraph_store_diseq_pre_expl(egraph_t *egraph, eterm_t t1, eterm_t t2, composite_t *hint, diseq_pre_expl_t *p) {
  occ_t u;

  p->hint = hint;
  p->t1 = t1;
  p->t2 = t2;

  u = find_equal_child(egraph, hint, pos_occ(t1));
  assert(u != null_occurrence && is_pos_occ(u) && egraph_equal_occ(egraph, pos_occ(t1), u));
  p->u1 = term_of_occ(u);

  u = find_equal_child(egraph, hint, pos_occ(t2));
  assert(u != null_occurrence && is_pos_occ(u) && egraph_equal_occ(egraph, pos_occ(t2), u));
  p->u2 = term_of_occ(u);

  assert(p->u1 != p->u2);
}



/*
 * Lazy step: expand a pre-explanation into an array of literals
 * - p: pre-explanation structured set by the previous function
 * - v: vector where literals will be added.
 */
void egraph_expand_diseq_pre_expl(egraph_t *egraph, diseq_pre_expl_t *p, ivector_t *v) {
  composite_t *hint;
  occ_t t;

  assert(egraph->expl_queue.size == 0);
  hint = p->hint;
  t = pos_occ(hint->id);
  if (composite_kind(hint) == COMPOSITE_EQ) {
    assert(egraph_label(egraph, t) == false_label);
    explain_eq(egraph, t, false_occ, v);
  } else {
    assert(composite_kind(hint) == COMPOSITE_DISTINCT && egraph_label(egraph, t) == true_label);
    explain_eq(egraph, t, true_occ, v);
  }

  explain_eq(egraph, pos_occ(p->t1), pos_occ(p->u1), v);
  explain_eq(egraph, pos_occ(p->t2), pos_occ(p->u2), v);

  build_explanation_vector(egraph, v);
}



/*
 * Explanation for (distinct t_1 ... t_n) == true,
 * when dmask[class[t1]] & ... & dmask[class[t_n]]) != 0
 * - d = (distinct t_1 ... t_n)
 * - dmsk = dmask[class[t1]] & ... & dmask[class[t_n]]
 */
static void explain_distinct_via_dmask(egraph_t *egraph, composite_t *d, uint32_t dmsk, ivector_t *v) {
  occ_t t, t1, t2;
  uint32_t i, j, m;
  composite_t *dpred;
  elabel_t x;
  int_hmap_t *imap;
  int_hmap_pair_t *p;

  assert(dmsk != 0);

  m = composite_arity(d);

  i = ctz(dmsk);
  assert(i < egraph->dtable.npreds);

  if (i == 0) {
    // t_1 ... t_m are equal to distinct constants a_1 ... a_m
    for (j=0; j<m; j++) {
      t1 = d->child[j];
      explain_eq(egraph, t1, constant_in_class(egraph, t1), v);
    }

  } else {
    // dpred implies d
    dpred = egraph->dtable.distinct[i];
    assert(dpred != NULL && composite_kind(dpred) == COMPOSITE_DISTINCT);

    // explain why dpred is true
    t = pos_occ(dpred->id);
    assert(egraph_label(egraph, t) == true_label);
    explain_eq(egraph, t, true_occ, v);

    imap = egraph_get_imap(egraph);
    for (i=0; i<m; i++) {
      t1 = d->child[i];
      x = egraph_label(egraph, t1);
      p = int_hmap_get(imap, x);
      assert(p->val < 0); // otherwise equal terms t_i and t_j occur in d
      p->val = t1;
    }

    m = composite_arity(dpred);
    for (i=0; i<m; i++) {
      t1 = dpred->child[i];
      x = egraph_label(egraph, t1);
      p = int_hmap_get(imap, x);
      t2 = p->val;
      if (t2 >= 0) {
        assert(egraph_equal_occ(egraph, t1, t2));
        explain_eq(egraph, t1, t2, v);
      }
    }

    int_hmap_reset(imap);
  }
}

#if 0
// NOT USED
/*
 * Explain distinct: general case
 */
static void explain_distinct(egraph_t *egraph, composite_t *d) {
  occ_t t;
  uint32_t i, j, m;
  uint32_t *dmask, dmsk;

  dmask = egraph->classes.dmask;
  m = composite_arity(d);
  assert(m > 0);

#ifndef NDEBUG
  for (i=0; i<m; i++) {
    assert(is_pos_occ(d->child[i]));
  }
#endif

  /*
   * try a cheap trick first: check whether all t_1 ... t_m are constant
   * or whether there's another atom (distinct u_1 ... u_p) that implies d
   */
  dmsk = ~((uint32_t) 0);
  i = 0;
  do {
    t = d->child[i];
    dmsk &= dmask[egraph_class(egraph, t)];
    i ++;
  } while (dmsk != 0 && i < m);

  if (dmsk) {
    explain_distinct_via_dmask(egraph, d, dmsk);
    return;
  }

  for (i=0; i<m; i++) {
    t = d->child[i];
    for (j=i+1; j<m; j++) {
      explain_diseq(egraph, t, d->child[j]);
    }
  }
}


// NOT USED
/*
 * Explain a conflict between
 * - assertion (distinct t_1 ... t_n) == false
 * - and the fact that (t_j /= t_i) for all pairs
 */
void egraph_explain_not_distinct_conflict(egraph_t *egraph, composite_t *d, ivector_t *v) {
  assert(egraph_equal_occ(egraph, pos_occ(d->id), false_occ));
  assert(egraph->expl_queue.size == 0);

  explain_eq(egraph, pos_occ(d->id), false_occ, v);
  explain_distinct(egraph, d);
  ivector_reset(v);
  build_explanation_vector(egraph, v);
}

#endif

/*
 * Check whether asserting equality (t1 == t2) is inconsistent
 * - if so, construct an explanation and store it in v
 * - i = index of the equality (t1 == t2) in egraph->stack.
 * Assumes t1 and t2 are not in the same class.
 */
bool egraph_inconsistent_edge(egraph_t *egraph, occ_t t1, occ_t t2, int32_t i, ivector_t *v) {
  occ_t aux;
  class_t c1, c2;
  uint32_t msk;
  composite_t *cmp;

  assert(egraph->expl_queue.size == 0 && ! tst_bit(egraph->stack.mark, i));

  egraph->top_id = INT32_MAX;

  if (egraph_opposite_occ(egraph, t1, t2)) {
    // t1 == (not t2);
    ivector_reset(v);
    explain_eq(egraph, t1, t2, v);
    goto conflict;
  }

  c1 = egraph_class(egraph, t1);
  c2 = egraph_class(egraph, t2);
  assert(c1 != c2);

  msk = egraph->classes.dmask[c1] & egraph->classes.dmask[c2];
  if ((msk & 1) != 0) {
    ivector_reset(v);
    explain_diseq_via_constants(egraph, t1, t2, v);
    goto conflict;
  } else if (msk != 0) {
    assert(1 <= ctz(msk) && ctz(msk) < egraph->dtable.npreds);
    ivector_reset(v);
    explain_diseq_via_dmasks(egraph, t1, t2, ctz(msk), egraph->stack.top, v);
    goto conflict;
  }

  cmp = congruence_table_find_eq(&egraph->ctable, t1, t2, egraph->terms.label);
  if (cmp != NULL && egraph_occ_is_false(egraph, pos_occ(cmp->id))) {
    // cmp is congruent to (eq t1 t2) and cmp == false
    ivector_reset(v);
    explain_eq(egraph, pos_occ(cmp->id), false_occ, v);

    if (c1 != egraph_class(egraph, cmp->child[0])) {
      assert(c2 == egraph_class(egraph, cmp->child[0]));
      aux = t1; t1 = t2; t2 = aux;
    }

    explain_eq(egraph, t1, cmp->child[0], v);
    explain_eq(egraph, t2, cmp->child[1], v);
    goto conflict;
  }

  return false;

 conflict:
  // add edge i to the explanation queue
  enqueue_edge(&egraph->expl_queue, egraph->stack.mark, i);
  build_explanation_vector(egraph, v);

  return true;
}


/*
 * Check whether asserting (distinct t1 ... t_m) is inconsistent
 * - i.e., whether t_i and t_j are equal for i /= j
 * - if so construct an explanation for the conflict and store in in v
 * - d = distinct atom
 */
bool egraph_inconsistent_distinct(egraph_t *egraph, composite_t *d, ivector_t *v) {
  occ_t t, t1, t2;
  elabel_t x;
  uint32_t i, m;
  int_hmap_t *imap;
  int_hmap_pair_t *p;

  assert(egraph->expl_queue.size == 0);

  egraph->top_id = INT32_MAX;

  imap = egraph_get_imap(egraph);

  // check whether two terms have the same label
  m = composite_arity(d);
  for (i=0; i<m; i++) {
    t1 = d->child[i];
    x = egraph_label(egraph, t1);
    assert(x >= 0);
    p = int_hmap_get(imap, x);
    t2 = p->val;
    if (t2 >= 0) goto conflict; // t1 and t2 have label x
    p->val = t1;
  }

  int_hmap_reset(imap);

  return false;

 conflict:
  int_hmap_reset(imap);

  // conflict explanation is (t1 == t2) + (d == true)
  ivector_reset(v);

  t = pos_occ(d->id);
  assert(egraph_occ_is_true(egraph, t));
  assert(egraph_equal_occ(egraph, t1, t2));

  explain_eq(egraph, t, true_occ, v);
  explain_eq(egraph, t1, t2, v);

  build_explanation_vector(egraph, v);

  return true;
}



/*
 * Test whether there is a term congruent to (eq t1 t2) and whether that
 * term is false.
 */
static bool check_diseq1(egraph_t *egraph, occ_t t1, occ_t t2) {
  composite_t *eq;

  eq = congruence_table_find_eq(&egraph->ctable, t1, t2, egraph->terms.label);
  return eq != NULL_COMPOSITE && egraph_occ_is_false(egraph, pos_occ(eq->id));
}




/*
 * Check whether asserting not d, where d is (distinct t_1 ... t_m) causes a conflict,
 * i.e., whether (t_i != t_j) holds for all i < j.
 * - if so construct an explanation and store it in v (reset v first)
 * Warning: can be expensive if m is large
 *
 * Assumptions:
 * - t_1 ... t_m are not boolean (all are positive occurrences)
 * - class[t_i] != class[t_j] when i != j
 */
bool egraph_inconsistent_not_distinct(egraph_t *egraph, composite_t *d, ivector_t *v) {
  occ_t t, t1, t2;
  uint32_t i, j, m;
  uint32_t *dmask, dmsk;

  assert(egraph->expl_queue.size == 0);

  egraph->top_id = INT32_MAX;

  dmask = egraph->classes.dmask;
  m = composite_arity(d);
  assert(m > 0);

#ifndef NDEBUG
  for (i=0; i<m; i++) {
    assert(is_pos_occ(d->child[i]));
  }
#endif

  /*
   * try a cheap trick first: check whether all t_1 ... t_m are constant
   * or whether there's another atom (distinct u_1 ... u_p) that implies d
   */
  dmsk = ~((uint32_t) 0);
  i = 0;
  do {
    t1 = d->child[i];
    dmsk &= dmask[egraph_class(egraph, t1)];
    i ++;
  } while (dmsk != 0 && i < m);

  if (dmsk) {
    // cheap trick worked: conflict detected
    ivector_reset(v);
    explain_distinct_via_dmask(egraph, d, dmsk, v);
    goto conflict;
  }

  /*
   * Cheap trick failed: check all the pairs
   */
  for (i=0; i<m; i++) {
    t1 = d->child[i];
    dmsk = dmask[egraph_class(egraph, t1)];
    for (j=i+1; j<m; j++) {
      t2 = d->child[j];
      if ((dmask[egraph_class(egraph, t2)] & dmsk) == 0 && ! check_diseq1(egraph, t1, t2)) {
        return false;
      }
    }
  }

  /*
   * All pairs are distinct: build conflict explanation
   */
  ivector_reset(v);
  for (i=0; i<m; i++) {
    t1 = d->child[i];
    for (j=i+1; j<m; j++) {
      explain_diseq(egraph, t1, d->child[j], v);
    }
  }

 conflict:
  // explain (d == false);
  t = pos_occ(d->id);
  assert(egraph_occ_is_false(egraph, t));
  explain_eq(egraph, t, false_occ, v);

  // expand the explanations
  build_explanation_vector(egraph, v);

  return true;
}



/*
 * SUPPORT FOR EGRAPH/THEORY SOLVER RECONCILIATION
 */


/*
 * Check whether the equation t1 == t2 is candidate for interface lemma
 */
static bool interface_lemma_candidate(egraph_t *egraph, occ_t t1, occ_t t2) {
  void *satellite;
  th_egraph_interface_t *interface;
  thvar_t x1, x2;

  x1 = egraph_base_thvar(egraph, t1);
  x2 = egraph_base_thvar(egraph, t2);

  if (x1 != null_thvar && x2 != null_thvar) {
    switch (egraph_type(egraph, t1)) {
    case ETYPE_INT:
    case ETYPE_REAL:
      satellite = egraph->th[ETYPE_REAL];
      interface = egraph->eg[ETYPE_REAL];
      return interface->equal_in_model(satellite, x1, x2);

    case ETYPE_BV:
      satellite = egraph->th[ETYPE_BV];
      interface = egraph->eg[ETYPE_BV];
      return interface->equal_in_model(satellite, x1, x2);

    default:
      break;
    }
  }

  return false;
}


/*
 * Scan the explanation queue until we get an edge that can be used for interface lemma
 * - the returned edge must be larger than source and be an equality between
 *   terms that have arithmetic or bit-vector variables
 * - return the index of that edge
 */
static int32_t egraph_search_for_reconcile_edge(egraph_t *egraph, int32_t source) {
  equeue_elem_t *eq;
  byte_t *mark;
  ivector_t *queue;
  unsigned char *etag;
  expl_data_t *edata;
  composite_t **body;
  bool saved_short_cuts;
  eterm_t t1, t2;
  uint32_t k;
  int32_t i, found;

  /*
   * We force short_cuts to false here since we're not
   * building an explanation.
   */
  saved_short_cuts = egraph->short_cuts;
  egraph->short_cuts = false;

  eq = egraph->stack.eq;
  mark = egraph->stack.mark;
  etag = egraph->stack.etag;
  edata = egraph->stack.edata;
  body = egraph->terms.body;
  queue = &egraph->expl_queue;

  found = -1;

  for (k = 0; k < queue->size; k++) {
    i = queue->data[k];
    assert(i >= 0 && tst_bit(mark, i));

    if (i >= source && interface_lemma_candidate(egraph, eq[i].lhs, eq[i].rhs)) {
      found = i;
      goto done;
    }

    switch (etag[i]) {
    case EXPL_AXIOM:
    case EXPL_ASSERT:
      break;

    case EXPL_EQ:
      explain_eq(egraph, edata[i].t[0], edata[i].t[1], NULL);
      break;

   case EXPL_DISTINCT0:
     explain_diseq_via_constants(egraph, edata[i].t[0], edata[i].t[1], NULL);
      break;

    case EXPL_DISTINCT1:
    case EXPL_DISTINCT2:
    case EXPL_DISTINCT3:
    case EXPL_DISTINCT4:
    case EXPL_DISTINCT5:
    case EXPL_DISTINCT6:
    case EXPL_DISTINCT7:
    case EXPL_DISTINCT8:
    case EXPL_DISTINCT9:
    case EXPL_DISTINCT10:
    case EXPL_DISTINCT11:
    case EXPL_DISTINCT12:
    case EXPL_DISTINCT13:
    case EXPL_DISTINCT14:
    case EXPL_DISTINCT15:
    case EXPL_DISTINCT16:
    case EXPL_DISTINCT17:
    case EXPL_DISTINCT18:
    case EXPL_DISTINCT19:
    case EXPL_DISTINCT20:
    case EXPL_DISTINCT21:
    case EXPL_DISTINCT22:
    case EXPL_DISTINCT23:
    case EXPL_DISTINCT24:
    case EXPL_DISTINCT25:
    case EXPL_DISTINCT26:
    case EXPL_DISTINCT27:
    case EXPL_DISTINCT28:
    case EXPL_DISTINCT29:
    case EXPL_DISTINCT30:
    case EXPL_DISTINCT31:
      explain_diseq_via_dmasks(egraph, edata[i].t[0], edata[i].t[1], (uint32_t) (etag[i] - EXPL_DISTINCT0), i, NULL);
      break;

    case EXPL_SIMP_OR:
      // eq[i].lhs = (or ...), rhs == false or term occurrence
      t1 = term_of_occ(eq[i].lhs);
      assert(composite_body(body[t1]));
      if (eq[i].rhs == false_occ) {
        explain_simp_or_false(egraph, body[t1], NULL);
      } else {
        explain_simp_or(egraph, body[t1], eq[i].rhs, NULL);
      }
      break;

    case EXPL_BASIC_CONGRUENCE:
      t1 = term_of_occ(eq[i].lhs);
      t2 = term_of_occ(eq[i].rhs);
      explain_congruence(egraph, body[t1], body[t2], NULL);
      break;

    case EXPL_EQ_CONGRUENCE1:
      t1 = term_of_occ(eq[i].lhs);
      t2 = term_of_occ(eq[i].rhs);
      explain_eq_congruence1(egraph, body[t1], body[t2], NULL);
      break;

    case EXPL_EQ_CONGRUENCE2:
      t1 = term_of_occ(eq[i].lhs);
      t2 = term_of_occ(eq[i].rhs);
      explain_eq_congruence2(egraph, body[t1], body[t2], NULL);
      break;

    case EXPL_ITE_CONGRUENCE1:
      t1 = term_of_occ(eq[i].lhs);
      t2 = term_of_occ(eq[i].rhs);
      explain_ite_congruence1(egraph, body[t1], body[t2], NULL);
      break;

    case EXPL_ITE_CONGRUENCE2:
      t1 = term_of_occ(eq[i].lhs);
      t2 = term_of_occ(eq[i].rhs);
      explain_ite_congruence2(egraph, body[t1], body[t2], NULL);
      break;

    case EXPL_OR_CONGRUENCE:
      t1 = term_of_occ(eq[i].lhs);
      t2 = term_of_occ(eq[i].rhs);
      explain_or_congruence(egraph, body[t1], body[t2], edata[i].ptr, NULL);
      break;

    case EXPL_DISTINCT_CONGRUENCE:
      t1 = term_of_occ(eq[i].lhs);
      t2 = term_of_occ(eq[i].rhs);
      explain_distinct_congruence(egraph, body[t1], body[t2], edata[i].ptr, NULL);
      break;

    case EXPL_ARITH_PROPAGATION:
    case EXPL_BV_PROPAGATION:
    case EXPL_FUN_PROPAGATION:
      // Don't explore this
      break;

    case EXPL_RECONCILE:
      found = i;
      goto done;
    }
  }

 done:
  // clear all the marks
  for (k=0; k<queue->size; k++) {
    i = queue->data[k];
    assert(i >= 0 && tst_bit(mark, i));
    clr_bit(mark, i);
  }
  ivector_reset(queue);

  assert(found >= 0);

  // restore the short_cuts flag
  egraph->short_cuts = saved_short_cuts;

  return found;
}


/*
 * Return an edge that's an antecedent of edge i and is an interface lemma candidate
 * - source must be the index of the EXPL_RECONCILE edge that triggered a conflict
 * - i must be the index of the conflict edge
 */
int32_t egraph_get_reconcile_edge(egraph_t *egraph, int32_t source, int32_t i) {
  assert(0 <= i && i < egraph->stack.top && source <= i);
  assert(egraph->expl_queue.size == 0 && ! tst_bit(egraph->stack.mark, i));
  enqueue_edge(&egraph->expl_queue, egraph->stack.mark, i);

  return egraph_search_for_reconcile_edge(egraph, source);
}


