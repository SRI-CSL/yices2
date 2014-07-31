/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * EGRAPH-UTILITIES SHARED BY SEVERAL EGRAPH MODULES
 */


#ifndef __EGRAPH_UTILS_H
#define __EGRAPH_UTILS_H

#include <assert.h>

#include "solvers/egraph/egraph_types.h"


/*********************
 *   INTERNAL IMAP   *
 ********************/

/*
 * Allocate and initialize the internal imap (int_hash_map)
 */
extern void egraph_alloc_imap(egraph_t *egraph);


/*
 * Return a pointer to egraph->imap (allocate and initialize it if needed)
 */
static inline int_hmap_t *egraph_get_imap(egraph_t *egraph) {
  if (egraph->imap == NULL) {
    egraph_alloc_imap(egraph);
  }
  return egraph->imap;
}




/***********************************
 *  ACCESS TO TERM AND CLASS DATA  *
 **********************************/

/*
 * Number of terms
 */
static inline uint32_t egraph_num_terms(egraph_t *egraph) {
  return egraph->terms.nterms;
}

/*
 * Number of classes
 */
static inline uint32_t egraph_num_classes(egraph_t *egraph) {
  return egraph->classes.nclasses;
}


/*
 * Check whether t is a valid term (not deleted)
 */
static inline bool egraph_term_is_valid(egraph_t *egraph, eterm_t t) {
  return 0 <= t && t < egraph->terms.nterms;
}

// same thing for x = t+ or t-
static inline bool egraph_occ_is_valid(egraph_t *egraph, occ_t x) {
  return egraph_term_is_valid(egraph, term_of_occ(x));
}

// same thing for a class c
static inline bool egraph_class_is_valid(egraph_t *egraph, class_t c) {
  return 0 <= c && c < egraph->classes.nclasses;
}

// same thing for a label l
static inline bool egraph_label_is_valid(egraph_t *egraph, elabel_t l) {
  return egraph_class_is_valid(egraph, class_of(l));
}


/*
 * Get fields of term t
 */
static inline composite_t *egraph_term_body(egraph_t *egraph, eterm_t t) {
  assert(egraph_term_is_valid(egraph, t));
  return egraph->terms.body[t];
}

static inline elabel_t egraph_term_label(egraph_t *egraph, eterm_t t) {
  assert(egraph_term_is_valid(egraph, t));
  return egraph->terms.label[t];
}

static inline class_t egraph_term_class(egraph_t *egraph, eterm_t t) {
  return class_of(egraph_term_label(egraph, t));
}

static inline eterm_t egraph_term_next(egraph_t *egraph, eterm_t t) {
  assert(egraph_term_is_valid(egraph, t));
  return term_of_occ(egraph->terms.next[t]);
}

static inline type_t egraph_term_real_type(egraph_t *egraph, eterm_t t) {
  assert(egraph_term_is_valid(egraph, t));
  return egraph->terms.real_type[t];
}

// theory variable of t at the base level
static inline thvar_t egraph_term_base_thvar(egraph_t *egraph, eterm_t t) {
  assert(egraph_term_is_valid(egraph, t));
  return egraph->terms.thvar[t];
}




/*
 * Get fields of class c
 */
static inline uint32_t egraph_class_dmask(egraph_t *egraph, class_t c) {
  assert(egraph_class_is_valid(egraph, c));
  return egraph->classes.dmask[c];
}

static inline occ_t egraph_class_root(egraph_t *egraph, class_t c) {
  assert(egraph_class_is_valid(egraph, c));
  return egraph->classes.root[c];
}

static inline use_vector_t *egraph_class_parents(egraph_t *egraph, class_t c) {
  assert(egraph_class_is_valid(egraph, c));
  return egraph->classes.parents + c;
}

// number of parents
static inline uint32_t egraph_class_nparents(egraph_t *egraph, class_t c) {
  return egraph_class_parents(egraph, c)->nelems;
}

static inline etype_t egraph_class_type(egraph_t *egraph, class_t c) {
  assert(egraph_class_is_valid(egraph, c));
  return (etype_t) egraph->classes.etype[c];
}

static inline thvar_t egraph_class_thvar(egraph_t *egraph, class_t c) {
  assert(egraph_class_is_valid(egraph, c));
  return egraph->classes.thvar[c];
}



/*
 * Check theory var and type of class c
 */
static inline bool egraph_class_has_thvar(egraph_t *egraph, class_t c) {
  return egraph_class_thvar(egraph, c) != null_thvar;
}

static inline bool egraph_class_is_bool(egraph_t *egraph, class_t c) {
  return egraph_class_type(egraph, c) == ETYPE_BOOL;
}

static inline bool egraph_class_is_int(egraph_t *egraph, class_t c) {
  return egraph_class_type(egraph, c) == ETYPE_INT;
}

static inline bool egraph_class_is_real(egraph_t *egraph, class_t c) {
  return egraph_class_type(egraph, c) == ETYPE_REAL;
}

static inline bool egraph_class_is_arith(egraph_t *egraph, class_t c) {
  return is_arith_etype(egraph_class_type(egraph, c));
}

static inline bool egraph_class_is_bv(egraph_t *egraph, class_t c) {
  return egraph_class_type(egraph, c) == ETYPE_BV;
}

static inline bool egraph_class_is_tuple(egraph_t *egraph, class_t c) {
  return egraph_class_type(egraph, c) == ETYPE_TUPLE;
}

static inline bool egraph_class_is_function(egraph_t *egraph, class_t c) {
  return egraph_class_type(egraph, c) == ETYPE_FUNCTION;
}



/*
 * Checks on t
 */
static inline bool egraph_term_is_variable(egraph_t *egraph, eterm_t t) {
  return egraph_term_body(egraph, t) == VARIABLE_BODY;
}

static inline bool egraph_term_is_constant(egraph_t *egraph, eterm_t t) {
  return constant_body(egraph_term_body(egraph, t));
}

static inline bool egraph_term_is_atomic(egraph_t *egraph, eterm_t t) {
  return atomic_body(egraph_term_body(egraph, t));
}

static inline bool egraph_term_is_composite(egraph_t *egraph, eterm_t t) {
  return composite_body(egraph_term_body(egraph, t));
}

static inline bool egraph_term_is_eq(egraph_t *egraph, eterm_t t) {
  composite_t *cmp;
  cmp = egraph_term_body(egraph, t);
  return composite_body(cmp) && composite_kind(cmp) == COMPOSITE_EQ;
}

static inline bool egraph_term_is_composite_tuple(egraph_t *egraph, eterm_t t) {
  composite_t *cmp;
  cmp = egraph_term_body(egraph, t);
  return composite_body(cmp) && composite_kind(cmp) == COMPOSITE_TUPLE;
}

static inline bool egraph_term_is_lambda(egraph_t *egraph, eterm_t t) {
  composite_t *cmp;
  cmp = egraph_term_body(egraph, t);
  return composite_body(cmp) && composite_kind(cmp) == COMPOSITE_LAMBDA;
}



/*
 * Assign type tau to term t
 */
static inline void egraph_set_term_real_type(egraph_t *egraph, eterm_t t, type_t tau) {
  assert(egraph_term_is_valid(egraph, t) && egraph->terms.real_type[t] == NULL_TYPE);
  egraph->terms.real_type[t] = tau;
}

/*
 * Current type and theory var of t (via t's class)
 */
static inline etype_t egraph_term_type(egraph_t *egraph, eterm_t t) {
  return egraph_class_type(egraph, egraph_term_class(egraph, t));
}

static inline thvar_t egraph_term_thvar(egraph_t *egraph, eterm_t t) {
  return egraph_class_thvar(egraph, egraph_term_class(egraph, t));
}

// check theory for term t
static inline bool egraph_term_is_bool(egraph_t *egraph, eterm_t t) {
  return egraph_class_is_bool(egraph, egraph_term_class(egraph, t));
}

static inline bool egraph_term_is_arith(egraph_t *egraph, eterm_t t) {
  return egraph_class_is_arith(egraph, egraph_term_class(egraph, t));
}

static inline bool egraph_term_is_bv(egraph_t *egraph, eterm_t t) {
  return egraph_class_is_bv(egraph, egraph_term_class(egraph, t));
}

static inline bool egraph_term_is_tuple(egraph_t *egraph, eterm_t t) {
  return egraph_class_is_tuple(egraph, egraph_term_class(egraph, t));
}

static inline bool egraph_term_is_function(egraph_t *egraph, eterm_t t) {
  return egraph_class_is_function(egraph, egraph_term_class(egraph, t));
}





/*
 * Class and label for a term occurrence x = t+ or t-
 */
static inline elabel_t egraph_label(egraph_t *egraph, occ_t x) {
  return egraph_term_label(egraph, term_of_occ(x)) ^ polarity_of_occ(x);
}

static inline class_t egraph_class(egraph_t *egraph, occ_t x) {
  return egraph_term_class(egraph, term_of_occ(x));
}

// successor occurrence of x in its class
static inline occ_t egraph_next(egraph_t *egraph, occ_t x) {
  assert(egraph_occ_is_valid(egraph, x));
  return egraph->terms.next[term_of_occ(x)] ^ polarity_of_occ(x);
}

// assign label c to x
static inline void egraph_set_label(egraph_t *egraph, occ_t x, elabel_t l) {
  assert(egraph_occ_is_valid(egraph, x));
  egraph->terms.label[term_of_occ(x)] = l ^ polarity_of_occ(x);
}

// assign y as successor of x
static inline void egraph_set_next(egraph_t *egraph, occ_t x, occ_t y) {
  assert(egraph_occ_is_valid(egraph, x) && egraph_occ_is_valid(egraph, y));
  egraph->terms.next[term_of_occ(x)] = y ^ polarity_of_occ(x);
}



/*
 * Type and theory variable of x (via its class)
 */
static inline etype_t egraph_type(egraph_t *egraph, occ_t x) {
  return egraph_class_type(egraph, egraph_class(egraph, x));
}

static inline thvar_t egraph_thvar(egraph_t *egraph, occ_t x) {
  return egraph_class_thvar(egraph, egraph_class(egraph, x));
}

// variable attached to x at the base level (null_thvar if none)
static inline thvar_t egraph_base_thvar(egraph_t *egraph, occ_t x) {
  return egraph_term_base_thvar(egraph, term_of_occ(x));
}

// check theory for occurrence x
static inline bool egraph_occ_is_bool(egraph_t *egraph, occ_t x) {
  return egraph_class_is_bool(egraph, egraph_class(egraph, x));
}

static inline bool egraph_occ_is_arith(egraph_t *egraph, occ_t x) {
  return egraph_class_is_arith(egraph, egraph_class(egraph, x));
}

static inline bool egraph_occ_is_bv(egraph_t *egraph, occ_t x) {
  return egraph_class_is_bv(egraph, egraph_class(egraph, x));
}

static inline bool egraph_occ_is_tuple(egraph_t *egraph, occ_t x) {
  return egraph_class_is_tuple(egraph, egraph_class(egraph, x));
}

static inline bool egraph_occ_is_function(egraph_t *egraph, occ_t x) {
  return egraph_class_is_function(egraph, egraph_class(egraph, x));
}




/*
 * Equality tests based on labels
 */
// check whether x == y
static inline bool egraph_equal_occ(egraph_t *egraph, occ_t x, occ_t y) {
  return egraph_label(egraph, x) == egraph_label(egraph, y);
}

// check whether x == not y
static inline bool egraph_opposite_occ(egraph_t *egraph, occ_t x, occ_t y) {
  return egraph_label(egraph, x) == opposite_label(egraph_label(egraph, y));
}

// check whether x == true
static inline bool egraph_occ_is_true(egraph_t *egraph, occ_t x) {
  return egraph_label(egraph, x) == true_label;
}

// check whether x == false
static inline bool egraph_occ_is_false(egraph_t *egraph, occ_t x) {
  return egraph_label(egraph, x) == false_label;
}

// check whether x and y are in the same class (either x == y or x == not y)
static inline bool egraph_same_class(egraph_t *egraph, occ_t x, occ_t y) {
  return egraph_class(egraph, x) == egraph_class(egraph, y);
}


/*
 * Truth-value of eterm t:
 * - if label[t] is C0+ == 0, t is true  --> truth_value is VAL_TRUE (== 3)
 * - if label[t] is C0- == 1, t is false --> truth_value is VAL_FALSE (== 2)
 *
 * Use only if t's class is C0
 */
static inline bval_t egraph_term_truth_value(egraph_t *egraph, eterm_t t) {
  assert(egraph_term_class(egraph, t) == bool_constant_class);
  return VAL_TRUE ^ egraph_term_label(egraph, t);
}

// variants: check whether t is true or false
static inline bool egraph_term_is_true(egraph_t *egraph, eterm_t t) {
  return egraph_term_label(egraph, t) == true_label;
}

static inline bool egraph_term_is_false(egraph_t *egraph, eterm_t t) {
  return egraph_term_label(egraph, t) == false_label;
}


/*
 * Equality test for two terms t1 and t2
 */
static inline bool egraph_equal_terms(egraph_t *egraph, eterm_t t1, eterm_t t2) {
  return egraph_term_label(egraph, t1) == egraph_term_label(egraph, t2);
}



/*
 * Check whether c is a root class
 */
static inline bool egraph_class_is_root_class(egraph_t *egraph, class_t c) {
  return egraph_class(egraph, egraph_class_root(egraph, c)) == c;
}




/*
 * Successor term of t in edge eq
 * - eq->lhs or eq->rhs must be either t+ or t-
 */
static inline eterm_t edge_next(equeue_elem_t *eq, eterm_t t) {
  assert(term_of_occ(eq->lhs) == t || term_of_occ(eq->rhs) == t);
  return term_of_occ(eq->lhs ^ eq->rhs) ^ t;
}

/*
 * Successor occurrence of u in edge eq
 * - eq is either (u == v) or ((not u) == v)
 * - since (not x) is (x ^ 0x1), xor does the trick:
 *   - if eq is (u == v) then u ^ v ^ u == v
 *   - if eq is ((not u) == v) then
 *   (not u) ^ v ^ u == (u ^ 0x1) ^ v ^ u == v ^ 0x1 == (not v)
 */
static inline occ_t edge_next_occ(equeue_elem_t *eq, occ_t u) {
  assert(term_of_occ(eq->lhs) == term_of_occ(u) ||
         term_of_occ(eq->rhs) == term_of_occ(u));
  return eq->lhs ^ eq->rhs ^ u;
}




/**************************************
 *  PARAMETERS AND OPTIONAL FEATURES  *
 *************************************/

/*
 * Check whether option(s) defined by x is (or are) enabled.
 * x must be a bit mask.
 */
static inline bool egraph_option_enabled(egraph_t *egraph, uint32_t x) {
  return (egraph->options & x) != 0;
}

static inline bool egraph_option_disabled(egraph_t *egraph, uint32_t x) {
  return (egraph->options &x) == 0;
}


/*
 * Set the option flag
 */
static inline void egraph_set_options(egraph_t *egraph, uint32_t x) {
  egraph->options = x;
}

static inline void egraph_enable_options(egraph_t *egraph, uint32_t x) {
  egraph->options |= x;
}

static inline void egraph_disable_options(egraph_t *egraph, uint32_t x) {
  egraph->options &= ~x;
}


/*
 * Enable the generation of ackermann lemmas (non-boolean) with a limit n.
 */
static inline void egraph_enable_dyn_ackermann(egraph_t *egraph, uint32_t n) {
  egraph_enable_options(egraph, EGRAPH_DYNAMIC_ACKERMANN);
  egraph->max_ackermann = n;
}

static inline void egraph_disable_dyn_ackermann(egraph_t *egraph) {
  egraph_disable_options(egraph, EGRAPH_DYNAMIC_ACKERMANN);
}

static inline uint32_t egraph_get_max_ackermann(egraph_t *egraph) {
  return egraph->max_ackermann;
}


/*
 * Set/get the threshold for Ackermann lemma generation
 */
static inline void egraph_set_ackermann_threshold(egraph_t *egraph, uint16_t x) {
  assert(x > 0);
  egraph->ackermann_threshold = x;
}

static inline uint16_t egraph_get_ackermann_threshold(egraph_t *egraph) {
  return egraph->ackermann_threshold;
}


/*
 * Enable the generation of ackermann lemmas (boolean) with a limit n.
 */
static inline void egraph_enable_dyn_boolackermann(egraph_t *egraph, uint32_t n) {
  egraph_enable_options(egraph, EGRAPH_DYNAMIC_BOOLACKERMANN);
  egraph->max_boolackermann = n;
}

static inline void egraph_disable_dyn_boolackermann(egraph_t *egraph) {
  egraph_disable_options(egraph, EGRAPH_DYNAMIC_BOOLACKERMANN);
}

static inline uint32_t egraph_get_max_boolackermann(egraph_t *egraph) {
  return egraph->max_boolackermann;
}


/*
 * Set/get the threshold for boolean Ackermann lemma generation
 */
static inline void egraph_set_boolack_threshold(egraph_t *egraph, uint16_t x) {
  assert(x > 0);
  egraph->boolack_threshold = x;
}

static inline uint16_t egraph_get_boolack_threshold(egraph_t *egraph) {
  return egraph->boolack_threshold;
}


/*
 * Set a quota: maximal number of new equalities created
 */
static inline void egraph_set_aux_eq_quota(egraph_t *egraph, uint32_t n) {
  egraph->aux_eq_quota = n;
}

static inline uint32_t egraph_get_aux_eq_quota(egraph_t *egraph) {
  return egraph->aux_eq_quota;
}


/*
 * Set the maximal number of interface equalities generated per call to final_check
 */
static inline void egraph_set_max_interface_eqs(egraph_t *egraph, uint32_t n) {
  egraph->max_interface_eqs = n;
}

static inline uint32_t egraph_get_max_interface_eqs(egraph_t *egraph) {
  return egraph->max_interface_eqs;
}


/*
 * Select final_check version:
 * - optimistic version should work better on most problems
 * - baseline version generates more interface equalities but it works
 *   better on a few problems (in QF_UFLIA)
 * - baseline is the default
 */
static inline void egraph_enable_optimistic_final_check(egraph_t *egraph) {
  egraph_enable_options(egraph, EGRAPH_OPTIMISTIC_FCHECK);
}

static inline void egraph_disable_optimistic_final_check(egraph_t *egraph) {
  egraph_disable_options(egraph, EGRAPH_OPTIMISTIC_FCHECK);
}




/************************************
 *  SUPPORT FOR GARBAGE COLLECTION  *
 ***********************************/

/*
 * Mark all types used by egraph to preserve them from deletion on
 * the next call to type_table_gc.
 *
 * Marked types include:
 * - any type tau that occurs in egraph->terms.real_type[i]
 * - all types that occur in egraph->tag_table.
 */
extern void egraph_gc_mark(egraph_t *egraph);


#endif
