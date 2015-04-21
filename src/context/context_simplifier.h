/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * UTiLITIES FOR SIMPLICATION AND PREPROCESSING
 */

/*
 * This module implements utilities and procedures to help
 * simplifying, preprocessing, and visiting assertions. These
 * proecedures are independent of the solvers used.
 */

#ifndef __CONTEXT_SIMPLIFIER_H
#define __CONTEXT_SIMPLIFIER_H

#include "context/context_types.h"


/*
 * SIMPLIFICATION
 */

/*
 * Check whether (t1 == t2) can be simplified to an existing term
 * (including true_term or false_term).
 * - t1 and t2 must be Boolean terms
 * - return NULL_TERM if no simplification is found
 */
extern term_t simplify_bool_eq(context_t *ctx, term_t t1, term_t t2);


/*
 * Same thing for bitvector terms
 * - both t1 and t2 must be root terms in the internalization table
 */
extern term_t simplify_bitvector_eq(context_t *ctx, term_t t1, term_t t2);



/*
 * FLATTENING AND VARIABLE ELIMINATION
 */

/*
 * Flattening of disjunctions
 * - rewrite nested OR terms to flat OR terms
 * - if option FLATTENDISEQ is enabled, also replace arithmetic
 *   disequalities by disjunctions of strict inequalities:
 *    (i.e., rewrite x!= 0 to (or (< x 0) (> x 0))
 *
 * The function applies flattening to composite term or:
 * - or must be of the form (or t1 .... tn)
 * - v must be empty
 * - flattening is applied recursively to t1 ... t_n
 * - the result is stored in v: it 's an array of Boolean terms
 *   u_1 .... u_m such that (or t1 ... t_n)  is equivalent to (or u_1 ... u_m).
 *
 * Side effect: use ctx's small_cache then reset it
 */
extern void flatten_or_term(context_t *ctx, ivector_t *v, composite_term_t *or);


/*
 * If t is (ite c a b), we can try to rewrite (= t k) into a conjunction
 * of terms using the two rules:
 *   (= (ite c a b) k) --> c and (= a k)        if k != b holds
 *   (= (ite c a b) k) --> (not c) and (= b k)  if k != a holds
 *
 * This works best for the NEC benchmarks in SMT LIB, where many terms
 * are deeply nested if-then-else terms with constant leaves.
 *
 * The function below does that: it rewrites (eq t k) to (and c_0 ... c_n (eq t' k))
 * - the boolean terms c_0 ... c_n are added to vector v
 * - the term t' is returned
 *
 * So the simplification worked it the returned term t' is different from t
 * (and then v->size is not 0).
 */
extern term_t flatten_ite_equality(context_t *ctx, ivector_t *v, term_t t, term_t k);


/*
 * Simplify and flatten assertion f.
 *
 * This function performs top-down Boolean propagation and collects
 * all subterms of f that can't be flattened into four vectors:
 *
 * 1) ctx->top_eqs = top-level equalities.
 *    Every t in top_eqs is (eq t1 * t2) (or a variant) asserted true.
 *    t is mapped to true in the internalization table.
 *
 * 2) ctx->top_atoms = top-level atoms.
 *    Every t in top_atoms is an atom or the negation of an atom (that
 *    can't go into top_eqs).
 *    t is mapped to true in the internalization table.
 *
 * 3) ctx->top_formulas = non-atomic terms.
 *    Every t in top_formulas is either an (OR ...) or (ITE ...) or (XOR ...)
 *    or the negation of such a term.
 *    t is mapped to true in the internalization table.
 *
 * 4) ctx->top_interns = already internalized terms.
 *    Every t in top_interns is a term that's been internalized before
 *    and is mapped to a literal l or an egraph occurrence g in
 *    the internalization table.
 *    l or g must be asserted true in later stages.
 *
 *
 * If variable elimination is enabled, then equalities of the form (= x t)
 * where x is a variable are converted to substitutions if possible:
 *
 * 1) if t is a constant or variable: then [x := t] is added as a substitution
 *    to ctx->intern_tbl (if possible)
 *
 * 2) other equalities of the form (= x t) are added to ctx->subst_eqs. to
 *    be processed later by process_candidate_subst
 *
 * This function raises an exception via longjmp if there's an error
 * or if a contradiction is detected. So ctx->env must be set.
 */
extern void flatten_assertion(context_t *ctx, term_t f);


/*
 * Process the auxiliary equalities:
 * - if substitution is not enabled, then all aux equalities are added to top_eqs
 * - otherwise, cheap substitutions are performed and candidate substitutions
 *   are added to subst_eqs.
 *
 * This function raises an exception via longjmp if a contradiction os detected.
 */
extern void process_aux_eqs(context_t *ctx);


/*
 * Process all candidate substitutions after flattening and processing of
 * auxiliary equalities.
 * - the candidate substitutions are in ctx->subst_eqs
 * - all elements of subst_eqs must be equality terms asserted true
 *   and of the form (= x t) for some variable x.
 * - converts these equalities into substitutions, as long as this
 *   can be done without creating substitution cycles.
 * - candidate substitution  that can't be converted are moved to
 *   ctx->top_eqs.
 */
extern void context_process_candidate_subst(context_t *ctx);


/*
 * Process the auxiliary atoms:
 * - take all atoms in ctx->aux_atoms and assert them
 *   (map them to true and add them to ctx->top_atoms)
 * - if there's a trivial contradiction: an atom is both
 *   asserted true and false, this function raises an exception
 *   via longjmp
 */
extern void process_aux_atoms(context_t *ctx);



/*
 * TYPES AFTER VARIABLE ELIMINATION
 */

/*
 * Get the type of r's class
 * - r must be a root in the internalization table
 */
static inline type_t type_of_root(context_t *ctx, term_t r) {
  return intern_tbl_type_of_root(&ctx->intern, r);
}

/*
 * Check whether r is root of an integer class
 * - r must be a root in the internalization table
 */
static inline bool is_integer_root(context_t *ctx, term_t r) {
  return intern_tbl_is_integer_root(&ctx->intern, r);
}


/*
 * Check whether t is in an integer or real class
 */
static inline bool in_integer_class(context_t *ctx, term_t t) {
  return is_integer_root(ctx, intern_tbl_get_root(&ctx->intern, t));
}

static inline bool in_real_class(context_t *ctx, term_t t) {
  return is_real_type(type_of_root(ctx, intern_tbl_get_root(&ctx->intern, t)));
}



/*
 * PREPROCESSING/ANALYSIS AFTER FLATTENING
 */

/*
 * Attempt to learn global equalities implied
 * by the formulas stored in ctx->top_formulas.
 * Any such equality is added to ctx->aux_eqs
 */
extern void analyze_uf(context_t *ctx);


/*
 * Check difference logic after flattening:
 * - check whether all formulas in top_eqs, top_atoms, and top_formulas
 *   are in the difference logic fragment. If so, compute the benchmark
 *   profile (i.e., statistics on number of variables + atoms)
 * - if idl is true, all variables must be integer (i.e., the formula is
 *   in the IDL fragment), otherwise all variables must be real (i.e., the
 *   formula is in the RDL fragment).
 *
 * - if all assertions are in IDL or RDL.
 *   the statistics are stored in ctx->dl_profile.
 * - raise an exception 'LOGIC_NOT_SUPPORTED' otherwise.
 *
 * This function is used to decide whether to use simplex or a
 * specialized solver when the architecture is CTX_AUTO_IDL or
 * CTX_AUTO_RDL.  Because this function is called before the actual
 * arithmetic solver is created, we assume that no arithmetic term is
 * internalized, and that top_interns is empty.
 */
extern void analyze_diff_logic(context_t *ctx, bool idl);


/*
 * Break symmetries for uf theory: this is based on the following paper:
 *
 *   David Deharbe, Pascal Fontaine, Stephan Merz, and Bruno Woltzenlogel Paleo
 *   Exploiting Symmetry in SMT Problems, CADE 2011
 *
 * Summary:
 * - search for clauses of the form (or (= t c0) ... (= t c_n))
 *   where c0 ... c_n are uninterpreted constants
 * - reduce the clause to (or (= t c0) .. (= t c_i)) for some i<n
 * - this can be done if the rest of the assertions are invariant
 *   with respect to permutations of c0 ... c_n, and if t doesn't
 *   contain c0 ... c_i.
 */
extern void break_uf_symmetries(context_t *ctx);


/*
 * Preprocessing of conditional definitions
 */
extern void process_conditional_definitions(context_t *ctx);



/*
 * CONDITIONALS/FLATTENING OF NESTED IF-THEN-ELSE
 */

/*
 * Attempt to convert an if-then-else term to a conditional
 * - return NULL if the conversion fails
 * - return a conditional descriptor otherwise
 * - if NON-NULL, the result must be freed when no-longer used
 *   by calling context_free_conditional
 */
extern conditional_t *context_make_conditional(context_t *ctx, composite_term_t *ite);

/*
 * Free a conditional descriptor returned by the previous function
 */
extern void context_free_conditional(context_t *ctx, conditional_t *d);


/*
 * Check whether conditional_t *d can be simplified
 * - d is of the form
 *    COND c1 --> a1
 *         c2 --> a2
 *         ...
 *         else --> b
 *    END
 *   where c_1 ... c_n are pairwise disjoint
 *
 * - if one of c_i is true, the function returns a_i
 * - if all c_i's are false, the function returns b
 * - in all other cases, the function returns NULL_TERM
 */
extern term_t simplify_conditional(context_t *ctx, conditional_t *d);


#endif /* CONTEXT_SIMPLIFIER_H */
