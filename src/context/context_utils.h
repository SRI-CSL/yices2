/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */

/*
 * UTILITIES TO ACCESS CONTEXT STRUCTURES
 */

#ifndef __CONTEXT_UTILS_H
#define __CONTEXT_UTILS_H

#include "context/context_types.h"


/*
 * SUBST AND MARK VECTOR
 */

/*
 * If variable elimination is enabled, then ctx->subst is used to
 * store candidate substitutions before we check for substitution
 * cycles. The mark vector is used to mark terms during cycle detection.
 */

/*
 * Return ctx->subst. Allocate and initialize it if necessary.
 */
extern pseudo_subst_t *context_get_subst(context_t *ctx);

/*
 * Free ctx->subst (if it's not NULL)
 */ 
extern void context_free_subst(context_t *ctx);


/*
 * Return ctx->marks. Allocate and initialize it if necessary.
 */
extern mark_vector_t *context_get_marks(context_t *ctx);


/*
 * Free the mark vector if non-NULL
 */ 
extern void context_free_marks(context_t *ctx);


/*
 * INTERNAL CACHES AND AUXILIARY STRUCTURES
 */

/*
 * There are two internal caches for visiting terms.
 * - the 'cache' uses a bitvector implementation and should be
 *   better for operations that visit many terms.
 * - the 'small_cache' uses a hash table and should be better
 *   for operations that visit a small number of terms.
 *
 * There are three buffers for internal construction of polynomials
 * - arith_buffer is more expensive (requires more memory) but
 *   it supports more operations (e.g., term constructors in yices_api.c
 *   take arith_buffers as arguments).
 * - poly_buffer is a cheaper data structure, but it does not support
 *   all the operations
 * - aux_poly is even cheaper, but it's for direct construction only
 *
 * There's one buffer for bitvector polynomials. It's suitable for all
 * bit widths.
 */

/*
 * Allocate/reset/free the small cache
 * - the cache is allocated and initialized on the first call to get_small_cache
 * - reset and free do nothing if the cache is not allocated
 */
extern int_hset_t *context_get_small_cache(context_t *ctx);
extern void context_reset_small_cache(context_t *ctx);
extern void context_free_small_cache(context_t *ctx);


/*
 * Allocate/free the cache
 * - same conventions as for the small_cache
 */
extern int_bvset_t *context_get_cache(context_t *ctx);
extern void context_free_cache(context_t *ctx);


/*
 * Buffers for polynomials
 */
extern rba_buffer_t *context_get_arith_buffer(context_t *ctx);
extern void context_free_arith_buffer(context_t *ctx);

extern poly_buffer_t *context_get_poly_buffer(context_t *ctx);
extern void context_free_poly_buffer(context_t *ctx);
extern void context_reset_poly_buffer(context_t *ctx);


/*
 * Allocate the auxiliary polynomial buffer and make it large enough
 * for n monomials.
 */
extern polynomial_t *context_get_aux_poly(context_t *ctx, uint32_t n);

/*
 * Free the auxiliary polynomial
 */
extern void context_free_aux_poly(context_t *ctx);


/*
 * Buffers for bitvector polynomials
 */
extern bvpoly_buffer_t *context_get_bvpoly_buffer(context_t *ctx);
extern void context_free_bvpoly_buffer(context_t *ctx);



/*
 * EQUALITY CACHE
 */

/*
 * If lift-if is enabled then arithmetic equalities
 *  (eq (ite c t1 t2) u) are rewritten to (ite c (eq t1 u) (eq t2 u))
 * We don't create new terms (eq t1 u) or (eq t2 u). Instead, we store
 * the internalization of equalities (eq t1 u) in the eq_cache:
 * This cache maps pairs of terms <t, u> to a literal l (such that
 * l is the internalization of (t == u)).
 *
 * The following functions operate on this cache: reset/free/push/pop
 * do nothing if the cache does not exist.
 */
extern pmap2_t *context_get_eq_cache(context_t *ctx);
extern void context_free_eq_cache(context_t *ctx);
extern void context_eq_cache_push(context_t *ctx);
extern void context_eq_cache_pop(context_t *ctx);

static inline void context_reset_eq_cache(context_t *ctx) {
  context_free_eq_cache(ctx);
}


/*
 * Check what's mapped to (t1, t2) in the internal eq_cache.
 * - return null_literal if nothing is mapped to (t1, t2) (or if the cache does not exit)
 */
extern literal_t find_in_eq_cache(context_t *ctx, term_t t1, term_t t2);


/*
 * Add the mapping (t1, t2) --> l to the equality cache.
 * - allocate and initialize the cache if needed.
 * - the pair (t1, t2) must not be in the cache already.
 * - l must be different from null_literal
 */
extern void add_to_eq_cache(context_t *ctx, term_t t1, term_t t2, literal_t l);



/*
 * DIV/MOD TABLE
 */

/*
 * Initialization/reset/deletion and push/pop
 * - get_divmod_table allocates and initializes the table if needed.
 * - free/reset/push/pop do nothing if the table does not exist.
 */
extern divmod_tbl_t *context_get_divmod_table(context_t *ctx);
extern void context_free_divmod_table(context_t *ctx);
extern void context_reset_divmod_table(context_t *ctx);
extern void context_divmod_table_push(context_t *ctx);
extern void context_divmod_table_pop(context_t *ctx);


/*
 * Check whether the record for (floor x) is in the table.
 * If so return the theory variable mapped to (floor x).
 * If not return null_thvar
 * Also returns null_thvar if the table does not exist.
 */
extern thvar_t context_find_var_for_floor(context_t *ctx, thvar_t x);


/*
 * Check whether the record for (ceil x) is in the table.
 * If so return the theory variable mapped to (ceil x).
 * If not return null_thvar
 * Also returns null_thvar if the table does not exist.
 */
extern thvar_t context_find_var_for_ceil(context_t *ctx, thvar_t x);

/*
 * Check whether the record for (div x k) is in the table.
 * If so return the theory variable mapped to (div x k).
 * If not return null_thvar.
 * Also returns null_thvar if the table does not exist.
 */
extern thvar_t context_find_var_for_div(context_t *ctx, thvar_t x, const rational_t *k);


/*
 * Add record for (floor x):
 * - y = theory variable for (floor x)
 * - this creates the table if needed.
 */
extern void context_record_floor(context_t *ctx, thvar_t x, thvar_t y);


/*
 * Same thing for (ceil x)
 * - y = theory variable for (ceil x)
 */
extern void context_record_ceil(context_t *ctx, thvar_t x, thvar_t y);


/*
 * Same thing for (div x k)
 * - y = theory variable for (div x k)
 */
extern void context_record_div(context_t *ctx, thvar_t x, const rational_t *k, thvar_t y);




/*
 * FACTORING OF DISJUNCTS
 */

/*
 * Return the explorer data structure
 * - allocate and initialize it if needed
 */
extern bfs_explorer_t *context_get_explorer(context_t *ctx);

/*
 * Free the explorer if it's not NULL
 */
extern void context_free_explorer(context_t *ctx);

/*
 * Reset it if it's not NULL
 */
extern void context_reset_explorer(context_t *ctx);

/*
 * Get the common factors of term t
 * - this checks whether t is of the form (or (and  ..) (and ..) ...))
 *   and stores all terms that occur in each conjuncts into vector v
 * - example: if t is (or (and A B) (and A C D)) then A is stored in v
 * - if t is not (OR ...) then t is added to v
 *
 * This allocates and initializes ctx->explorer if needed
 */
extern void context_factor_disjunction(context_t *ctx, term_t t, ivector_t *v);


/*
 * AUXILIARY ATOMS
 */

/*
 * Simplification procedures can add equalities to the aux_eq vector
 * or atoms to the aux_atom vector. These vectors can then be processed
 * later by the internalization/flatteining procedures.
 */

/*
 * Auxiliary equalities:
 * - add a new equality (x == y) in the aux_eq vector.
 * - this is useful for simplification procedures that are executed after
 *   assertion flattening (e.g., symmetry breaking).
 * - the auxiliary equalities can then be processed by process_aux_eqs
 */
extern void add_aux_eq(context_t *ctx, term_t x, term_t y);

/*
 * Variant: add term e as an auxiliary equality
 * - e can be either ARITH_BINEQ_ATOM or ARITH_EQ_ATOM
 */
extern void add_arith_aux_eq(context_t *ctx, term_t eq);


/*
 * Auxiliary atoms:
 * - add atom a to the aux_atoms vector
 * - the auxiliary atom can be processed later by process_aux_atoms
 */
extern void add_aux_atom(context_t *ctx, term_t atom);



/*
 * DIFFERENCE-LOGIC DATA
 */

/*
 * Map to compute a bound on the length path:
 * - allocate and initialize the table if needed
 */
extern int_rat_hmap_t *context_get_edge_map(context_t *ctx);

/*
 * Delete the map
 */
extern void context_free_edge_map(context_t *ctx);

/*
 * Difference-logic profile:
 * - allocate and initialize the structure if it does not exist
 */
extern dl_data_t *context_get_dl_profile(context_t *ctx);

/*
 * Free the profile record if it's not NULL
 */
extern void context_free_dl_profile(context_t *ctx);


/*
 * TESTS
 */

/*
 * Check whether t is true or false (i.e., mapped to 'true_occ' or 'false_occ'
 * in the internalization table.
 * - t must be a root in the internalization table
 */
extern bool term_is_true(context_t *ctx, term_t t);
extern bool term_is_false(context_t *ctx, term_t t);

/*
 * Check whether (or a[0] ...  a[n-1]) is true by checking whether
 * one of the a[i] is internalized to a true term
 */
extern bool disjunct_is_true(context_t *ctx, term_t *a, uint32_t n);

/*
 * Check whether t is not internalized and of the form (ite c a b) 
 * - takes the substitution into account
 */
extern bool term_is_ite(context_t *ctx, term_t t);

/*
 * Given a descriptor  (ite c t e), checks whether it
 * contains nested if-then-elses (i.e., whether t or e
 * are themselves if-then-else terms).
 *
 * This takes the substitution/internalization table into account:
 * - if t or e is already internalized, it's not considered an if-then-else
 * - otherwise t and e are replaced by their root in the internalization
 *   table
 */
extern bool ite_is_deep(context_t *ctx, composite_term_t *ite);



/*
 * OPTIONS/SUPPORTED FEATURES
 */

/*
 * Set or clear preprocessing options
 */
static inline void enable_variable_elimination(context_t *ctx) {
  ctx->options |= VARELIM_OPTION_MASK;
}

static inline void disable_variable_elimination(context_t *ctx) {
  ctx->options &= ~VARELIM_OPTION_MASK;
}

static inline void enable_or_flattening(context_t *ctx) {
  ctx->options |= FLATTENOR_OPTION_MASK;
}

static inline void disable_or_flattening(context_t *ctx) {
  ctx->options &= ~FLATTENOR_OPTION_MASK;
}

static inline void enable_diseq_and_or_flattening(context_t *ctx) {
  ctx->options |= FLATTENOR_OPTION_MASK|FLATTENDISEQ_OPTION_MASK;
}

static inline void disable_diseq_and_or_flattening(context_t *ctx) {
  ctx->options &= ~(FLATTENOR_OPTION_MASK|FLATTENDISEQ_OPTION_MASK);
}

static inline void enable_eq_abstraction(context_t *ctx) {
  ctx->options |= EQABSTRACT_OPTION_MASK;
}

static inline void disable_eq_abstraction(context_t *ctx) {
  ctx->options &= ~EQABSTRACT_OPTION_MASK;
}

static inline void enable_arith_elimination(context_t *ctx) {
  ctx->options |= ARITHELIM_OPTION_MASK;
}

static inline void disable_arith_elimination(context_t *ctx) {
  ctx->options &= ~ARITHELIM_OPTION_MASK;
}

static inline void enable_keep_ite(context_t *ctx) {
  ctx->options |= KEEP_ITE_OPTION_MASK;
}

static inline void disable_keep_ite(context_t *ctx) {
  ctx->options &= ~KEEP_ITE_OPTION_MASK;
}

static inline void enable_bvarith_elimination(context_t *ctx) {
  ctx->options |= BVARITHELIM_OPTION_MASK;
}

static inline void disable_bvarith_elimination(context_t *ctx) {
  ctx->options &= ~BVARITHELIM_OPTION_MASK;
}

static inline void enable_symmetry_breaking(context_t *ctx) {
  ctx->options |= BREAKSYM_OPTION_MASK;
}

static inline void disable_symmetry_breaking(context_t *ctx) {
  ctx->options &= ~BREAKSYM_OPTION_MASK;
}

static inline void enable_pseudo_inverse_simplification(context_t *ctx) {
  ctx->options |= PSEUDO_INVERSE_OPTION_MASK;
}

static inline void disable_pseudo_inverse_simplification(context_t *ctx) {
  ctx->options &= ~PSEUDO_INVERSE_OPTION_MASK;
}

static inline void enable_assert_ite_bounds(context_t *ctx) {
  ctx->options |= ITE_BOUNDS_OPTION_MASK;
}

static inline void disable_assert_ite_bounds(context_t *ctx) {
  ctx->options &= ~ITE_BOUNDS_OPTION_MASK;
}

static inline void enable_cond_def_preprocessing(context_t *ctx) {
  ctx->options |= CONDITIONAL_DEF_OPTION_MASK;
}

static inline void disable_cond_def_preprocessing(context_t *ctx) {
  ctx->options &= ~CONDITIONAL_DEF_OPTION_MASK;
}

static inline void enable_ite_flattening(context_t *ctx) {
  ctx->options |= FLATTEN_ITE_OPTION_MASK;
}

static inline void disable_ite_flattening(context_t *ctx) {
  ctx->options &= ~FLATTEN_ITE_OPTION_MASK;
}

static inline void enable_or_factoring(context_t *ctx) {
  ctx->options |= FACTOR_OR_OPTION_MASK;
}

static inline void disable_or_factoring(context_t *ctx) {
  ctx->options &= ~FACTOR_OR_OPTION_MASK;
}



/*
 * Check which options are enabled
 */
static inline bool context_var_elim_enabled(context_t *ctx) {
  return (ctx->options & VARELIM_OPTION_MASK) != 0;
}

static inline bool context_flatten_or_enabled(context_t *ctx) {
  return (ctx->options & FLATTENOR_OPTION_MASK) != 0;
}

static inline bool context_flatten_diseq_enabled(context_t *ctx) {
  return (ctx->options & FLATTENDISEQ_OPTION_MASK) != 0;
}

static inline bool context_eq_abstraction_enabled(context_t *ctx) {
  return (ctx->options & EQABSTRACT_OPTION_MASK) != 0;
}

static inline bool context_arith_elim_enabled(context_t *ctx) {
  return (ctx->options & ARITHELIM_OPTION_MASK) != 0;
}

static inline bool context_keep_ite_enabled(context_t *ctx) {
  return (ctx->options & KEEP_ITE_OPTION_MASK) != 0;
}

static inline bool context_bvarith_elim_enabled(context_t *ctx) {
  return (ctx->options & BVARITHELIM_OPTION_MASK) != 0;
}

static inline bool context_breaksym_enabled(context_t *ctx) {
  return (ctx->options & BREAKSYM_OPTION_MASK) != 0;
}

static inline bool context_pseudo_inverse_enabled(context_t *ctx) {
  return (ctx->options & PSEUDO_INVERSE_OPTION_MASK) != 0;
}

static inline bool context_ite_bounds_enabled(context_t *ctx) {
  return (ctx->options & ITE_BOUNDS_OPTION_MASK) != 0;
}

static inline bool context_cond_def_preprocessing_enabled(context_t *ctx) {
  return (ctx->options & CONDITIONAL_DEF_OPTION_MASK) != 0;
}

static inline bool context_ite_flattening_enabled(context_t *ctx) {
  return (ctx->options & FLATTEN_ITE_OPTION_MASK) != 0;
}

static inline bool context_or_factoring_enabled(context_t *ctx) {
  return (ctx->options & FACTOR_OR_OPTION_MASK) != 0;
}

static inline bool context_has_preprocess_options(context_t *ctx) {
  return (ctx->options & PREPROCESSING_OPTIONS_MASK) != 0;
}

static inline bool context_dump_enabled(context_t *ctx) {
  return (ctx->options & DUMP_OPTION_MASK) != 0;
}

static inline bool splx_eager_lemmas_enabled(context_t *ctx) {
  return (ctx->options & SPLX_EGRLMAS_OPTION_MASK) != 0;
}

static inline bool splx_periodic_icheck_enabled(context_t *ctx) {
  return (ctx->options & SPLX_ICHECK_OPTION_MASK) != 0;
}

static inline bool splx_eqprop_enabled(context_t *ctx) {
  return (ctx->options & SPLX_EQPROP_OPTION_MASK) != 0;
}


/*
 * Provisional: set/clear/test dump mode
 */
static inline void enable_dump(context_t *ctx) {
  ctx->options |= DUMP_OPTION_MASK;
}

static inline void disable_dump(context_t *ctx) {
  ctx->options &= ~DUMP_OPTION_MASK;
}

// Lax mode
static inline void enable_lax_mode(context_t *ctx) {
  ctx->options |= LAX_OPTION_MASK;
}

static inline void disable_lax_mode(context_t *ctx) {
  ctx->options &= ~LAX_OPTION_MASK;
}

static inline bool context_in_strict_mode(context_t *ctx) {
  return (ctx->options & LAX_OPTION_MASK) == 0;
}


/*
 * Supported theories
 */
static inline bool context_allows_uf(context_t *ctx) {
  return (ctx->theories & UF_MASK) != 0;
}

static inline bool context_allows_bv(context_t *ctx) {
  return (ctx->theories & BV_MASK) != 0;
}

static inline bool context_allows_idl(context_t *ctx) {
  return (ctx->theories & IDL_MASK) != 0;
}

static inline bool context_allows_rdl(context_t *ctx) {
  return (ctx->theories & RDL_MASK) != 0;
}

static inline bool context_allows_lia(context_t *ctx) {
  return (ctx->theories & LIA_MASK) != 0;
}

static inline bool context_allows_lra(context_t *ctx) {
  return (ctx->theories & LRA_MASK) != 0;
}

static inline bool context_allows_lira(context_t *ctx) {
  return (ctx->theories & LIRA_MASK) != 0;
}

static inline bool context_allows_nlarith(context_t *ctx) {
  return (ctx->theories & NLIRA_MASK) != 0;
}

static inline bool context_allows_fun_updates(context_t *ctx) {
  return (ctx->theories & FUN_UPDT_MASK) != 0;
}

static inline bool context_allows_extensionality(context_t *ctx) {
  return (ctx->theories & FUN_EXT_MASK) != 0;
}

static inline bool context_allows_quantifiers(context_t *ctx) {
  return (ctx->theories & QUANT_MASK) != 0;
}


/*
 * Check which solvers are present
 */
static inline bool context_has_egraph(context_t *ctx) {
  return ctx->egraph != NULL;
}

static inline bool context_has_arith_solver(context_t *ctx) {
  return ctx->arith_solver != NULL;
}

static inline bool context_has_bv_solver(context_t *ctx) {
  return ctx->bv_solver != NULL;
}

static inline bool context_has_fun_solver(context_t *ctx) {
  return ctx->fun_solver != NULL;
}

static inline bool context_has_quant_solver(context_t *ctx) {
  return ctx->quant_solver != NULL;
}

static inline bool context_has_mcsat(context_t *ctx) {
  return ctx->mcsat != NULL;
}


/*
 * Get the difference-logic profile record (only useful for contexts
 * with architecture CTX_ARCH_AUTO_IDL or CTX_ARCH_AUTO_RDL).
 */
static inline dl_data_t *get_diff_logic_profile(context_t *ctx) {
  return ctx->dl_profile;
}


/*
 * Optional features
 */
static inline bool context_supports_multichecks(context_t *ctx) {
  return (ctx->options & MULTICHECKS_OPTION_MASK) != 0;
}

static inline bool context_supports_pushpop(context_t *ctx) {
  return (ctx->options & PUSHPOP_OPTION_MASK) != 0;
}

static inline bool context_supports_cleaninterrupt(context_t *ctx) {
  return (ctx->options & CLEANINT_OPTION_MASK) != 0;
}

static inline bool context_supports_model_interpolation(context_t* ctx) {
  return (ctx->mcsat != NULL && ctx->mcsat_options.model_interpolation);
}

/*
 * Read the mode flag
 */
static inline context_mode_t context_get_mode(context_t *ctx) {
  return ctx->mode;
}


/*
 * Read the enable quant flag
 */
static inline bool context_quant_enabled(context_t *ctx) {
  return ctx->en_quant;
}


/*
 * Enable definition clause (to be done before bit-blasting).
 */
static inline void context_enable_def_clauses(context_t *ctx) {
  if (ctx->core != NULL) {
    ctx->core->enable_def_clauses = true;
  }
}


#endif /* __CONTEXT_UTILS_H */

