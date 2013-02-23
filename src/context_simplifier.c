/*
 * SIMPLIFICATIONS AND PREPROCESSING OF ASSERTIONS
 *
 * This module implements preprocessing and simplification procedures
 * that do not depend on the solvers used. These procedures used to be
 * in context.c. Moved them to this new module created in February 2013.
 */

#include "memalloc.h"
#include "term_utils.h"
#include "arith_buffer_terms.h"
#include "poly_buffer_terms.h"
#include "term_manager.h"

#include "context.h"
#include "eq_learner.h"
#include "symmetry_breaking.h"


#define TRACE_SUBST  0
#define TRACE_EQ_ABS 0
#define TRACE_DL     0

#define TRACE_SYM_BREAKING 1

#if TRACE_SUBST || TRACE_EQ_ABS || TRACE_DEL || TRACE_SYM_BREAKING

#include <stdio.h>
#include <inttypes.h>

#include "term_printer.h"

#endif




/***************
 *  UTILITIES  *
 **************/

/*
 * SUBST AND MARK VECTOR
 *
 * If variable elimination is enabled, then ctx->subst is used to
 * store candidate substitutions before we check for substitution
 * cycles. The mark vector is used to mark terms during cycle detection.
 */

/*
 * Allocate and initialize ctx->subst
 */
static pseudo_subst_t *context_get_subst(context_t *ctx) {
  pseudo_subst_t *tmp;

  tmp = ctx->subst;
  if (tmp == NULL) {
    tmp = (pseudo_subst_t *) safe_malloc(sizeof(pseudo_subst_t));
    init_pseudo_subst(tmp, 0);
    ctx->subst = tmp;
  }

  return tmp;
}


/*
 * Free ctx->subst
 */
void context_free_subst(context_t *ctx) {
  if (ctx->subst != NULL) {
    delete_pseudo_subst(ctx->subst);
    safe_free(ctx->subst);
    ctx->subst = NULL;
  }
}




/*
 * Allocate and initialize mark vectors
 */
static mark_vector_t *context_get_marks(context_t *ctx) {
  mark_vector_t *tmp;

  tmp = ctx->marks;
  if (tmp == NULL) {
    tmp = (mark_vector_t *) safe_malloc(sizeof(mark_vector_t));
    init_mark_vector(tmp, 100, WHITE);
    ctx->marks = tmp;
  }

  return tmp;
}


/*
 * Free the mark vector
 */
void context_free_marks(context_t *ctx) {
  if (ctx->marks != NULL) {
    delete_mark_vector(ctx->marks);
    safe_free(ctx->marks);
    ctx->marks = NULL;
  }
}


/*
 * CACHES
 *
 * There are two internal caches for visiting formulas/terms.
 * - the 'cache' uses a bitvector implementation and should be 
 *   better for operations that visit many terms.
 * - the 'small_cache' uses a hash table and should be better
 *   for operations that visit a small number of terms.
 */

/*
 * Allocate and initialize the internal small_cache if needed
 */
int_hset_t *context_get_small_cache(context_t *ctx) {
  int_hset_t *tmp;

  tmp = ctx->small_cache;
  if (tmp == NULL) {
    tmp = (int_hset_t *) safe_malloc(sizeof(int_hset_t));
    init_int_hset(tmp, 32);
    ctx->small_cache = tmp;
  }
  return tmp;
}


/*
 * Empty the small_cache
 */
void context_reset_small_cache(context_t *ctx) {
  int_hset_t *tmp;

  tmp = ctx->small_cache;
  if (tmp != NULL) {
    int_hset_reset(tmp);
  }
}

/*
 * Free the small_cache
 */
void context_free_small_cache(context_t *ctx) {
  int_hset_t *tmp;

  tmp = ctx->small_cache;
  if (tmp != NULL) {
    delete_int_hset(tmp);
    safe_free(tmp);
    ctx->small_cache = NULL;
  }
}


/*
 * Allocate and initialize the cache
 */
int_bvset_t *context_get_cache(context_t *ctx) {
  int_bvset_t *tmp;

  tmp = ctx->cache;
  if (tmp == NULL) {
    tmp = (int_bvset_t *) safe_malloc(sizeof(int_bvset_t));
    init_int_bvset(tmp, 0);
    ctx->cache = tmp;
  }

  return tmp;
}



/*
 * Free the cache
 */
void context_free_cache(context_t *ctx) {
  int_bvset_t *tmp;

  tmp = ctx->cache;
  if (tmp != NULL) {
    delete_int_bvset(tmp);
    safe_free(tmp);
    ctx->cache = NULL;
  }
}


/*
 * ARITHMETIC BUFFERS
 *
 * There are three buffers for internal construction of polynomials
 * - arith_buffer is more expensive (requires more memory) but 
 *   it supports more operations (e.g., term constructors in yices_api.c
 *   take arith_buffers as arguments).
 * - poly_buffer is a cheaper data structure, but it does not support 
 *   all the operations
 * - aux_poly is even cheaper, but it's for direct construction only 
 */

/*
 * Allocate the arithmetic buffer + store if necessary
 */
arith_buffer_t *context_get_arith_buffer(context_t *ctx) {
  arith_buffer_t *tmp;
  object_store_t *store;

  tmp = ctx->arith_buffer;
  if (tmp == NULL) {
    assert(ctx->mlist_store == NULL);
    store = (object_store_t *) safe_malloc(sizeof(object_store_t));
    init_mlist_store(store);
    ctx->mlist_store = store;

    tmp = (arith_buffer_t *) safe_malloc(sizeof(arith_buffer_t));
    init_arith_buffer(tmp, ctx->terms->pprods, store);
    ctx->arith_buffer = tmp;
  }
  
  return tmp;
}


/*
 * Free the arithmetic buffer + store
 */
void context_free_arith_buffer(context_t *ctx) {
  arith_buffer_t *tmp;
  object_store_t *store;

  tmp = ctx->arith_buffer;
  if (tmp != NULL) {
    delete_arith_buffer(tmp);
    safe_free(tmp);
    ctx->arith_buffer = NULL;

    store = ctx->mlist_store;
    assert(store != NULL);
    delete_mlist_store(store);
    safe_free(store);
    ctx->mlist_store = NULL;
  }
}



/*
 * Allocate the poly_buffer
 */
poly_buffer_t *context_get_poly_buffer(context_t *ctx) {
  poly_buffer_t *tmp;

  tmp = ctx->poly_buffer;
  if (tmp == NULL) {
    tmp = (poly_buffer_t *) safe_malloc(sizeof(poly_buffer_t));
    init_poly_buffer(tmp);
    ctx->poly_buffer = tmp;
  }

  return tmp;
}


/*
 * Free it
 */
void context_free_poly_buffer(context_t *ctx) {
  poly_buffer_t *tmp;

  tmp = ctx->poly_buffer;
  if (tmp != NULL) {
    delete_poly_buffer(tmp);
    safe_free(tmp);
    ctx->poly_buffer = NULL;
  }
}


/*
 * Reset it
 */
void context_reset_poly_buffer(context_t *ctx) {
  if (ctx->poly_buffer != NULL) {
    reset_poly_buffer(ctx->poly_buffer);
  }
}


/*
 * Allocate the auxiliary polynomial buffer and make it large enough
 * for n monomials.
 */
polynomial_t *context_get_aux_poly(context_t *ctx, uint32_t n) {
  polynomial_t *p;
  uint32_t k;

  assert(n > 0);

  p = ctx->aux_poly;
  k = ctx->aux_poly_size;
  if (k < n) {
    if (k == 0) {
      assert(p == NULL);
      if (n < 10) n = 10;
      p = alloc_raw_polynomial(n);
    } else {
      free_polynomial(p);
      p = alloc_raw_polynomial(n);
    }
    ctx->aux_poly = p;
    ctx->aux_poly_size = n;
  }

  assert(p != NULL && ctx->aux_poly_size >= n);
  
  return p;
}


/*
 * Reset the auxiliary polynomial
 */
void context_free_aux_poly(context_t *ctx) {
  polynomial_t *p;
  
  p = ctx->aux_poly;
  if (p != NULL) {
    free_polynomial(p);
    ctx->aux_poly = NULL;
    ctx->aux_poly_size = 0;
  }
}



/*
 * CACHE/HASH MAP FOR LIFTED EQUALITIES
 *
 * If lift-if is enabled then arithmetic equalities
 *  (eq (ite c t1 t2) u) are rewritten to (ite c (eq t1 u) (eq t2 u))
 * We don't create new terms (eq t1 u) or (eq t2 u). Instead, we store
 * the internalization of equalities (eq t1 u) in the eq_cache:
 * This cache maps pairs of terms <t, u> to a literal l (such that
 * l is the internalization of (t == u)).
 */

/*
 * Allocate and initialize the cache
 */
pmap2_t *context_get_eq_cache(context_t *ctx) {
  pmap2_t *tmp;

  tmp = ctx->eq_cache;
  if (tmp == NULL) {
    tmp = (pmap2_t *) safe_malloc(sizeof(pmap2_t));
    init_pmap2(tmp);
    pmap2_set_level(tmp, ctx->base_level);
    ctx->eq_cache = tmp;
  }

  return tmp;
}


/*
 * Free the cache
 */
void context_free_eq_cache(context_t *ctx) {
  pmap2_t *tmp;

  tmp = ctx->eq_cache;
  if (tmp != NULL) {
    delete_pmap2(tmp);
    safe_free(tmp);
    ctx->eq_cache = NULL;
  }
}


/*
 * Push/pop/reset if the cache exists
 */
void context_eq_cache_push(context_t *ctx) {
  pmap2_t *tmp;

  tmp = ctx->eq_cache;
  if (tmp != NULL) {
    pmap2_push(tmp);
  }
}

void context_eq_cache_pop(context_t *ctx) {
  pmap2_t *tmp;

  tmp = ctx->eq_cache;
  if (tmp != NULL) {
    pmap2_pop(tmp);
  }
}



/*
 * Check what's mapped to (t1, t2) in the internal eq_cache.
 * - return null_literal if nothing is mapped to (t1, t2) (or if the cache does not exit)
 */
literal_t find_in_eq_cache(context_t *ctx, term_t t1, term_t t2) {
  pmap2_t *eq_cache;
  pmap2_rec_t *eq;
  term_t aux;
  literal_t l;

  l = null_literal;
  eq_cache = ctx->eq_cache;
  if (eq_cache != NULL) {
    // normalize the pair: we want t1 >= t2
    if (t1 < t2) {
      aux = t1; t1 = t2; t2 = aux;
    }
    assert(t1 >= t2);

    eq = pmap2_find(eq_cache, t1, t2);
    if (eq != NULL) {
      l = eq->val;
      assert(l != null_literal);
    }
  }

  return l;
}


/*
 * Add the mapping (t1, t2) --> l to the equality cache.
 * - allocate and initialize the cache if needed.
 * - the pair (t1, t2) must not be in the cache already.
 * - l must be different from null_literal
 */
void add_to_eq_cache(context_t *ctx, term_t t1, term_t t2, literal_t l) {
  pmap2_t *eq_cache;
  pmap2_rec_t *eq;
  term_t aux;

  assert(l != null_literal);

  eq_cache = context_get_eq_cache(ctx);
  if (t1 < t2) {
    aux = t1; t1 = t2; t2 = aux;
  }
  eq = pmap2_get(eq_cache, t1, t2);
  assert(eq != NULL && eq->val == -1);
  eq->val = l;
}




/*
 * DIFFERENCE-LOGIC DATA
 */

/*
 * Difference-logic profile: 
 * - allocate and initialize the structure if it does not exist
 */
static dl_data_t *context_get_dl_profile(context_t *ctx) {
  dl_data_t *tmp;

  tmp = ctx->dl_profile;
  if (tmp == NULL) {
    tmp = (dl_data_t *) safe_malloc(sizeof(dl_data_t));
    q_init(&tmp->sum_const);
    tmp->num_vars = 0;
    tmp->num_atoms = 0;
    tmp->num_eqs = 0;
    ctx->dl_profile = tmp;
  }

  return tmp;
}


/*
 * Free the profile record
 */
void context_free_dl_profile(context_t *ctx) {
  dl_data_t *tmp;

  tmp = ctx->dl_profile;
  if (tmp != NULL) {
    q_clear(&tmp->sum_const);
    safe_free(tmp);
    ctx->dl_profile = NULL;
  }
}





/*****************************
 *  FORMULA SIMPLIFICATION   *
 ****************************/

/*
 * Check whether t is true or false (i.e., mapped to 'true_occ' or 'false_occ'
 * in the internalization table.
 * - t must be a root in the internalization table
 */
 bool term_is_true(context_t *ctx, term_t t) {
  bool tt;

  assert(intern_tbl_is_root(&ctx->intern, t));
  tt = is_pos_term(t);
  t = unsigned_term(t);
  
  return intern_tbl_root_is_mapped(&ctx->intern, t) && 
    intern_tbl_map_of_root(&ctx->intern, t) == bool2code(tt);
}

bool term_is_false(context_t *ctx, term_t t) {
  bool tt;

  assert(intern_tbl_is_root(&ctx->intern, t));
  tt = is_pos_term(t);
  t = unsigned_term(t);
  
  return intern_tbl_root_is_mapped(&ctx->intern, t) && 
    intern_tbl_map_of_root(&ctx->intern, t) == bool2code(! tt);
}


/*
 * All functions below attempt to rewrite a (boolean) term r to an
 * equivalent (boolean) term q. They return NULL_TERM if the
 * simplification fails.
 */
static term_t simplify_select(context_t *ctx, term_t r) {
  select_term_t *sel;
  composite_term_t *tuple;
  term_t t;

  sel = select_term_desc(ctx->terms, r);  
  t = intern_tbl_get_root(&ctx->intern, sel->arg);
  if (term_kind(ctx->terms, t) == TUPLE_TERM) {
    // select i (tuple ... t_i ...) --> t_i
    tuple = tuple_term_desc(ctx->terms, t);
    return tuple->arg[sel->idx];
  }

  return NULL_TERM;
}

static term_t simplify_bit_select(context_t *ctx, term_t r) {
  select_term_t *sel;
  term_t t;

  sel = bit_term_desc(ctx->terms, r);
  t = intern_tbl_get_root(&ctx->intern, sel->arg);
  return extract_bit(ctx->terms, t, sel->idx);
}

static term_t simplify_arith_geq0(context_t *ctx, term_t r) {
  term_table_t *terms;
  composite_term_t *d;
  term_t t, x, y;

  terms = ctx->terms;
  t = arith_ge_arg(terms, r);
  t = intern_tbl_get_root(&ctx->intern, t);
  if (is_ite_term(terms, t)) {
    /*
     * (ite c x y) >= 0 --> c  if (x >= 0) and (y < 0)
     * (ite c x y) >= 0 --> ~c if (x < 0) and (y >= 0)
     */
    d = ite_term_desc(terms, t);
    x = intern_tbl_get_root(&ctx->intern, d->arg[1]);
    y = intern_tbl_get_root(&ctx->intern, d->arg[2]);

    if (arith_term_is_nonneg(terms, x) && 
        arith_term_is_negative(terms, y)) {
      return d->arg[0];
    }

    if (arith_term_is_negative(terms, x) && 
        arith_term_is_nonneg(terms, y)) {
      return opposite_term(d->arg[0]);
    }
  }

  return NULL_TERM;
}

static term_t simplify_arith_eq0(context_t *ctx, term_t r) {
  term_table_t *terms;
  composite_term_t *d;
  term_t t, x, y;

  terms = ctx->terms;
  t = arith_eq_arg(terms, r);
  t = intern_tbl_get_root(&ctx->intern, t);
  if (is_ite_term(terms, t)) {
    /*
     * (ite c 0 y) == 0 -->  c if y != 0
     * (ite c x 0) == 0 --> ~c if x != 0
     */
    d = ite_term_desc(terms, t);
    x = intern_tbl_get_root(&ctx->intern, d->arg[1]);
    y = intern_tbl_get_root(&ctx->intern, d->arg[2]);

    if (x == zero_term && arith_term_is_nonzero(terms, y)) {
      return d->arg[0];
    }

    if (y == zero_term && arith_term_is_nonzero(terms, x)) {
      return opposite_term(d->arg[0]);
    }
  }

  return NULL_TERM;
}


/*
 * Simplification of if-then-else: (ite c t1 t2)
 * - c, t1, and t2 are all root terms in the internalization table
 * - flatten_bool_ite does more simplifications
 */
static term_t simplify_ite(context_t *ctx, term_t c, term_t t1, term_t t2) {
  if (t1 == t2) return t1;                // (ite c t1 t1) --> t1
  if (term_is_true(ctx, c)) return t1;    // (ite true t1 t2) --> t1
  if (term_is_false(ctx, c)) return t2;   // (ite false t1 t2) --> t2

  return NULL_TERM;
}
                                                                                


/*
 * Simplification for equalities between two terms t1 and t2.
 * - both t1 and t2 are root terms in the internalization table
 * - the simplification functions don't check whether t1 = t2
 * - all simplification functions either a boolean term t equivalent
 *   to (t1 == t2) or return NULL_TERM if no simplification is found
 */

// t1 and t2 are arithmetic terms
static term_t simplify_arith_bineq(context_t *ctx, term_t t1, term_t t2) {
  term_table_t *terms;
  composite_term_t *d;
  term_t x, y;

  terms = ctx->terms;
  if (is_ite_term(terms, t1)) {
    /*
     * (ite c x y) == x --> c  if x != y
     * (ite c x y) == y --> ~c if x != y
     */
    d = ite_term_desc(terms, t1);
    x = intern_tbl_get_root(&ctx->intern, d->arg[1]);
    y = intern_tbl_get_root(&ctx->intern, d->arg[2]);

    if (x == t2 && disequal_arith_terms(terms, y, t2)) {
      return d->arg[0];
    }

    if (y == t2 && disequal_arith_terms(terms, x, t2)) {
      return opposite_term(d->arg[0]);
    }
  }

  if (is_ite_term(terms, t2)) {
    // symmetric case
    d = ite_term_desc(terms, t2);
    x = intern_tbl_get_root(&ctx->intern, d->arg[1]);
    y = intern_tbl_get_root(&ctx->intern, d->arg[2]);

    if (x == t1 && disequal_arith_terms(terms, y, t1)) {
      return d->arg[0];
    }

    if (y == t1 && disequal_arith_terms(terms, x, t1)) {
      return opposite_term(d->arg[0]);
    }    
  }

  return NULL_TERM;
}

// t1 and t2 are boolean terms
term_t simplify_bool_eq(context_t *ctx, term_t t1, term_t t2) {
  if (term_is_true(ctx, t1)) return t2;  // (eq true t2) --> t2
  if (term_is_true(ctx, t2)) return t1;  // (eq t1 true) --> t1
  if (term_is_false(ctx, t1)) return opposite_term(t2); // (eq false t2) --> not t2
  if (term_is_false(ctx, t2)) return opposite_term(t1); // (eq t1 false) --> not t1

  return NULL_TERM;
}



/*
 * Simplification for (bveq t1 t2)
 * - both t1 and t2 must be root terms in the internalization table
 */
term_t simplify_bitvector_eq(context_t *ctx, term_t t1, term_t t2) {
  term_table_t *terms;
  term_t t;

  terms = ctx->terms;
  if (t1 == t2) {
    t = true_term;
  } else if (disequal_bitvector_terms(terms, t1, t2)) {
    t = false_term;
  } else {
    t = simplify_bveq(terms, t1, t2);
  }

  return t;  
}



/**************************
 *  VARIABLE ELIMINATION  *
 *************************/

/*
 * If variable elimination is enabled, some top-level equalities (eq x
 * <term>) are converted into substitutions [x := term] and variable x
 * is eliminated. This is done in three phases:
 *
 * 1) Cheap substitutions (X := constant or X := variable) are performed first.
 *    Other possible substitutions (X := <term>) are stored into vector subst_eqs.
 *
 * 2) After flattening, the terms in subst_eqs are scanned and converted to 
 *    potential substitutions [X --> <term>] whenever possible. Terms in subst_eqs
 *    that are no longer possible substitutions are copied into top_eqs.
 *
 * 3) Substitution cycles are removed. Every substitution that does not cause
 *    a cycle is stored in intern_table.
 *
 * NOTE: it's too expensive to check for cycles in every candidate substitution
 * (i.e., we can't call intern_tbl_valid_subst in phase 1).
 */


/*
 * VARIABLE ELIMINATION: PHASE 1
 */

/*
 * Process a candidate substitution [t1 := t2]
 * - e is a term equivalent to (eq t1 t2) and e has been asserted true
 * - both t1 and t2 are roots in the internalization table
 * - t1 is free and t2 is not
 * - if t2 is constant, perform the substitution now
 * - otherwise store e into subst_eqs for Phase 2 processing
 */
static void process_candidate_subst(context_t *ctx, term_t t1, term_t t2, term_t e) {
  intern_tbl_t *intern;

  assert(term_is_true(ctx, e));

  intern = &ctx->intern;
  if (is_constant_term(ctx->terms, t2)) {
    if (intern_tbl_valid_const_subst(intern, t1, t2)) {
#if TRACE_SUBST
      printf("Eager substitution: ");
      print_term_desc(stdout, ctx->terms, t1);
      printf(" := ");;
      print_term_desc(stdout, ctx->terms, 2);
      printf("\n");
      fflush(stdout);
#endif
      intern_tbl_add_subst(intern, t1, t2);
    } else {
      // unsat by type incompatibility
      longjmp(ctx->env, TRIVIALLY_UNSAT);
    }
  } else {
    ivector_push(&ctx->subst_eqs, e);
  }
}

/*
 * Attempt to turn (eq t1 t2) into a variable substitution
 * - both t1 and t2 are root terms in the internalization table
 *   (and t1 and t2 are not boolean so they have positive polarity)
 * - e is a term equivalent to (eq t1 t2)
 * - if both t1 and t2 are free merge their classes in the internalization table
 * - if one is free and the other is a constant perform the substitution now
 * - if one is free and the other is not a constant store e in subst_eqs for Phase 2
 * - otherwise, add e to the top_eqs
 */
static void try_substitution(context_t *ctx, term_t t1, term_t t2, term_t e) {
  intern_tbl_t *intern;
  bool free1, free2;

  assert(is_pos_term(t1) && is_pos_term(t2) && term_is_true(ctx, e));

  if (context_var_elim_enabled(ctx)) {
    intern = &ctx->intern;

    free1 = intern_tbl_root_is_free(intern, t1);
    free2 = intern_tbl_root_is_free(intern, t2);

    if (free1 && free2) {
      intern_tbl_merge_classes(intern, t1, t2);
      return;
    }
    
    if (free1) {
      process_candidate_subst(ctx, t1, t2, e);
      return;
    }

    if (free2) {
      process_candidate_subst(ctx, t2, t1, e);
      return;
    }
  }

  // no substitution: record e as a top-equality
  ivector_push(&ctx->top_eqs, e);
}


/*
 * Attempt to turn (eq t1 t2) into a variable substitution 
 * - both t1 and t2 are boolean root terms in the internalization table
 * - e is a term equivalent to (eq t1 t2)
 * - neither t1 nor t2 are constant
 */
static void try_bool_substitution(context_t *ctx, term_t t1, term_t t2, term_t e) {
  intern_tbl_t *intern;
  bool free1, free2;

  assert(term_is_true(ctx, e));

  if (context_var_elim_enabled(ctx)) {
    intern = &ctx->intern;

    free1 = intern_tbl_root_is_free(intern, t1);
    free2 = intern_tbl_root_is_free(intern, t2);

    if (free1 && free2) {
      /*
       * Both t1 and t2 are free
       */
      intern_tbl_merge_classes(intern, t1, t2);
      return;
    }

    if (free1 || free2) {
      /*
       * Only one is free: save e in subst_eqs for future processing
       */
      ivector_push(&ctx->subst_eqs, e);
      return;
    }
  }
  
  // no substitution
  ivector_push(&ctx->top_eqs, e);
}



/*
 * VARIABLE ELIMINATION: PHASE 2
 */

/*  
 * Check whether x is already mapped in the candidate substitution
 * - if not, store [x := t] as a candidate
 * - otherwise, add e to the top_eqs vector
 */
static void try_pseudo_subst(context_t *ctx, pseudo_subst_t *subst, term_t x, term_t t, term_t e) {
  subst_triple_t *s;

  assert(is_pos_term(x) && intern_tbl_root_is_free(&ctx->intern, x) && term_is_true(ctx, e));

  s = pseudo_subst_get(subst, x);
  assert(s->var == x);
  if (s->map == NULL_TERM) {
    // x := t is a candidate
    assert(s->eq == NULL_TERM);
    s->map = t;
    s->eq = e;

#if TRACE_SUBST
    printf("Add subst candidate ");
    print_term_desc(stdout, ctx->terms, x);
    printf(" := ");;
    print_term_desc(stdout, ctx->terms, t);
    printf(" by assertion ");
    print_term_desc(stdout, ctx->terms, e);
    printf("\n");
    fflush(stdout);
#endif
    
  } else {
    ivector_push(&ctx->top_eqs, e);
  }
} 

/*
 * Check whether (eq t1 t2) can still be turned into a substitution (X := term)
 * - if so add the candidate substitution [X --> term] to subst
 * - otherwise, move e to the top-level equalities
 * - both t1 and t2 are root terms in the internalization table
 * - e is equivalent to (eq t1 t2))
 * - t1 and t2 are not boolean terms
 */
static void check_candidate_subst(context_t *ctx, pseudo_subst_t *subst, term_t t1, term_t t2, term_t e) {
  assert(is_pos_term(t1) && is_pos_term(t2) && term_is_true(ctx, e));

  if (intern_tbl_root_is_free(&ctx->intern, t1)) {
    try_pseudo_subst(ctx, subst, t1, t2, e);
  } else if (intern_tbl_root_is_free(&ctx->intern, t2)) {
    try_pseudo_subst(ctx, subst, t2, t1, e);
  } else {
    ivector_push(&ctx->top_eqs, e);
  }
}



/*
 * Same thing for an equality between booleans terms
 */
static void check_candidate_bool_subst(context_t *ctx, pseudo_subst_t *subst, term_t t1, term_t t2, term_t e) {
  assert(is_boolean_term(ctx->terms, t1) && is_boolean_term(ctx->terms, t2) && term_is_true(ctx, e));

  if (intern_tbl_root_is_free(&ctx->intern, t1)) {
    // if t1 is (not u1), rewrite to (u1 == not t2)
    t2 ^= polarity_of(t1);
    t1 = unsigned_term(t1);
    try_pseudo_subst(ctx, subst, t1, t2, e);
  } else if (intern_tbl_root_is_free(&ctx->intern, t2)) {
    // fix polarities too
    t1 ^= polarity_of(t2);
    t2 = unsigned_term(t2);
    try_pseudo_subst(ctx, subst, t2, t1, e);
  } else {
    ivector_push(&ctx->top_eqs, e);
  }
}


/*
 * Process all elements in subst_eqs:
 * - turn them into substitution candidates or move them to top_eqs
 */
static void process_subst_eqs(context_t *ctx, pseudo_subst_t *subst) {
  term_table_t *terms;
  ivector_t *subst_eqs;
  composite_term_t *eq;
  term_t e, t1, t2;
  uint32_t i, n;

  terms = ctx->terms;
  subst_eqs = &ctx->subst_eqs;

  n = subst_eqs->size;
  for (i=0; i<n; i++) {
    e = subst_eqs->data[i];
    assert(term_is_true(ctx, e));

    switch (term_kind(terms, e)) {
    case EQ_TERM:
    case ARITH_BINEQ_ATOM:
    case BV_EQ_ATOM:      
      eq = composite_term_desc(terms, e);
      assert(eq->arity == 2);
      t1 = intern_tbl_get_root(&ctx->intern, eq->arg[0]);
      t2 = intern_tbl_get_root(&ctx->intern, eq->arg[1]);

      if (is_boolean_term(terms, t1)) {
        /*
         * e was asserted true
         * it's either (eq t1 t2) or (not (eq t1 t2))
         * in the latter case, we use the equivalence
         *  (not (eq t1 t2)) <--> (eq t1 (not t2))
         * i.e., we flip t2's polarity if e has negative polarity
         */
        t2 ^= polarity_of(e);
        check_candidate_bool_subst(ctx, subst, t1, t2, e);
      } else {
        /*
         * e is (eq t1 t2) for two non-boolean terms t1 and t2
         */
        assert(is_pos_term(e));
        check_candidate_subst(ctx, subst, t1, t2, e);
      }
      break;

    default:
      assert(false);
      break;
    }
  }
}


/*
 * VARIABLE ELIMINATION PHASE 3: CYCLE REMOVAL
 */

/*
 * We use a depth-first search in the dependency graph:
 * - vertices are terms,
 * - edges are of two forms: 
 *    t --> u if u is a child subterm of t
 *    x := t  if x is a variable and t is the substitution candidate for x
 *
 * By construction, the graph restricted to edges t --> u (without the 
 * substitution edges) is a DAG. So we can remove cycles by removing some 
 * substitution edges x := t.
 */

/*
 * Substitution candidate for term t:
 * - return NULL_TERM if there's no candidate
 */
static term_t subst_candidate(context_t *ctx, term_t t) {
  subst_triple_t *s;

  assert(ctx->subst != NULL);
  s = pseudo_subst_find(ctx->subst, t);
  if (s == NULL) {
    return NULL_TERM;
  } else {
    assert(s->var == t);
    return s->map;
  }
}


/*
 * Remove substitution candidate for t
 */
static void remove_subst_candidate(context_t *ctx, term_t t) {
  subst_triple_t *s;

  assert(ctx->subst != NULL);
  s = pseudo_subst_find(ctx->subst, t);
  assert(s != NULL && s->var == t && s->map != NULL_TERM);

#if TRACE_SUBST
  printf("Removing subst candidate ");
  print_term_desc(stdout, ctx->terms, t);
  printf(" := ");;
  print_term_desc(stdout, ctx->terms, s->map);
  printf("\n");
  fflush(stdout);
#endif

  s->map = NULL_TERM;
}


/*
 * Visit t: return true if t is on a cycle.
 */
static bool visit(context_t *ctx, term_t t);

static bool visit_composite(context_t *ctx, composite_term_t *c) {
  uint32_t i, n;

  n = c->arity;
  for (i=0; i<n; i++) {
    if (visit(ctx, c->arg[i])) {
      return true;
    }
  }
  
  return false;
}

static bool visit_pprod(context_t *ctx, pprod_t *p) {
  uint32_t i, n;

  n = p->len;
  for (i=0; i<n; i++) {
    if (visit(ctx, p->prod[i].var)) {
      return true;
    }
  }

  return false;
}

static bool visit_arith_poly(context_t *ctx, polynomial_t *p) {
  monomial_t *m;
  uint32_t i, n;

  m = p->mono;
  n = p->nterms;
  assert(n > 0);
  // skip constant marker
  if (m[0].var == const_idx) {
    m++;
    n--;
  }

  for (i=0; i<n; i++) {
    if (visit(ctx, m[i].var)) {
      return true;
    }
  }

  return false;
}

static bool visit_bv_poly(context_t *ctx, bvpoly_t *p) {
  bvmono_t *m;
  uint32_t i, n;

  m = p->mono;
  n = p->nterms;
  assert(n > 0);
  // skip constant marker
  if (m[0].var == const_idx) {
    m++;
    n--;
  }

  for (i=0; i<n; i++) {
    if (visit(ctx, m[i].var)) {
      return true;
    }
  }

  return false;
}


static bool visit_bv64_poly(context_t *ctx, bvpoly64_t *p) {
  bvmono64_t *m;
  uint32_t i, n;

  m = p->mono;
  n = p->nterms;
  assert(n > 0);
  // skip constant marker
  if (m[0].var == const_idx) {
    m++;
    n--;
  }

  for (i=0; i<n; i++) {
    if (visit(ctx, m[i].var)) {
      return true;
    }
  }

  return false;
}


static bool visit(context_t *ctx, term_t t) {
  term_table_t *terms;
  term_t r;
  int32_t i;
  bool result;
  uint8_t color;

  assert(ctx->marks != NULL);
  i = index_of(t);
  color = mark_vector_get_mark(ctx->marks, i);

  if (color == WHITE) {
    /*
     * i not visited yet
     */
    terms = ctx->terms;
    mark_vector_add_mark(ctx->marks, i, GREY);

    switch (kind_for_idx(terms, i)) {
    case CONSTANT_TERM:
    case ARITH_CONSTANT:
    case BV64_CONSTANT:
    case BV_CONSTANT:
    case VARIABLE:
      result = false;
      break;

    case UNINTERPRETED_TERM:
      r = intern_tbl_get_root(&ctx->intern, t);
      if (r != t) {
        result = visit(ctx, r);
      } else {
        r = subst_candidate(ctx, pos_term(i));
        if (r != NULL_TERM && visit(ctx, r)) {
          /*
           * There's a cycle u --> ... --> t := r --> ... --> u
           * remove the substitution t := r to break the cycle
           */
          remove_subst_candidate(ctx, pos_term(i));
        }
        result = false;
      }
      break;

    case ARITH_EQ_ATOM:
    case ARITH_GE_ATOM:
      result = visit(ctx, integer_value_for_idx(terms, i));
      break;

    case ITE_TERM:
    case ITE_SPECIAL:
    case APP_TERM:
    case UPDATE_TERM:
    case TUPLE_TERM:
    case EQ_TERM:
    case DISTINCT_TERM:
    case FORALL_TERM:
    case LAMBDA_TERM:
    case OR_TERM:
    case XOR_TERM:
    case ARITH_BINEQ_ATOM:
    case BV_ARRAY:
    case BV_DIV:
    case BV_REM:
    case BV_SDIV:
    case BV_SREM:
    case BV_SMOD:
    case BV_SHL:
    case BV_LSHR:
    case BV_ASHR:
    case BV_EQ_ATOM:
    case BV_GE_ATOM:
    case BV_SGE_ATOM:
      result = visit_composite(ctx, composite_for_idx(terms, i));
      break;

    case SELECT_TERM:
    case BIT_TERM:
      result = visit(ctx, select_for_idx(terms, i)->arg);
      break;

    case POWER_PRODUCT:
      result = visit_pprod(ctx, pprod_for_idx(terms, i));
      break;

    case ARITH_POLY:
      result = visit_arith_poly(ctx, polynomial_for_idx(terms, i));
      break;

    case BV64_POLY:
      result = visit_bv64_poly(ctx, bvpoly64_for_idx(terms, i));
      break;

    case BV_POLY:
      result = visit_bv_poly(ctx, bvpoly_for_idx(terms, i));
      break;

    case UNUSED_TERM:
    case RESERVED_TERM:
    default:
      assert(false);
      longjmp(ctx->env, INTERNAL_ERROR);
      break;
    }

    if (result) {
      /*
       * t is on a cycle of grey terms:
       *  v --> .. x := u --> ... --> t --> ... --> v
       * all terms on the cycle must be cleared except v
       */
      mark_vector_add_mark(ctx->marks, i, WHITE);
    } else {
      // no cycle containing t: mark i black
      mark_vector_add_mark(ctx->marks, i, BLACK);
    }

  } else {
    /*
     * i already visited before
     * - if it's black there's no cycle
     * - if it's grey, we've just detected a cycle
     */
    assert(color == GREY || color == BLACK);
    result = (color == GREY);
  }

  return result;
}


/*
 * Iterator for remove cycle:
 * - s is a triple [x, t, e] for a candidate substitution x := t
 */
static void visit_subst_candidate(context_t *ctx, subst_triple_t *s) {
  term_t x;

  x = s->var;
  assert(intern_tbl_is_root(&ctx->intern, x) && intern_tbl_root_is_free(&ctx->intern, x));
  if (mark_vector_get_mark(ctx->marks, index_of(x)) == WHITE) {
    (void) visit(ctx, x);
  }
}


/*
 * Remove cycles in the candidate substitutions
 */
static void remove_subst_cycles(context_t *ctx) {
  pseudo_subst_iterate(ctx->subst, ctx, (pseudo_subst_iterator_t) visit_subst_candidate);
}


/*
 * Iterator for finalize subst:
 * - s is a triple [x, t, e] 
 * - if t is NULL_TERM, that's no longer a good substitution: add e to top_eqs
 * - otherwise add x := t as a substitution in the internalization table
 */
static void finalize_subst_triple(context_t *ctx, subst_triple_t *s) {
  assert(s->eq != NULL_TERM && term_is_true(ctx, s->eq));

  if (s->map != NULL_TERM) {
    intern_tbl_add_subst(&ctx->intern, s->var, s->map);
  } else {
    ivector_push(&ctx->top_eqs, s->eq);
  }
}


/*
 * Finalize all candidate substitutions
 */
static void finalize_subst_candidates(context_t *ctx) {
  pseudo_subst_iterate(ctx->subst, ctx, (pseudo_subst_iterator_t) finalize_subst_triple);  
}







/***************************
 *  ASSERTION FLATTENING   *
 **************************/

/*
 * Assertions are processed by performing top-down boolean propagation
 * and collecting all subterms that can't be flattened into four vectors:
 *
 * 1) ctx->top_eqs = top-level equalities.
 *    Every t in top_eqs is (eq t1 t2) (or a variant) asserted true.
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
 * Flattening is done breadth-first:
 * - the subterms to process are stored into ctx->queue.
 * - each subterm in that queue is a boolean term that's asserted true
 */


/*
 * Each function below processes an assertion of the form (r == tt)
 * where r is a boolean term (with positive polarity) and tt is either
 * true or false. The term r is a root in the internalization table
 * and r is not internalized yet.
 *
 * Processing:
 * - try to simplify (r == tt) to a boolean term q. If that works
 *   add q to the internal queue.
 * - check for boolean propagation from (r == tt) to r's children.
 *   Example: (or t_1 ... t_n) == false ---> (t_1 == false), etc.
 * - if (r == tt) can be rewritten to an equality (t1 == t2), check
 *   whether we can eliminate t1 or t2 by substitution.
 * - otherwise, add r or (not r) to one of top_eqs, top_atoms, or top_formulas.
 */

/*
 * Atoms, except equalities
 */
// r is (p t_1 ... t_n)
static void flatten_bool_app(context_t *ctx, term_t r, bool tt) {
  ivector_push(&ctx->top_atoms, signed_term(r, tt));
}

// r is (distinct t1 .... t_n)
static void flatten_distinct(context_t *ctx, term_t r, bool tt) {
  if (tt) {
    ivector_push(&ctx->top_atoms, r);
  } else {
    // not (distinct ...) expands to an or 
    ivector_push(&ctx->top_formulas, not(r));
  }
}

// r is (select i t) for a tuple t
static void flatten_select(context_t *ctx, term_t r, bool tt) {
  term_t t;

  t = simplify_select(ctx, r);
  if (t != NULL_TERM) {
    int_queue_push(&ctx->queue, signed_term(t, tt));
  } else {
    ivector_push(&ctx->top_atoms, signed_term(r, tt));    
  }
}

// r is (bit i t) for a bitvector term t
static void flatten_bit_select(context_t *ctx, term_t r, bool tt) {
  term_t t;

  t = simplify_bit_select(ctx, r);
  if (t != NULL_TERM) {
    int_queue_push(&ctx->queue, signed_term(t, tt));
  } else {
    ivector_push(&ctx->top_atoms, signed_term(r, tt));
  }
}

// r is (t >= 0) for an arithmetic term t
static void flatten_arith_geq0(context_t *ctx, term_t r, bool tt) {
  term_t t;

  t = simplify_arith_geq0(ctx, r);
  if (t != NULL_TERM) {
    int_queue_push(&ctx->queue, signed_term(t, tt));
  } else {
    ivector_push(&ctx->top_atoms, signed_term(r, tt));
  }
}

// r is (bvge t1 t2) for two bitvector terms t1 and t2
static void flatten_bvge(context_t *ctx, term_t r, bool tt) {
  ivector_push(&ctx->top_atoms, signed_term(r, tt));
}

// r is (bvsge t1 t2) for two bitvector terms t1 and t2
static void flatten_bvsge(context_t *ctx, term_t r, bool tt) {
  ivector_push(&ctx->top_atoms, signed_term(r, tt));
}


/*
 * Equalities
 */
// r is (t == 0) for an arithmetic term t
static void flatten_arith_eq0(context_t *ctx, term_t r, bool tt) {
  term_t t;

  t = simplify_arith_eq0(ctx, r);
  if (t != NULL_TERM) {
    int_queue_push(&ctx->queue, signed_term(t, tt));
  } else if (tt) {
    ivector_push(&ctx->top_eqs, r);
  } else {
    ivector_push(&ctx->top_atoms, opposite_term(r));
  }
}

// r is (t1 == t2) for two arithmetic terms t1 and t2
static void flatten_arith_eq(context_t *ctx, term_t r, bool tt) {
  composite_term_t *eq;
  term_t t1, t2, t;

  eq = arith_bineq_atom_desc(ctx->terms, r);
  t1 = intern_tbl_get_root(&ctx->intern, eq->arg[0]);
  t2 = intern_tbl_get_root(&ctx->intern, eq->arg[1]);

  if (t1 == t2) {
    if (!tt) {
      longjmp(ctx->env, TRIVIALLY_UNSAT);
    }
    return; // redundant
  }

  t = simplify_arith_bineq(ctx, t1, t2);
  if (t != NULL_TERM) {
    int_queue_push(&ctx->queue, signed_term(t, tt));
  } else if (tt) {
    try_substitution(ctx, t1, t2, r);
  } else {
    ivector_push(&ctx->top_atoms, opposite_term(r));
  }
}

// r is (eq t1 t2): t1 and t2 are either boolean or tuples or uninterpreted
static void flatten_eq(context_t *ctx, term_t r, bool tt) {
  term_table_t *terms;
  composite_term_t *eq;
  term_t t1, t2, t;

  terms = ctx->terms;
  eq = eq_term_desc(terms, r);
  t1 = intern_tbl_get_root(&ctx->intern, eq->arg[0]);
  t2 = intern_tbl_get_root(&ctx->intern, eq->arg[1]);

  if (is_boolean_term(terms, t1)) {
    /*
     * Boolean equality
     */
    assert(is_boolean_term(terms, t2));

    t = simplify_bool_eq(ctx, t1, t2);
    if (t != NULL_TERM) {
      int_queue_push(&ctx->queue, signed_term(t, tt));
    } else {
      // not (eq t1 t2) --> (eq t1 (not t2))
      if (! tt) {
        r = opposite_term(r);
        t2 = opposite_term(t2);
      }

      if (index_of(t1) == index_of(t2)) {
        // either (eq t1 t1) or (eq t1 (not t1))
        if (t1 == t2) return;
        assert(opposite_bool_terms(t1, t2));
        longjmp(ctx->env, TRIVIALLY_UNSAT);
      }

      try_bool_substitution(ctx, t1, t2, r);
    }

  } else {
    /*
     * Non-boolean
     */
    if (t1 == t2) {
      if (! tt) {
        longjmp(ctx->env, TRIVIALLY_UNSAT);
      }
      return;
    }

    if (tt) {
      try_substitution(ctx, t1, t2, r);
    } else {
      ivector_push(&ctx->top_atoms, opposite_term(r));
    }
  }
}

// r is (bveq t1 t2) for two bitvector terms t1 and t2
static void flatten_bveq(context_t *ctx, term_t r, bool tt) {
  term_table_t *terms;
  composite_term_t *eq;
  ivector_t *v;
  term_t t1, t2, t;

  terms = ctx->terms;
  eq = bveq_atom_desc(terms, r);
  t1 = intern_tbl_get_root(&ctx->intern, eq->arg[0]);
  t2 = intern_tbl_get_root(&ctx->intern, eq->arg[1]);

  /*
   * First check whether (eq t1 t2) is equivalent to
   * a Boolean term t
   */
  t = simplify_bitvector_eq(ctx, t1, t2);
  if (t != NULL_TERM) {
    t = signed_term(t, tt);
    if (t == false_term) {
      longjmp(ctx->env, TRIVIALLY_UNSAT);
    } else if (t != true_term) {
      int_queue_push(&ctx->queue, t);
    } 

  } else if (tt) {
    /*
     * try to flatten into a conjunction of terms
     */
    v = &ctx->aux_vector;
    assert(v->size == 0);
    if (bveq_flattens(ctx->terms, t1, t2, v)) {
      /*
       * (bveq t1 t2) is equivalent to (and v[0] ... v[k-1])
       * (bveq t1 t2) is asserted true
       */
      int_queue_push_array(&ctx->queue, v->data, v->size);
    } else {
      /*
       * Did not flatten
       */
      try_substitution(ctx, t1, t2, r);
    }

    ivector_reset(v);

  } else {
    ivector_push(&ctx->top_atoms, opposite_term(r));
  }
}


/*
 * Non-atomic terms
 */
// r is (or t1 .... t_n)
static void flatten_or(context_t *ctx, term_t r, bool tt) {
  composite_term_t *d;
  uint32_t i, n;

  if (tt) {
    ivector_push(&ctx->top_formulas, r);
  } else {
    d = or_term_desc(ctx->terms, r);
    n = d->arity;
    for (i=0; i<n; i++) {
      int_queue_push(&ctx->queue, opposite_term(d->arg[i]));
    }
  }
}

// r is (xor t1 ... t_n)
static void flatten_xor(context_t *ctx, term_t r, bool tt) {
  ivector_push(&ctx->top_formulas, signed_term(r, tt));
}

// r is (ite c t1 t2) where t1 and t2 are boolean terms
static void flatten_bool_ite(context_t *ctx, term_t r, bool tt) {
  term_table_t *terms;
  composite_term_t *d;
  term_t c, t1, t2, t;

  terms = ctx->terms;
  d = ite_term_desc(terms, r);
  c = intern_tbl_get_root(&ctx->intern, d->arg[0]);
  t1 = intern_tbl_get_root(&ctx->intern, d->arg[1]);
  t2 = intern_tbl_get_root(&ctx->intern, d->arg[2]);

  t = simplify_ite(ctx, c, t1, t2);
  if (t != NULL_TERM) {
    int_queue_push(&ctx->queue, signed_term(t, tt));
  } else {

    if (tt) {
      if (c == t2 || term_is_false(ctx, t2)) {
        // assert (ite c a false) --> assert c and a
        // assert (ite c a c)     --> assert c and a
        int_queue_push(&ctx->queue, c);
        int_queue_push(&ctx->queue, t1);
        return;
      }

      if (opposite_bool_terms(c, t1) || term_is_false(ctx, t1)) {
        // assert (ite c false b)   --> assert (not c) and b
        // assert (ite c (not c) b) --> assert (not c) and b
        int_queue_push(&ctx->queue, opposite_term(c));
        int_queue_push(&ctx->queue, t2);
        return;
      }

    } else {
      if (opposite_bool_terms(c, t2) || term_is_true(ctx, t2)) {
        // assert not (ite c a true)    --> assert c and (not a)
        // assert not (ite c a (not c)) --> assert c and (not a)
        int_queue_push(&ctx->queue, c);
        int_queue_push(&ctx->queue, opposite_term(t1));
        return;
      }

      if (c == t1 || term_is_true(ctx, t1)) {
        // assert not (ite c true b) --> assert (not c) and (not b)
        // assert not (ite c c b)    --> assert (not c) and (not b)
        int_queue_push(&ctx->queue, opposite_term(c));
        int_queue_push(&ctx->queue, opposite_term(t2));
        return;
      }
    }

    // no flattening found
    ivector_push(&ctx->top_formulas, signed_term(r, tt));
  }
}


/*
 * Simplify and flatten assertion f.
 * 
 * Raise an exception via longjmp if there's an error or if a
 * contradiction is detected.
 */
void flatten_assertion(context_t *ctx, term_t f) {
  intern_tbl_t *intern;
  int_queue_t *queue;
  term_table_t *terms;
  term_t t, r;
  int32_t x;
  bool tt;
  int32_t exception;

  queue = &ctx->queue;
  intern = &ctx->intern;
  terms = ctx->terms;

  assert(int_queue_is_empty(queue));
  int_queue_push(queue, f);

  do {
    t = int_queue_pop(queue);           // assert t

    /*
     * Convert (assert t) to (assert r == tt)
     * where r is positive (equal to t or not t)
     * and polarity is either true or false
     */
    r = intern_tbl_get_root(intern, t); // r == t by substitution
    tt = is_pos_term(r);
    r = unsigned_term(r);

    assert(is_pos_term(r) && intern_tbl_is_root(intern, r));

    if (intern_tbl_root_is_mapped(intern, r)) {
      /*
       * r already mapped to something
       * check for trivial unsat 
       * then add r or (not r) to top_intern
       */
      x = intern_tbl_map_of_root(intern, r);
      if (x == bool2code(! tt)) {
        exception = TRIVIALLY_UNSAT;
        goto abort;
      }

      if (x != bool2code(tt)) {
        ivector_push(&ctx->top_interns, signed_term(r, tt));
      }

    } else {
      /*
       * r not seen before: record r = tt then explore r
       */
      switch (term_kind(terms, r)) {
      case UNUSED_TERM:
      case RESERVED_TERM:
      case CONSTANT_TERM:
        /*
         * NOTE: the constant boolean terms are true and false, which
         * should always be internalized to true_literal or false_literal.
         * That's why we don't have a separate 'CONSTANT_TERM' case.
         */
        exception = INTERNAL_ERROR;
        goto abort;
        
      case ARITH_CONSTANT:
      case BV64_CONSTANT:
      case BV_CONSTANT:
      case UPDATE_TERM:
      case TUPLE_TERM:
      case LAMBDA_TERM:
      case BV_ARRAY:
      case BV_DIV:
      case BV_REM:
      case BV_SDIV:
      case BV_SREM:
      case BV_SMOD:
      case BV_SHL:
      case BV_LSHR:
      case BV_ASHR:
      case POWER_PRODUCT:
      case ARITH_POLY:
      case BV64_POLY:
      case BV_POLY:
        exception = TYPE_ERROR;
        goto abort;

      case VARIABLE:
        exception = FREE_VARIABLE_IN_FORMULA;
        goto abort;

      case UNINTERPRETED_TERM:
        assert(intern_tbl_root_is_free(intern, r));
        if (context_var_elim_enabled(ctx)) {
          intern_tbl_add_subst(intern, r, bool2term(tt));
        } else {
          intern_tbl_map_root(intern, r, bool2code(tt));
        }
        break;

      case ARITH_EQ_ATOM:
        intern_tbl_map_root(intern, r, bool2code(tt));
        flatten_arith_eq0(ctx, r, tt);
        break;

      case ARITH_GE_ATOM:
        intern_tbl_map_root(intern, r, bool2code(tt));
        flatten_arith_geq0(ctx, r, tt);
        break;

      case ITE_TERM:
      case ITE_SPECIAL:
        intern_tbl_map_root(intern, r, bool2code(tt));
        flatten_bool_ite(ctx, r, tt);
        break;

      case APP_TERM:
        intern_tbl_map_root(intern, r, bool2code(tt));
        flatten_bool_app(ctx, r, tt);
        break;

      case EQ_TERM:
        intern_tbl_map_root(intern, r, bool2code(tt));
        flatten_eq(ctx, r, tt);
        break;

      case DISTINCT_TERM:
        intern_tbl_map_root(intern, r, bool2code(tt));
        flatten_distinct(ctx, r, tt);
        break;

      case FORALL_TERM:
        intern_tbl_map_root(intern, r, bool2code(tt));
        ivector_push(&ctx->top_atoms, signed_term(r, tt));
        break;

      case OR_TERM:
        intern_tbl_map_root(intern, r, bool2code(tt));
        flatten_or(ctx, r, tt);
        break;

      case XOR_TERM:
        intern_tbl_map_root(intern, r, bool2code(tt));
        flatten_xor(ctx, r, tt);
        break;

      case ARITH_BINEQ_ATOM:
        intern_tbl_map_root(intern, r, bool2code(tt));
        flatten_arith_eq(ctx, r, tt);
        break;

      case BV_EQ_ATOM:
        intern_tbl_map_root(intern, r, bool2code(tt));
        flatten_bveq(ctx, r, tt);
        break;

      case BV_GE_ATOM:
        intern_tbl_map_root(intern, r, bool2code(tt));
        flatten_bvge(ctx, r, tt);
        break;

      case BV_SGE_ATOM:
        intern_tbl_map_root(intern, r, bool2code(tt));
        flatten_bvsge(ctx, r, tt);
        break;

      case SELECT_TERM:
        intern_tbl_map_root(intern, r, bool2code(tt));
        flatten_select(ctx, r, tt);
        break;

      case BIT_TERM:
        intern_tbl_map_root(intern, r, bool2code(tt));
        flatten_bit_select(ctx, r, tt);
        break;
      }
    }
    
  } while (! int_queue_is_empty(queue));

  return;

 abort:
  assert(exception != 0);
  longjmp(ctx->env, exception);
}




/*
 * Process all candidate substitutions after flattening
 * - the candidate substitutions are in ctx->subst_eqs
 * - each element in ctx->subst_eqs is a boolean term e 
 *   such that e is true or false (by flattening)
 *         and e is equivalent to an equality (t1 == t2)
 *   where one of t1 and t2 is a variable.
 */
void context_process_candidate_subst(context_t *ctx) {
  pseudo_subst_t *subst;
  mark_vector_t *marks;

  subst = context_get_subst(ctx);
  marks = context_get_marks(ctx);
  process_subst_eqs(ctx, subst);
  remove_subst_cycles(ctx);
  finalize_subst_candidates(ctx);

  // cleanup
  ivector_reset(&ctx->subst_eqs);
  reset_pseudo_subst(subst);
  reset_mark_vector(marks);
}




/********************************
 *  FLATTENING OF DISJUNCTIONS  *
 *******************************/

/*
 * This does two things:
 * 1) rewrite nested OR terms to flat OR terms
 * 2) replace arithmetic disequality by disjunctions of strict inequalities
 *    (i.e., rewrite (x != 0) to (or (x < 0) (x > 0))
 */

/*
 * Build the atom (t < 0)
 */
static term_t lt0_atom(context_t *ctx, term_t t) {
  arith_buffer_t *b;

  assert(is_pos_term(t) && is_arithmetic_term(ctx->terms, t));

  b = ctx->arith_buffer;
  assert(b != NULL && arith_buffer_is_zero(b));

  arith_buffer_add_term(b, ctx->terms, t);
  return mk_direct_arith_lt0(ctx->terms, b);
}

/*
 * Build a term equivalent to (t > 0)
 */
static term_t gt0_atom(context_t *ctx, term_t t) {
  arith_buffer_t *b;

  assert(is_pos_term(t) && is_arithmetic_term(ctx->terms, t));

  b = ctx->arith_buffer;
  assert(b != NULL && arith_buffer_is_zero(b));

  arith_buffer_add_term(b, ctx->terms, t);
  return mk_direct_arith_gt0(ctx->terms, b);  
}


/*
 * Flatten term t:
 * - if t is already internalized, keep t and add it to v
 * - if t is (OR t1 ... t_n), recursively flatten t_1 ... t_n
 * - if flattening of disequalities is enabled, and t is (NOT (x == 0)) then
 *   we rewrite (NOT (x == 0)) to (OR (< x 0) (> x 0))
 * - otherwise store t into v
 * All terms already in v must be in the small cache
 */
static void flatten_or_recur(context_t *ctx, ivector_t *v, term_t t) {
  term_table_t *terms;
  composite_term_t *or;
  uint32_t i, n;
  term_kind_t kind;
  term_t x;

  assert(is_boolean_term(ctx->terms, t));

  // apply substitutions
  t = intern_tbl_get_root(&ctx->intern, t);

  if (int_hset_add(ctx->small_cache, t)) {
    /*
     * t not already in v and not visited before
     */
    if (intern_tbl_root_is_mapped(&ctx->intern, t)) {
      // t is already internalized, keep it as is
      ivector_push(v, t); 
    } else {
      terms = ctx->terms;
      kind = term_kind(terms, t);
      if (is_pos_term(t) && kind == OR_TERM) {
        // recursively flatten t
        or = or_term_desc(terms, t);
        n = or->arity;
        for (i=0; i<n; i++) {
          flatten_or_recur(ctx, v, or->arg[i]);
        }
      } else if (is_neg_term(t) && kind == ARITH_EQ_ATOM && 
                 context_flatten_diseq_enabled(ctx)) {
        // t is (not (eq x 0)): rewrite to (or (x < 0) (x > 0))
        x = intern_tbl_get_root(&ctx->intern, arith_eq_arg(terms, t));
        ivector_push(v, lt0_atom(ctx, x));
        ivector_push(v, gt0_atom(ctx, x));

      } else {
        // can't flatten
        ivector_push(v, t);
      }
    }
  }
}


/*
 * Flatten a top-level (or t1 .... tp)
 * - initialize the small_cache, then calls the recursive function
 * - the result is stored in v
 */
void flatten_or_term(context_t *ctx, ivector_t *v, composite_term_t *or) {
  uint32_t i, n;

  assert(v->size == 0);

  (void) context_get_small_cache(ctx); // initialize the cache
  if (context_flatten_diseq_enabled(ctx)) {
    (void) context_get_arith_buffer(ctx);  // allocate the internal buffer
  }

  n = or->arity;
  for (i=0; i<n; i++) {
    flatten_or_recur(ctx, v, or->arg[i]);
  }
  //  context_delete_small_cache(ctx);
  context_reset_small_cache(ctx);
}






/************************
 *  EQUALITY LEARNING   *
 ***********************/

/*
 * Process implied equality (x == y):
 * - x and y should not be boolean, bitvector, or arithmetic terms,
 * - we check whether (eq x y) is true or false
 * - if it's false, the return code is TRIVIALLY_UNSAT
 * - if it's true, we do nothing
 * - otherwise, (eq x y) is added to top_eqs, and assigned to true
 */
static int32_t add_aux_eq(context_t *ctx, term_t x, term_t y) {
  term_table_t *terms;
  term_t eq;
  int32_t code;

  x = intern_tbl_get_root(&ctx->intern, x);
  y = intern_tbl_get_root(&ctx->intern, y);

  if (x != y) {
    /*
     * Build/get term (eq x y)
     */
    terms = ctx->terms;  
    if (x > y) {
      eq = eq_term(terms, y, x);
    } else {
      eq = eq_term(terms, x, y);
    }

    assert(intern_tbl_is_root(&ctx->intern, eq));

#if TRACE_EQ_ABS
    printf("---> learned equality: ");
    print_term_def(stdout, ctx->terms, eq);
    printf("\n");
#endif 

    if (intern_tbl_root_is_mapped(&ctx->intern, eq)) {
      // eq is already internalized
      code = intern_tbl_map_of_root(&ctx->intern, eq);
      if (code == bool2code(false)) {
        return TRIVIALLY_UNSAT;
      } 

      if (code != bool2code(true)) {
        ivector_push(&ctx->top_interns, eq);
      }

    } else {
      // map e to true and add it to top_eqs
      intern_tbl_map_root(&ctx->intern, eq, bool2code(true));
      ivector_push(&ctx->top_eqs, eq);
    }    

  }

  return CTX_NO_ERROR;
}


/*
 * Add implied top_level equalities defined by the partition p
 * - return CTX_NO_ERROR if the equalities could be added
 * - return TRIVIALLY_UNSAT if an equality to add is known to be false
 */
static int32_t add_implied_equalities(context_t *ctx, epartition_t *p) {
  uint32_t i, n;
  term_t *q, x, y;
  int32_t k;
  
  n = p->nclasses;
  q = p->data;
  for (i=0; i<n; i++) {
    x = *q++;
    assert(x >= 0);
    y = *q ++;
    while (y >= 0) {
      k = add_aux_eq(ctx, x, y);
      if (k != CTX_NO_ERROR) return k;
      y = *q ++;
    }
  }
  return CTX_NO_ERROR;
}


/*
 * Attempt to learn global equalities implied 
 * by the formulas stored in ctx->top_formulas.
 * Any such equality is added to ctx->top_eqs
 * - return CTX_NO_ERROR if no contradiction is found
 * - return TRIVIALLY_UNSAT if a contradiction is found
 */
int32_t analyze_uf(context_t *ctx) {
  ivector_t *v;
  uint32_t i, n;
  eq_learner_t eql;
  epartition_t *p;
  int32_t k;

  init_eq_learner(&eql, ctx->terms);
  v = &ctx->top_formulas;
  n = v->size;

  k = CTX_NO_ERROR;
  for (i=0; i<n; i++) {
    p = eq_learner_process(&eql, v->data[i]);
    if (p->nclasses > 0) {
      k = add_implied_equalities(ctx, p);
      if (k != CTX_NO_ERROR) break;
    }
  }

  delete_eq_learner(&eql);
  return k;
}




/*************************************************
 *  ANALYSIS FOR THE DIFFERENCE LOGIC FRAGMENTS  *
 ************************************************/

/*
 * Increment the number of variables if t has not been seen before
 */
static void count_dl_var(context_t *ctx, dl_data_t *stats, term_t t) {
  int32_t idx;

  assert(is_pos_term(t) && intern_tbl_is_root(&ctx->intern, t));

  idx = index_of(t);
  if (int_bvset_add_check(ctx->cache, idx)) {
    stats->num_vars ++;
  }
}


/*
 * Check whether (x - y <= a) or (x - y = a) is a valid IDL or RDL atom
 * If so, update the statistics array stats and return true.
 * Otherwise return false.
 * - x and y are arithmetic terms (x or y or both may be the zero_term).
 * - x and y must be roots in ctx->intern
 * - a is either a rational constant or NULL (if NULL, that's interpreted as zero)
 *
 * TODO: use a hash table? The same atom may be counted twice.
 *
 * NOTE: we could check whether x and y are uninterpreted, but that
 * will be detected in later phases of internalization anyway.
 */
static bool check_dl_atom(context_t *ctx, dl_data_t *stats, term_t x, term_t y, rational_t *a, bool idl) {
  assert(is_arithmetic_term(ctx->terms, x) && is_pos_term(x) && intern_tbl_is_root(&ctx->intern, x));
  assert(is_arithmetic_term(ctx->terms, y) && is_pos_term(y) && intern_tbl_is_root(&ctx->intern, y));

  // check the types first
  if (x != zero_term && is_integer_root(ctx, x) != idl) {
    return false;
  }
  if (y != zero_term && is_integer_root(ctx, y) != idl) {
    return false;
  }
  if (idl && a != NULL && ! q_is_integer(a)) {
    return false;
  }

  // if x == y, we ignore the atom. It will simplify to true or false anyway.
  if (x != y) {
    count_dl_var(ctx, stats, x); // we must count zero_term as a variable
    count_dl_var(ctx, stats, y); // same thing

    /*
     * stats->sum_const is intended to be an upper bound on the
     * longest path in the difference-logic graph.
     * 
     * for idl, we add max( |a|, |-a -1|) to sum_const
     * for rdl, we add |a| to sum_const
     */
    if (a != NULL) {
      if (q_is_neg(a)) {        
        // a < 0  so max(|a|, |-a - 1|) is - a
        q_sub(&stats->sum_const, a);
      } else {
        // a >= 0 so max(|a|, |-a - 1|) is a + 1
        q_add(&stats->sum_const, a);
        if (idl) q_add_one(&stats->sum_const);
      }
    } else if (idl) {
      // a = 0
      q_add_one(&stats->sum_const);
    }
  }
  
  stats->num_atoms ++;

  return true;
}


/*
 * Check whether aux contains a difference logic term, i.e., 
 * a term of the form (a + x - y) or (a + x) or (a - y) or (x - y) or +x or -y or a,
 * where a is a constant and x and y are two arithmetic variables.
 *
 * All terms of aux must be roots in ctx->intern.
 */
static bool check_dl_poly_buffer(context_t *ctx, dl_data_t *stats, poly_buffer_t *aux, bool idl) {
  uint32_t n;
  rational_t *a;
  monomial_t *q;

  n = poly_buffer_nterms(aux);
  if (n > 3) return false;
  if (n == 0) return true;

  a = NULL;
  q = poly_buffer_mono(aux);

  // get a pointer to the constant if any
  if (q[0].var == const_idx) {
    a = &q[0].coeff;
    q ++;
    n --; 
  }

  // deal with the non-constant terms
  if (n == 2 && q_opposite(&q[0].coeff, &q[1].coeff)) {
    if (q_is_one(&q[0].coeff)) {
      // a_0 + x_1 - x_2 >= 0  <--> (x_2 - x_1 <= a_0)
      return check_dl_atom(ctx, stats, q[1].var, q[0].var, a, idl);
    }
      
    if (q_is_one(&q[1].coeff)) {
      // a_0 - x_1 + x_2 >= 0  <--> (x_1 - x_2 <= a_0)
      return check_dl_atom(ctx, stats, q[0].var, q[1].var, a, idl);
    }

  } else if (n == 1) {
    if (q_is_one(&q[0].coeff)) {
      // a_0 + x_1 >= 0  <--> (0 - x_1 <= a_0)
      return check_dl_atom(ctx, stats, zero_term, q[0].var, a, idl);
    }

    if (q_is_minus_one(&q[0].coeff)) {
      // a_0 - x_1 >= 0  <--> (x_1 - 0 <= a_0)
      return check_dl_atom(ctx, stats, q[0].var, zero_term, a, idl);
    }
  }

  return n == 0;
}


/*
 * Apply substitutions then check whether p is a difference logic term
 */
static bool check_diff_logic_poly(context_t *ctx, dl_data_t *stats, polynomial_t *p, bool idl) {
  poly_buffer_t *aux;
  monomial_t *mono;
  term_table_t *terms;
  uint32_t i, n;
  term_t t;

  aux = context_get_poly_buffer(ctx);
  reset_poly_buffer(aux);

  assert(poly_buffer_is_zero(aux));

  n = p->nterms;
  mono = p->mono;

  /*
   * p is of the form a0 + a_1 t_1 + ... + a_n t_n 
   * We replace t_i by its root in S(t_i) in the intern table.
   * The result a0 + a_1 S(t_1) + ... + a_n S(t_n) is stored in buffer aux..
   * Then we check whether aux is a difference logic polynomial.
   */
  assert(n > 0); // because zero polynomial is converted to 0 constant 
  
  // deal with the constant first
  if (mono[0].var == const_idx) {
    poly_buffer_add_const(aux, &mono[0].coeff);
    n --;
    mono ++;
  }

  terms = ctx->terms;
  for (i=0; i<n; i++) {
    t = intern_tbl_get_root(&ctx->intern, mono[i].var);
    poly_buffer_addmul_term(terms, aux, t, &mono[i].coeff);
  }

  normalize_poly_buffer(aux);

  return check_dl_poly_buffer(ctx, stats, aux, idl);
}


/*
 * Check whether (x - y) is a difference logic term
 */
static bool check_diff_logic_eq(context_t *ctx, dl_data_t *stats, term_t x, term_t y, bool idl) {
  term_table_t *terms;
  poly_buffer_t *aux;

  assert(is_arithmetic_term(ctx->terms, x) && is_pos_term(x) &&
         is_arithmetic_term(ctx->terms, y) && is_pos_term(y));

  aux = context_get_poly_buffer(ctx);
  reset_poly_buffer(aux);
  assert(poly_buffer_is_zero(aux));

  // build polynomial (x - y) after applying substitutions
  terms = ctx->terms;
  poly_buffer_add_term(terms, aux, intern_tbl_get_root(&ctx->intern, x));
  poly_buffer_sub_term(terms, aux, intern_tbl_get_root(&ctx->intern, y));    
  normalize_poly_buffer(aux);

  return check_dl_poly_buffer(ctx, stats, aux, idl);
}




/*
 * Check whether term t is a difference logic term and update stats
 * - if idl is true, check whether t is in the IDL fragment
 * - otherwise, check whether t is in the RDL fragment
 *
 * The difference logic fragment contains terms of the following forms:
 *   a + x - y
 *   a + x
 *   a - y
 *   a
 * where x and y are arithmetic variables and a is a constant (possibly a = 0).
 *
 * In IDL, x and y must be integer variables and 'a' must be an integer constant.
 * (TODO: We could relax that and accept rational a?)
 * In RDL, x and y must be real variables.
 */
static bool check_diff_logic_term(context_t *ctx, dl_data_t *stats, term_t t, bool idl) {
  term_table_t *terms;


  assert(is_arithmetic_term(ctx->terms, t));

  terms = ctx->terms;

  // apply substitution
  t = intern_tbl_get_root(&ctx->intern, t);

  assert(is_arithmetic_term(terms, t) && is_pos_term(t) 
         && intern_tbl_is_root(&ctx->intern, t));

  switch (term_kind(terms, t)) {
  case ARITH_CONSTANT:
    return !idl || q_is_integer(rational_term_desc(terms, t));

  case UNINTERPRETED_TERM:
    return check_diff_logic_eq(ctx, stats, t, zero_term, idl);

  case ARITH_POLY:
    return check_diff_logic_poly(ctx, stats, poly_term_desc(terms, t), idl);

  default:
    // TODO: we could accept if-then-else here?
    return false;
  }
}


/*
 * Analyze all arithmetic atoms in term t and fill in stats
 * - if idl is true, this checks for integer difference logic
 *   otherwise, checks for real difference logic
 * - cache must be initialized and contain all the terms already visited
 */
static void analyze_dl(context_t *ctx, dl_data_t *stats, term_t t, bool idl) {
  term_table_t *terms;
  composite_term_t *cmp;
  uint32_t i, n;
  int32_t idx;
  term_t r;

  assert(is_boolean_term(ctx->terms, t));

  idx = index_of(t); // remove negation

  if (int_bvset_add_check(ctx->cache, idx)) {
    /*
     * idx not visited yet
     */
    terms = ctx->terms;
    switch (kind_for_idx(terms, idx)) {
    case CONSTANT_TERM:
      assert(idx == bool_const);
      break;

    case UNINTERPRETED_TERM:
      // follow the substitutions if any
      r = intern_tbl_get_root(&ctx->intern, pos_term(idx));
      if (r != pos_term(idx)) {
        analyze_dl(ctx, stats, r, idl);
      }
      break;
      
    case ITE_TERM:
    case ITE_SPECIAL:
    case OR_TERM:
    case XOR_TERM:
      cmp = composite_for_idx(terms, idx);
      n = cmp->arity;
      for (i=0; i<n; i++) {
        analyze_dl(ctx, stats, cmp->arg[i], idl);
      }
      break;

    case EQ_TERM:
      cmp = composite_for_idx(terms, idx);
      assert(cmp->arity == 2);
      if (is_boolean_term(terms, cmp->arg[0])) {
        // boolean equality
        analyze_dl(ctx, stats, cmp->arg[0], idl);
        analyze_dl(ctx, stats, cmp->arg[1], idl);
      } else {
        goto abort;
      }
      break;

    case ARITH_EQ_ATOM:
      // term (x == 0): check whether x is a difference logic term
      if (! check_diff_logic_term(ctx, stats, integer_value_for_idx(terms, idx), idl)) {
        goto abort;
      }
      stats->num_eqs ++;
      break;

    case ARITH_GE_ATOM:
      // term (x >= 0): check whether x is a difference logic term
      if (! check_diff_logic_term(ctx, stats, integer_value_for_idx(terms, idx), idl)) {
        goto abort;
      }
      break;

    case ARITH_BINEQ_ATOM:
      // term (x == y): check whether x - y is a difference logic term
      cmp = composite_for_idx(terms, idx);
      assert(cmp->arity == 2);
      if (! check_diff_logic_eq(ctx, stats, cmp->arg[0], cmp->arg[1], idl)) {
        goto abort;
      }
      break;

    default:
      goto abort;
    }
  }

  return;

 abort:  
  longjmp(ctx->env, LOGIC_NOT_SUPPORTED);
}
  

/*
 * Check all terms in vector v
 */
static void analyze_diff_logic_vector(context_t *ctx, dl_data_t *stats, ivector_t *v, bool idl) {
  uint32_t i, n;

  n = v->size;
  for (i=0; i<n; i++) {
    analyze_dl(ctx, stats, v->data[i], idl);
  }
}


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
void analyze_diff_logic(context_t *ctx, bool idl) {
  dl_data_t *stats;

  stats = context_get_dl_profile(ctx);
  (void) context_get_cache(ctx); // allocate and initialize the cache

  analyze_diff_logic_vector(ctx, stats, &ctx->top_eqs, idl);
  analyze_diff_logic_vector(ctx, stats, &ctx->top_atoms, idl);
  analyze_diff_logic_vector(ctx, stats, &ctx->top_formulas, idl);


#if (TRACE || TRACE_DL)
  printf("==== Difference logic ====\n");
  if (idl) {
    printf("---> IDL\n");
  } else {
    printf("---> RDL\n");
  }
  printf("---> %"PRIu32" variables\n", stats->num_vars);
  printf("---> %"PRIu32" atoms\n", stats->num_atoms);
  printf("---> %"PRIu32" equalities\n", stats->num_eqs);
  printf("---> sum const = ");
  q_print(stdout, &stats->sum_const);
  printf("\n");
#endif

  context_free_cache(ctx);
}





/****************************************************
 *  SIMPLIFICATIONS FOR SPECIAL IF-THEN-ELSE TERMS  *
 ***************************************************/

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
 * So the simplification worked it the returned term t' is different from t
 * (and then v->size is not 0).
 */
term_t flatten_ite_equality(context_t *ctx, ivector_t *v, term_t t, term_t k) {
  term_table_t *terms;
  composite_term_t *ite;

  terms = ctx->terms;
  assert(is_pos_term(t) && good_term(terms, t));

  while (is_ite_term(terms, t)) {
    // t is (ite c a b)
    ite = ite_term_desc(terms, t);
    assert(ite->arity == 3);

    if (disequal_terms(terms, k, ite->arg[1])) {
      // (t == k) is (not c) and (t == b)
      ivector_push(v, opposite_term(ite->arg[0]));
      t = intern_tbl_get_root(&ctx->intern, ite->arg[2]);

    } else if (disequal_terms(terms, k, ite->arg[2])) {
      // (t == k) is c and (t == a)
      ivector_push(v, ite->arg[0]);
      t = intern_tbl_get_root(&ctx->intern, ite->arg[1]);

    } else {
      // no more flattening possible
      break;
    }
  }

  return t;
}







/***********************
 *  SYMMETRY BREAKING  *
 **********************/

#if TRACE_SYM_BREAKING

static void show_constant_set(yices_pp_t *pp, term_table_t *terms, rng_record_t *r) {
  uint32_t i, n;

  n = r->num_constants;
  pp_open_block(pp, PP_OPEN);
  for (i=0; i<n; i++) {
    pp_term(pp, terms, r->cst[i]);
  }
  pp_close_block(pp, false);  
}

static void pp_constraints(yices_pp_t *pp, sym_breaker_t *breaker, rng_record_t *r) {
  uint32_t i, j, n;

  n = r->num_terms;
  for (i=0; i<n; i++) {
    j = r->idx[i];
    pp_open_block(pp, PP_OPEN);
    pp_string(pp, "Formula ");
    pp_uint32(pp, j);
    pp_close_block(pp, false);
    flush_yices_pp(pp);

    pp_term_full(pp, breaker->terms, breaker->ctx->top_formulas.data[j]);
    flush_yices_pp(pp);

    pp_open_block(pp, PP_OPEN);
    pp_string(pp, "constraint on term ");
    pp_term_full(pp, breaker->terms, r->trm[i]);
    pp_close_block(pp, false);
    flush_yices_pp(pp);
    flush_yices_pp(pp);
  }
}

static void show_range_constraints(sym_breaker_t *breaker) {
  yices_pp_t pp;
  pp_area_t area;
  rng_vector_t *v;
  uint32_t i, n;

  area.width = 150;
  area.height = 30;
  area.offset = 0;
  area.stretch = false;
  area.truncate = true;
  init_default_yices_pp(&pp, stdout, &area);

  v = &breaker->range_constraints;
  n = v->nelems;
  for (i=0; i<n; i++) {
    pp_open_block(&pp, PP_OPEN);
    pp_string(&pp, "Range constraints for set: ");
    show_constant_set(&pp, breaker->terms, v->data + i);
    pp_close_block(&pp, false);
    flush_yices_pp(&pp);
    flush_yices_pp(&pp);
    pp_constraints(&pp, breaker, v->data + i);
  }
}

#endif


/*
 * For testing only: to be completed
 */
void break_uf_symmetries(context_t *ctx) {
  sym_breaker_t breaker;

  init_sym_breaker(&breaker, ctx);
  collect_range_constraints(&breaker);
#if TRACE_SYM_BREAKING
  show_range_constraints(&breaker);
#endif

  delete_sym_breaker(&breaker);
}

