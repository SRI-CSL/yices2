/*
 * Assertion CONTEXT
 */

#include "memalloc.h"
#include "term_utils.h"
#include "yices_extensions.h"
#include "arith_buffer_terms.h"

#include "context.h"
#include "eq_learner.h"
#include "idl_floyd_warshall.h"
#include "rdl_floyd_warshall.h"
#include "simplex.h"
#include "fun_solver.h"


#define TRACE_SUBST  0
#define TRACE_EQ_ABS 0
#define TRACE_DL     0
#define TRACE        0

#if TRACE_SUBST || TRACE_EQ_ABS || TRACE_DL || TRACE

#include <stdio.h>
#include "term_printer.h"

#endif



/***************
 *  UTILITIES  *
 **************/

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
static void context_free_subst(context_t *ctx) {
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
static void context_free_marks(context_t *ctx) {
  if (ctx->marks != NULL) {
    delete_mark_vector(ctx->marks);
    safe_free(ctx->marks);
    ctx->marks = NULL;
  }
}


/*
 * There are two internal caches for visiting formulas/terms.
 * - the 'cache' uses a bitvector implementation and should be 
 *   better for operations that visit many terms.
 * - the 'small_cache' uses a hash table and should be better
 *   for operations that visit a small number of terms.
 */

/*
 * Allocate and initialize the internal small_cache if needed
 */
static int_hset_t *context_get_small_cache(context_t *ctx) {
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
static void context_reset_small_cache(context_t *ctx) {
  int_hset_t *tmp;

  tmp = ctx->small_cache;
  if (tmp != NULL) {
    int_hset_reset(tmp);
  }
}

/*
 * Free the small_cache
 */
static void context_free_small_cache(context_t *ctx) {
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
static int_bvset_t *context_get_cache(context_t *ctx) {
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
static void context_free_cache(context_t *ctx) {
  int_bvset_t *tmp;

  tmp = ctx->cache;
  if (tmp != NULL) {
    delete_int_bvset(tmp);
    safe_free(tmp);
    ctx->cache = NULL;
  }
}



/*
 * There are three buffers for internal construction of polynomials
 * - arith_buffer is more expensive (requires more memory) but 
 *   it supports more operations (e.g., term constructors in yices_api.c
 *   take arith_buffers as arguments).
 * - poly_buffer is a cheaper data structure, but it does not support 
 *   all the operations
 * - aux_poly is even cheaper, but it's for direct construction only 
 */

/*
 * Allocate the arithmetic buffer
 */
static arith_buffer_t *context_get_arith_buffer(context_t *ctx) {
  arith_buffer_t *tmp;

  tmp = ctx->arith_buffer;
  if (tmp == NULL) {
    tmp = yices_new_arith_buffer();
    ctx->arith_buffer = tmp;
  }
  
  return tmp;
}


/*
 * Free the arithmetic buffer
 */
static void context_free_arith_buffer(context_t *ctx) {
  arith_buffer_t *tmp;

  tmp = ctx->arith_buffer;
  if (tmp != NULL) {
    yices_free_arith_buffer(tmp);
    ctx->arith_buffer = NULL;
  }
}



/*
 * Allocate the poly_buffer
 */
static poly_buffer_t *context_get_poly_buffer(context_t *ctx) {
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
static void context_free_poly_buffer(context_t *ctx) {
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
static void context_reset_poly_buffer(context_t *ctx) {
  if (ctx->poly_buffer != NULL) {
    reset_poly_buffer(ctx->poly_buffer);
  }
}


/*
 * Allocate the auxiliary polynomial buffer and make it large enough
 * for n monomials.
 */
static polynomial_t *context_get_aux_poly(context_t *ctx, uint32_t n) {
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
static void context_free_aux_poly(context_t *ctx) {
  polynomial_t *p;
  
  p = ctx->aux_poly;
  if (p != NULL) {
    free_polynomial(p);
    ctx->aux_poly = NULL;
    ctx->aux_poly_size = 0;
  }
}






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
static void context_free_dl_profile(context_t *ctx) {
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
static bool term_is_true(context_t *ctx, term_t t) {
  bool tt;

  assert(intern_tbl_is_root(&ctx->intern, t));
  tt = is_pos_term(t);
  t = unsigned_term(t);
  
  return intern_tbl_root_is_mapped(&ctx->intern, t) && 
    intern_tbl_map_of_root(&ctx->intern, t) == bool2code(tt);
}

static bool term_is_false(context_t *ctx, term_t t) {
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
static term_t simplify_bool_eq(context_t *ctx, term_t t1, term_t t2) {
  if (term_is_true(ctx, t1)) return t2;  // (eq true t2) --> t2
  if (term_is_true(ctx, t2)) return t1;  // (eq t1 true) --> t1
  if (term_is_false(ctx, t1)) return opposite_term(t2); // (eq false t2) --> not t2
  if (term_is_false(ctx, t2)) return opposite_term(t1); // (eq t1 false) --> not t1

  return NULL_TERM;
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



/****************************************************
 *  TYPES AFTER SUBSTITUTIONS/VARIABLE ELIMINATION  *
 ***************************************************/

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
 * Check whethre t is in an integer or real class
 */
static inline bool in_integer_class(context_t *ctx, term_t t) {
  return is_integer_root(ctx, intern_tbl_get_root(&ctx->intern, t));
}

static inline bool in_real_class(context_t *ctx, term_t t) {
  return is_real_type(type_of_root(ctx, intern_tbl_get_root(&ctx->intern, t)));
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

// r is (t1 == t2) for two arithemtic terms t1 and t2
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
  term_t t1, t2, t;

  terms = ctx->terms;
  eq = bveq_atom_desc(terms, r);
  t1 = intern_tbl_get_root(&ctx->intern, eq->arg[0]);
  t2 = intern_tbl_get_root(&ctx->intern, eq->arg[1]);

  if (t1 == t2) {
    if (!tt) {
      longjmp(ctx->env, TRIVIALLY_UNSAT);
    }
    return;
  }

  t = simplify_bveq(terms, t1, t2);
  if (t != NULL_TERM) {
    int_queue_push(&ctx->queue, signed_term(t, tt));
  } else if (tt) {
    try_substitution(ctx, t1, t2, r);
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
static void flatten_assertion(context_t *ctx, term_t f) {
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
 *   such that e is true or false (by flatteing)
 *         and e is equivalent to an equality (t1 == t2)
 *   where one of t1 and t2 is a variable.
 */
static void context_process_candidate_subst(context_t *ctx) {
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
  return arith_buffer_get_lt0_atom(b);
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
  return arith_buffer_get_gt0_atom(b);  
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
static void flatten_or_term(context_t *ctx, ivector_t *v, composite_term_t *or) {
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
static term_t flatten_ite_equality(context_t *ctx, ivector_t *v, term_t t, term_t k) {
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
static int32_t analyze_uf(context_t *ctx) {
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
  if (int_bvset_add(ctx->cache, idx)) {
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
  term_table_t *terms;

  terms = ctx->terms;

  assert(is_arithmetic_term(terms, x) && is_pos_term(x) && intern_tbl_is_root(&ctx->intern, x));
  assert(is_arithmetic_term(terms, y) && is_pos_term(y) && intern_tbl_is_root(&ctx->intern, y));

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
 * Add a * t to a buffer (and variants).
 * - we must deal with the case where t is a constant here.
 */
static void poly_buffer_addmul_term(term_table_t *terms, poly_buffer_t *aux, term_t t, rational_t *a) {
  assert(is_arithmetic_term(terms, t) && is_pos_term(t));

  if (term_kind(terms, t) == ARITH_CONSTANT) {
    poly_buffer_addmul_monomial(aux, const_idx, a, rational_term_desc(terms, t));
  } else {
    poly_buffer_add_monomial(aux, t, a);
  }
}												     

static void poly_buffer_add_term(term_table_t *terms, poly_buffer_t *aux, term_t t) {
  assert(is_arithmetic_term(terms, t) && is_pos_term(t));

  if (term_kind(terms, t) == ARITH_CONSTANT) {
    poly_buffer_add_const(aux, rational_term_desc(terms, t));
  } else {
    poly_buffer_add_var(aux, t);
  }
}

static void poly_buffer_sub_term(term_table_t *terms, poly_buffer_t *aux, term_t t) {
  assert(is_arithmetic_term(terms, t) && is_pos_term(t));

  if (term_kind(terms, t) == ARITH_CONSTANT) {
    poly_buffer_sub_const(aux, rational_term_desc(terms, t));
  } else {
    poly_buffer_sub_var(aux, t);
  }
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

  if (int_bvset_add(ctx->cache, idx)) {
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
static void analyze_diff_logic(context_t *ctx, bool idl) {
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



/**********************
 *  INTERNALIZATION   *
 *********************/

/*
 * Main internalization functions:
 * - convert a term t to an egraph term
 * - convert a boolean term t to a literal
 * - convert an integer or real term t to an arithmetic variable
 * - convert a bitvector term t to a bitvector variable
 */
static occ_t internalize_to_eterm(context_t *ctx, term_t t);
static literal_t internalize_to_literal(context_t *ctx, term_t t);
static thvar_t internalize_to_arith(context_t *ctx, term_t t);
static thvar_t internalize_to_bv(context_t *ctx, term_t t);


/*
 * Place holders for now
 */
static thvar_t internalize_to_bv(context_t *ctx, term_t t) {
  longjmp(ctx->env, BV_NOT_SUPPORTED);
  return null_thvar;
}




/****************************************
 *  CONSTRUCTION OF EGRAPH OCCURRENCES  *
 ***************************************/

/*
 * Create a new egraph constant of the given type
 */
static eterm_t make_egraph_constant(context_t *ctx, type_t type, int32_t id) {
  assert(type_kind(ctx->types, type) == UNINTERPRETED_TYPE || 
	 type_kind(ctx->types, type) == SCALAR_TYPE);
  return egraph_make_constant(ctx->egraph, type, id);
}


/*
 * Create a new egraph variable
 * - type = its type
 */
static eterm_t make_egraph_variable(context_t *ctx, type_t type) {
  eterm_t u;
  bvar_t v;
  
  if (type == bool_type(ctx->types)) {
    v = create_boolean_variable(ctx->core);
    u = egraph_bvar2term(ctx->egraph, v);
  } else {
    u = egraph_make_variable(ctx->egraph, type);    
  }
  return u;
}


/*
 * Add the tuple skolemization axiom for term occurrence 
 * u of type tau, if needed.
 */
static void skolemize_if_tuple(context_t *ctx, occ_t u, type_t tau) {
  type_table_t *types;
  tuple_type_t *d;
  uint32_t i, n;
  occ_t *arg;
  eterm_t tup;

  types = ctx->types;
  if (type_kind(types, tau) == TUPLE_TYPE && !is_maxtype(types, tau)) {
    // instantiate the axiom
    d = tuple_type_desc(types, tau);
    n = d->nelem;
    arg = alloc_istack_array(&ctx->istack, n);
    for (i=0; i<n; i++) {
      arg[i] = pos_occ(make_egraph_variable(ctx, d->elem[i]));
      // recursively skolemize
      skolemize_if_tuple(ctx, arg[i], d->elem[i]);
    }

    tup = egraph_make_tuple(ctx->egraph, n, arg, tau);
    free_istack_array(&ctx->istack, arg);

    egraph_assert_eq_axiom(ctx->egraph, u, pos_occ(tup));
  }
}


/*
 * Build a tuple of same type as t then assert that it's equal to t
 * - t must be a root in the internalization table
 * - u1 must be equal to t's internalization (as stored in intern_table)
 * This is the skolemization of (exist (x1...x_n) t == (tuple x1 ... x_n))
 */
static eterm_t skolem_tuple(context_t *ctx, term_t t, occ_t u1) {
  type_t tau;
  eterm_t u;
  tuple_type_t *d;
  uint32_t i, n;
  occ_t *arg;

  assert(intern_tbl_is_root(&ctx->intern, t) && is_pos_term(t) &&
	 intern_tbl_map_of_root(&ctx->intern, t) == occ2code(u1));

  tau = intern_tbl_type_of_root(&ctx->intern, t);
  d = tuple_type_desc(ctx->types, tau);
  n = d->nelem;
  arg = alloc_istack_array(&ctx->istack, n);
  for (i=0; i<n; i++) {
    arg[i] = pos_occ(make_egraph_variable(ctx, d->elem[i]));
    // recursively skolemize
    skolemize_if_tuple(ctx, arg[i], d->elem[i]);
  }

  u = egraph_make_tuple(ctx->egraph, n, arg, tau);
  free_istack_array(&ctx->istack, arg);

  egraph_assert_eq_axiom(ctx->egraph, u1, pos_occ(u));
  
  return u;
}


/*
 * Convert arithmetic variable x to an egraph term
 * - tau = type of x (int or real)
 */
static occ_t translate_arithvar_to_eterm(context_t *ctx, thvar_t x, type_t tau) {
  eterm_t u;

  u = ctx->arith.eterm_of_var(ctx->arith_solver, x);
  if (u == null_eterm) {
    u = egraph_thvar2term(ctx->egraph, x, tau);
  }

  return pos_occ(u);
}


/*
 * Same thing for a bit-vector variable x
 */
static occ_t translate_bvvar_to_eterm(context_t *ctx, thvar_t x, type_t tau) {
#if 0
  eterm_t u;

  u = ctx->bv.eterm_of_var(ctx->bv_solver, v);
  if (u == null_eterm) {
    u = egraph_thvar2term(ctx->egraph, v, tau);
  }

  return pos_occ(u);
#endif

  longjmp(ctx->env, BV_NOT_SUPPORTED);
  return null_occurrence;
}


/*
 * Convert variable x into an eterm internalization for t
 * - tau = type of t
 * - if x is mapped to an existing eterm u, return pos_occ(u)
 * - otherwise, create an egraph variable u and attach x to u
 *   then record the converse mapping [x --> u] in the relevant
 *   theory solver
 */
static occ_t translate_thvar_to_eterm(context_t *ctx, thvar_t x, type_t tau) {
  if (is_arithmetic_type(tau)) {
    return translate_arithvar_to_eterm(ctx, x, tau);
  } else if (is_bv_type(ctx->types, tau)) {
    return translate_bvvar_to_eterm(ctx, x, tau);
  } else {
    longjmp(ctx->env, INTERNAL_ERROR);
  }
}


/*
 * Convert internalization code x for a term t into an egraph term
 * - t must be a root in the internalization table and must have
 *   positive polarity
 */
static occ_t translate_code_to_eterm(context_t *ctx, term_t t, int32_t x) {
  occ_t u;
  type_t tau;

  assert(is_pos_term(t) && intern_tbl_is_root(&ctx->intern, t) &&
	 intern_tbl_map_of_root(&ctx->intern, t) == x);

  if (code_is_eterm(x)) {
    u = code2occ(x);
  } else {
    // x encodes a theory variable or a literal
    // convert that to an egraph term
    tau = type_of_root(ctx, t);
    switch (type_kind(ctx->types, tau)) {
    case BOOL_TYPE:
      u = egraph_literal2occ(ctx->egraph, code2literal(x));
      break;

    case INT_TYPE:
    case REAL_TYPE:
      u = translate_arithvar_to_eterm(ctx, code2thvar(x), tau);
      break;

    case BITVECTOR_TYPE:
      u = translate_bvvar_to_eterm(ctx, code2thvar(x), tau);
      break;

    default:
      assert(false);
      longjmp(ctx->env, INTERNAL_ERROR);
    }

    // remap t to u
    intern_tbl_remap_root(&ctx->intern, t, occ2code(u));
  }

  return u;
}



/***********************************************
 *  CONVERSION OF COMPOSITES TO EGRAPH TERMS   *
 **********************************************/

/*
 * Map apply term to an eterm
 * - tau = type of that term
 */
static occ_t map_apply_to_eterm(context_t *ctx, composite_term_t *app, type_t tau) {
  eterm_t u;
  occ_t *a;
  uint32_t i, n;

  assert(app->arity > 0);
  n = app->arity;
  a = alloc_istack_array(&ctx->istack, n);
  for (i=0; i<n; i++) {
    a[i] = internalize_to_eterm(ctx, app->arg[i]);
  }

  // a[0] = function
  // a[1 ... n-1] are the arguments
  u = egraph_make_apply(ctx->egraph, a[0], n-1, a+1, tau);
  free_istack_array(&ctx->istack, a);

  skolemize_if_tuple(ctx, pos_occ(u), tau);

  return pos_occ(u);
}


/*
 * Convert (select i t) to an egraph term 
 * - tau must be the type of that term (should not be bool)
 * - if a new eterm u is created, attach a theory variable to it
 */
static occ_t map_select_to_eterm(context_t *ctx, select_term_t *s, type_t tau) {
  occ_t u1;
  eterm_t tuple;
  composite_t *tp;

  u1 = internalize_to_eterm(ctx, s->arg);
  tuple = egraph_get_tuple_in_class(ctx->egraph, term_of_occ(u1));
  if (tuple == null_eterm) {
    tuple = skolem_tuple(ctx, s->arg, u1);
  }

  tp = egraph_term_body(ctx->egraph, tuple);
  assert(composite_body(tp) && tp != NULL && composite_kind(tp) == COMPOSITE_TUPLE);

  return tp->child[s->idx];
}


/*
 * Convert (ite c t1 t2) to an egraph term
 * - tau = type of (ite c t1 t2)
 */
static occ_t map_ite_to_eterm(context_t *ctx, composite_term_t *ite, type_t tau) {
  eterm_t u;
  occ_t u1, u2, u3;
  literal_t c, l1, l2;

  c = internalize_to_literal(ctx, ite->arg[0]);
  if (c == true_literal) {
    return internalize_to_eterm(ctx, ite->arg[1]);
  }
  if (c == false_literal) {
    return internalize_to_eterm(ctx, ite->arg[2]);
  }

  u2 = internalize_to_eterm(ctx, ite->arg[1]);
  u3 = internalize_to_eterm(ctx, ite->arg[2]);

  if (context_keep_ite_enabled(ctx)) {
    // build the if-then-else in the egraph
    u1 = egraph_literal2occ(ctx->egraph, c);
    u = egraph_make_ite(ctx->egraph, u1, u2, u3, tau);
  } else {
    // eliminate the if-then-else
    u = make_egraph_variable(ctx, tau);
    l1 = egraph_make_eq(ctx->egraph, pos_occ(u), u2); 
    l2 = egraph_make_eq(ctx->egraph, pos_occ(u), u3);

    assert_ite(&ctx->gate_manager, c, l1, l2, true);
  }

  return pos_occ(u);
}



/*
 * Convert (update f t_1 ... t_n v) to a term
 * - tau = type of that term
 */
static occ_t map_update_to_eterm(context_t *ctx, composite_term_t *update, type_t tau) {
  eterm_t u;
  occ_t *a;
  uint32_t i, n;

  assert(update->arity > 2);

  n = update->arity; 
  a = alloc_istack_array(&ctx->istack, n);
  for (i=0; i<n; i++) {
    a[i] = internalize_to_eterm(ctx, update->arg[i]);
  }

  // a[0]: function f
  // a[1] ... a[n-2]: t_1 .. t_{n-2}
  // a[n-1]: new value v
  u = egraph_make_update(ctx->egraph, a[0], n-2, a+1, a[n-1], tau);

  free_istack_array(&ctx->istack, a);

  return pos_occ(u);
}



/*
 * Convert (tuple t_1 ... t_n) to a term
 * - tau = type of the tuple
 */
static occ_t map_tuple_to_eterm(context_t *ctx, composite_term_t *tuple, type_t tau) {
  eterm_t u;
  occ_t *a;
  uint32_t i, n;

  n = tuple->arity;
  a = alloc_istack_array(&ctx->istack, n);
  for (i=0; i<n; i++) {
    a[i] = internalize_to_eterm(ctx, tuple->arg[i]);
  }

  u = egraph_make_tuple(ctx->egraph, n, a, tau);
  free_istack_array(&ctx->istack, a);

  return pos_occ(u);
}


/*
 * Convert arithmetic and bitvector constants to eterm
 * - check whether the relevant solver exists first
 * - then map the constant to a solver variable x
 *   and convert x to an egraph occurrence
 */
static occ_t map_arith_constant_to_eterm(context_t *ctx, rational_t *q) {
  thvar_t x;
  type_t tau;

  if (! context_has_arith_solver(ctx)) {
    longjmp(ctx->env, ARITH_NOT_SUPPORTED);
  }

  x = ctx->arith.create_const(ctx->arith_solver, q);
  tau = real_type(ctx->types);
  if (q_is_integer(q)) {
    tau = int_type(ctx->types);
  }

  return translate_arithvar_to_eterm(ctx, x, tau);
}

static occ_t map_bvconst64_to_eterm(context_t *ctx, bvconst64_term_t *c) {
  // TBD
  longjmp(ctx->env, BV_NOT_SUPPORTED);
  return null_occurrence;
}

static occ_t map_bvconst_to_eterm(context_t *ctx, bvconst_term_t *c) {
  // TBD
  longjmp(ctx->env, BV_NOT_SUPPORTED);
  return null_occurrence;
}




/******************************************************
 *  CONVERSION OF COMPOSITES TO ARITHMETIC VARIABLES  *
 *****************************************************/

/*
 * Convert if-then-else to an arithmetic variable
 * - if is_int is true, the if-then-else term is integer
 * - otherwise, it's real
 */
static thvar_t map_ite_to_arith(context_t *ctx, composite_term_t *ite, bool is_int) {
  literal_t c;
  thvar_t v, x;

  assert(ite->arity == 3);

  c = internalize_to_literal(ctx, ite->arg[0]); // condition
  if (c == true_literal) {
    return internalize_to_arith(ctx, ite->arg[1]);
  }
  if (c == false_literal) {
    return internalize_to_arith(ctx, ite->arg[2]);
  }

  /*
   * no simplification: create a fresh variable v and assert (c ==> v = t1)
   * and (not c ==> v = t2)
   */
  v = ctx->arith.create_var(ctx->arith_solver, is_int);

  x = internalize_to_arith(ctx, ite->arg[1]);  
  ctx->arith.assert_cond_vareq_axiom(ctx->arith_solver, c, v, x); // c ==> v = t1

  x = internalize_to_arith(ctx, ite->arg[2]);
  ctx->arith.assert_cond_vareq_axiom(ctx->arith_solver, not(c), v, x); // (not c) ==> v = t2

  return v;
}


/*
 * Convert a power product to an arithmetic variable
 */
static thvar_t map_pprod_to_arith(context_t *ctx, pprod_t *p) {
  uint32_t i, n;
  thvar_t *a;
  thvar_t x;

  n = p->len;
  a = alloc_istack_array(&ctx->istack, n);
  for (i=0; i<n; i++) {
    a[i] = internalize_to_arith(ctx, p->prod[i].var);
  }

  x = ctx->arith.create_pprod(ctx->arith_solver, p, a);
  free_istack_array(&ctx->istack, a);

  return x;
}


/*
 * Convert polynomial p to an arithmetic variable
 */
static thvar_t map_poly_to_arith(context_t *ctx, polynomial_t *p) {
  uint32_t i, n;
  thvar_t *a;
  thvar_t x;

  n = p->nterms;
  a = alloc_istack_array(&ctx->istack, n);

  // skip the constant if any
  i = 0;
  if (p->mono[0].var == const_idx) {
    a[0] = null_thvar;
    i ++;
  }

  // deal with the non-constant monomials
  while (i<n) {
    a[i] = internalize_to_arith(ctx, p->mono[i].var);
    i ++;
  }

  // build the polynomial
  x = ctx->arith.create_poly(ctx->arith_solver, p, a);
  free_istack_array(&ctx->istack, a);

  return x;
}


/******************************************************
 *  CONVERSION OF COMPOSITES TO BIT-VECTOR VARIABLES  *
 *****************************************************/

/*
 * Array of bits b
 */
static thvar_t map_bvarray_to_bv(context_t *ctx, composite_term_t *b) {
  longjmp(ctx->env, BV_NOT_SUPPORTED);
  return null_thvar;
}


/*
 * Unsigned division: quotient (div u v)
 */
static thvar_t map_bvdiv_to_bv(context_t *ctx, composite_term_t *div) {
  assert(div->arity == 2);
  longjmp(ctx->env, BV_NOT_SUPPORTED);
  return null_thvar;
}


/*
 * Unsigned division: remainder (rem u v)
 */
static thvar_t map_bvrem_to_bv(context_t *ctx, composite_term_t *rem) {
  assert(rem->arity == 2);
  longjmp(ctx->env, BV_NOT_SUPPORTED);
  return null_thvar;
}


/*
 * Signed division/rounding toward 0: quotient (sdiv u v)
 */
static thvar_t map_bvsdiv_to_bv(context_t *ctx, composite_term_t *sdiv) {
  assert(sdiv->arity == 2);
  longjmp(ctx->env, BV_NOT_SUPPORTED);
  return null_thvar;
}


/*
 * Signed division/rounding toward 0: remainder (srem u v)
 */
static thvar_t map_bvsrem_to_bv(context_t *ctx, composite_term_t *srem) {
  assert(srem->arity == 2);
  longjmp(ctx->env, BV_NOT_SUPPORTED);
  return null_thvar;
}


/*
 * Signed division/rounding toward -infinity: remainder (smod u v)
 */
static thvar_t map_bvsmod_to_bv(context_t *ctx, composite_term_t *smod) {
  assert(smod->arity == 2);
  longjmp(ctx->env, BV_NOT_SUPPORTED);
  return null_thvar;
}


/*
 * Left shift: (shl u v)
 */
static thvar_t map_bvshl_to_bv(context_t *ctx, composite_term_t *shl) {
  assert(shl->arity == 2);
  longjmp(ctx->env, BV_NOT_SUPPORTED);
  return null_thvar;
}


/*
 * Logical shift right: (lshr u v)
 */
static thvar_t map_bvlshr_to_bv(context_t *ctx, composite_term_t *lshr) {
  assert(lshr->arity == 2);
  longjmp(ctx->env, BV_NOT_SUPPORTED);
  return null_thvar;
}


/*
 * Arithmetic shift right: (ashr u v)
 */
static thvar_t map_bvashr_to_bv(context_t *ctx, composite_term_t *ashr) {
  assert(ashr->arity == 2);
  longjmp(ctx->env, BV_NOT_SUPPORTED);
  return null_thvar;
}


/*
 * Power product
 */
static thvar_t map_pprod_to_bv(context_t *ctx, pprod_t *p) {
  longjmp(ctx->env, BV_NOT_SUPPORTED);
  return null_thvar;  
}


/*
 * Bitvector polynomial, 64bit coefficients
 */
static thvar_t map_bvpoly64_to_bv(context_t *ctx, bvpoly64_t *p) {
  longjmp(ctx->env, BV_NOT_SUPPORTED);
  return null_thvar;
}


/*
 * Bitvector polynomial, coefficients have more than 64bits
 */
static thvar_t map_bvpoly_to_bv(context_t *ctx, bvpoly_t *p) {
  longjmp(ctx->env, BV_NOT_SUPPORTED);
  return null_thvar;
}




/****************************
 *  CONVERSION TO LITERALS  *
 ***************************/

/*
 * Boolean if-then-else
 */
static literal_t map_ite_to_literal(context_t *ctx, composite_term_t *ite) {
  literal_t l1, l2, l3;

  assert(ite->arity == 3);
  l1 = internalize_to_literal(ctx, ite->arg[0]); // condition
  if (l1 == true_literal) {
    return internalize_to_literal(ctx, ite->arg[1]);
  }
  if (l1 == false_literal) {
    return internalize_to_literal(ctx, ite->arg[2]);
  }

  l2 = internalize_to_literal(ctx, ite->arg[1]);
  l3 = internalize_to_literal(ctx, ite->arg[2]);

  return mk_ite_gate(&ctx->gate_manager, l1, l2, l3);
}


/*
 * Generic equality: (eq t1 t2)
 * - t1 and t2 are not arithmetic or bitvector terms
 */
static literal_t map_eq_to_literal(context_t *ctx, composite_term_t *eq) {
  occ_t u, v;
  literal_t l1, l2, l;

  assert(eq->arity == 2);

  if (is_boolean_term(ctx->terms, eq->arg[0])) {
    assert(is_boolean_term(ctx->terms, eq->arg[1]));

    l1 = internalize_to_literal(ctx, eq->arg[0]);
    l2 = internalize_to_literal(ctx, eq->arg[1]);
    l = mk_iff_gate(&ctx->gate_manager, l1, l2);
  } else {
    u = internalize_to_eterm(ctx, eq->arg[0]);
    v = internalize_to_eterm(ctx, eq->arg[1]);
    l = egraph_make_eq(ctx->egraph, u, v);
  }

  return l;
}


/*
 * (or t1 ... t_n)
 */
static literal_t map_or_to_literal(context_t *ctx, composite_term_t *or) {
  int32_t *a;
  ivector_t *v;
  literal_t l;
  uint32_t i, n;

  if (context_flatten_or_enabled(ctx)) {
    // flatten (or ...): store result in v
    v = &ctx->aux_vector;
    assert(v->size == 0);
    flatten_or_term(ctx, v, or);

    // make a copy of v
    n = v->size;
    a = alloc_istack_array(&ctx->istack, n);
    for (i=0; i<n; i++) {
      a[i] = v->data[i];
    }
    ivector_reset(v);

    // internalize a[0 ... n-1]
    for (i=0; i<n; i++) {
      a[i] = internalize_to_literal(ctx, a[i]);
    }

  } else {
    // no flattening
    n = or->arity;
    a = alloc_istack_array(&ctx->istack, n);
    for (i=0; i<n; i++) {
      a[i] = internalize_to_literal(ctx, or->arg[i]);
    }
  }

  l = mk_or_gate(&ctx->gate_manager, n, a);
  free_istack_array(&ctx->istack, a);

  return l;
}


/*
 * (xor t1 ... t_n)
 */
static literal_t map_xor_to_literal(context_t *ctx, composite_term_t *xor) {
  int32_t *a;
  literal_t l;
  uint32_t i, n;

  // TODO: add flattening here?

  n = xor->arity;
  a = alloc_istack_array(&ctx->istack, n);
  for (i=0; i<n; i++) {
    a[i] = internalize_to_literal(ctx, xor->arg[i]);
  }

  l = mk_xor_gate(&ctx->gate_manager, n, a);
  free_istack_array(&ctx->istack, a);

  return l;
}


/*
 * Convert (p t_1 .. t_n) to a literal
 * - create an egraph atom
 */
static literal_t map_apply_to_literal(context_t *ctx, composite_term_t *app) {
  occ_t *a;
  uint32_t i, n;
  literal_t l;

  assert(app->arity > 0);
  n = app->arity;
  a = alloc_istack_array(&ctx->istack, n);
  for (i=0; i<n; i++) {
    a[i] = internalize_to_eterm(ctx, app->arg[i]);
  }

  // a[0] = predicate
  // a[1 ...n-1] = arguments
  l = egraph_make_pred(ctx->egraph, a[0], n-1, a + 1);
  free_istack_array(&ctx->istack, a);

  return l;
}



/*
 * Auxiliary function: translate (distinct a[0 ... n-1]) to a literal,
 * when a[0] ... a[n-1] are arithmetic variables. 
 * 
 * We expand this into a quadratic number of disequalities.
 */
static literal_t make_arith_distinct(context_t *ctx, uint32_t n, thvar_t *a) {
  uint32_t i, j;
  ivector_t *v;
  literal_t l;

  assert(n >= 2);

  v = &ctx->aux_vector;
  assert(v->size == 0);
  for (i=0; i<n-1; i++) {
    for (j=i+1; j<n; j++) {
      l = ctx->arith.create_vareq_atom(ctx->arith_solver, a[i], a[j]);
      ivector_push(v, l);
    }
  }
  l = mk_or_gate(&ctx->gate_manager, v->size, v->data);
  ivector_reset(v);
  return not(l);
}

/*
 * Auxiliary function: translate (distinct a[0 ... n-1]) to a literal,
 * when a[0] ... a[n-1] are bitvector variables. 
 * 
 * We expand this into a quadratic number of disequalities.
 */
static literal_t make_bv_distinct(context_t *ctx, uint32_t n, thvar_t *a) {
#if 0
  uint32_t i, j;
  ivector_t *v;
  literal_t l;

  assert(n >= 2);

  v = &ctx->aux_vector;
  assert(v->size == 0);
  for (i=0; i<n-1; i++) {
    for (j=i+1; j<n; j++) {
      l = ctx->bv.create_eq_atom(ctx->arith_solver, a[i], a[j]);
      ivector_push(v, l);
    }
  }
  l = mk_or_gate(&ctx->gate_manager, v->size, v->data);
  ivector_reset(v);
  return not(l);
#endif

  longjmp(ctx->env, BV_NOT_SUPPORTED);
  return null_literal;
}


/*
 * Convert (distinct t_1 ... t_n) to a literal
 */
static literal_t map_distinct_to_literal(context_t *ctx, composite_term_t *distinct) {
  int32_t *a;
  literal_t l;
  uint32_t i, n;

  n = distinct->arity;
  a = alloc_istack_array(&ctx->istack, n);
  if (context_has_egraph(ctx)) {
    // default: translate to the egraph
    for (i=0; i<n; i++) {
      a[i] = internalize_to_eterm(ctx, distinct->arg[i]);
    }
    l = egraph_make_distinct(ctx->egraph, n, a);

  } else if (is_arithmetic_term(ctx->terms, distinct->arg[0])) {
    // translate to arithmetic variables
    for (i=0; i<n; i++) {
      a[i] = internalize_to_arith(ctx, distinct->arg[i]);
    }
    l = make_arith_distinct(ctx, n, a);

  } else if (is_bitvector_term(ctx->terms, distinct->arg[0])) {
    // translate to bitvector variables
    for (i=0; i<n; i++) {
      a[i] = internalize_to_bv(ctx, distinct->arg[i]);
    }
    l = make_bv_distinct(ctx, n, a);

  } else {
    longjmp(ctx->env, UF_NOT_SUPPORTED);
  }

  free_istack_array(&ctx->istack, a);

  return l;
}



/*
 * Arithmetic atom: (t == 0)
 */
static literal_t map_arith_eq_to_literal(context_t *ctx, term_t t) {
  thvar_t x;

  x = internalize_to_arith(ctx, t);
  return ctx->arith.create_eq_atom(ctx->arith_solver, x);
}


/*
 * Arithmetic atom: (t >= 0)
 */
static literal_t map_arith_geq_to_literal(context_t *ctx, term_t t) {
  thvar_t x;

  x = internalize_to_arith(ctx, t);
  return ctx->arith.create_ge_atom(ctx->arith_solver, x);
}


/*
 * Arithmetic atom: (eq t1 t2)
 */
static literal_t map_arith_bineq_to_literal_aux(context_t *ctx, term_t t1, term_t t2) {
  thvar_t x, y;
  occ_t u, v;
  literal_t l;

  // add the atom to the egraph if possible
  if (context_has_egraph(ctx)) {
    u = internalize_to_eterm(ctx, t1);
    v = internalize_to_eterm(ctx, t2);
    l = egraph_make_eq(ctx->egraph, u, v);
  } else {
    x = internalize_to_arith(ctx, t1);
    y = internalize_to_arith(ctx, t2);
    l = ctx->arith.create_vareq_atom(ctx->arith_solver, x, y);
  }

  return l;  
}

static inline literal_t map_arith_bineq_to_literal(context_t *ctx, composite_term_t *eq) {
#if 1
  ivector_t *v;
  int32_t *a;
  uint32_t i, n;
  term_t t1, u1, t2, u2;
  literal_t l;

  assert(eq->arity == 2);
  t1 = intern_tbl_get_root(&ctx->intern, eq->arg[0]);
  u1 = intern_tbl_get_root(&ctx->intern, eq->arg[1]);

  /*
   * Try to flatten the if-then-else equalities
   */
  v = &ctx->aux_vector;
  assert(v->size == 0);
  t2 = flatten_ite_equality(ctx, v, t1, u1);
  u2 = flatten_ite_equality(ctx, v, u1, t2);

  /*
   * (t1 == u1) is equivalent to (and (t2 == u2) v[0] ... v[n-1])
   * where v[i] = element i of v
   */
  n = v->size;
  if (n == 0) {
    // empty v: return (t2 == u2)
    assert(t1 == t2 && u1 == u2);
    l = map_arith_bineq_to_literal_aux(ctx, t2, u2);

  } else {
    // build (and (t2 == u2) v[0] ... v[n-1])
    // first make a copy of v into a[0 .. n-1]
    a = alloc_istack_array(&ctx->istack, n+1);
    for (i=0; i<n; i++) {
      a[i] = v->data[i];
    }
    ivector_reset(v);

    // build the internalization of a[0 .. n-1]
    for (i=0; i<n; i++) {
      a[i] = internalize_to_literal(ctx, a[i]);
    }
    a[n] = map_arith_bineq_to_literal_aux(ctx, t2, u2);

    // build (and a[0] ... a[n])
    l = mk_and_gate(&ctx->gate_manager, n+1, a);
    free_istack_array(&ctx->istack, a);
  }

  return l;

#else
  assert(eq->arity == 2);
  return map_arith_bineq_to_literal_aux(ctx, eq->arg[0], eq->arg[1]);
#endif
}



/****************************************
 *  INTERNALIZATION TO ETERM: TOPLEVEL  *
 ***************************************/

static occ_t internalize_to_eterm(context_t *ctx, term_t t) {
  term_table_t *terms;
  term_t r;
  uint32_t polarity;
  int32_t code;
  int32_t exception;
  type_t tau;
  occ_t u;
  literal_t l;
  thvar_t x;

  if (! context_has_egraph(ctx)) {
    exception = UF_NOT_SUPPORTED;
    goto abort;
  }

  r = intern_tbl_get_root(&ctx->intern, t);
  polarity = polarity_of(r);
  r  = unsigned_term(r);

  /*
   * r is a positive root in the internalization table
   * polarity is 0 or 1
   * if polarity is 0, then t is equal to r by substitution
   * if polarity is 1, then t is equal to (not r)
   */

  if (intern_tbl_root_is_mapped(&ctx->intern, r)) {
    /*
     * r already internalized
     */
    code = intern_tbl_map_of_root(&ctx->intern, r);
    u = translate_code_to_eterm(ctx, r, code);
  } else {
    /*
     * Compute r's internalization:
     * - if it's a boolean term, convert r to a literal l then
     *   remap l to an egraph term
     * - otherwise, recursively construct an egraph term and map it to r
     */
    terms = ctx->terms;
    tau = type_of_root(ctx, r);
    if (is_boolean_type(tau)) {
      l = internalize_to_literal(ctx, r);
      u = egraph_literal2occ(ctx->egraph, l);
      intern_tbl_remap_root(&ctx->intern, r, u);
    } else {
      /*
       * r is not a boolean term
       */
      assert(polarity == 0);

      switch (term_kind(terms, r)) {
      case CONSTANT_TERM:
	u = pos_occ(make_egraph_constant(ctx, tau, constant_term_index(terms, r)));
	break;

      case ARITH_CONSTANT:
	u = map_arith_constant_to_eterm(ctx, rational_term_desc(terms, r));
	break;

      case BV64_CONSTANT:
	u = map_bvconst64_to_eterm(ctx, bvconst64_term_desc(terms, r));
	break;

      case BV_CONSTANT:
	u = map_bvconst_to_eterm(ctx, bvconst_term_desc(terms, r));
	break;

      case VARIABLE:
	exception = FREE_VARIABLE_IN_FORMULA;
	goto abort;

      case UNINTERPRETED_TERM:
	u = pos_occ(make_egraph_variable(ctx, tau));
	skolemize_if_tuple(ctx, u, tau);
	break;

      case ITE_TERM:
      case ITE_SPECIAL:
	u = map_ite_to_eterm(ctx, ite_term_desc(terms, r), tau);
	break;

      case APP_TERM:
	u = map_apply_to_eterm(ctx, app_term_desc(terms, r), tau);
	break;

      case TUPLE_TERM:
	u = map_tuple_to_eterm(ctx, tuple_term_desc(terms, r), tau);
	break;

      case SELECT_TERM:
	u = map_select_to_eterm(ctx, select_term_desc(terms, r), tau);
	break;

      case UPDATE_TERM:
	u = map_update_to_eterm(ctx, update_term_desc(terms, r), tau);
	break;

      case BV_ARRAY:
	x = map_bvarray_to_bv(ctx, bvarray_term_desc(terms, r));
	u = translate_thvar_to_eterm(ctx, x, tau);
	break;

      case BV_DIV:
	x = map_bvdiv_to_bv(ctx, bvdiv_term_desc(terms, r));
	u = translate_thvar_to_eterm(ctx, x, tau);
	break;

      case BV_REM:
	x = map_bvrem_to_bv(ctx, bvrem_term_desc(terms, r));
	u = translate_thvar_to_eterm(ctx, x, tau);
	break;

      case BV_SDIV:
	x = map_bvsdiv_to_bv(ctx, bvsdiv_term_desc(terms, r));
	u = translate_thvar_to_eterm(ctx, x, tau);
	break;

      case BV_SREM:
	x = map_bvsrem_to_bv(ctx, bvsrem_term_desc(terms, r));
	u = translate_thvar_to_eterm(ctx, x, tau);
	break;

      case BV_SMOD:
	x = map_bvsmod_to_bv(ctx, bvsmod_term_desc(terms, r));
	u = translate_thvar_to_eterm(ctx, x, tau);
	break;

      case BV_SHL:
	x = map_bvshl_to_bv(ctx, bvshl_term_desc(terms, r));
	u = translate_thvar_to_eterm(ctx, x, tau);
	break;

      case BV_LSHR:
	x = map_bvlshr_to_bv(ctx, bvlshr_term_desc(terms, r));
	u = translate_thvar_to_eterm(ctx, x, tau);
	break;

      case BV_ASHR:
	x = map_bvashr_to_bv(ctx, bvashr_term_desc(terms, r));
	u = translate_thvar_to_eterm(ctx, x, tau);
	break;

      case POWER_PRODUCT:
	if (is_arithmetic_type(tau)) {
	  x = map_pprod_to_arith(ctx, pprod_term_desc(terms, r));
	} else {
	  assert(is_bv_type(ctx->types, tau));
	  x = map_pprod_to_bv(ctx, pprod_term_desc(terms, r));
	}
	u = translate_thvar_to_eterm(ctx, x, tau);
	break;

      case ARITH_POLY:
	x = map_poly_to_arith(ctx, poly_term_desc(terms, r));
	u = translate_thvar_to_eterm(ctx, x, tau);
	break;

      case BV64_POLY:
	x = map_bvpoly64_to_bv(ctx, bvpoly64_term_desc(terms, r));
	u = translate_thvar_to_eterm(ctx, x, tau);
	break;

      case BV_POLY:
	x = map_bvpoly_to_bv(ctx, bvpoly_term_desc(terms, r));
	u = translate_thvar_to_eterm(ctx, x, tau);
	break;

      default:
	exception = INTERNAL_ERROR;
	goto abort;
      }

      // store the mapping r --> u
      intern_tbl_map_root(&ctx->intern, r, occ2code(u));
    }
  }

  // fix the polarity
  return u ^ polarity;

 abort:
  longjmp(ctx->env, exception);
}




/****************************************
 *  CONVERSION TO ARITHMETIC VARIABLES  *
 ***************************************/

/*
 * Translate internalization code x to an arithmetic variable
 * - if the code is for an egraph term u, then we return the 
 *   theory variable attached to u in the egraph.
 * - otherwise, x must be the code of an arithmetic variable v,
 *   we return v.
 */
static thvar_t translate_code_to_arith(context_t *ctx, int32_t x) {
  eterm_t u;
  thvar_t v;

  assert(code_is_valid(x));
  
  if (code_is_eterm(x)) {
    u = code2eterm(x);
    assert(ctx->egraph != NULL && egraph_term_is_arith(ctx->egraph, u));
    v = egraph_term_base_thvar(ctx->egraph, u);
  } else {
    v = code2thvar(x);
  }

  assert(v != null_thvar);
  return v;
}


static thvar_t internalize_to_arith(context_t *ctx, term_t t) {
  term_table_t *terms;
  int32_t exception;
  int32_t code;
  term_t r;
  occ_t u;
  thvar_t x;

  assert(is_arithmetic_term(ctx->terms, t));

  if (! context_has_arith_solver(ctx)) {
    exception = ARITH_NOT_SUPPORTED;
    goto abort;
  }

  /*
   * Apply term substitution: t --> r
   */
  r = intern_tbl_get_root(&ctx->intern, t);
  if (intern_tbl_root_is_mapped(&ctx->intern, r)) {
    /*
     * r already internalized
     */
    code = intern_tbl_map_of_root(&ctx->intern, r);
    x = translate_code_to_arith(ctx, code);

  } else {
    /*
     * Compute the internalization
     */
    terms = ctx->terms;

    switch (term_kind(terms, r)) {
    case ARITH_CONSTANT:
      x = ctx->arith.create_const(ctx->arith_solver, rational_term_desc(terms, r));
      intern_tbl_map_root(&ctx->intern, r, thvar2code(x));
      break;

    case UNINTERPRETED_TERM:
      x = ctx->arith.create_var(ctx->arith_solver, is_integer_root(ctx, r));
      intern_tbl_map_root(&ctx->intern, r, thvar2code(x));
      break;

    case ITE_TERM:
    case ITE_SPECIAL:
      x = map_ite_to_arith(ctx, ite_term_desc(terms, r), is_integer_root(ctx, r));
      intern_tbl_map_root(&ctx->intern, r, thvar2code(x));
      break;

    case APP_TERM:
      u = map_apply_to_eterm(ctx, app_term_desc(terms, r), type_of_root(ctx, r));
      assert(egraph_term_is_arith(ctx->egraph, term_of_occ(u)));
      intern_tbl_map_root(&ctx->intern, r, occ2code(u));
      x = egraph_term_base_thvar(ctx->egraph, term_of_occ(u));
      assert(x != null_thvar);
      break;

    case SELECT_TERM:
      u = map_select_to_eterm(ctx, select_term_desc(terms, r), type_of_root(ctx, r));
      assert(egraph_term_is_arith(ctx->egraph, term_of_occ(u)));
      intern_tbl_map_root(&ctx->intern, r, occ2code(u));
      x = egraph_term_base_thvar(ctx->egraph, term_of_occ(u));
      assert(x != null_thvar);
      break;

    case POWER_PRODUCT:
      x = map_pprod_to_arith(ctx, pprod_term_desc(terms, r));
      intern_tbl_map_root(&ctx->intern, r, thvar2code(x));
      break;

    case ARITH_POLY:
      x = map_poly_to_arith(ctx, poly_term_desc(terms, r));
      intern_tbl_map_root(&ctx->intern, r, thvar2code(x));
      break;

    case VARIABLE:
      exception = FREE_VARIABLE_IN_FORMULA;
      goto abort;

    default:
      exception = INTERNAL_ERROR;
      goto abort;
    }

  }

  return x;

 abort:
  longjmp(ctx->env, exception);
}


/****************************
 *  CONVERSION TO LITERALS  *
 ***************************/

/*
 * Translate an internalization code x to a literal
 * - if x is the code of an egraph occurrence u, we return the 
 *   theory variable for u in the egraph
 * - otherwise, x should be the code of a literal l in the core
 */
static literal_t translate_code_to_literal(context_t *ctx, int32_t x) {
  occ_t u;
  literal_t l;

  assert(code_is_valid(x));
  if (code_is_eterm(x)) {
    u = code2occ(x);
    if (term_of_occ(u) == true_eterm) {
      l = mk_lit(const_bvar, polarity_of(u));

      assert((u == true_occ && l == true_literal) || 
	     (u == false_occ && l == false_literal));
    } else {
      assert(ctx->egraph != NULL);
      l = egraph_occ2literal(ctx->egraph, u);
    }
  } else {
    l = code2literal(x);
  }

  return l;
}

static literal_t internalize_to_literal(context_t *ctx, term_t t) {
  term_table_t *terms;
  int32_t code;
  uint32_t polarity;
  term_t r;
  literal_t l;
  occ_t u;

  assert(is_boolean_term(ctx->terms, t));  

  r = intern_tbl_get_root(&ctx->intern, t);
  polarity = polarity_of(r);
  r = unsigned_term(r);

  /*
   * At this point:
   * 1) r is a positive root in the internalization table
   * 2) polarity is 1 or 0
   * 3) if polarity is 0, then t is equal to r by substitution
   *    if polarity is 1, then t is equal to (not r)
   *
   * We get l := internalization of r
   * then return l or (not l) depending on polarity.
   */

  if (intern_tbl_root_is_mapped(&ctx->intern, r)) {
    /*
     * r already internalized
     */
    code = intern_tbl_map_of_root(&ctx->intern, r);
    l = translate_code_to_literal(ctx, code);

  } else {
    /*
     * Recursively compute r's internalization
     */
    terms = ctx->terms;
    switch (term_kind(terms, r)) {
    case CONSTANT_TERM:
      assert(r == true_term);
      l = true_literal;
      break;

    case VARIABLE:
      longjmp(ctx->env, FREE_VARIABLE_IN_FORMULA);
      break;
	      
    case UNINTERPRETED_TERM:
      l = pos_lit(create_boolean_variable(ctx->core));
      break;

    case ITE_TERM:
    case ITE_SPECIAL:
      l = map_ite_to_literal(ctx, ite_term_desc(terms, r));
      break;

    case EQ_TERM:
      l = map_eq_to_literal(ctx, eq_term_desc(terms, r));
      break;

    case OR_TERM:
      l = map_or_to_literal(ctx, or_term_desc(terms, r));
      break;

    case XOR_TERM:
      l = map_xor_to_literal(ctx, xor_term_desc(terms, r));
      break;

    case ARITH_EQ_ATOM:
      l = map_arith_eq_to_literal(ctx, arith_eq_arg(terms, r));
      break;

    case ARITH_GE_ATOM:
      l = map_arith_geq_to_literal(ctx, arith_ge_arg(terms, r));
      break;

    case ARITH_BINEQ_ATOM:
      l = map_arith_bineq_to_literal(ctx, arith_bineq_atom_desc(terms, r));
      break;

    case APP_TERM:
      l = map_apply_to_literal(ctx, app_term_desc(terms, r));
      break;

    case SELECT_TERM:
      u = map_select_to_eterm(ctx, select_term_desc(terms, r), bool_type(ctx->types));
      assert(egraph_term_is_bool(ctx->egraph, term_of_occ(u)));
      intern_tbl_map_root(&ctx->intern, r, occ2code(u));
      l = egraph_occ2literal(ctx->egraph, u);
      // we don't want to map r to l here
      goto done;

    case DISTINCT_TERM:
      l = map_distinct_to_literal(ctx, distinct_term_desc(terms, r));
      break;

    case FORALL_TERM:
      if (context_in_strict_mode(ctx)) {
	longjmp(ctx->env, QUANTIFIERS_NOT_SUPPORTED);
      }
      // sloppy mode: turn forall into a proposition
      l = pos_lit(create_boolean_variable(ctx->core));
      break;

    case BIT_TERM:
    case BV_EQ_ATOM:
    case BV_GE_ATOM:
    case BV_SGE_ATOM:
      if (context_in_strict_mode(ctx)) {
	longjmp(ctx->env, BV_NOT_SUPPORTED);
      }
      // sloppy mode: turn bitvector atoms into propositions
      l = pos_lit(create_boolean_variable(ctx->core));
      break;

    default:
      longjmp(ctx->env, INTERNAL_ERROR);
      break;
    }

    // map r to l in the internalization table
    intern_tbl_map_root(&ctx->intern, r, literal2code(l));
  }

 done:
  return l ^ polarity;
}



/******************************************************
 *  TOP-LEVEL ASSERTIONS: TERMS ALREADY INTERNALIZED  *
 *****************************************************/

/*
 * Assert (x == tt) for an internalization code x
 */
static void assert_internalization_code(context_t *ctx, int32_t x, bool tt) {
  occ_t g;
  literal_t l;
  
  assert(code_is_valid(x));

  if (code_is_eterm(x)) {
    // normalize to assertion (g == true)
    g = code2occ(x);
    if (! tt) g = opposite_occ(g);

    // We must deal with 'true_occ/false_occ' separately
    // since they may be used even if there's no actual egraph.
    if (g == false_occ) {
      longjmp(ctx->env, TRIVIALLY_UNSAT);
    } else if (g != true_occ) {
      assert(ctx->egraph != NULL);
      egraph_assert_axiom(ctx->egraph, g);
    }
  } else {
    l = code2literal(x);
    if (! tt) l = not(l);
    add_unit_clause(ctx->core, l);    
  }
}

/*
 * Assert t == true where t is a term that's already mapped
 * either to a literal or to an egraph occurrence.
 * - t must be a root in the internalization table
 */
static void assert_toplevel_intern(context_t *ctx, term_t t) {
  int32_t code;
  bool tt;

  assert(is_boolean_term(ctx->terms, t) && 
	 intern_tbl_is_root(&ctx->intern, t) &&
	 intern_tbl_root_is_mapped(&ctx->intern, t));

  tt = is_pos_term(t);
  t = unsigned_term(t);
  code = intern_tbl_map_of_root(&ctx->intern, t);

  assert_internalization_code(ctx, code, tt);
}







/********************************
 *   ARITHMETIC SUBSTITUTIONS   *
 *******************************/

/*
 * TODO: improve this in the integer case:
 * - all_int is based on p's type in the term table and does 
 *   not take the context's substitutions into account.
 * - integral_poly_after_div requires all coefficients
 *   to be integer. This could be generalized to polynomials
 *   with integer variables and rational coefficients.
 */

/*
 * Check whether term t can be eliminated by an arithmetic substitution
 * - t's root must be uninterpreted and not internalized yet
 */
static bool is_elimination_candidate(context_t *ctx, term_t t) {
  term_t r;

  r = intern_tbl_get_root(&ctx->intern, t);
  return intern_tbl_root_is_free(&ctx->intern, r);
}


/*
 * Auxiliary function: check whether p/a is an integral polynomial
 * assuming all variables and coefficients of p are integer.
 * - check whether all coefficients are multiple of a
 * - a must be non-zero
 */
static bool integralpoly_after_div(polynomial_t *p, rational_t *a) {
  uint32_t i, n;

  if (q_is_one(a) || q_is_minus_one(a)) {
    return true;
  }

  n = p->nterms;
  for (i=0; i<n; i++) {
    if (! q_divides(a, &p->mono[i].coeff)) return false;
  }
  return true;
}


/*
 * Check whether a top-level assertion (p == 0) can be
 * rewritten (t == q) where t is not internalized yet.
 * - all_int is true if p is an integer polynomial (i.e., 
 *   all coefficients and all terms of p are integer).
 * - p = input polynomial
 * - return t or null_term if no adequate t is found
 */
static term_t try_poly_substitution(context_t *ctx, polynomial_t *p, bool all_int) {
  uint32_t i, n;
  term_t t;

  n = p->nterms;
  for (i=0; i<n; i++) {
    t = p->mono[i].var;
    if (t != const_idx && is_elimination_candidate(ctx, t)) {
      if (in_real_class(ctx, t) || 
	  (all_int && integralpoly_after_div(p, &p->mono[i].coeff))) {
	// t is candidate for elimination
	return t;
      }
    }
  }

  return NULL_TERM;
}


/*
 * Build polynomial - p/a + x in the context's aux_poly buffer
 * where a = coefficient of x in p
 * - x must occur in p
 */
static polynomial_t *build_poly_substitution(context_t *ctx, polynomial_t *p, term_t x) {
  polynomial_t *q;
  monomial_t *mono;
  uint32_t i, n;
  term_t y;
  rational_t *a;

  n = p->nterms;

  // first get coefficient of x in p
  a = NULL; // otherwise GCC complains
  for (i=0; i<n; i++) {
    y = p->mono[i].var;
    if (y == x) {
      a = &p->mono[i].coeff;
    }
  }
  assert(a != NULL && n > 0);

  q = context_get_aux_poly(ctx, n);
  q->nterms = n-1;
  mono = q->mono;

  // compute - p/a (but skip monomial a.x)
  for (i=0; i<n; i++) {
    y = p->mono[i].var;
    if (y != x) {
      mono->var = y;
      q_set_neg(&mono->coeff, &p->mono[i].coeff);
      q_div(&mono->coeff, a);
      mono ++;
    }
  }

  // end marker
  mono->var = max_idx;

  return q;
}



/*
 * Try to eliminate a toplevel equality (p == 0) by variable substitution:
 * - i.e., try to rewrite p == 0 into (x - q) == 0 where x is a free variable
 *   then store the substitution x --> q in the internalization table.
 * - all_int is true if p is an integer polynomial (i.e., all variables and all 
 *   coefficients of p are integer)
 *
 * - return true if the elimination succeeds
 * - return false otherwise
 */
static bool try_arithvar_elim(context_t *ctx, polynomial_t *p, bool all_int) {
  polynomial_t *q;
  uint32_t i, n;
  term_t t, u, r;
  thvar_t x;

  /*
   * First pass: internalize every term of p that's not a variable
   * - we do that first to avoid circular substitutions (occurs-check)
   */
  n = p->nterms;
  for (i=0; i<n; i++) {
    t = p->mono[i].var;
    if (t != const_idx && ! is_elimination_candidate(ctx, t)) {
      (void) internalize_to_arith(ctx, t);
    }
  }

  /*
   * Search for a variable to substitute
   */
  u = try_poly_substitution(ctx, p, all_int);
  if (u == NULL_TERM) {
    return false; // no substitution found
  }


  /*
   * p is of the form a.u + p0, we rewrite (p == 0) to (u == q)
   * where q = -1/a * p0
   */
  q = build_poly_substitution(ctx, p, u); // q is in ctx->aux_poly
  
  // convert q to a theory variable in the arithmetic solver
  x = map_poly_to_arith(ctx, q);
    
  // map u (and its root) to x
  r = intern_tbl_get_root(&ctx->intern, u);
  assert(intern_tbl_root_is_free(&ctx->intern, r) && is_pos_term(r));
  intern_tbl_map_root(&ctx->intern, r, thvar2code(x));

#if TRACE
  printf("---> toplevel equality: ");
  print_polynomial(stdout, p);
  printf(" == 0\n");
  printf("     simplified to ");
  print_term(stdout, ctx->terms, u);
  printf(" := ");
  print_polynomial(stdout, q);
  printf("\n");
#endif

  return true;
}




/*****************************************************
 *  INTERNALIZATION OF TOP-LEVEL ATOMS AND FORMULAS  *
 ****************************************************/

/*
 * Recursive function: assert (t == tt) for a boolean term t
 * - this is used when a toplevel formula simplified to t
 *   For example (ite c t u) --> t if c is true.
 * - t is not necessarily a root in the internalization table
 */ 
static void assert_term(context_t *ctx, term_t t, bool tt);



/*
 * Top-level predicate: (p t_1 .. t_n)
 * - if tt is true: assert (p t_1 ... t_n)
 * - if tt is false: assert (not (p t_1 ... t_n))
 */
static void assert_toplevel_apply(context_t *ctx, composite_term_t *app, bool tt) {
  occ_t *a;
  uint32_t i, n;

  assert(app->arity > 0);

  n = app->arity;
  a = alloc_istack_array(&ctx->istack, n);
  for (i=0; i<n; i++) {
    a[i] = internalize_to_eterm(ctx, app->arg[i]);
  }

  if (tt) {
    egraph_assert_pred_axiom(ctx->egraph, a[0], n-1, a+1);
  } else {
    egraph_assert_notpred_axiom(ctx->egraph, a[0], n-1, a+1);
  }

  free_istack_array(&ctx->istack, a);
}


/*
 * Top-level (select i t)
 * - if tt is true: assert (select i t)
 * - if tt is false: assert (not (select i t))
 */
static void assert_toplevel_select(context_t *ctx, select_term_t *select, bool tt) {
  occ_t u;

  u = map_select_to_eterm(ctx, select, bool_type(ctx->types));
  if (! tt) {
    u = opposite_occ(u);
  }
  egraph_assert_axiom(ctx->egraph, u);
}


/*
 * Top-level equality assertion (eq t1 t2):
 * - if tt is true, assert (t1 == t2)
 *   if tt is false, assert (t1 != t2)
 */
static void assert_toplevel_eq(context_t *ctx, composite_term_t *eq, bool tt) {
  occ_t u1, u2;
  literal_t l1, l2;

  assert(eq->arity == 2);

  if (is_boolean_term(ctx->terms, eq->arg[0])) {
    assert(is_boolean_term(ctx->terms, eq->arg[1]));

    l1 = internalize_to_literal(ctx, eq->arg[0]);
    l2 = internalize_to_literal(ctx, eq->arg[1]);
    assert_iff(&ctx->gate_manager, l1, l2, tt);

  } else {
    u1 = internalize_to_eterm(ctx, eq->arg[0]);
    u2 = internalize_to_eterm(ctx, eq->arg[1]);
    if (tt) {
      egraph_assert_eq_axiom(ctx->egraph, u1, u2);
    } else {
      egraph_assert_diseq_axiom(ctx->egraph, u1, u2);
    }
  }
}


/*
 * Assertion (distinct a[0] .... a[n-1]) == tt
 * when a[0] ... a[n-1] are arithmetic variables.
 */
static void assert_arith_distinct(context_t *ctx, uint32_t n, thvar_t *a, bool tt) {
  literal_t l;

  l = make_arith_distinct(ctx, n, a);
  if (! tt) {
    l = not(l);
  }
  add_unit_clause(ctx->core, l);
}


/*
 * Assertion (distinct a[0] .... a[n-1]) == tt
 * when a[0] ... a[n-1] are bitvector variables.
 */
static void assert_bv_distinct(context_t *ctx, uint32_t n, thvar_t *a, bool tt) {
  literal_t l;

  l = make_bv_distinct(ctx, n, a);
  if (! tt) {
    l = not(l);
  }
  add_unit_clause(ctx->core, l);
}


/*
 * Generic (distinct t1 .. t_n)
 * - if tt: assert (distinct t_1 ... t_n)
 * - otherwise: assert (not (distinct t_1 ... t_n))
 */
static void assert_toplevel_distinct(context_t *ctx, composite_term_t *distinct, bool tt) {
  uint32_t i, n;
  int32_t *a;

  n = distinct->arity;
  assert(n >= 2);

  a = alloc_istack_array(&ctx->istack, n);

  if (context_has_egraph(ctx)) {
    // forward the assertion to the egraph
    for (i=0; i<n; i++) {
      a[i] = internalize_to_eterm(ctx, distinct->arg[i]);
    }

    if (tt) {
      egraph_assert_distinct_axiom(ctx->egraph, n, a);
    } else {
      egraph_assert_notdistinct_axiom(ctx->egraph, n, a);
    }

  } else if (is_arithmetic_term(ctx->terms, distinct->arg[0])) {
    // translate to arithmetic then assert
    for (i=0; i<n; i++) {
      a[i] = internalize_to_arith(ctx, distinct->arg[i]);
    }
    assert_arith_distinct(ctx, n, a, tt);

  } else if (is_bitvector_term(ctx->terms, distinct->arg[0])) {
    // translate to bitvectors then assert
    for (i=0; i<n; i++) {
      a[i] = internalize_to_bv(ctx, distinct->arg[i]);
    }
    assert_bv_distinct(ctx, n, a, tt);

  } else {
    longjmp(ctx->env, UF_NOT_SUPPORTED);
  }

  free_istack_array(&ctx->istack, a);
}


/*
 * Top-level arithmetic equality:
 * - t is an arithmetic term
 * - if tt is true, assert (t == 0)
 * - otherwise, assert (t != 0)
 */
static void assert_toplevel_arith_eq(context_t *ctx, term_t t, bool tt) {
  term_table_t *terms;
  polynomial_t *p;
  bool all_int;
  thvar_t x;

  assert(is_arithmetic_term(ctx->terms, t));
  terms = ctx->terms;
  if (tt && context_arith_elim_enabled(ctx) && term_kind(terms, t) == ARITH_POLY) {
    /*
     * Polynomial equality: a_1 t_1 + ... + a_n t_n = 0
     * attempt to eliminate one of t_1 ... t_n
     */
    p = poly_term_desc(terms, t);
    all_int = is_integer_term(terms, t);
    if (try_arithvar_elim(ctx, p, all_int)) { // elimination worked
      return;
    }
  }

  // default
  x = internalize_to_arith(ctx, t);
  ctx->arith.assert_eq_axiom(ctx->arith_solver, x, tt);
}


/*
 * Top-level arithmetic inequality:
 * - t is an arithmetic term
 * - if tt is true, assert (t >= 0)
 * - if tt is false, assert (t < 0)
 */
static void assert_toplevel_arith_geq(context_t *ctx, term_t t, bool tt) {
  thvar_t x;

  assert(is_arithmetic_term(ctx->terms, t));

  x = internalize_to_arith(ctx, t);
  ctx->arith.assert_ge_axiom(ctx->arith_solver, x, tt);
}


/*
 * Top-level binary equality: (eq t u)
 * - both t and u are arithmetic terms
 * - if tt is true, assert (t == u)
 * - if tt is false, assert (t != u)
 */
static void assert_toplevel_arith_bineq(context_t *ctx, composite_term_t *eq, bool tt) {
#if 1
  ivector_t *v;
  int32_t *a;
  uint32_t i, n;
  term_t t1, u1, t2, u2;
  thvar_t x, y;
  literal_t l;

  assert(eq->arity == 2);
  t1 = intern_tbl_get_root(&ctx->intern, eq->arg[0]);
  u1 = intern_tbl_get_root(&ctx->intern, eq->arg[1]);

  /*
   * eq is equivalent to (t1 == u1)
   * try flattening of if-then-else equality
   */
  v = &ctx->aux_vector;
  assert(v->size == 0);
  t2 = flatten_ite_equality(ctx, v, t1, u1);
  u2 = flatten_ite_equality(ctx, v, u1, t2);

  /*
   * (t1 == u1) is now equivalent to 
   * the conjunction of (t2 == u2) and all the terms in v
   */
  n = v->size;
  if (n == 0) {
    // not simplification found
    assert(t1 == t2 && u1 == u2);
    x = internalize_to_arith(ctx, t2);
    y = internalize_to_arith(ctx, u2);
    ctx->arith.assert_vareq_axiom(ctx->arith_solver, x, y, tt);

  } else {
    // make a copy of v[0 ... n-1]
    // + reserve a[n] for the literal (eq t2 u2)
    a = alloc_istack_array(&ctx->istack, n+1);
    for (i=0; i<n; i++) {
      a[i] = v->data[i];
    }
    ivector_reset(v);

    // l := (eq t2 u2)
    l = map_arith_bineq_to_literal_aux(ctx, t2, u2);

    if (tt) {
      // assert (and l a[0] ... a[n-1])
      if (l == false_literal) {
	longjmp(ctx->env, TRIVIALLY_UNSAT);
      }
      add_unit_clause(ctx->core, l);
      for (i=0; i<n; i++) {
	assert_term(ctx, a[i], true);
      }

    } else {
      // assert (or (not a[0]) ... (not a[n-1]) (not l))
      for (i=0; i<n; i++) {
	a[i] = not(internalize_to_literal(ctx, a[i]));
      }
      a[n] = not(l);
      add_clause(ctx->core, n+1, a);
    }

    free_istack_array(&ctx->istack, a);
  }
#else
  thvar_t x, y;

  assert(eq->arity == 2);

  x = internalize_to_arith(ctx, eq->arg[0]);
  y = internalize_to_arith(ctx, eq->arg[1]);
  ctx->arith.assert_vareq_axiom(ctx->arith_solver, x, y, tt);

#endif
}


/*
 * Top-level boolean if-then-else (ite c t1 t2)
 * - if tt is true: assert (ite c t1 t2)
 * - if tt is false: assert (not (ite c t1 t2))
 */
static void assert_toplevel_ite(context_t *ctx, composite_term_t *ite, bool tt) {
  literal_t l1, l2, l3;

  assert(ite->arity == 3);

  l1 = internalize_to_literal(ctx, ite->arg[0]);
  if (l1 == true_literal) {
    assert_term(ctx, ite->arg[1], tt); 
  } else if (l1 == false_literal) {
    assert_term(ctx, ite->arg[2], tt);
  } else {
    l2 = internalize_to_literal(ctx, ite->arg[1]);
    l3 = internalize_to_literal(ctx, ite->arg[2]);
    assert_ite(&ctx->gate_manager, l1, l2, l3, tt);
  }
}


/*
 * Top-level (or t1 ... t_n)
 * - it tt is true: add a clause
 * - it tt is false: add unit clauses
 */
static void assert_toplevel_or(context_t *ctx, composite_term_t *or, bool tt) {
  ivector_t *v;
  int32_t *a;
  uint32_t i, n;
  literal_t l;

  // TODO: improve this
  if (context_flatten_or_enabled(ctx)) {
    // flatten: the result is in v
    v = &ctx->aux_vector;
    assert(v->size == 0);
    flatten_or_term(ctx, v, or);

    // make a copy of v
    n = v->size;
    a = alloc_istack_array(&ctx->istack, n);
    for (i=0; i<n; i++) {
      a[i] = v->data[i];
    }
    ivector_reset(v);

    // internalize all elements of a
    for (i=0; i<n; i++) {
      a[i] = internalize_to_literal(ctx, a[i]);
    }

    if (tt) {
      // assert (or a[0] ... a[n-1]) 
      add_clause(ctx->core, n, a);
    } else {
      // assert (not a[0]) ... (not a[n-1])
      for (i=0; i<n; i++) {
	add_unit_clause(ctx->core, not(a[i]));
      }
    }

    free_istack_array(&ctx->istack, a);

  } else if (tt) {
    // no flattening, asserted true
    n = or->arity;
    a = alloc_istack_array(&ctx->istack, n);
    for (i=0; i<n; i++) {
      a[i] = internalize_to_literal(ctx, or->arg[i]);
    }

    add_clause(ctx->core, n, a);
    free_istack_array(&ctx->istack, a);

  } else {
    // no flattening, asserted false
    n = or->arity;
    for (i=0; i<n; i++) {
      l = internalize_to_literal(ctx, or->arg[i]);
      add_unit_clause(ctx->core, not(l));
    }
  }
}


/*
 * Top-level (xor t1 ... t_n) == tt
 */
static void assert_toplevel_xor(context_t *ctx, composite_term_t *xor, bool tt) {
  int32_t *a;
  uint32_t i, n;

  n = xor->arity;
  a = alloc_istack_array(&ctx->istack, n);
  for (i=0; i<n; i++) {
    a[i] = internalize_to_literal(ctx, xor->arg[i]);
  }

  assert_xor(&ctx->gate_manager, n, a, tt);
  free_istack_array(&ctx->istack, a);
}
 


/*
 * Top-level formula t:
 * - t is a boolean term (or the negation of a boolean term)
 * - t must be a root in the internalization table and must be mapped to true
 */
static void assert_toplevel_formula(context_t *ctx, term_t t) {
  term_table_t *terms;
  int32_t code;
  bool tt;

  assert(is_boolean_term(ctx->terms, t) && 
	 intern_tbl_is_root(&ctx->intern, t) &&
	 term_is_true(ctx, t));

  tt = is_pos_term(t);
  t = unsigned_term(t);

  /*
   * Now: t is a root and has positive polarity
   * - tt indicates whether we assert t or (not t):
   *   tt true: assert t
   *   tt false: assert (not t)
   */
  terms = ctx->terms;
  switch (term_kind(terms, t)) {
  case CONSTANT_TERM:
  case UNINTERPRETED_TERM:
    // should be eliminated by flattening
    code = INTERNAL_ERROR;
    goto abort;

  case ITE_TERM:
  case ITE_SPECIAL:
    assert_toplevel_ite(ctx, ite_term_desc(terms, t), tt);
    break;

  case OR_TERM:
    assert_toplevel_or(ctx, or_term_desc(terms, t), tt);
    break;

  case XOR_TERM:
    assert_toplevel_xor(ctx, xor_term_desc(terms, t), tt);
    break;

  case EQ_TERM:
    assert_toplevel_eq(ctx, eq_term_desc(terms, t), tt);
    break;

  case ARITH_EQ_ATOM:
    assert_toplevel_arith_eq(ctx, arith_eq_arg(terms, t), tt);
    break;

  case ARITH_GE_ATOM:
    assert_toplevel_arith_geq(ctx, arith_ge_arg(terms, t), tt);
    break;

  case ARITH_BINEQ_ATOM:
    assert_toplevel_arith_bineq(ctx, arith_bineq_atom_desc(terms, t), tt);
    break;

  case APP_TERM:
    assert_toplevel_apply(ctx, app_term_desc(terms, t), tt);
    break;

  case SELECT_TERM:
    assert_toplevel_select(ctx, select_term_desc(terms, t), tt);
    break;

  case DISTINCT_TERM:
    assert_toplevel_distinct(ctx, distinct_term_desc(terms, t), tt);
    break;

  case VARIABLE:
    code = FREE_VARIABLE_IN_FORMULA;
    goto abort;

  case FORALL_TERM:
    if (context_in_strict_mode(ctx)) {
      code = QUANTIFIERS_NOT_SUPPORTED;
      goto abort;
    }
    break;

  case BIT_TERM:
  case BV_EQ_ATOM:
  case BV_GE_ATOM:
  case BV_SGE_ATOM:
    if (context_in_strict_mode(ctx)) {
      code = BV_NOT_SUPPORTED;
      goto abort;
    }
    break;

  default:
    code = INTERNAL_ERROR;
    goto abort;
  }

  return;

 abort:
  longjmp(ctx->env, code);
}



/*
 * Assert (t == tt) for a boolean term t:
 * - if t is not internalized, record the mapping 
 *   (root t) --> tt in the internalization table 
 */
static void assert_term(context_t *ctx, term_t t, bool tt) {
  term_table_t *terms;
  int32_t code;
  
  assert(is_boolean_term(ctx->terms, t));

  /*
   * Apply substitution + fix polarity
   */
  t = intern_tbl_get_root(&ctx->intern, t);
  tt ^= is_neg_term(t);
  t = unsigned_term(t);

  if (intern_tbl_root_is_mapped(&ctx->intern, t)) {
    /*
     * The root is already mapped:
     * Either t is already internalized, or it occurs in
     * one of the vectors top_eqs, top_atoms, top_formulas
     * and it will be internalize/asserted later.
     */
    code = intern_tbl_map_of_root(&ctx->intern, t);
    assert_internalization_code(ctx, code, tt);

  } else {
    // store the mapping t --> tt
    intern_tbl_map_root(&ctx->intern, t, bool2code(tt));

    // internalize and assert
    terms = ctx->terms;
    switch (term_kind(terms, t)) {
    case CONSTANT_TERM:
      // should always be internalized
      code = INTERNAL_ERROR;
      goto abort;

    case UNINTERPRETED_TERM: 
      // nothing to do: t --> true/false in the internalization table
      break;

    case ITE_TERM:
    case ITE_SPECIAL:
      assert_toplevel_ite(ctx, ite_term_desc(terms, t), tt);
      break;

    case OR_TERM:
      assert_toplevel_or(ctx, or_term_desc(terms, t), tt);
      break;

    case XOR_TERM:
      assert_toplevel_xor(ctx, xor_term_desc(terms, t), tt);
      break;

    case EQ_TERM:
      assert_toplevel_eq(ctx, eq_term_desc(terms, t), tt);
      break;

    case ARITH_EQ_ATOM:
      assert_toplevel_arith_eq(ctx, arith_eq_arg(terms, t), tt);
      break;

    case ARITH_GE_ATOM:
      assert_toplevel_arith_geq(ctx, arith_ge_arg(terms, t), tt);
      break;

    case ARITH_BINEQ_ATOM:
      assert_toplevel_arith_bineq(ctx, arith_bineq_atom_desc(terms, t), tt);
      break;

    case APP_TERM:
      assert_toplevel_apply(ctx, app_term_desc(terms, t), tt);
      break;

    case SELECT_TERM:
      assert_toplevel_select(ctx, select_term_desc(terms, t), tt);
      break;

    case DISTINCT_TERM:
      assert_toplevel_distinct(ctx, distinct_term_desc(terms, t), tt);
      break;

    case VARIABLE:
      code = FREE_VARIABLE_IN_FORMULA;
      goto abort;

    case FORALL_TERM:
      if (context_in_strict_mode(ctx)) {
	code = QUANTIFIERS_NOT_SUPPORTED;
	goto abort;
      }
      break;

    case BIT_TERM:
    case BV_EQ_ATOM:
    case BV_GE_ATOM:
    case BV_SGE_ATOM:
      if (context_in_strict_mode(ctx)) {
	code = BV_NOT_SUPPORTED;
	goto abort;
      }
      break;

    default:
      code = INTERNAL_ERROR;
      goto abort;
    }
  }

  return;

 abort:
  longjmp(ctx->env, code);
} 




/************************
 *  PARAMETERS/OPTIONS  *
 ***********************/

/*
 * Map architecture id to theories word
 */
static const uint32_t const arch2theories[NUM_ARCH] = {
  0,                           //  CTX_ARCH_NOSOLVERS --> empty theory

  UF_MASK,                     //  CTX_ARCH_EG
  ARITH_MASK,                  //  CTX_ARCH_SPLX
  IDL_MASK,                    //  CTX_ARCH_IFW
  RDL_MASK,                    //  CTX_ARCH_RFW
  BV_MASK,                     //  CTX_ARCH_BV
  UF_MASK|FUN_MASK,            //  CTX_ARCH_EGFUN
  UF_MASK|ARITH_MASK,          //  CTX_ARCH_EGSPLX
  UF_MASK|BV_MASK,             //  CTX_ARCH_EGBV
  UF_MASK|ARITH_MASK|FUN_MASK, //  CTX_ARCH_EGFUNSPLX
  UF_MASK|BV_MASK|FUN_MASK,    //  CTX_ARCH_EGFUNBV
  ALLTH_MASK,                  //  CTX_ARCH_EGFUNSPLXBV

  IDL_MASK,                    //  CTX_ARCH_AUTO_IDL
  RDL_MASK,                    //  CTX_ARCH_AUTO_RDL
};


/*
 * Each architecture has a fixed set of solver components:
 * - the set of components is stored as a bit vector (on 8bits)
 * - this uses the following bit-masks
 * For the AUTO_xxx architecture, nothing is required initially,
 * so the bitmask is 0.
 */
#define EGRPH  0x1
#define SPLX   0x2
#define IFW    0x4
#define RFW    0x8
#define BVSLVR 0x10
#define FSLVR  0x20

static const uint8_t const arch_components[NUM_ARCH] = {
  0,                        //  CTX_ARCH_NOSOLVERS

  EGRPH,                    //  CTX_ARCH_EG
  SPLX,                     //  CTX_ARCH_SPLX
  IFW,                      //  CTX_ARCH_IFW
  RFW,                      //  CTX_ARCH_RFW
  BVSLVR,                   //  CTX_ARCH_BV
  EGRPH|FSLVR,              //  CTX_ARCH_EGFUN
  EGRPH|SPLX,               //  CTX_ARCH_EGSPLX
  EGRPH|BVSLVR,             //  CTX_ARCH_EGBV
  EGRPH|SPLX|FSLVR,         //  CTX_ARCH_EGFUNSPLX
  EGRPH|BVSLVR|FSLVR,       //  CTX_ARCH_EGFUNBV
  EGRPH|SPLX|BVSLVR|FSLVR,  //  CTX_ARCH_EGFUNSPLXBV

  0,                        //  CTX_ARCH_AUTO_IDL
  0,                        //  CTX_ARCH_AUTO_RDL
};


/*
 * Smt mode for a context mode
 */
static const smt_mode_t const core_mode[NUM_MODES] = {
  SMT_MODE_BASIC,       // one check
  SMT_MODE_BASIC,       // multichecks
  SMT_MODE_PUSHPOP,     // push/pop
  SMT_MODE_INTERACTIVE, // interactive
};


/*
 * Flags for a context mode
 */
static const uint32_t const mode2options[NUM_MODES] = {
  0,
  MULTICHECKS_OPTION_MASK,
  MULTICHECKS_OPTION_MASK|PUSHPOP_OPTION_MASK,
  MULTICHECKS_OPTION_MASK|PUSHPOP_OPTION_MASK|CLEANINT_OPTION_MASK,
};




/******************
 *  EMPTY SOLVER  *
 *****************/

/*
 * We need an empty theory solver for initializing
 * the core if the architecture is NOSOLVERS.
 */
static void donothing(void *solver) {  
}

static void null_backtrack(void *solver, uint32_t backlevel) {
}

static bool null_propagate(void *solver) {
  return true;
}

static fcheck_code_t null_final_check(void *solver) {
  return FCHECK_SAT;
}

static th_ctrl_interface_t null_ctrl = {
  donothing,        // start_internalization
  donothing,        // start_search
  null_propagate,   // propagate
  null_final_check, // final check
  donothing,        // increase_decision_level
  null_backtrack,   // backtrack
  donothing,        // push
  donothing,        // pop
  donothing,        // reset
};


// for the smt interface, nothing should be called since there are no atoms
static th_smt_interface_t null_smt = {
  NULL, NULL, NULL, NULL, NULL,
};





/*********************
 *  SIMPLEX OPTIONS  *
 ********************/

/*
 * Which version of the arithmetic solver is present
 */
bool context_has_idl_solver(context_t *ctx) {
  uint8_t solvers;
  solvers = arch_components[ctx->arch];
  return ctx->arith_solver != NULL && (solvers & IFW);
}

bool context_has_rdl_solver(context_t *ctx) {
  uint8_t solvers;
  solvers = arch_components[ctx->arch];
  return ctx->arith_solver != NULL && (solvers & RFW);
}

bool context_has_simplex_solver(context_t *ctx) {
  uint8_t solvers;
  solvers = arch_components[ctx->arch];
  return ctx->arith_solver != NULL && (solvers & SPLX);
}


/*
 * If the simplex solver already exists, the options are propagated.
 * Otherwise, they are recorded into the option flags. They will
 * be set up when the simplex solver is created.
 */
void enable_splx_eager_lemmas(context_t *ctx) {
  ctx->options |= SPLX_EGRLMAS_OPTION_MASK;
}

void disable_splx_eager_lemmas(context_t *ctx) {
  ctx->options &= ~SPLX_EGRLMAS_OPTION_MASK;
}


void enable_splx_periodic_icheck(context_t *ctx) {
  ctx->options |= SPLX_ICHECK_OPTION_MASK;
}

void disable_splx_periodic_icheck(context_t *ctx) {
  ctx->options &= ~SPLX_ICHECK_OPTION_MASK;
}



/****************************
 *  SOLVER INITIALIZATION   *
 ***************************/

/*
 * Create and initialize the egraph
 * - the core must be created first
 */
static void create_egraph(context_t *ctx) {
  egraph_t *egraph;

  assert(ctx->egraph == NULL);

  egraph = (egraph_t *) safe_malloc(sizeof(egraph_t));
  init_egraph(egraph, ctx->types);
  ctx->egraph = egraph;
}


/*
 * Create and initialize the idl solver and attach it to the core
 * - there must be no other solvers and no egraph
 * - also initialize the core
 * - copy the solver's internalization interface into arith
 */
static void create_idl_solver(context_t *ctx) {
  idl_solver_t *solver;
  smt_mode_t cmode;

  assert(ctx->egraph == NULL && ctx->arith_solver == NULL && ctx->bv_solver == NULL &&
	 ctx->fun_solver == NULL && ctx->core != NULL);

  cmode = core_mode[ctx->mode];
  solver = (idl_solver_t *) safe_malloc(sizeof(idl_solver_t));
  init_idl_solver(solver, ctx->core, &ctx->gate_manager);
  init_smt_core(ctx->core, CTX_DEFAULT_CORE_SIZE, solver, idl_ctrl_interface(solver),
		idl_smt_interface(solver), cmode);
  idl_solver_init_jmpbuf(solver, &ctx->env);
  ctx->arith_solver = solver;
  ctx->arith = *idl_arith_interface(solver);
}


/*
 * Create and initialize the rdl solver and attach it to the core.
 * - there must be no other solvers and no egraph
 * - also initialize the core
 * - copy the solver's internalization interface in ctx->arith
 */
static void create_rdl_solver(context_t *ctx) {
  rdl_solver_t *solver;
  smt_mode_t cmode;

  assert(ctx->egraph == NULL && ctx->arith_solver == NULL && ctx->bv_solver == NULL &&
	 ctx->fun_solver == NULL && ctx->core != NULL);

  cmode = core_mode[ctx->mode];
  solver = (rdl_solver_t *) safe_malloc(sizeof(rdl_solver_t));
  init_rdl_solver(solver, ctx->core, &ctx->gate_manager);
  init_smt_core(ctx->core, CTX_DEFAULT_CORE_SIZE, solver, rdl_ctrl_interface(solver),
		rdl_smt_interface(solver), cmode);
  rdl_solver_init_jmpbuf(solver, &ctx->env);
  ctx->arith_solver = solver;
  ctx->arith = *rdl_arith_interface(solver);
}


/*
 * Create an initialize the simplex solver and attach it to the core
 * or to the egraph if the egraph exists.
 */
static void create_simplex_solver(context_t *ctx) {
  simplex_solver_t *solver;
  smt_mode_t cmode;

  assert(ctx->arith_solver == NULL && ctx->core != NULL);

  cmode = core_mode[ctx->mode];
  solver = (simplex_solver_t *) safe_malloc(sizeof(simplex_solver_t));
  init_simplex_solver(solver, ctx->core, &ctx->gate_manager, ctx->egraph);

  // set simplex options
  if (splx_eager_lemmas_enabled(ctx)) {
    simplex_enable_eager_lemmas(solver);
  }
  if (splx_periodic_icheck_enabled(ctx)) {
    simplex_enable_periodic_icheck(solver);
  }

  // row saving must be enabled unless we're in ONECHECK mode
  if (ctx->mode != CTX_MODE_ONECHECK) {
    simplex_enable_row_saving(solver);
  }

  if (ctx->egraph != NULL) {
    // attach the simplex solver as a satellite solver to the egraph
    egraph_attach_arithsolver(ctx->egraph, solver, simplex_ctrl_interface(solver),
			      simplex_smt_interface(solver), simplex_egraph_interface(solver),
			      simplex_arith_egraph_interface(solver));
  } else {
    // attach simplex to the core and initialize the core
    init_smt_core(ctx->core, CTX_DEFAULT_CORE_SIZE, solver, simplex_ctrl_interface(solver),
		  simplex_smt_interface(solver), cmode);
  }

  simplex_solver_init_jmpbuf(solver, &ctx->env);
  ctx->arith_solver = solver;
  ctx->arith = *simplex_arith_interface(solver);
}


/*
 * Create IDL/SIMPLEX solver based on ctx->dl_profile
 */
static void create_auto_idl_solver(context_t *ctx) {
  dl_data_t *profile;
  int32_t sum_const;
  double atom_density;

  assert(ctx->dl_profile != NULL);
  profile = ctx->dl_profile;

  if (q_is_smallint(&profile->sum_const)) {
    sum_const = q_get_smallint(&profile->sum_const);
  } else {
    sum_const = INT32_MAX;
  }

  if (sum_const >= 1073741824) {
    // simplex required because of arithmetic overflow
    create_simplex_solver(ctx);
    ctx->arch = CTX_ARCH_SPLX;
  } else if (profile->num_vars >= 1000) {
    // too many variables for FW
    create_simplex_solver(ctx);
    ctx->arch = CTX_ARCH_SPLX;
  } else if (profile->num_vars <= 200 || profile->num_eqs == 0) {
    // use FW for now, until we've tested SIMPLEX more
    // 0 equalities usually means a scheduling problem
    // --flatten works better on IDL/FW
    create_idl_solver(ctx);
    ctx->arch = CTX_ARCH_IFW;
    enable_diseq_and_or_flattening(ctx);

  } else {

    // problem density
    if (profile->num_vars > 0) {
      atom_density = ((double) profile->num_atoms)/profile->num_vars;
    } else {
      atom_density = 0;
    }    

    if (atom_density >= 10.0) {
      // high density: use FW
      create_idl_solver(ctx);
      ctx->arch = CTX_ARCH_IFW;
      enable_diseq_and_or_flattening(ctx);
    } else {
      create_simplex_solver(ctx);
      ctx->arch = CTX_ARCH_SPLX;
    }
  }
}


/*
 * Create RDL/SIMPLEX solver based on ctx->dl_profile
 */
static void create_auto_rdl_solver(context_t *ctx) {
  dl_data_t *profile;
  double atom_density;

  assert(ctx->dl_profile != NULL);
  profile = ctx->dl_profile;

  if (profile->num_vars >= 1000) {
    create_simplex_solver(ctx);
    ctx->arch = CTX_ARCH_SPLX;
  } else if (profile->num_vars <= 200 || profile->num_eqs == 0) {
    create_rdl_solver(ctx); 
    ctx->arch = CTX_ARCH_RFW;
  } else {
    // problem density
    if (profile->num_vars > 0) {
      atom_density = ((double) profile->num_atoms)/profile->num_vars;
    } else {
      atom_density = 0;
    }    

    if (atom_density >= 7.0) {
      // high density: use FW
      create_rdl_solver(ctx);
      ctx->arch = CTX_ARCH_RFW;
    } else {
      // low-density: use SIMPLEX
      create_simplex_solver(ctx);
      ctx->arch = CTX_ARCH_SPLX;
    }
  }
}



/*
 * Create the array/function theory solver and attach it to the egraph
 */
static void create_fun_solver(context_t *ctx) {
  fun_solver_t *solver;

  assert(ctx->egraph != NULL && ctx->fun_solver == NULL);

  solver = (fun_solver_t *) safe_malloc(sizeof(fun_solver_t));
  init_fun_solver(solver, ctx->core, &ctx->gate_manager, ctx->egraph, ctx->types);
  egraph_attach_funsolver(ctx->egraph, solver, fun_solver_ctrl_interface(solver),
			  fun_solver_egraph_interface(solver),
			  fun_solver_fun_egraph_interface(solver));

  ctx->fun_solver = solver;
}




/*
 * Allocate and initialize solvers based on architecture and mode
 * - core and gate manager must exist at this point 
 * - if the architecture is either AUTO_IDL or AUTO_RDL, nothing is done yet,
 *   and the core is not initialized.
 * - otherwise, all components are ready and initialized, including the core.
 */
static void init_solvers(context_t *ctx) {
  uint8_t solvers;
  smt_core_t *core;
  smt_mode_t cmode;
  egraph_t *egraph;

  solvers = arch_components[ctx->arch];

  ctx->egraph = NULL;
  ctx->arith_solver = NULL;
  ctx->bv_solver = NULL;
  ctx->fun_solver = NULL;

  // Create egraph first, then satellite solvers
  if (solvers & EGRPH) {
    create_egraph(ctx);
  }

  // Arithmetic solver
  if (solvers & SPLX) {
    create_simplex_solver(ctx);
  } else if (solvers & IFW) {
    create_idl_solver(ctx);
  } else if (solvers & RFW) {
    create_rdl_solver(ctx);
  }

  // Array solver
  if (solvers & FSLVR) {
    create_fun_solver(ctx);
  }

  /*
   * At this point all solvers are ready and initialized,
   * except the egraph and core if the egraph is present 
   * or the core if there are no solvers
   */
  cmode = core_mode[ctx->mode];   // initialization mode for the core
  egraph = ctx->egraph;
  core = ctx->core;
  if (egraph != NULL) {
    init_smt_core(core, CTX_DEFAULT_CORE_SIZE, egraph, egraph_ctrl_interface(egraph), 
		  egraph_smt_interface(egraph), cmode);
    egraph_attach_core(egraph, core);

  } else if (ctx->theories == 0) {
    /*
     * Boolean solver only
     */
    assert(ctx->arith_solver == NULL && ctx->bv_solver == NULL && ctx->fun_solver == NULL);
    init_smt_core(core, CTX_DEFAULT_CORE_SIZE, NULL, &null_ctrl, &null_smt, cmode);
  }
}




/*
 * Delete the arithmetic solver
 */
static void delete_arith_solver(context_t *ctx) {
  uint8_t solvers;

  assert(ctx->arith_solver != NULL);

  solvers = arch_components[ctx->arch];
  if (solvers & IFW) {
    delete_idl_solver(ctx->arith_solver);    
  } else if (solvers & RFW) {
    delete_rdl_solver(ctx->arith_solver);
  } else if (solvers & SPLX) {
    delete_simplex_solver(ctx->arith_solver);
  }
  safe_free(ctx->arith_solver);
  ctx->arith_solver = NULL;
}




/*****************************
 *  CONTEXT INITIALIZATION   *
 ****************************/

/*
 * Check mode and architecture
 */
static inline bool valid_mode(context_mode_t mode) {
  return CTX_MODE_ONECHECK <= mode && mode <= CTX_MODE_INTERACTIVE;
}

static inline bool valid_arch(context_arch_t arch) {
  return CTX_ARCH_NOSOLVERS <= arch && arch <= CTX_ARCH_AUTO_RDL;
}



/*
 * Initialize ctx for the given mode and architecture
 * - terms = term table for that context
 * - qflag = true means quantifiers allowed
 * - qflag = false means no quantifiers
 */
void init_context(context_t *ctx, term_table_t *terms,
		  context_mode_t mode, context_arch_t arch, bool qflag) {  
  assert(valid_mode(mode) && valid_arch(arch));

  /*
   * Set architecture and options
   */
  ctx->mode = mode;
  ctx->arch = arch;
  ctx->theories = arch2theories[arch];
  ctx->options = mode2options[mode];
  if (qflag) {
    // quantifiers require egraph
    assert((ctx->theories & UF_MASK) != 0);
    ctx->theories |= QUANT_MASK;
  }

  ctx->base_level = 0;

  /*
   * The core is always needed: allocate it here. It's not initialized yet.
   * The other solver are optionals.
   */
  ctx->core = (smt_core_t *) safe_malloc(sizeof(smt_core_t));
  ctx->egraph = NULL;
  ctx->arith_solver = NULL;
  ctx->bv_solver = NULL;
  ctx->fun_solver = NULL;

  /*
   * Global tables + gate manager
   */
  ctx->types = terms->types;
  ctx->terms = terms;
  init_gate_manager(&ctx->gate_manager, ctx->core);

  /*
   * Simplification/internalization support
   */
  init_intern_tbl(&ctx->intern, 0, terms);  
  init_ivector(&ctx->assertions, CTX_DEFAULT_VECTOR_SIZE);
  init_ivector(&ctx->top_eqs, CTX_DEFAULT_VECTOR_SIZE);
  init_ivector(&ctx->top_atoms, CTX_DEFAULT_VECTOR_SIZE);
  init_ivector(&ctx->top_formulas, CTX_DEFAULT_VECTOR_SIZE);
  init_ivector(&ctx->top_interns, CTX_DEFAULT_VECTOR_SIZE);

  /*
   * Force the internalization mapping for true and false
   * - true  term --> true_occ
   * - false term --> false_occ 
   * This mapping holds even if there's no egraph.
   */
  intern_tbl_map_root(&ctx->intern, true_term, bool2code(true));

  /*
   * Auxiliary internalization buffers
   */
  init_ivector(&ctx->subst_eqs, CTX_DEFAULT_VECTOR_SIZE);
  init_ivector(&ctx->aux_vector, CTX_DEFAULT_VECTOR_SIZE);
  init_istack(&ctx->istack);
  init_int_queue(&ctx->queue, 0);
  ctx->subst = NULL;
  ctx->marks = NULL;
  ctx->cache = NULL;
  ctx->small_cache = NULL;

  ctx->dl_profile = NULL;
  ctx->arith_buffer = NULL;
  ctx->poly_buffer = NULL;
  ctx->aux_poly = NULL;
  ctx->aux_poly_size = 0;

  /*
   * Allocate and initialize the solvers and core
   * NOTE: the core is not initialized yet if arch is AUTO_IDL or AUTO_RDL
   */
  init_solvers(ctx);
}




/*
 * Delete ctx
 */
void delete_context(context_t *ctx) {
  if (ctx->core != NULL) {
    if (ctx->arch != CTX_ARCH_AUTO_IDL && ctx->arch != CTX_ARCH_AUTO_RDL) {
      delete_smt_core(ctx->core);
    }
    safe_free(ctx->core);
    ctx->core = NULL;
  }

  if (ctx->egraph != NULL) {
    delete_egraph(ctx->egraph);
    safe_free(ctx->egraph);
    ctx->egraph = NULL;
  }

  if (ctx->arith_solver != NULL) {
    delete_arith_solver(ctx);
  }

  if (ctx->fun_solver != NULL) {
    delete_fun_solver(ctx->fun_solver);
    safe_free(ctx->fun_solver);
    ctx->fun_solver = NULL;
  }

  delete_gate_manager(&ctx->gate_manager);

  delete_intern_tbl(&ctx->intern);
  delete_ivector(&ctx->assertions);
  delete_ivector(&ctx->top_eqs);
  delete_ivector(&ctx->top_atoms);
  delete_ivector(&ctx->top_formulas);
  delete_ivector(&ctx->top_interns);

  delete_ivector(&ctx->subst_eqs);
  delete_ivector(&ctx->aux_vector);
  delete_istack(&ctx->istack);
  delete_int_queue(&ctx->queue);

  context_free_subst(ctx);
  context_free_marks(ctx);
  context_free_cache(ctx);
  context_free_small_cache(ctx);

  context_free_dl_profile(ctx);
  context_free_arith_buffer(ctx);
  context_free_poly_buffer(ctx);
  context_free_aux_poly(ctx);
}



/*
 * Reset: remove all assertions and clear all internalization tables
 */
void reset_context(context_t *ctx) {
  ctx->base_level = 0;

  reset_smt_core(ctx->core); // this propagates reset to all solvers

  reset_gate_manager(&ctx->gate_manager);

  reset_intern_tbl(&ctx->intern);
  ivector_reset(&ctx->assertions);
  ivector_reset(&ctx->top_eqs);
  ivector_reset(&ctx->top_atoms);
  ivector_reset(&ctx->top_formulas);
  ivector_reset(&ctx->top_interns);

  // Force the internalization mapping for true and false
  intern_tbl_map_root(&ctx->intern, true_term, bool2code(true));

  ivector_reset(&ctx->subst_eqs);
  ivector_reset(&ctx->aux_vector);
  reset_istack(&ctx->istack);
  int_queue_reset(&ctx->queue);

  context_free_subst(ctx);
  context_free_marks(ctx);
  context_reset_small_cache(ctx);

  context_free_arith_buffer(ctx);
  context_reset_poly_buffer(ctx);
  context_free_aux_poly(ctx);
  context_free_dl_profile(ctx);
}



/*
 * Push and pop
 */
void context_push(context_t *ctx) {
  assert(context_supports_pushpop(ctx));
  smt_push(ctx->core);  // propagates to all solvers
  gate_manager_push(&ctx->gate_manager);
  intern_tbl_push(&ctx->intern);
  ctx->base_level ++;
}

void context_pop(context_t *ctx) {
  assert(ctx->base_level > 0);
  smt_pop(ctx->core);   // propagates to all solvers
  gate_manager_pop(&ctx->gate_manager);
  intern_tbl_pop(&ctx->intern);
  ctx->base_level --;
}





/****************************
 *   ASSERTIONS AND CHECK   *
 ***************************/

/*
 * Flatten and internalize assertions a[0 ... n-1]
 * - all elements a[i] must be valid boolean term in ctx->terms
 * - return code: 
 *   TRIVIALLY_UNSAT if there's an easy contradiction
 *   CTX_NO_ERROR if the assertions were processed without error
 *   a negative error code otherwise.
 */
static int32_t context_process_assertions(context_t *ctx, uint32_t n, term_t *a) {
  ivector_t *v;
  uint32_t i;
  int code;

  ivector_reset(&ctx->top_eqs);
  ivector_reset(&ctx->top_atoms);
  ivector_reset(&ctx->top_formulas);
  ivector_reset(&ctx->top_interns);
  ivector_reset(&ctx->subst_eqs);

  code = setjmp(ctx->env);
  if (code == 0) {
    // flatten
    for (i=0; i<n; i++) {
      flatten_assertion(ctx, a[i]);
    }

    // deal with variable substitutions if any
    if (ctx->subst_eqs.size > 0) {
      context_process_candidate_subst(ctx);
    }

    /*
     * At this point, the assertions are stored into the four vectors
     * top_eqs, top_atoms, top_formulas, and top_interns, and
     * ctx->intern stores the internalized terms and the variable
     * substitutions.
     */

    // optional processing
    switch (ctx->arch) {
    case CTX_ARCH_EG:
      if (context_eq_abstraction_enabled(ctx)) {
	code = analyze_uf(ctx);
	if (code != CTX_NO_ERROR) return code;
      }
      break;

    case CTX_ARCH_AUTO_IDL:
      analyze_diff_logic(ctx, true);
      create_auto_idl_solver(ctx);
      break;
      
    case CTX_ARCH_AUTO_RDL:
      analyze_diff_logic(ctx, false);
      create_auto_rdl_solver(ctx);
      break;

    default:
      break;
    }


    /*
     * Notify the core + solver(s)
     */
    internalization_start(ctx->core); // ?? Get rid of this?

    /*
     * Assert top_eqs, top_atoms, top_formulas, top_interns
     */
    code = CTX_NO_ERROR;

    // first: all terms that are already internalized
    v = &ctx->top_interns;
    n = v->size;
    if (n > 0) {
      i = 0;
      do {
	assert_toplevel_intern(ctx, v->data[i]);
	i ++;
      } while (i < n);

      // one round of propagation
      if (! base_propagate(ctx->core)) {
	code = TRIVIALLY_UNSAT;
	goto done;
      }
    }

    // second: all top-level equalities
    v = &ctx->top_eqs;
    n = v->size;
    if (n > 0) {
      i = 0;
      do {
	assert_toplevel_formula(ctx, v->data[i]);
	i ++;
      } while (i < n);

      // one round of propagation
      if (! base_propagate(ctx->core)) {
	code = TRIVIALLY_UNSAT;
	goto done;
      }
    }

    // third: all top-level atoms (other than equalities)
    v = &ctx->top_atoms;
    n = v->size;
    if (n > 0) {
      i = 0;
      do {
	assert_toplevel_formula(ctx, v->data[i]);
	i ++;
      } while (i < n);

      // one round of propagation
      if (! base_propagate(ctx->core)) {
	code = TRIVIALLY_UNSAT;
	goto done;
      }
    }

    // last: all non-atomic, formulas
    v =  &ctx->top_formulas;
    n = v->size;
    if (n > 0) {
      i = 0;
      do {
	assert_toplevel_formula(ctx, v->data[i]);
	i ++;
      } while (i < n);

      // one round of propagation
      if (! base_propagate(ctx->core)) {
	code = TRIVIALLY_UNSAT;
	goto done;
      }
    }

  } else {
    /*
     * Exception: return from longjmp(ctx->env, code);
     */
    reset_istack(&ctx->istack);
    int_queue_reset(&ctx->queue);
    context_free_subst(ctx);
    context_free_marks(ctx);
  }

 done:
  return code;
}



/*
 * Assert all formulas f[0] ... f[n-1]
 * The context status must be IDLE.
 *
 * Return code:
 * - TRIVIALLY_UNSAT means that an inconsistency is detected
 *   (in that case the context status is set to UNSAT)
 * - CTX_NO_ERROR means no internalization error and status not 
 *   determined
 * - otherwise, the code is negative to report an error.
 */
int32_t assert_formulas(context_t *ctx, uint32_t n, term_t *f) {
  int32_t code;

  assert(ctx->arch == CTX_ARCH_AUTO_IDL || 
	 ctx->arch == CTX_ARCH_AUTO_RDL ||
	 smt_status(ctx->core) == STATUS_IDLE);

  code = context_process_assertions(ctx, n, f);
  if (code == TRIVIALLY_UNSAT &&
      ctx->arch != CTX_ARCH_AUTO_IDL &&
      ctx->arch != CTX_ARCH_AUTO_RDL &&
      smt_status(ctx->core) != STATUS_UNSAT) {
    // force UNSAT in the core
    // we can't do that in AUTO_IDL/AUTO_RDL modes since
    // the core is not initialized yet.
    add_empty_clause(ctx->core);
    ctx->core->status = STATUS_UNSAT;
  }

  return code;
}



/*
 * Assert a boolean formula f.
 *
 * The context status must be IDLE.
 *
 * Return code:
 * - TRIVIALLY_UNSAT means that an inconsistency is detected
 *   (in that case the context status is set to UNSAT)
 * - CTX_NO_ERROR means no internalization error and status not 
 *   determined
 * - otherwise, the code is negative. The assertion could 
 *   not be processed.
 */
int32_t assert_formula(context_t *ctx, term_t f) {
  return assert_formulas(ctx, 1, &f);
}


/*
 * Clear: prepare for more assertions and checks
 * - free the boolean assignment
 * - reset the status to IDLE
 */
void context_clear(context_t *ctx) {
  assert(context_supports_multichecks(ctx));
  smt_clear(ctx->core);
}

