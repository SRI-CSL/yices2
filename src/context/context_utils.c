/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * UTILITIES TO ACCESS CONTEXT STRUCTURES
 */

#include "context/context_utils.h"
#include "context/internalization_codes.h"



/*
 * SUBST AND MARK VECTOR
 */

/*
 * If variable elimination is enabled, then ctx->subst is used to
 * store candidate substitutions before we check for substitution
 * cycles. The mark vector is used to mark terms during cycle detection.
 */

/*
 * Allocate and initialize ctx->subst
 */
pseudo_subst_t *context_get_subst(context_t *ctx) {
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
mark_vector_t *context_get_marks(context_t *ctx) {
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
 */

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
 */

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
 * Allocate the arithmetic buffer + store if necessary
 */
rba_buffer_t *context_get_arith_buffer(context_t *ctx) {
  rba_buffer_t *tmp;

  tmp = ctx->arith_buffer;
  if (tmp == NULL) {
    tmp = (rba_buffer_t *) safe_malloc(sizeof(rba_buffer_t));
    init_rba_buffer(tmp, ctx->terms->pprods);
    ctx->arith_buffer = tmp;
  }

  return tmp;
}


/*
 * Free the arithmetic buffer + store
 */
void context_free_arith_buffer(context_t *ctx) {
  rba_buffer_t *tmp;

  tmp = ctx->arith_buffer;
  if (tmp != NULL) {
    delete_rba_buffer(tmp);
    safe_free(tmp);
    ctx->arith_buffer = NULL;
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
 */

/*
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
 * DIV/MOD TABLE
 */

/*
 * Return the table. Allocate and initialize it if needed.
 */
divmod_tbl_t *context_get_divmod_table(context_t *ctx) {
  divmod_tbl_t *tmp;

  tmp = ctx->divmod_table;
  if (tmp == NULL) {
    tmp = (divmod_tbl_t *) safe_malloc(sizeof(divmod_tbl_t));
    init_divmod_table(tmp);
    divmod_table_set_level(tmp, ctx->base_level);
    ctx->divmod_table = tmp;
  }

  return tmp;
}


/*
 * Free the table
 */
void context_free_divmod_table(context_t *ctx) {
  divmod_tbl_t *tmp;

  tmp = ctx->divmod_table;
  if (tmp != NULL) {
    delete_divmod_table(tmp);
    safe_free(tmp);
    ctx->divmod_table = NULL;
  }
}


/*
 * Push/pop/reset
 */
void context_divmod_table_push(context_t *ctx) {
  divmod_tbl_t *tmp;

  tmp = ctx->divmod_table;
  if (tmp != NULL) {
    divmod_table_push(tmp);
  }
}

void context_divmod_table_pop(context_t *ctx) {
  divmod_tbl_t *tmp;

  tmp = ctx->divmod_table;
  if (tmp != NULL) {
    divmod_table_pop(tmp);
  }
}

void context_reset_divmod_table(context_t *ctx) {
  divmod_tbl_t *tmp;

  tmp = ctx->divmod_table;
  if (tmp != NULL) {
    reset_divmod_table(tmp);
  }
}


/*
 * Find records in the table:
 * - three functions for floor/ceil/div
 * - all find functions return null_thvar if the table does not exist or
 *   if the relevant record is not in the table.
 */
thvar_t context_find_var_for_floor(context_t *ctx, thvar_t x) {
  divmod_tbl_t *tmp;
  divmod_rec_t *r;
  thvar_t y;

  y = null_thvar;
  tmp = ctx->divmod_table;
  if (tmp != NULL) {
    r = divmod_table_find_floor(tmp, x);
    if (r != NULL) {
      y = r->val;
    }
  }

  return y;
}

thvar_t context_find_var_for_ceil(context_t *ctx, thvar_t x) {
  divmod_tbl_t *tmp;
  divmod_rec_t *r;
  thvar_t y;

  y = null_thvar;
  tmp = ctx->divmod_table;
  if (tmp != NULL) {
    r = divmod_table_find_ceil(tmp, x);
    if (r != NULL) {
      y = r->val;
    }
  }

  return y;
}

thvar_t context_find_var_for_div(context_t *ctx, thvar_t x, const rational_t *k) {
  divmod_tbl_t *tmp;
  divmod_rec_t *r;
  thvar_t y;

  y = null_thvar;
  tmp = ctx->divmod_table;
  if (tmp != NULL) {
    r = divmod_table_find_div(tmp, x, k);
    if (r != NULL) {
      y = r->val;
    }
  }

  return y;
}


/*
 * Add records in the table:
 * - three functions for floor/ceil/div
 * - all three functions initialize the table if needed
 */

// record for y = (floor x)
void context_record_floor(context_t *ctx, thvar_t x, thvar_t y) {
  divmod_tbl_t *tmp;
  divmod_rec_t *r;

  tmp = context_get_divmod_table(ctx);
  r = divmod_table_get_floor(tmp, x);
  assert(r->val < 0);
  r->val = y;
}

// record for y = (ceil x)
void context_record_ceil(context_t *ctx, thvar_t x, thvar_t y) {
  divmod_tbl_t *tmp;
  divmod_rec_t *r;

  tmp = context_get_divmod_table(ctx);
  r = divmod_table_get_ceil(tmp, x);
  assert(r->val < 0);
  r->val = y;
}

// record for y = (div x k)
void context_record_div(context_t *ctx, thvar_t x, const rational_t *k, thvar_t y) {
  divmod_tbl_t *tmp;
  divmod_rec_t *r;

  tmp = context_get_divmod_table(ctx);
  r = divmod_table_get_div(tmp, x, k);
  assert(r->val < 0);
  r->val = y;
}



/*
 * FACTORING OF DISJUNCTS
 */

/*
 * Return the explorer data structure
 * - allocate and initialize it if needed
 */
bfs_explorer_t *context_get_explorer(context_t *ctx) {
  bfs_explorer_t *tmp;

  tmp = ctx->explorer;  
  if (tmp == NULL) {
    tmp = (bfs_explorer_t *) safe_malloc(sizeof(bfs_explorer_t));
    init_bfs_explorer(tmp, ctx->terms);
    ctx->explorer = tmp;
  }

  return tmp;
}

/*
 * Free the explorer if it's not NULL
 */
void context_free_explorer(context_t *ctx) {
  bfs_explorer_t *tmp;

  tmp = ctx->explorer;
  if (tmp != NULL) {
    delete_bfs_explorer(tmp);
    safe_free(tmp);
    ctx->explorer = NULL;
  }
}


/*
 * Reset the explorer if it's not NULL
 */
void context_reset_explorer(context_t *ctx) {
  bfs_explorer_t *tmp;

  tmp = ctx->explorer;
  if (tmp != NULL) {
    reset_bfs_explorer(tmp);
  }
}

/*
 * Get the common factors of term t
 * - this checks whether t is of the form (or (and  ..) (and ..) ...))
 *   and stores all terms that occur in each conjuncts into vector v
 * - example: if t is (or (and A B) (and A C D)) then A is stored in v
 * - if t is not (OR ...) then t is added to v
 */
void context_factor_disjunction(context_t *ctx, term_t t, ivector_t *v) {
  bfs_explorer_t *explorer;

  explorer = context_get_explorer(ctx);
  bfs_factor_disjunction(explorer, t, v);
}



/*
 * DIFFERENCE-LOGIC DATA
 */

/*
 * Difference-logic profile:
 * - allocate and initialize the structure if it does not exist
 */
dl_data_t *context_get_dl_profile(context_t *ctx) {
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


/*
 * CHECKS
 */

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
 * Check whether x is an if-then-else term
 */
bool term_is_ite(context_t *ctx, term_t x) {
  x = intern_tbl_get_root(&ctx->intern, x);
  return is_pos_term(x) && is_ite_term(ctx->terms, x) && 
    !intern_tbl_root_is_mapped(&ctx->intern, x);
}


/*
 * Checks whether ite contains nested if-then-elses
 */
bool ite_is_deep(context_t *ctx, composite_term_t *ite) {
  assert(ite->arity == 3);
  return term_is_ite(ctx, ite->arg[1]) || term_is_ite(ctx, ite->arg[2]);
}


/*
 * AUXILIARY EQUALITIES
 */

/*
 * Add an auxiliary equality (x == y) to the context
 * - this create eq := (eq x y) then add it to aux_eq
 */
void add_aux_eq(context_t *ctx, term_t x, term_t y) {
  term_table_t *terms;
  term_t eq;

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

    ivector_push(&ctx->aux_eqs, eq);
  }
}


/*
 * Add an auxiliary arithmetic equality to the context.
 * - this adds eq to aux_eq
 */
void add_arith_aux_eq(context_t *ctx, term_t eq) {
  assert(intern_tbl_is_root(&ctx->intern, eq));
  assert(is_pos_term(eq));
  assert(term_kind(ctx->terms, eq) == ARITH_EQ_ATOM ||
	 term_kind(ctx->terms, eq) == ARITH_BINEQ_ATOM);
  ivector_push(&ctx->aux_eqs, eq);
}



/*
 * LEARNED ATOMS
 */

/*
 * Add an atom (learned by preprocessing) to ctx->aux_atoms
 */
void add_aux_atom(context_t *ctx, term_t atom) {
  assert(is_boolean_term(ctx->terms, atom));
  ivector_push(&ctx->aux_atoms, atom);
}


