/*
 * ASSERTION CONTEXT
 */

#include "memalloc.h"
#include "term_utils.h"
#include "context.h"


/*******************************
 *  FLATTENING/SIMPLIFICATION  *
 ******************************/

/*
 * Assertions are processed by performing top-down boolean propagation
 * and collecting all subterms that can't be flattened into four vectors:
 *
 * 1) ctx->top_eqs = top-level equalities.
 *    Every t in top_eqs is (eq t1 t2) (or a variant) asserted true.
 *    t is mapped to true_occ in the internalization table.
 *
 * 2) ctx->top_atoms = top-level atoms.
 *    Every t in top_atoms is an atom (that can't go into top_eqs).
 *    t is mapped to true_occ or false_occ in the internalization table.
 *
 * 3) ctx->top_formulas = non-atomic terms.
 *    Every t in top_formulas is either an (OR ...) or (ITE ...) or (XOR ...)
 *    that can't be further flattend.
 *    t is mapped to true_occ or false_occ.
 *
 * 4) ctx->top_interns = already internalized terms.
 *    Every t in top_interns is a term that's been internalized before
 *    and is mapped to a literal l or an egraph occurrence g.
 *    l or g must be asserted true in later stages.
 * 
 * If variable elimination is enabled, some top-level equalities 
 * (eq x <term>) are converted into substitutions [x := term].
 *
 * Flattening is done breadth-first:
 * - the subterms to process are stored into ctx->queue.
 * - each subterm in that queue is a boolean term that's asserted true
 */


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
 * Check whether [t1 := t2] is a possible substitution
 * - both t1 and t2 are root terms of positive polarity
 *   in the internalization table (non boolean)
 * - return true if the substitution works
 * - raise an exception via longjmp if the equality is unsat
 *   (e.g., x := 1/2 when x is an integer).
 * - return false otherwise.
 */
static bool good_subst(context_t *ctx, term_t t1, term_t t2) {
  intern_tbl_t *intern;

  intern = &ctx->intern;
  if (is_constant_term(ctx->terms, t2)) {
    if (intern_tbl_valid_const_subst(intern, t1, t2)) {
      return true;
    } else {
      // trivially unsat by type incompatibility
      longjmp(ctx->env, TRIVIALLY_UNSAT);
    }
  } else {
    return intern_tbl_valid_subst(intern, t1, t2);
  }
}


/*
 * Attempt to turn (eq t1 t2) into a variable substitution
 * - both t1 and t2 are root terms in the internalization table
 *   (and t1 and t2 are not boolean so they have positive polarity)
 * - e is a term equivalent to (eq t1 t2)
 */
static void try_substitution(context_t *ctx, term_t t1, term_t t2, term_t e) {
  intern_tbl_t *intern;
  bool free1, free2;

  assert(is_pos_term(t1) && is_pos_term(t2));

  if (context_var_elim_enabled(ctx)) {
    intern = &ctx->intern;

    free1 = intern_tbl_root_is_free(intern, t1);
    free2 = intern_tbl_root_is_free(intern, t2);

    if (free1 && free2) {
      intern_tbl_merge_classes(intern, t1, t2);
      return;
    }
    
    if (free1 && good_subst(ctx, t1, t2)) {
      intern_tbl_add_subst(intern, t1, t2);
      return;
    }

    if (free2 && good_subst(ctx, t2, t1)) {
      intern_tbl_add_subst(intern, t2, t1);
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

  if (context_var_elim_enabled(ctx)) {
    intern = &ctx->intern;

    if (intern_tbl_root_is_free(intern, t1)) {
      if (intern_tbl_root_is_free(intern, t2)) {
	/*
	 * Both t1 and t2 are free
	 */
	intern_tbl_merge_classes(intern, t1, t2);
	return;

      } else {
	/* 
	 * t1 is free, t2 is not free
	 */
	if (is_neg_term(t1)) {
	  t1 = opposite_term(t1);
	  t2 = opposite_term(t2);
	}

	if (intern_tbl_valid_subst(intern, t1, t2)) {
	  intern_tbl_add_subst(intern, t1, t2);
	  return;
	}

      }
      
    } else if (intern_tbl_root_is_free(intern, t2)) {
      /*
       * t2 is free, t1 is not free
       */
      if (is_neg_term(t2)) {
	t1 = opposite_term(t1);
	t2 = opposite_term(t2);
      }

      if (intern_tbl_valid_subst(intern, t2, t1)) {
	intern_tbl_add_subst(intern, t2, t1);
	return;
      }
    }

  }
  
  // no substitution
  ivector_push(&ctx->top_eqs, e);
}




/*
 * Simplification: all functions below attempt to rewrite a (boolean)
 * term r to an equivalent (boolean) term q. They return NULL_TERM if 
 * the simplification fails.
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
 * Simplification for equalities between two terms t1 and t2.
 * - both t1 and t2 are root terms in the internalization table
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
      try_bool_substitution(ctx, t1, t2, r);
    }

  } else {
    /*
     * Non-boolean
     */
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
  ivector_push(&ctx->top_formulas, signed_term(r, tt));
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
       * then add r or not r to top_intern
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
 * Flatten and internalize assertions a[0 ... n-1]
 * - all elements a[i] must be valid boolean term in ctx->terms
 * - return code: 
 *   TRIVIALLY_UNSAT if there's an easy contradiction
 *   CTX_NO_ERROR if the assertions were processed without error
 *   a negative error code otherwise.
 */
static int32_t context_process_assertions(context_t *ctx, uint32_t n, term_t *a) {
  uint32_t i;
  int code;

  ivector_reset(&ctx->top_eqs);
  ivector_reset(&ctx->top_atoms);
  ivector_reset(&ctx->top_formulas);
  ivector_reset(&ctx->top_interns);

  code = setjmp(ctx->env);
  if (code == 0) {
    for (i=0; i<n; i++) {
      flatten_assertion(ctx, a[i]);
    }

    return CTX_NO_ERROR;

  } else {
    /*
     * Exception: return from longjmp(ctx->env, code);
     */
    reset_istack(&ctx->istack);
    int_queue_reset(&ctx->queue);

    return (int32_t) code;
  }
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
  smt_mode_t cmode;

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
  init_istack(&ctx->istack);
  init_int_queue(&ctx->queue, 0);


  // TEMPORARY HACK: INITIALIZE THE CORE WITH THE EMPTY SOLVER
  cmode = core_mode[mode];
  init_smt_core(ctx->core, CTX_DEFAULT_CORE_SIZE, NULL, &null_ctrl, &null_smt, cmode);
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

  delete_gate_manager(&ctx->gate_manager);

  delete_intern_tbl(&ctx->intern);
  delete_ivector(&ctx->assertions);
  delete_ivector(&ctx->top_eqs);
  delete_ivector(&ctx->top_atoms);
  delete_ivector(&ctx->top_formulas);
  delete_ivector(&ctx->top_interns);

  delete_istack(&ctx->istack);
  delete_int_queue(&ctx->queue);
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


  reset_istack(&ctx->istack);
  int_queue_reset(&ctx->queue);
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
 * Assert all formulas f[0] ... f[n-1]
 * same return code as above.
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

