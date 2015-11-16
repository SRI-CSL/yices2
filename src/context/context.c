/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * ASSERTION CONTEXT
 */

#include "context/context.h"
#include "context/context_simplifier.h"
#include "context/context_utils.h"
#include "context/internalization_codes.h"
#include "context/ite_flattener.h"
#include "solvers/bv/bvsolver.h"
#include "terms/term_utils.h"
#include "utils/memalloc.h"

#define TRACE 0

#if TRACE

#include <stdio.h>
#include <inttypes.h>

#include "io/term_printer.h"
#include "solvers/cdcl/smt_core_printer.h"

#endif





/**********************
 *  INTERNALIZATION   *
 *********************/

/*
 * Main internalization functions:
 * - convert a boolean term t to a literal
 * - convert a bitvector term t to a bitvector variable
 */
static literal_t internalize_to_literal(context_t *ctx, term_t t);
static thvar_t internalize_to_bv(context_t *ctx, term_t t);




/******************************************************
 *  CONVERSION OF COMPOSITES TO BIT-VECTOR VARIABLES  *
 *****************************************************/

/*
 * Convert if-then-else to a bitvector variable
 */
static thvar_t map_ite_to_bv(context_t *ctx, composite_term_t *ite) {
  literal_t c;
  thvar_t x, y;

  assert(ite->arity == 3);

  c = internalize_to_literal(ctx, ite->arg[0]);
  if (c == true_literal) {
    return internalize_to_bv(ctx, ite->arg[1]);
  }
  if (c == false_literal) {
    return internalize_to_bv(ctx, ite->arg[2]);
  }

  // no simplification
  x = internalize_to_bv(ctx, ite->arg[1]);
  y = internalize_to_bv(ctx, ite->arg[2]);

  return ctx->bv.create_bvite(ctx->bv_solver, c, x, y);
}


/*
 * Array of bits b
 * - hackish: we locally disable flattening here
 */
static thvar_t map_bvarray_to_bv(context_t *ctx, composite_term_t *b) {
  uint32_t i, n;
  uint32_t save_options;
  literal_t *a;
  thvar_t x;

  n = b->arity;
  a = alloc_istack_array(&ctx->istack, n);

  save_options = ctx->options;
  disable_diseq_and_or_flattening(ctx);
  for (i=0; i<n; i++) {
    a[i] = internalize_to_literal(ctx, b->arg[i]);
  }
  ctx->options = save_options;

  x = ctx->bv.create_bvarray(ctx->bv_solver, a, n);

  free_istack_array(&ctx->istack, a);

  return x;
}


/*
 * Unsigned division: quotient (div u v)
 */
static thvar_t map_bvdiv_to_bv(context_t *ctx, composite_term_t *div) {
  thvar_t x, y;

  assert(div->arity == 2);
  x = internalize_to_bv(ctx, div->arg[0]);
  y = internalize_to_bv(ctx, div->arg[1]);

  return ctx->bv.create_bvdiv(ctx->bv_solver, x, y);
}


/*
 * Unsigned division: remainder (rem u v)
 */
static thvar_t map_bvrem_to_bv(context_t *ctx, composite_term_t *rem) {
  thvar_t x, y;

  assert(rem->arity == 2);
  x = internalize_to_bv(ctx, rem->arg[0]);
  y = internalize_to_bv(ctx, rem->arg[1]);

  return ctx->bv.create_bvrem(ctx->bv_solver, x, y);
}


/*
 * Signed division/rounding toward 0: quotient (sdiv u v)
 */
static thvar_t map_bvsdiv_to_bv(context_t *ctx, composite_term_t *sdiv) {
  thvar_t x, y;

  assert(sdiv->arity == 2);
  x = internalize_to_bv(ctx, sdiv->arg[0]);
  y = internalize_to_bv(ctx, sdiv->arg[1]);

  return ctx->bv.create_bvsdiv(ctx->bv_solver, x, y);
}


/*
 * Signed division/rounding toward 0: remainder (srem u v)
 */
static thvar_t map_bvsrem_to_bv(context_t *ctx, composite_term_t *srem) {
  thvar_t x, y;

  assert(srem->arity == 2);
  x = internalize_to_bv(ctx, srem->arg[0]);
  y = internalize_to_bv(ctx, srem->arg[1]);

  return ctx->bv.create_bvsrem(ctx->bv_solver, x, y);
}


/*
 * Signed division/rounding toward -infinity: remainder (smod u v)
 */
static thvar_t map_bvsmod_to_bv(context_t *ctx, composite_term_t *smod) {
  thvar_t x, y;

  assert(smod->arity == 2);
  x = internalize_to_bv(ctx, smod->arg[0]);
  y = internalize_to_bv(ctx, smod->arg[1]);

  return ctx->bv.create_bvsmod(ctx->bv_solver, x, y);
}


/*
 * Left shift: (shl u v)
 */
static thvar_t map_bvshl_to_bv(context_t *ctx, composite_term_t *shl) {
  thvar_t x, y;

  assert(shl->arity == 2);
  x = internalize_to_bv(ctx, shl->arg[0]);
  y = internalize_to_bv(ctx, shl->arg[1]);

  return ctx->bv.create_bvshl(ctx->bv_solver, x, y);
}


/*
 * Logical shift right: (lshr u v)
 */
static thvar_t map_bvlshr_to_bv(context_t *ctx, composite_term_t *lshr) {
  thvar_t x, y;

  assert(lshr->arity == 2);
  x = internalize_to_bv(ctx, lshr->arg[0]);
  y = internalize_to_bv(ctx, lshr->arg[1]);

  return ctx->bv.create_bvlshr(ctx->bv_solver, x, y);
}


/*
 * Arithmetic shift right: (ashr u v)
 */
static thvar_t map_bvashr_to_bv(context_t *ctx, composite_term_t *ashr) {
  thvar_t x, y;

  assert(ashr->arity == 2);
  x = internalize_to_bv(ctx, ashr->arg[0]);
  y = internalize_to_bv(ctx, ashr->arg[1]);

  return ctx->bv.create_bvashr(ctx->bv_solver, x, y);
}



/*
 * TODO: check for simplifications in bitvector arithmetic
 * before translation to bitvector variables.
 *
 * This matters for the wienand-cav2008 benchmarks.
 */

/*
 * Power product
 */
static thvar_t map_pprod_to_bv(context_t *ctx, pprod_t *p) {
  uint32_t i, n;
  thvar_t *a;
  thvar_t x;

  n = p->len;
  a = alloc_istack_array(&ctx->istack, n);
  for (i=0; i<n; i++) {
    a[i] = internalize_to_bv(ctx, p->prod[i].var);
  }

  x = ctx->bv.create_pprod(ctx->bv_solver, p, a);
  free_istack_array(&ctx->istack, a);

  return x;
}


/*
 * Bitvector polynomial, 64bit coefficients
 */
static thvar_t map_bvpoly64_to_bv(context_t *ctx, bvpoly64_t *p) {
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

  // non-constant monomials
  while (i < n) {
    a[i] = internalize_to_bv(ctx, p->mono[i].var);
    i ++;
  }

  x = ctx->bv.create_poly64(ctx->bv_solver, p, a);
  free_istack_array(&ctx->istack, a);

  return x;
}


/*
 * Bitvector polynomial, coefficients have more than 64bits
 */
static thvar_t map_bvpoly_to_bv(context_t *ctx, bvpoly_t *p) {
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

  // non-constant monomials
  while (i < n) {
    a[i] = internalize_to_bv(ctx, p->mono[i].var);
    i ++;
  }

  x = ctx->bv.create_poly(ctx->bv_solver, p, a);
  free_istack_array(&ctx->istack, a);

  return x;
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
  literal_t l1, l2, l;

  assert(eq->arity == 2);

  assert(is_boolean_term(ctx->terms, eq->arg[0]) &&
	 is_boolean_term(ctx->terms, eq->arg[1]));

  l1 = internalize_to_literal(ctx, eq->arg[0]);
  l2 = internalize_to_literal(ctx, eq->arg[1]);
  l = mk_iff_gate(&ctx->gate_manager, l1, l2);

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
      l = internalize_to_literal(ctx, a[i]);
      if (l == true_literal) goto done;
      a[i] = l;
    }

  } else {
    // no flattening
    n = or->arity;
    a = alloc_istack_array(&ctx->istack, n);
    for (i=0; i<n; i++) {
      l = internalize_to_literal(ctx, or->arg[i]);
      if (l == true_literal) goto done;
      a[i] = l;
    }
  }

  l = mk_or_gate(&ctx->gate_manager, n, a);

 done:
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
 * Auxiliary function: translate (distinct a[0 ... n-1]) to a literal,
 * when a[0] ... a[n-1] are bitvector variables.
 *
 * We expand this into a quadratic number of disequalities.
 */
static literal_t make_bv_distinct(context_t *ctx, uint32_t n, thvar_t *a) {
  uint32_t i, j;
  ivector_t *v;
  literal_t l;

  assert(n >= 2);

  v = &ctx->aux_vector;
  assert(v->size == 0);
  for (i=0; i<n-1; i++) {
    for (j=i+1; j<n; j++) {
      l = ctx->bv.create_eq_atom(ctx->bv_solver, a[i], a[j]);
      ivector_push(v, l);
    }
  }
  l = mk_or_gate(&ctx->gate_manager, v->size, v->data);
  ivector_reset(v);

  return not(l);
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
  assert(is_bitvector_term(ctx->terms, distinct->arg[0]));
  // translate to bitvector variables
  for (i=0; i<n; i++) {
    a[i] = internalize_to_bv(ctx, distinct->arg[i]);
  }
  l = make_bv_distinct(ctx, n, a);
  free_istack_array(&ctx->istack, a);

  return l;
}



/*
 * BITVECTOR ATOMS
 */
static literal_t map_bveq_to_literal(context_t *ctx, composite_term_t *eq) {
  term_t t, t1, t2;
  thvar_t x, y;

  assert(eq->arity == 2);

  /*
   * Apply substitution then check for simplifications
   */
  t1 = intern_tbl_get_root(&ctx->intern, eq->arg[0]);
  t2 = intern_tbl_get_root(&ctx->intern, eq->arg[1]);
  t = simplify_bitvector_eq(ctx, t1, t2);
  if (t != NULL_TERM) {
    // (bveq t1 t2) is equivalent to t
    return internalize_to_literal(ctx, t);
  }

  /*
   * NOTE: creating (eq t1 t2) in the egraph instead makes things worse
   */
  // no simplification
  x = internalize_to_bv(ctx, t1);
  y = internalize_to_bv(ctx, t2);
  return ctx->bv.create_eq_atom(ctx->bv_solver, x, y);
}

static literal_t map_bvge_to_literal(context_t *ctx, composite_term_t *ge) {
  thvar_t x, y;

  assert(ge->arity == 2);
  x = internalize_to_bv(ctx, ge->arg[0]);
  y = internalize_to_bv(ctx, ge->arg[1]);

  return ctx->bv.create_ge_atom(ctx->bv_solver, x, y);
}

static literal_t map_bvsge_to_literal(context_t *ctx, composite_term_t *sge) {
  thvar_t x, y;

  assert(sge->arity == 2);
  x = internalize_to_bv(ctx, sge->arg[0]);
  y = internalize_to_bv(ctx, sge->arg[1]);

  return ctx->bv.create_sge_atom(ctx->bv_solver, x, y);
}


// Select bit
static literal_t map_bit_select_to_literal(context_t *ctx, select_term_t *select) {
  term_t t, s;
  thvar_t x;

  /*
   * Apply substitution then try to simplify
   */
  t = intern_tbl_get_root(&ctx->intern, select->arg);
  s = extract_bit(ctx->terms, t, select->idx);
  if (s != NULL_TERM) {
    // (select t i) is s
    return internalize_to_literal(ctx, s);
  } else {
    // no simplification
    x = internalize_to_bv(ctx, t);
    return ctx->bv.select_bit(ctx->bv_solver, x, select->idx);
  }
}


/***************************************
 *  CONVERSION TO BITVECTOR VARIABLES  *
 **************************************/

/*
 * Translate internalization code x to a bitvector variable
 * - if x is for an egraph term u, then we return the theory variable
 *   attached to u in the egraph.
 * - otherwise, x must be the code of a bitvector variable v, so we return v.
 */
static thvar_t translate_code_to_bv(context_t *ctx, int32_t x) {
  thvar_t v;

  assert(code_is_valid(x));
  v = code2thvar(x);
  assert(v != null_thvar);

  return v;
}

/*
 * Place holders for now
 */
static thvar_t internalize_to_bv(context_t *ctx, term_t t) {
  term_table_t *terms;
  int32_t exception;
  int32_t code;
  term_t r;
  thvar_t x;

  assert(is_bitvector_term(ctx->terms, t));

  if (! context_has_bv_solver(ctx)) {
    exception = BV_NOT_SUPPORTED;
    goto abort;
  }

  /*
   * Apply the term substitution: t --> r
   */
  r = intern_tbl_get_root(&ctx->intern, t);
  if (intern_tbl_root_is_mapped(&ctx->intern, r)) {
    // r is already internalized
    code = intern_tbl_map_of_root(&ctx->intern, r);
    x = translate_code_to_bv(ctx, code);
  } else {
    // compute r's internalization
    terms = ctx->terms;

    switch (term_kind(terms, r)) {
    case BV64_CONSTANT:
      x = ctx->bv.create_const64(ctx->bv_solver, bvconst64_term_desc(terms, r));
      intern_tbl_map_root(&ctx->intern, r, thvar2code(x));
      break;

    case BV_CONSTANT:
      x = ctx->bv.create_const(ctx->bv_solver, bvconst_term_desc(terms, r));
      intern_tbl_map_root(&ctx->intern, r, thvar2code(x));
      break;

    case UNINTERPRETED_TERM:
      x = ctx->bv.create_var(ctx->bv_solver, term_bitsize(terms, r));
      intern_tbl_map_root(&ctx->intern, r, thvar2code(x));
      break;

    case ITE_TERM:
      x = map_ite_to_bv(ctx, ite_term_desc(terms, r));
      intern_tbl_map_root(&ctx->intern, r, thvar2code(x));
      break;

    case BV_ARRAY:
      x = map_bvarray_to_bv(ctx, bvarray_term_desc(terms, r));
      intern_tbl_map_root(&ctx->intern, r, thvar2code(x));
      break;

    case BV_DIV:
      x = map_bvdiv_to_bv(ctx, bvdiv_term_desc(terms, r));
      intern_tbl_map_root(&ctx->intern, r, thvar2code(x));
      break;

    case BV_REM:
      x = map_bvrem_to_bv(ctx, bvrem_term_desc(terms, r));
      intern_tbl_map_root(&ctx->intern, r, thvar2code(x));
      break;

    case BV_SDIV:
      x = map_bvsdiv_to_bv(ctx, bvsdiv_term_desc(terms, r));
      intern_tbl_map_root(&ctx->intern, r, thvar2code(x));
      break;

    case BV_SREM:
      x = map_bvsrem_to_bv(ctx, bvsrem_term_desc(terms, r));
      intern_tbl_map_root(&ctx->intern, r, thvar2code(x));
      break;

    case BV_SMOD:
      x = map_bvsmod_to_bv(ctx, bvsmod_term_desc(terms, r));
      intern_tbl_map_root(&ctx->intern, r, thvar2code(x));
      break;

    case BV_SHL:
      x = map_bvshl_to_bv(ctx, bvshl_term_desc(terms, r));
      intern_tbl_map_root(&ctx->intern, r, thvar2code(x));
      break;

    case BV_LSHR:
      x = map_bvlshr_to_bv(ctx, bvlshr_term_desc(terms, r));
      intern_tbl_map_root(&ctx->intern, r, thvar2code(x));
      break;

    case BV_ASHR:
      x = map_bvashr_to_bv(ctx, bvashr_term_desc(terms, r));
      intern_tbl_map_root(&ctx->intern, r, thvar2code(x));
      break;

    case POWER_PRODUCT:
      x = map_pprod_to_bv(ctx, pprod_term_desc(terms, r));
      intern_tbl_map_root(&ctx->intern, r, thvar2code(x));
      break;

    case BV64_POLY:
      x = map_bvpoly64_to_bv(ctx, bvpoly64_term_desc(terms, r));
      intern_tbl_map_root(&ctx->intern, r, thvar2code(x));
      break;

    case BV_POLY:
      x = map_bvpoly_to_bv(ctx, bvpoly_term_desc(terms, r));
      intern_tbl_map_root(&ctx->intern, r, thvar2code(x));
      break;

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
    assert(term_of_occ(u) == true_eterm);
    l = mk_lit(const_bvar, polarity_of(u));
    assert((u == true_occ && l == true_literal) ||
	   (u == false_occ && l == false_literal));
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

    case UNINTERPRETED_TERM:
      l = pos_lit(create_boolean_variable(ctx->core));
      break;

    case ITE_TERM:
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

    case DISTINCT_TERM:
      l = map_distinct_to_literal(ctx, distinct_term_desc(terms, r));
      break;

    case BIT_TERM:
      l = map_bit_select_to_literal(ctx, bit_term_desc(terms, r));
      break;

    case BV_EQ_ATOM:
      l = map_bveq_to_literal(ctx, bveq_atom_desc(terms, r));
      break;

    case BV_GE_ATOM:
      l = map_bvge_to_literal(ctx, bvge_atom_desc(terms, r));
      break;

    case BV_SGE_ATOM:
      l = map_bvsge_to_literal(ctx, bvsge_atom_desc(terms, r));
      break;

    default:
      longjmp(ctx->env, INTERNAL_ERROR);
      break;
    }

    // map r to l in the internalization table
    intern_tbl_map_root(&ctx->intern, r, literal2code(l));
  }

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
    assert(g == false_occ || g == true_occ);
    if (g == false_occ) {
      longjmp(ctx->env, TRIVIALLY_UNSAT);
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





/*****************************************************
 *  INTERNALIZATION OF TOP-LEVEL ATOMS AND FORMULAS  *
 ****************************************************/

/*
 * Recursive function: assert (t == tt) for a boolean term t
 * - this is used when a toplevel formula simplifies to t
 *   For example (ite c t u) --> t if c is true.
 * - t is not necessarily a root in the internalization table
 */
static void assert_term(context_t *ctx, term_t t, bool tt);


/*
 * Top-level equality between Boolean terms
 * - if tt is true, assert t1 == t2
 * - if tt is false, assert t1 != t2
 */
static void assert_toplevel_iff(context_t *ctx, term_t t1, term_t t2, bool tt) {
  term_t t;
  literal_t l1, l2;

  /*
   * Apply substitution then try flattening
   */
  t1 = intern_tbl_get_root(&ctx->intern, t1);
  t2 = intern_tbl_get_root(&ctx->intern, t2);
  if (t1 == t2) {
    // (eq t1 t2) is true
    if (!tt) {
      longjmp(ctx->env, TRIVIALLY_UNSAT);
    }
  }
  // try simplification
  t = simplify_bool_eq(ctx, t1, t2);
  if (t != NULL_TERM) {
    // (eq t1 t2) is equivalent to t
    assert_term(ctx, t, tt) ;
  } else {
    // no simplification
    l1 = internalize_to_literal(ctx, t1);
    l2 = internalize_to_literal(ctx, t2);
    assert_iff(&ctx->gate_manager, l1, l2, tt);

#if 0
    if (tt) {
      printf("top assert: (eq ");
      print_literal(stdout, l1);
      printf(" ");
      print_literal(stdout, l2);
      printf(")\n");
    } else {
      printf("top assert: (xor ");
      print_literal(stdout, l1);
      printf(" ");
      print_literal(stdout, l2);
      printf(")\n");
    }
#endif
  }
}

/*
 * Top-level equality assertion (eq t1 t2):
 * - if tt is true, assert (t1 == t2)
 *   if tt is false, assert (t1 != t2)
 */
static void assert_toplevel_eq(context_t *ctx, composite_term_t *eq, bool tt) {
  assert(eq->arity == 2);
  assert(is_boolean_term(ctx->terms, eq->arg[0]) && 
	 is_boolean_term(ctx->terms, eq->arg[1]));

  assert_toplevel_iff(ctx, eq->arg[0], eq->arg[1], tt);
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

  assert(is_bitvector_term(ctx->terms, distinct->arg[0]));
  // translate to bitvectors then assert
  for (i=0; i<n; i++) {
    a[i] = internalize_to_bv(ctx, distinct->arg[i]);
  }
  assert_bv_distinct(ctx, n, a, tt);

  free_istack_array(&ctx->istack, a);
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
 * - it tt is false: assert (not t1) ... (not t_n)
 */
static void assert_toplevel_or(context_t *ctx, composite_term_t *or, bool tt) {
  ivector_t *v;
  int32_t *a;
  uint32_t i, n;

  if (tt) {
    if (context_flatten_or_enabled(ctx)) {
      // Flatten into vector v
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

      for (i=0; i<n; i++) {
        a[i] = internalize_to_literal(ctx, a[i]);
        if (a[i] == true_literal) goto done;
      }

    } else {
      /*
       * No flattening
       */
      n = or->arity;
      a = alloc_istack_array(&ctx->istack, n);
      for (i=0; i<n; i++) {
        a[i] = internalize_to_literal(ctx, or->arg[i]);
        if (a[i] == true_literal) goto done;
      }
    }

    // assert (or a[0] ... a[n-1])
    add_clause(ctx->core, n, a);

  done:
    free_istack_array(&ctx->istack, a);

  } else {
    /*
     * Propagate to children:
     *  (or t_0 ... t_n-1) is false
     * so all children must be false too
     */
    n = or->arity;
    for (i=0; i<n; i++) {
      assert_term(ctx, or->arg[i], false);
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
 * Top-level bit select
 */
static void assert_toplevel_bit_select(context_t *ctx, select_term_t *select, bool tt) {
  term_t t, s;
  thvar_t x;

  /*
   * Check for simplification
   */
  t = intern_tbl_get_root(&ctx->intern, select->arg);
  s = extract_bit(ctx->terms, t, select->idx);
  if (s != NULL_TERM) {
    // (select t i) is s
    assert_term(ctx, s, tt);
  } else {
    // no simplification
    x = internalize_to_bv(ctx, select->arg);
    ctx->bv.set_bit(ctx->bv_solver, x, select->idx, tt);
  }
}


/*
 * Top-level bitvector atoms
 */
static void assert_toplevel_bveq(context_t *ctx, composite_term_t *eq, bool tt) {
  ivector_t *v;
  int32_t *a;
  term_t t, t1, t2;
  thvar_t x, y;
  uint32_t i, n;

  assert(eq->arity == 2);

  t1 = intern_tbl_get_root(&ctx->intern, eq->arg[0]);
  t2 = intern_tbl_get_root(&ctx->intern, eq->arg[1]);
  t = simplify_bitvector_eq(ctx, t1, t2);
  if (t != NULL_TERM) {
    // (bveq t1 t2) is equivalent to t
    assert_term(ctx, t, tt);
    return;
  }

  if (tt) {
    // try to flatten to a conjunction of terms
    v = &ctx->aux_vector;
    assert(v->size == 0);
    if (bveq_flattens(ctx->terms, t1, t2, v)) {
      /*
       * (bveq t1 t2) is equivalent to (and v[0] ... v[k])
       * (bveq t1 t2) is true at the toplevel so v[0] ... v[k] must all be true
       */

      // make a copy of v
      n = v->size;
      a = alloc_istack_array(&ctx->istack, n);
      for (i=0; i<n; i++) {
        a[i] = v->data[i];
      }
      ivector_reset(v);

      // assert
      for (i=0; i<n; i++) {
        assert_term(ctx, a[i], true);
      }

      free_istack_array(&ctx->istack, a);
      return;
    }

    // flattening failed
    ivector_reset(v);
  }

  /*
   * NOTE: asserting (eq t1 t2) in the egraph instead makes things worse
   */
  x = internalize_to_bv(ctx, t1);
  y = internalize_to_bv(ctx, t2);
  ctx->bv.assert_eq_axiom(ctx->bv_solver, x,  y, tt);
}

static void assert_toplevel_bvge(context_t *ctx, composite_term_t *ge, bool tt) {
  thvar_t x, y;

  assert(ge->arity == 2);

  x = internalize_to_bv(ctx, ge->arg[0]);
  y = internalize_to_bv(ctx, ge->arg[1]);
  ctx->bv.assert_ge_axiom(ctx->bv_solver, x,  y, tt);
}

static void assert_toplevel_bvsge(context_t *ctx, composite_term_t *sge, bool tt) {
  thvar_t x, y;

  assert(sge->arity == 2);

  x = internalize_to_bv(ctx, sge->arg[0]);
  y = internalize_to_bv(ctx, sge->arg[1]);
  ctx->bv.assert_sge_axiom(ctx->bv_solver, x,  y, tt);
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
    
  case DISTINCT_TERM:
    assert_toplevel_distinct(ctx, distinct_term_desc(terms, t), tt);
    break;

  case BIT_TERM:
    assert_toplevel_bit_select(ctx, bit_term_desc(terms, t), tt);
    break;

  case BV_EQ_ATOM:
    assert_toplevel_bveq(ctx, bveq_atom_desc(terms, t), tt);
    break;

  case BV_GE_ATOM:
    assert_toplevel_bvge(ctx, bvge_atom_desc(terms, t), tt);
    break;

  case BV_SGE_ATOM:
    assert_toplevel_bvsge(ctx, bvsge_atom_desc(terms, t), tt);
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
     * and it will be internalized/asserted later.
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

    case DISTINCT_TERM:
      assert_toplevel_distinct(ctx, distinct_term_desc(terms, t), tt);
      break;

    case BIT_TERM:
      assert_toplevel_bit_select(ctx, bit_term_desc(terms, t), tt);
      break;

    case BV_EQ_ATOM:
      assert_toplevel_bveq(ctx, bveq_atom_desc(terms, t), tt);
      break;

    case BV_GE_ATOM:
      assert_toplevel_bvge(ctx, bvge_atom_desc(terms, t), tt);
      break;

    case BV_SGE_ATOM:
      assert_toplevel_bvsge(ctx, bvsge_atom_desc(terms, t), tt);
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
static const uint32_t arch2theories[NUM_ARCH] = {
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
  UF_MASK|BV_MASK|ARITH_MASK,  //  CTX_ARCH_EGSPLXBV
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

static const uint8_t arch_components[NUM_ARCH] = {
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
  EGRPH|SPLX|BVSLVR,        //  CTX_ARCH_EGSPLXBV
  EGRPH|SPLX|BVSLVR|FSLVR,  //  CTX_ARCH_EGFUNSPLXBV

  0,                        //  CTX_ARCH_AUTO_IDL
  0,                        //  CTX_ARCH_AUTO_RDL
};


/*
 * Smt mode for a context mode
 */
static const smt_mode_t core_mode[NUM_MODES] = {
  SMT_MODE_BASIC,       // one check
  SMT_MODE_BASIC,       // multichecks
  SMT_MODE_PUSHPOP,     // push/pop
  SMT_MODE_INTERACTIVE, // interactive
};


/*
 * Flags for a context mode
 */
static const uint32_t mode2options[NUM_MODES] = {
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
  donothing,        // clear
};


// for the smt interface, nothing should be called since there are no atoms
static th_smt_interface_t null_smt = {
  NULL, NULL, NULL, NULL, NULL,
};





/****************************
 *  SOLVER INITIALIZATION   *
 ***************************/

/*
 * Create the bitvector solver
 * - attach it to the egraph if there's an egraph
 * - attach it to the core and initialize the core otherwise
 */
static void create_bv_solver(context_t *ctx) {
  bv_solver_t *solver;
  smt_mode_t cmode;

  assert(ctx->bv_solver == NULL && ctx->core != NULL);

  cmode = core_mode[ctx->mode];
  solver = (bv_solver_t *) safe_malloc(sizeof(bv_solver_t));
  init_bv_solver(solver, ctx->core);

  // attach to the core and initialize the core
  init_smt_core(ctx->core, CTX_DEFAULT_CORE_SIZE, solver, bv_solver_ctrl_interface(solver),
		bv_solver_smt_interface(solver), cmode);
  // EXPERIMENT
  //  smt_core_make_etable(ctx->core);
  // END

  bv_solver_init_jmpbuf(solver, &ctx->env);
  ctx->bv_solver = solver;
  ctx->bv = *bv_solver_bv_interface(solver);
}



/*
 * Allocate and initialize solvers based on architecture and mode
 * - core and gate manager must exist at this point
 * - if the architecture is either AUTO_IDL or AUTO_RDL, no theory solver
 *   is allocated yet, and the core is initialized for Boolean only
 * - otherwise, all components are ready and initialized, including the core.
 */
static void init_solvers(context_t *ctx) {
  uint8_t solvers;
  smt_core_t *core;
  smt_mode_t cmode;

  solvers = arch_components[ctx->arch];

  ctx->bv_solver = NULL;

  // Bitvector solver
  if (solvers & BVSLVR) {
    create_bv_solver(ctx);
  }

  /*
   * At this point all solvers are ready and initialized, except the
   * core if there are* no solvers, or if arch is AUTO_IDL or AUTO_RDL.
   */
  cmode = core_mode[ctx->mode];   // initialization mode for the core
  core = ctx->core;
  if (solvers == 0) {
    /*
     * Boolean solver only. If arch if AUTO_IDL or AUTO_RDL, the
     * theory solver will be changed lated by create_auto_idl_solver
     * or create_auto_rdl_solver.
     */
    assert(ctx->bv_solver == NULL);
    init_smt_core(core, CTX_DEFAULT_CORE_SIZE, NULL, &null_ctrl, &null_smt, cmode);
  }

  /*
   * Optimization: if the arch is NOSOLVERS or BV then we set bool_only in the core
   */
  if (ctx->arch == CTX_ARCH_NOSOLVERS || ctx->arch == CTX_ARCH_BV) {
    smt_core_set_bool_only(core);
  }
}





/*****************************
 *  CONTEXT INITIALIZATION   *
 ****************************/

/*
 * Check mode and architecture
 */
#ifndef NDEBUG
static inline bool valid_mode(context_mode_t mode) {
  return CTX_MODE_ONECHECK <= mode && mode <= CTX_MODE_INTERACTIVE;
}

static inline bool valid_arch(context_arch_t arch) {
  return CTX_ARCH_NOSOLVERS <= arch && arch <= CTX_ARCH_BV;
}
#endif


/*
 * Initialize ctx for the given mode and architecture
 * - terms = term table for that context
 * - qflag = true means quantifiers allowed
 * - qflag = false means no quantifiers
 */
void init_context(context_t *ctx, term_table_t *terms, smt_logic_t logic,
                  context_mode_t mode, context_arch_t arch, bool qflag) {
  assert(valid_mode(mode) && valid_arch(arch));

  /*
   * Set architecture and options
   */
  ctx->mode = mode;
  ctx->arch = arch;
  ctx->logic = logic;
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
  ctx->bv_solver = NULL;

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
  init_ivector(&ctx->aux_eqs, CTX_DEFAULT_VECTOR_SIZE);
  init_ivector(&ctx->aux_atoms, CTX_DEFAULT_VECTOR_SIZE);
  init_ivector(&ctx->aux_vector, CTX_DEFAULT_VECTOR_SIZE);
  init_int_queue(&ctx->queue, 0);
  init_istack(&ctx->istack);
  init_sharing_map(&ctx->sharing, &ctx->intern);
  init_objstore(&ctx->cstore, sizeof(conditional_t), 32);

  ctx->subst = NULL;
  ctx->marks = NULL;
  ctx->cache = NULL;
  ctx->small_cache = NULL;
  ctx->eq_cache = NULL;
  ctx->explorer = NULL;

  init_bvconstant(&ctx->bv_buffer);

  ctx->trace = NULL;

  /*
   * Allocate and initialize the solvers and core
   * NOTE: no theory solver yet if arch is AUTO_IDL or AUTO_RDL
   */
  init_solvers(ctx);
}




/*
 * Delete ctx
 */
void delete_context(context_t *ctx) {
  if (ctx->core != NULL) {
    delete_smt_core(ctx->core);
    safe_free(ctx->core);
    ctx->core = NULL;
  }

  if (ctx->bv_solver != NULL) {
    delete_bv_solver(ctx->bv_solver);
    safe_free(ctx->bv_solver);
    ctx->bv_solver = NULL;
  }

  delete_gate_manager(&ctx->gate_manager);

  delete_intern_tbl(&ctx->intern);
  delete_ivector(&ctx->top_eqs);
  delete_ivector(&ctx->top_atoms);
  delete_ivector(&ctx->top_formulas);
  delete_ivector(&ctx->top_interns);

  delete_ivector(&ctx->subst_eqs);
  delete_ivector(&ctx->aux_eqs);
  delete_ivector(&ctx->aux_atoms);
  delete_ivector(&ctx->aux_vector);
  delete_int_queue(&ctx->queue);
  delete_istack(&ctx->istack);
  delete_sharing_map(&ctx->sharing);
  delete_objstore(&ctx->cstore);

  context_free_subst(ctx);
  context_free_marks(ctx);
  context_free_cache(ctx);
  context_free_small_cache(ctx);
  context_free_eq_cache(ctx);
  context_free_explorer(ctx);

  delete_bvconstant(&ctx->bv_buffer);
}



/*
 * Reset: remove all assertions and clear all internalization tables
 */
void reset_context(context_t *ctx) {
  ctx->base_level = 0;

  reset_smt_core(ctx->core); // this propagates reset to all solvers

  reset_gate_manager(&ctx->gate_manager);

  reset_intern_tbl(&ctx->intern);
  ivector_reset(&ctx->top_eqs);
  ivector_reset(&ctx->top_atoms);
  ivector_reset(&ctx->top_formulas);
  ivector_reset(&ctx->top_interns);

  // Force the internalization mapping for true and false
  intern_tbl_map_root(&ctx->intern, true_term, bool2code(true));

  ivector_reset(&ctx->subst_eqs);
  ivector_reset(&ctx->aux_eqs);
  ivector_reset(&ctx->aux_atoms);
  ivector_reset(&ctx->aux_vector);
  int_queue_reset(&ctx->queue);
  reset_istack(&ctx->istack);
  reset_sharing_map(&ctx->sharing);
  reset_objstore(&ctx->cstore);

  context_free_subst(ctx);
  context_free_marks(ctx);
  context_reset_small_cache(ctx);
  context_reset_eq_cache(ctx);
  context_reset_explorer(ctx);
}


/*
 * Add tracer to ctx and ctx->core
 */
void context_set_trace(context_t *ctx, tracer_t *trace) {
  assert(ctx->trace == NULL);
  ctx->trace = trace;
  smt_core_set_trace(ctx->core, trace);
}


/*
 * Push and pop
 */
void context_push(context_t *ctx) {
  assert(context_supports_pushpop(ctx));
  smt_push(ctx->core);  // propagates to all solvers
  gate_manager_push(&ctx->gate_manager);
  intern_tbl_push(&ctx->intern);
  context_eq_cache_push(ctx);

  ctx->base_level ++;
}

void context_pop(context_t *ctx) {
  assert(context_supports_pushpop(ctx) && ctx->base_level > 0);
  smt_pop(ctx->core);   // propagates to all solvers
  gate_manager_pop(&ctx->gate_manager);
  intern_tbl_pop(&ctx->intern);
  context_eq_cache_pop(ctx);

  ctx->base_level --;
}





/****************************
 *   ASSERTIONS AND CHECK   *
 ***************************/

/*
 * Build the sharing data
 * - processes all the assertions in vectors top_eqs, top_atoms, top_formulas
 * - this function should be called after building the substitutions
 */
static void context_build_sharing_data(context_t *ctx) {
  sharing_map_t *map;

  map = &ctx->sharing;
  reset_sharing_map(map);
  sharing_map_add_terms(map, ctx->top_eqs.data, ctx->top_eqs.size);
  sharing_map_add_terms(map, ctx->top_atoms.data, ctx->top_atoms.size);
  sharing_map_add_terms(map, ctx->top_formulas.data, ctx->top_formulas.size);
}

/*
 * Flatten and internalize assertions a[0 ... n-1]
 * - all elements a[i] must be valid boolean term in ctx->terms
 * - return code:
 *   TRIVIALLY_UNSAT if there's an easy contradiction
 *   CTX_NO_ERROR if the assertions were processed without error
 *   a negative error code otherwise.
 */
static int32_t context_process_assertions(context_t *ctx, uint32_t n, const term_t *a) {
  ivector_t *v;
  uint32_t i;
  int code;

  ivector_reset(&ctx->top_eqs);
  ivector_reset(&ctx->top_atoms);
  ivector_reset(&ctx->top_formulas);
  ivector_reset(&ctx->top_interns);
  ivector_reset(&ctx->subst_eqs);
  ivector_reset(&ctx->aux_eqs);
  ivector_reset(&ctx->aux_atoms);

  code = setjmp(ctx->env);
  if (code == 0) {
    // flatten
    for (i=0; i<n; i++) {
      flatten_assertion(ctx, a[i]);
    }

    /*
     * At this point, the assertions are stored into the vectors
     * top_eqs, top_atoms, top_formulas, and top_interns
     * - more top-level equalities may be in subst_eqs
     * - ctx->intern stores the internalized terms and the variable
     *   substitutions.
     */

    /*
     * Process the candidate variable substitutions if any
     */
    if (ctx->subst_eqs.size > 0) {
      context_process_candidate_subst(ctx);
    }

    /*
     * Sharing
     */
    context_build_sharing_data(ctx);

    /*
     * Notify the core + solver(s)
     */
    internalization_start(ctx->core);

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
    ivector_reset(&ctx->aux_vector);
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
int32_t assert_formulas(context_t *ctx, uint32_t n, const term_t *f) {
  int32_t code;

  assert(ctx->arch == CTX_ARCH_AUTO_IDL ||
         ctx->arch == CTX_ARCH_AUTO_RDL ||
         smt_status(ctx->core) == STATUS_IDLE);

  code = context_process_assertions(ctx, n, f);
  if (code == TRIVIALLY_UNSAT) {
    if( smt_status(ctx->core) != STATUS_UNSAT) {
      // force UNSAT in the core
      add_empty_clause(ctx->core);
      ctx->core->status = STATUS_UNSAT;
    }
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
 * Convert boolean term t to a literal l in context ctx
 * - t must be a boolean term
 * - return a negative code if there's an error
 * - return a literal (l >= 0) otherwise.
 */
int32_t context_internalize(context_t *ctx, term_t t) {
  int code;
  literal_t l;

  ivector_reset(&ctx->top_eqs);
  ivector_reset(&ctx->top_atoms);
  ivector_reset(&ctx->top_formulas);
  ivector_reset(&ctx->top_interns);
  ivector_reset(&ctx->subst_eqs);
  ivector_reset(&ctx->aux_eqs);

  code = setjmp(ctx->env);
  if (code == 0) {
    l = internalize_to_literal(ctx, t);
  } else {
    assert(code < 0);
    /*
     * Clean up
     */
    ivector_reset(&ctx->aux_vector);
    reset_istack(&ctx->istack);
    int_queue_reset(&ctx->queue);
    context_free_subst(ctx);
    context_free_marks(ctx);
    l = code;
  }

  return l;
}


/*
 * PROVISIONAL: FOR TESTING/DEBUGGING
 */

/*
 * Preprocess formula f or array of formulas f[0 ... n-1]
 * - this does flattening + build substitutions
 * - return code: as in assert_formulas
 * - the result is stored in the internal vectors
 *     ctx->top_interns
 *     ctx->top_eqs
 *     ctx->top_atoms
 *     ctx->top_formulas
 *   + ctx->intern stores substitutions
 */
int32_t context_process_formulas(context_t *ctx, uint32_t n, term_t *f) {
  uint32_t i;
  int code;

  ivector_reset(&ctx->top_eqs);
  ivector_reset(&ctx->top_atoms);
  ivector_reset(&ctx->top_formulas);
  ivector_reset(&ctx->top_interns);
  ivector_reset(&ctx->subst_eqs);
  ivector_reset(&ctx->aux_eqs);
  ivector_reset(&ctx->aux_atoms);

  code = setjmp(ctx->env);
  if (code == 0) {
    // flatten
    for (i=0; i<n; i++) {
      flatten_assertion(ctx, f[i]);
    }

    /*
     * At this point, the assertions are stored into the vectors
     * top_eqs, top_atoms, top_formulas, and top_interns
     * - more top-level equalities may be in subst_eqs
     * - ctx->intern stores the internalized terms and the variable
     *   substitutions.
     */

    /*
     * Process the candidate variable substitutions if any
     */
    if (ctx->subst_eqs.size > 0) {
      context_process_candidate_subst(ctx);
    }

    /*
     * Sharing
     */
    context_build_sharing_data(ctx);

    code = CTX_NO_ERROR;

  } else {
    /*
     * Exception: return from longjmp(ctx->env, code);
     */
    ivector_reset(&ctx->aux_vector);
    reset_istack(&ctx->istack);
    int_queue_reset(&ctx->queue);
    context_free_subst(ctx);
    context_free_marks(ctx);
  }

  return code;
}

int32_t context_process_formula(context_t *ctx, term_t f) {
  return context_process_formulas(ctx, 1, &f);
}



/*
 * The search function 'check_context' is defined in context_solver.c
 */


/*
 * Interrupt the search
 */
void context_stop_search(context_t *ctx) {
  stop_search(ctx->core);
}



/*
 * Cleanup: restore ctx to a good state after check_context
 * is interrupted.
 */
void context_cleanup(context_t *ctx) {
  // restore the state to IDLE, propagate to all solvers (via pop)
  assert(context_supports_cleaninterrupt(ctx));
  smt_cleanup(ctx->core);
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



/*
 * Clear_unsat: prepare for pop if the status is UNSAT
 * - if clean interrupt is enabled, then there may be a mismatch between
 *   the context's base_level and the core base_level.
 * - it's possible to have ctx->core.base_level = ctx->base_level + 1
 * - this happens because start_search in smt_core does an internal smt_push
 *   to allow the core to be restored to a clean state if search is interrupted.
 * - if search is not interrupted and the search returns UNSAT, then we're
 *   in a state with core base level = context base level + 1.
 */
void context_clear_unsat(context_t *ctx) {
  if (smt_base_level(ctx->core) > ctx->base_level) {
    assert(smt_base_level(ctx->core) == ctx->base_level + 1);
    smt_clear_unsat(ctx->core);
  }

  assert(smt_base_level(ctx->core) == ctx->base_level);
}



/*
 * Add the blocking clause to ctx
 * - ctx->status must be either SAT or UNKNOWN
 * - this collects all decision literals in the current truth assignment
 *   (say l_1, ..., l_k) then clears the current assignment and adds the
 *  clause ((not l_1) \/ ... \/ (not l_k)).
 *
 * Return code:
 * - TRIVIALLY_UNSAT: means that the blocking clause is empty (i.e., k = 0)
 *   (in that case, the context status is set to UNSAT)
 * - CTX_NO_ERROR: means that the blocking clause is not empty (i.e., k > 0)
 *   (In this case, the context status is set to IDLE)
 */
int32_t assert_blocking_clause(context_t *ctx) {
  ivector_t *v;
  uint32_t i, n;
  int32_t code;

  assert(smt_status(ctx->core) == STATUS_SAT ||
         smt_status(ctx->core) == STATUS_UNKNOWN);

  // get decision literals and build the blocking clause
  v = &ctx->aux_vector;
  assert(v->size == 0);
  collect_decision_literals(ctx->core, v);
  n = v->size;
  for (i=0; i<n; i++) {
    v->data[i] = not(v->data[i]);
  }

  // prepare for the new assertion + notify solvers of a new assertion
  context_clear(ctx);
  internalization_start(ctx->core);

  // add the blocking clause
  add_clause(ctx->core, n, v->data);
  ivector_reset(v);

  // force UNSAT if n = 0
  code = CTX_NO_ERROR;
  if (n == 0) {
    code = TRIVIALLY_UNSAT;
    ctx->core->status = STATUS_UNSAT;
  }

  assert(n == 0 || smt_status(ctx->core) == STATUS_IDLE);

  return code;
}




/********************************
 *  GARBAGE COLLECTION SUPPORT  *
 *******************************/

/*
 * Marker for all terms present in the eq_map
 * - aux = the relevant term table.
 * - each record p stores <k0, k1, val> where k0 and k1 are both
 *   terms in aux and val is a literal in the core
 */
static void ctx_mark_eq(void *aux, const pmap2_rec_t *p) {
  term_table_set_gc_mark(aux, index_of(p->k0));
  term_table_set_gc_mark(aux, index_of(p->k1));
}


/*
 * Go through all data structures in ctx and mark all terms and types
 * that they use.
 */
void context_gc_mark(context_t *ctx) {
  intern_tbl_gc_mark(&ctx->intern);

  // empty all the term vectors to be safe
  ivector_reset(&ctx->top_eqs);
  ivector_reset(&ctx->top_atoms);
  ivector_reset(&ctx->top_formulas);
  ivector_reset(&ctx->top_interns);
  ivector_reset(&ctx->subst_eqs);
  ivector_reset(&ctx->aux_eqs);

  if (ctx->eq_cache != NULL) {
    pmap2_iterate(ctx->eq_cache, ctx->terms, ctx_mark_eq);
  }
}
