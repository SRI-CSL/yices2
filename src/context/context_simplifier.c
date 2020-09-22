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
 * SIMPLIFICATIONS AND PREPROCESSING OF ASSERTIONS
 *
 * This module implements preprocessing and simplification procedures
 * that do not depend on the solvers used. These procedures used to be
 * in context.c. Moved them to this new module created in February 2013.
 */

#include "context/conditional_definitions.h"
#include "context/context_simplifier.h"
#include "context/context_utils.h"
#include "context/internalization_codes.h"
#include "context/eq_learner.h"
#include "context/symmetry_breaking.h"
#include "terms/bvfactor_buffers.h"
#include "terms/poly_buffer_terms.h"
#include "terms/power_products.h"
#include "terms/rba_buffer_terms.h"
#include "terms/term_utils.h"


#define TRACE_SUBST  0
#define TRACE_EQ_ABS 0
#define TRACE_DL     0

#define TRACE_SYM_BREAKING 0

#if TRACE_SUBST || TRACE_EQ_ABS || TRACE_DL || TRACE_SYM_BREAKING

#include <stdio.h>
#include <inttypes.h>

#include "io/term_printer.h"
#include "terms/bv64_constants.h"

#endif



/*****************************
 *  FORMULA SIMPLIFICATION   *
 ****************************/

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

    // DJ: We're passing true for simplify_ite?
    if (arith_term_is_nonneg(terms, x, true) &&
        arith_term_is_negative(terms, y, true)) {
      return d->arg[0];
    }

    if (arith_term_is_negative(terms, x, true) &&
        arith_term_is_nonneg(terms, y, true)) {
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

    if (x == zero_term && arith_term_is_nonzero(terms, y, true)) {
      return d->arg[0];
    }

    if (y == zero_term && arith_term_is_nonzero(terms, x, true)) {
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

    if (x == t2 && disequal_arith_terms(terms, y, t2, true)) {
      return d->arg[0];
    }

    if (y == t2 && disequal_arith_terms(terms, x, t2, true)) {
      return opposite_term(d->arg[0]);
    }
  }

  if (is_ite_term(terms, t2)) {
    // symmetric case
    d = ite_term_desc(terms, t2);
    x = intern_tbl_get_root(&ctx->intern, d->arg[1]);
    y = intern_tbl_get_root(&ctx->intern, d->arg[2]);

    if (x == t1 && disequal_arith_terms(terms, y, t1, true)) {
      return d->arg[0];
    }

    if (y == t1 && disequal_arith_terms(terms, x, t1, true)) {
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


/*
 * Try arithmetic/rewriting simplifications for (t1 == t2)
 * - t1 and t2 must be root terms in the internalization table
 * - the result is stored in *r
 * - if r->code is REDUCED then (t1 == t2) is equivalent to (u1 == u2)
 *   the two terms u1 and u2 are stored in r->left and r->right.
 * - if r->code is REDUCED0 then (t1 == t2) is equivalent to (u1 == 0)
 *   u1 is stored in r->left and NULL_TERM is stored in r->right.
 */
void try_arithmetic_bveq_simplification(context_t *ctx, bveq_simp_t *r, term_t t1, term_t t2) {
  term_table_t *terms;
  bvpoly_buffer_t *b;
  uint32_t n;
  term_t u1, u2;

  terms = ctx->terms;

  r->code = BVEQ_CODE_NOCHANGE;

  if (is_bvpoly_term(terms, t1) || is_bvpoly_term(terms, t2)) {
    b = context_get_bvpoly_buffer(ctx);
    n = term_bitsize(terms, t1);

    reset_bvpoly_buffer(b, n);
    add_bvterm_to_buffer(terms, t1, b);
    sub_bvterm_from_buffer(terms, t2, b);
    normalize_bvpoly_buffer(b);

    if (bvpoly_buffer_is_zero(b)) {
      r->code = BVEQ_CODE_TRUE;
    } else if (bvpoly_buffer_is_constant(b)) {
      r->code = BVEQ_CODE_FALSE;
    } else if (bvpoly_buffer_is_pm_var(b, &u1)) {
      r->code = BVEQ_CODE_REDUCED0;
      r->left = u1;
      r->right = NULL_TERM;
    } else if (bvpoly_buffer_is_var_minus_var(b, &u1, &u2)) {
      r->code = BVEQ_CODE_REDUCED;
      r->left = u1;
      r->right = u2;
    }
  }
}



/*
 * SIMPLIFICATION OF EQUALITY USING FACTORING
 */

#if 0

/*
 * Print
 */
static void show_factors(bvfactor_buffer_t *b) {
  pprod_t *aux;
  bvpoly64_t *p;
  bvpoly_t *q;

  printf("constant: ");
  if (b->bitsize <= 64) {
    bvconst64_print(stdout, b->constant64, b->bitsize);
  } else {
    bvconst_print(stdout, b->constant.data, b->bitsize);
  }
  printf("\nproduct: ");
  aux = pp_buffer_getprod(&b->product);
  print_pprod(stdout, aux);
  free_pprod(aux);
  printf("\nexponent: ");
  if (b->bitsize <= 64) {
    p = bvpoly_buffer_getpoly64(&b->exponent);
    print_bvpoly64(stdout, p);
    free_bvpoly64(p);
  } else {
    q = bvpoly_buffer_getpoly(&b->exponent);
    print_bvpoly(stdout, q);
    free_bvpoly(q);
  }
  printf("\n");
}

static void show_bvfactoring(bvfactoring_t *r) {
  uint32_t i;

  printf("\n--- reduced 1 ---\n");
  for (i=0; i<r->n1; i++) {
    printf("reduced1[%"PRIu32"]\n", i);
    show_factors(r->reduced1 + i);
    printf("\n");
  }

  printf("--- reduced 2 ---\n");
  for (i=0; i<r->n2; i++) {
    printf("reduced2[%"PRIu32"]\n", i);
    show_factors(r->reduced2 + i);
    printf("\n");
  }

  fflush(stdout);
}

static void show_product(pp_buffer_t *f) {
  pprod_t *pp;

  pp = pp_buffer_getprod(f);
  print_pprod(stdout, pp);
  free_pprod(pp);

  fflush(stdout);
}

#endif

/*
 * Factoring buffers:
 * - initialize: just set code to BVFACTOR_TODO
 * - other fields are initialized lazily
 */
void init_bvfactoring(bvfactoring_t *r) {
  r->code = BVFACTOR_TODO;
  r->bitsize = 0;
  r->poly_buffer = NULL;
  r->pp_buffer = NULL;
}


/*
 * Delete buffers
 */
void delete_bvfactoring(bvfactoring_t *r) {
  uint32_t i;

  if (r->code != BVFACTOR_TODO) {
    delete_bvfactor_buffer(&r->common);
    for (i=0; i<r->n1; i++) {
      delete_bvfactor_buffer(r->reduced1+i);
    }
    for (i=0; i<r->n2; i++) {
      delete_bvfactor_buffer(r->reduced2+i);
    }
    r->code = BVFACTOR_TODO;
  }

  if (r->poly_buffer != NULL) {
    delete_bvpoly_buffer(r->poly_buffer);
    safe_free(r->poly_buffer);
    r->poly_buffer = NULL;
  }

  if (r->pp_buffer != NULL) {
    delete_pp_buffer(r->pp_buffer);
    safe_free(r->pp_buffer);
    r->pp_buffer = NULL;
  }
}


/*
 * Allocate the auxiliary buffers
 */
static bvpoly_buffer_t *factoring_get_poly_buffer(bvfactoring_t *r) {
  bvpoly_buffer_t *p;

  p = r->poly_buffer;
  if (p == NULL) {
    p =  (bvpoly_buffer_t *) safe_malloc(sizeof(bvpoly_buffer_t));
    init_bvpoly_buffer(p);
    r->poly_buffer = p;
  }

  return p;
}

static pp_buffer_t *factoring_get_pp_buffer(bvfactoring_t *r) {
  pp_buffer_t *p;

  p = r->pp_buffer;
  if (p == NULL) {
    p = (pp_buffer_t *) safe_malloc(sizeof(pp_buffer_t));
    init_pp_buffer(p, 4);
    r->pp_buffer = p;
  }

  return p;
}



/*
 * Prepare: allocate buffers
 * - n1 = number of buffers for reduced1
 * - n2 = number of buffers for reduced2
 * - bitsize = number of bits
 */
static void prepare_bvfactoring(bvfactoring_t *r, uint32_t bitsize, uint32_t n1, uint32_t n2) {
  uint32_t i;

  assert(0 < n1 && n1 <= MAX_BVFACTORS);
  assert(0 < n2 && n2 <= MAX_BVFACTORS);
  assert(r->code == BVFACTOR_TODO);

  r->code = BVFACTOR_FAILED; // safe default
  r->bitsize = bitsize;
  r->n1 = n1;
  r->n2 = n2;
  init_bvfactor_buffer(&r->common);
  for (i=0; i<n1; i++) {
    init_bvfactor_buffer(r->reduced1 + i);
  }
  for (i=0; i<n2; i++) {
    init_bvfactor_buffer(r->reduced2 + i);
  }
}


/*
 * Compute factors of t
 */
static void factoring_set_left_term(bvfactoring_t *r, term_table_t *terms, term_t t) {
  assert(r->n1 >= 1);
  factor_bvterm(terms, t, r->reduced1);
}

static void factoring_set_right_term(bvfactoring_t *r, term_table_t *terms, term_t t) {
  assert(r->n2 >= 1);
  factor_bvterm(terms, t, r->reduced2);
}

/*
 * Add factors of p to r->reduced1
 */
static void factoring_set_right_poly64(bvfactoring_t *r, term_table_t *terms, bvpoly64_t *p) {
  assert(p->nterms <= r->n2);
  factor_bvpoly64_monomials(terms, p, r->reduced2);
}

static void factoring_set_right_poly(bvfactoring_t *r, term_table_t *terms, bvpoly_t *p) {
  assert(p->nterms <= r->n2);
  factor_bvpoly_monomials(terms, p, r->reduced2);
}


/*
 * Try to expand:
 * - if a factor is of the form  c * var * 2^e and var is a small polynomial,
 *   we can try to expand var and see if that reveals more factors.
 * - return true if this works
 */

// extend r->reduced1 from size 1 to size n. Copy r->reduced[0] in the new elements
static void bvfactoring_expand_left(bvfactoring_t *r, uint32_t n) {
  uint32_t i;

  assert(r->n1 == 1 && n <= MAX_BVFACTORS);
  r->n1 = n;
  for (i=1; i<n; i++) {
    bvfactor_buffer_init_copy(r->reduced1 + i, r->reduced1);
  }
}

// extend r->reduced2 from size 1 to size n. Copy r->reduced[0] in the new elements
static void bvfactoring_expand_right(bvfactoring_t *r, uint32_t n) {
  uint32_t i;

  assert(r->n2 == 1 && n <= MAX_BVFACTORS);
  r->n2 = n;
  for (i=1; i<n; i++) {
    bvfactor_buffer_init_copy(r->reduced2 + i, r->reduced2);
  }
}

// try to replace t by p in r->reduced1
static bool try_left_replace64(bvfactoring_t *r, term_table_t *terms, term_t t, bvpoly64_t *p) {
  uint32_t i;

  assert(r->n1 == 1 && bvfactor_buffer_is_var(r->reduced1) && t == bvfactor_buffer_get_var(r->reduced1));

  if (p->nterms <= MAX_BVFACTORS) {
    bvfactor_buffer_reduce_by_var(r->reduced1, t);
    bvfactoring_expand_left(r, p->nterms);
    assert(r->n1 == p->nterms);
    i = 0;
    if (p->mono[0].var == const_idx) {
      bvfactor_buffer_mulconst64(r->reduced1, p->mono[i].coeff, 1);
      bvfactor_buffer_normalize(r->reduced1);
      i = 1;
    }
    while (i<r->n1) {
      factor_mul_bvterm64(terms, p->mono[i].coeff, p->mono[i].var, r->reduced1 + i);
      i ++;
    }
    return true;
  }

  return false;
}

static bool try_left_replace(bvfactoring_t *r, term_table_t *terms, term_t t, bvpoly_t *p) {
  uint32_t i;

  assert(r->n1 == 1 && bvfactor_buffer_is_var(r->reduced1) && t == bvfactor_buffer_get_var(r->reduced1));

  if (p->nterms <= MAX_BVFACTORS) {
    bvfactor_buffer_reduce_by_var(r->reduced1, t);
    bvfactoring_expand_left(r, p->nterms);
    assert(r->n1 == p->nterms);
    i = 0;
    if (p->mono[0].var == const_idx) {
      bvfactor_buffer_mulconst(r->reduced1, p->mono[i].coeff, 1);
      bvfactor_buffer_normalize(r->reduced1);
      i = 1;
    }
    while (i<r->n1) {
      factor_mul_bvterm(terms, p->mono[i].coeff, p->mono[i].var, r->reduced1 + i);
      i ++;
    }
    return true;
  }

  return false;
}

// try to replace t by p in r->reduced2
static bool try_right_replace64(bvfactoring_t *r, term_table_t *terms, term_t t, bvpoly64_t *p) {
  uint32_t i;

  assert(r->n2 == 1 && bvfactor_buffer_is_var(r->reduced2) && t == bvfactor_buffer_get_var(r->reduced2));

  if (p->nterms <= MAX_BVFACTORS) {
    bvfactor_buffer_reduce_by_var(r->reduced2, t);
    bvfactoring_expand_right(r, p->nterms);
    assert(r->n2 == p->nterms);
    i = 0;
    if (p->mono[0].var == const_idx) {
      bvfactor_buffer_mulconst64(r->reduced2, p->mono[i].coeff, 1);
      bvfactor_buffer_normalize(r->reduced2);
      i = 1;
    }
    while (i<r->n2) {
      factor_mul_bvterm64(terms, p->mono[i].coeff, p->mono[i].var, r->reduced2 + i);
      i ++;
    }
    return true;
  }

  return false;
}

static bool try_right_replace(bvfactoring_t *r, term_table_t *terms, term_t t, bvpoly_t *p) {
  uint32_t i;

  assert(r->n2 == 1 && bvfactor_buffer_is_var(r->reduced2) && t == bvfactor_buffer_get_var(r->reduced2));

  if (p->nterms <= MAX_BVFACTORS) {
    bvfactor_buffer_reduce_by_var(r->reduced2, t);
    bvfactoring_expand_right(r, p->nterms);
    assert(r->n2 == p->nterms);
    i = 0;
    if (p->mono[0].var == const_idx) {
      bvfactor_buffer_mulconst(r->reduced2, p->mono[i].coeff, 1);
      bvfactor_buffer_normalize(r->reduced2);
      i = 1;
    }
    while (i<r->n2) {
      factor_mul_bvterm(terms, p->mono[i].coeff, p->mono[i].var, r->reduced2 + i);
      i ++;
    }
    return true;
  }

  return false;
}


static bool try_left_expansion(bvfactoring_t *r, term_table_t *terms) {
  term_t t;
  term_kind_t kind;

  if (r->n1 == 1 && bvfactor_buffer_is_var(r->reduced1)) {
    t = bvfactor_buffer_get_var(r->reduced1);
    kind = term_kind(terms, t);
    if (kind == BV64_POLY) {
      return try_left_replace64(r, terms, t, bvpoly64_term_desc(terms, t));
    } else if (kind == BV_POLY) {
      return try_left_replace(r, terms, t, bvpoly_term_desc(terms, t));
    }
  }

  return false;
}

static bool try_right_expansion(bvfactoring_t *r, term_table_t *terms) {
  term_t t;
  term_kind_t kind;

  if (r->n2 == 1 && bvfactor_buffer_is_var(r->reduced2)) {
    t = bvfactor_buffer_get_var(r->reduced2);
    kind = term_kind(terms, t);
    if (kind == BV64_POLY) {
      return try_right_replace64(r, terms, t, bvpoly64_term_desc(terms, t));
    } else if (kind == BV_POLY) {
      return try_right_replace(r, terms, t, bvpoly_term_desc(terms, t));
    }
  }

  return false;
}



/*
 * Check whether both reduced parts of r are linear
 * - ignore exponents
 */
static bool linear_reduced_factoring(bvfactoring_t *r) {
  uint32_t i;

  for (i=0; i<r->n1; i++) {
    if (! bvfactor_buffer_is_linear(r->reduced1 + i)) {
      return false;
    }
  }

  for (i=0; i<r->n2; i++) {
    if (! bvfactor_buffer_is_linear(r->reduced2 + i)) {
      return false;
    }
  }

  return true;
}

/*
 * Check whether both reduced parts of r have the same exponent
 */
static bool factoring_has_unique_exponent(bvfactoring_t *r) {
  uint32_t i;
  bvfactor_buffer_t *f0;

  assert(r->n1 > 0 && r->n2 > 0);
  f0 = r->reduced1;

  for (i=1; i<r->n1; i++) {
    if (! bvfactor_buffer_equal_exponents(f0, r->reduced1 + i)) {
      return false;
    }
  }

  for (i=0; i<r->n2; i++) {
    if (! bvfactor_buffer_equal_exponents(f0, r->reduced2 + i)) {
      return false;
    }
  }

  return true;
}



/*
 * Add factor f to buffer b:
 * - ignore the exponent of f
 * - f must be linear
 */
static void bvpoly_buffer_add_factor64(bvpoly_buffer_t *b, term_table_t *terms, bvfactor_buffer_t *f) {
  term_t t;

  assert(bvfactor_buffer_is_linear(f));
  assert(b->bitsize == f->bitsize && f->bitsize <= 64);

  if (bvfactor_buffer_product_is_one(f)) {
    bvpoly_buffer_add_const64(b, f->constant64);
  } else {
    t = bvfactor_buffer_get_var(f);
    addmul_bvterm64_to_buffer(terms, t, f->constant64, b);
  }
}

static void bvpoly_buffer_add_factor(bvpoly_buffer_t *b, term_table_t *terms, bvfactor_buffer_t *f) {
  term_t t;

  assert(bvfactor_buffer_is_linear(f));
  assert(b->bitsize == f->bitsize && f->bitsize > 64);

  if (bvfactor_buffer_product_is_one(f)) {
    bvpoly_buffer_add_constant(b, f->constant.data);
  } else {
    t = bvfactor_buffer_get_var(f);
    addmul_bvterm_to_buffer(terms, t, f->constant.data, b);
  }
}


/*
 * Subtract f from b
 */
static void bvpoly_buffer_sub_factor64(bvpoly_buffer_t *b, term_table_t *terms, bvfactor_buffer_t *f) {
  term_t t;

  assert(bvfactor_buffer_is_linear(f));
  assert(b->bitsize == f->bitsize && f->bitsize <= 64);

  if (bvfactor_buffer_product_is_one(f)) {
    bvpoly_buffer_sub_const64(b, f->constant64);
  } else {
    t = bvfactor_buffer_get_var(f);
    submul_bvterm64_from_buffer(terms, t, f->constant64, b);
  }
}

static void bvpoly_buffer_sub_factor(bvpoly_buffer_t *b, term_table_t *terms, bvfactor_buffer_t *f) {
  term_t t;

  assert(bvfactor_buffer_is_linear(f));
  assert(b->bitsize == f->bitsize && f->bitsize > 64);

  if (bvfactor_buffer_product_is_one(f)) {
    bvpoly_buffer_sub_constant(b, f->constant.data);
  } else {
    t = bvfactor_buffer_get_var(f);
    submul_bvterm_from_buffer(terms, t, f->constant.data, b);
  }
}


/*
 * Check whether the reduced factors are linear and equal
 */
static bool factoring_equal_linear_factors(bvfactoring_t *r, term_table_t *terms) {
  bvpoly_buffer_t *b;
  uint32_t i;

  b = factoring_get_poly_buffer(r);
  reset_bvpoly_buffer(b, r->bitsize);

  if (r->bitsize <= 64) {
    for (i=0; i<r->n1; i++) {
      bvpoly_buffer_add_factor64(b, terms, r->reduced1 + i);
    }
    for (i=0; i<r->n2; i++) {
      bvpoly_buffer_sub_factor64(b, terms, r->reduced2 + i);
    }
  } else {
    for (i=0; i<r->n1; i++) {
      bvpoly_buffer_add_factor(b, terms, r->reduced1 + i);
    }
    for (i=0; i<r->n2; i++) {
      bvpoly_buffer_sub_factor(b, terms, r->reduced2 + i);
    }
  }

  normalize_bvpoly_buffer(b);
  return bvpoly_buffer_is_zero(b);
}



/*
 * Prepate equality factoring: both t1 and t2 are products
 */
static void build_prod_prod_factoring(bvfactoring_t *r, term_table_t *terms, term_t t1, term_t t2) {
  uint32_t n;

  n = term_bitsize(terms, t1);
  assert(n == term_bitsize(terms, t2));

  prepare_bvfactoring(r, n, 1, 1);
  factoring_set_left_term(r, terms, t1);
  factoring_set_right_term(r, terms, t2);
}


/*
 * Prepare factoring: t1 + polynomial
 * - fails if p is too large
 */
static bool build_prod_poly64_factoring(bvfactoring_t *r, term_table_t *terms, term_t t1, bvpoly64_t *p) {
  uint32_t n;

  n = p->bitsize;
  assert(n == term_bitsize(terms, t1));
  if (p->nterms > 0 && p->nterms <= MAX_BVFACTORS) {
    prepare_bvfactoring(r, n, 1, p->nterms);
    factoring_set_left_term(r, terms, t1);
    factoring_set_right_poly64(r, terms, p);
    return true;
  }

  return false;
}

static bool build_prod_poly_factoring(bvfactoring_t *r, term_table_t *terms, term_t t1, bvpoly_t *p) {
  uint32_t n;

  n = p->bitsize;
  assert(n == term_bitsize(terms, t1));
  if (p->nterms > 0 && p->nterms <= MAX_BVFACTORS) {
    prepare_bvfactoring(r, n, 1, p->nterms);
    factoring_set_left_term(r, terms, t1);
    factoring_set_right_poly(r, terms, p);
    return true;
  }

  return false;
}

static bool try_term_poly_factoring(bvfactoring_t *r, term_table_t *terms, term_t t1, term_t t2) {
  switch (term_kind(terms, t2)) {
  case BV64_POLY:
    return build_prod_poly64_factoring(r, terms, t1, bvpoly64_term_desc(terms, t2));

  case BV_POLY:
    return build_prod_poly_factoring(r, terms, t1, bvpoly_term_desc(terms, t2));

  default:
    return false;
  }
}


/*
 * Reduce and store the common factors in p
 */
static void reduce_bvfactoring(bvfactoring_t *r, pp_buffer_t *p) {
  uint32_t i;

  pp_buffer_reset(p);
  bvfactor_buffer_array_common_factors(p, r->reduced1, r->n1, r->reduced2, r->n2);
  for (i=0; i<r->n1; i++) {
    bvfactor_buffer_reduce(r->reduced1 + i, p);
  }
  for (i=0; i<r->n2; i++) {
    bvfactor_buffer_reduce(r->reduced2 + i, p);
  }
}


/*
 * Compute the common factors of r->reduced1 and r->reduced2
 */
static void try_common_factors(bvfactoring_t *r, term_table_t *terms) {
  pp_buffer_t *common;

  common = factoring_get_pp_buffer(r);
  reduce_bvfactoring(r, common);
  r->code = BVFACTOR_FOUND;

#if 0
  printf("--- Common factors ---\n");
  show_product(common);
  printf("\n");
  show_bvfactoring(r);
  printf("\n");
#endif

  if (linear_reduced_factoring(r) && factoring_has_unique_exponent(r)
      && factoring_equal_linear_factors(r, terms)) {
    //    printf("Linear equal\n\n");
    r->code = BVFACTOR_EQUAL;
    return;
  }

  if (try_left_expansion(r, terms)) {
    //    printf("Left expansion\n");
    //    show_bvfactoring(r);

    reduce_bvfactoring(r, common);

#if 0
    printf("--- Common factors ---\n");
    show_product(common);
    printf("\n");
    show_bvfactoring(r);
    printf("\n");
#endif

    if (linear_reduced_factoring(r) && factoring_has_unique_exponent(r)
	&& factoring_equal_linear_factors(r, terms)) {
      //      printf("Linear equal after left expansion\n\n");
      r->code = BVFACTOR_EQUAL;
      return;
    }
  }

  if (try_right_expansion(r, terms)) {
    //    printf("Right expansion\n");
    //    show_bvfactoring(r);

    reduce_bvfactoring(r, common);

#if 0
    printf("--- Common factors ---\n");
    show_product(common);
    printf("\n");
    show_bvfactoring(r);
    printf("\n");
#endif

    if (linear_reduced_factoring(r) && factoring_has_unique_exponent(r)
	&& factoring_equal_linear_factors(r, terms)) {
      //      printf("Linear equal after right expansion\n\n");
      r->code = BVFACTOR_EQUAL;
      return;
    }
  }
}


#if 0
/*
 * For testing: convert the left/righ part of r to terms
 */
static void test_factor_to_terms(context_t *ctx, bvfactoring_t *r) {
  bvpoly_buffer_t *b;
  term_t left, right;

  b = factoring_get_poly_buffer(r);

  if (r->n1 > 0) {
    printf("Test: convert reduced1 to term\n");
    if (r->n1 == 1) {
      left = bvfactor_buffer_to_term(ctx->terms, b, r->reduced1);
    } else {
      left = bvfactor_buffer_array_to_term(ctx->terms, b, r->reduced1, r->n1);
    }
    print_term_full(stdout, ctx->terms, left);
    printf("\n\n");
  }

  if (r->n2 > 0) {
    printf("Test: convert reduced2 to term\n");
    if (r->n2 == 1) {
      right = bvfactor_buffer_to_term(ctx->terms, b, r->reduced2);
    } else {
      right = bvfactor_buffer_array_to_term(ctx->terms, b, r->reduced2, r->n2);
    }
    print_term_full(stdout, ctx->terms, right);
    printf("\n\n");
  }
}

#endif

/*
 * Try factoring of t1 and t2
 */
void try_bitvector_factoring(context_t *ctx, bvfactoring_t *r, term_t t1, term_t t2) {
  term_table_t *terms;
  bool t1_is_prod, t2_is_prod;

  terms = ctx->terms;
  t1_is_prod = term_is_bvprod(terms, t1);
  t2_is_prod = term_is_bvprod(terms, t2);

  if (t1_is_prod && t2_is_prod) {
    build_prod_prod_factoring(r, terms, t1, t2);
    if (bvfactor_buffer_equal(r->reduced1, r->reduced2)) {
#if 0
      show_bvfactoring(r);
      printf("\n");
      printf("Simple equal\n\n");
#endif

      r->code = BVFACTOR_EQUAL;
      return;
    }
    try_common_factors(r, terms);

  } else if (t1_is_prod && try_term_poly_factoring(r, terms, t1, t2)) {
    try_common_factors(r, terms);

  } else if (t2_is_prod && try_term_poly_factoring(r, terms, t2, t1)) {
    try_common_factors(r, terms);
  }

}


/*
 * Check whether t1 and t2 have the same factor decomposition
 */
bool equal_bitvector_factors(context_t *ctx, term_t t1, term_t t2) {
  bvfactoring_t factoring;
  bool eq;

  init_bvfactoring(&factoring);
  try_bitvector_factoring(ctx, &factoring, t1, t2);
  eq = factoring.code == BVFACTOR_EQUAL;
  delete_bvfactoring(&factoring);

  return eq;
}


/*
 * Convert the left/right parts of r to terms
 * - r must contain a valid factoring
 */
static term_t reduced_array_to_term(term_table_t *terms, bvfactoring_t *r, bvfactor_buffer_t *f, uint32_t n) {
  bvpoly_buffer_t *aux;

  aux = factoring_get_poly_buffer(r);
  if (n == 1) {
    return bvfactor_buffer_to_term(terms, aux, f);
  } else {
    return bvfactor_buffer_array_to_term(terms, aux, f, n);
  }
}

term_t bitvector_factoring_left_term(context_t *ctx, bvfactoring_t *r) {
  assert(r->code == BVFACTOR_FOUND);
  assert(r->n1 > 0);
  return reduced_array_to_term(ctx->terms, r, r->reduced1, r->n1);
}

term_t bitvector_factoring_right_term(context_t *ctx, bvfactoring_t *r) {
  assert(r->code == BVFACTOR_FOUND);
  assert(r->n2 > 0);
  return reduced_array_to_term(ctx->terms, r, r->reduced2, r->n2);
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
  } else if (intern_tbl_sound_subst(intern, t1, t2)) {
    ivector_push(&ctx->subst_eqs, e);
  } else {
    // can't substitute
    ivector_push(&ctx->top_eqs, e);
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
  //  ivector_push(&ctx->top_eqs, e);
  ivector_push(&ctx->top_formulas, e);
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
    case ARITH_IS_INT_ATOM:
    case ARITH_FLOOR:
    case ARITH_CEIL:
    case ARITH_ABS:
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
    case ARITH_RDIV:
    case ARITH_IDIV:
    case ARITH_MOD:
    case ARITH_DIVIDES_ATOM:
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
 *    Every t in top_formulas is either an (OR ...) or (ITE ...) or (XOR ...) or (IFF ..)
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

// r is (is-int t)
static void flatten_arith_is_int(context_t *ctx, term_t r, bool tt) {
  ivector_push(&ctx->top_atoms, signed_term(r, tt));
}

// r is (divides t1 t2)
static void flatten_arith_divides(context_t *ctx, term_t r, bool tt) {
  ivector_push(&ctx->top_atoms, signed_term(r, tt));
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


#if 0
/*
 * Display the results of factoring r
 */
static void show_common_factors(context_t *ctx, term_t r, ivector_t *v) {
  yices_pp_t printer;
  uint32_t i, n;

  n = v->size;
  if (n > 0) {
    printf("--- common factors of r = %"PRId32" ---\n", r);
    init_yices_pp(&printer, stdout, NULL, PP_VMODE, 0);
    pp_term_full(&printer, ctx->terms, r);
    flush_yices_pp(&printer);

    for (i=0; i<n; i++) {
      printf("factor[%"PRIu32"]: ", i);
      pp_term_full(&printer, ctx->terms, v->data[i]);
      flush_yices_pp(&printer);
    }

    delete_yices_pp(&printer, true);
  }
}

#endif

/*
 * Search for common factors of an or
 * - push them in the queue for further flattening
 */
static void push_common_factors(context_t *ctx, term_t r) {
  ivector_t *v;
  uint32_t i, n;

  v = &ctx->aux_vector;
  context_factor_disjunction(ctx, r, v);

#if 0
  show_common_factors(ctx, r, v);
#endif

  n = v->size;
  for (i=0; i<n; i++) {
    int_queue_push(&ctx->queue, v->data[i]);
  }
  ivector_reset(v);
}

/*
 * Non-atomic terms
 */
// r is (or t1 ... t_n)
static void flatten_or(context_t *ctx, term_t r, bool tt) {
  composite_term_t *d;
  uint32_t i, n;

  if (tt) {
    ivector_push(&ctx->top_formulas, r);
    if (context_or_factoring_enabled(ctx)) {
      push_common_factors(ctx, r);
    }
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
      case ARITH_FLOOR:
      case ARITH_CEIL:
      case ARITH_ABS:
      case UPDATE_TERM:
      case TUPLE_TERM:
      case LAMBDA_TERM:
      case ARITH_RDIV:
      case ARITH_IDIV:
      case ARITH_MOD:
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

      case ARITH_ROOT_ATOM:
        exception = FORMULA_NOT_LINEAR;
        goto abort;

      case ARITH_IS_INT_ATOM:
        intern_tbl_map_root(intern, r, bool2code(tt));
        flatten_arith_is_int(ctx, r, tt);
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

      case ARITH_DIVIDES_ATOM:
        intern_tbl_map_root(intern, r, bool2code(tt));
        flatten_arith_divides(ctx, r, tt);
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




/**************************
 *  AUXILIARY EQUALITIES  *
 *************************/

/*
 * Process an auxiliary equality eq
 * - eq must be an equality term (i.e.,
 *   either EQ_TERM, ARITH_EQ_ATOM, ARITH_BINEQ_ATOM, BVEQ_ATOM)
 */
static void process_aux_eq(context_t *ctx, term_t eq) {
  composite_term_t *d;
  term_t t1, t2;
  int32_t code;

  assert(intern_tbl_is_root(&ctx->intern, eq));

  if (intern_tbl_root_is_mapped(&ctx->intern, eq)) {
    // eq is already internalized
    code = intern_tbl_map_of_root(&ctx->intern, eq);
    if (code == bool2code(false)) {
      // contradiction
      longjmp(ctx->env, TRIVIALLY_UNSAT);
    } else if (code != bool2code(true)) {
      ivector_push(&ctx->top_interns, eq);
    }
  } else {
    // map e to true and try to process it as a substitution
    intern_tbl_map_root(&ctx->intern, eq, bool2code(true));

    switch (term_kind(ctx->terms, eq)) {
    case EQ_TERM:
    case ARITH_BINEQ_ATOM:
    case BV_EQ_ATOM:
      // process e as a substitution if possible
      d = composite_term_desc(ctx->terms, eq);
      assert(d->arity == 2);
      t1 = intern_tbl_get_root(&ctx->intern, d->arg[0]);
      t2 = intern_tbl_get_root(&ctx->intern, d->arg[1]);
      if (is_boolean_term(ctx->terms, t1)) {
	try_bool_substitution(ctx, t1, t2, eq);
      } else {
	try_substitution(ctx, t1, t2, eq);
      }
      break;

    case ARITH_EQ_ATOM:
      ivector_push(&ctx->top_eqs, eq);
      break;

    default:
      assert(false);
      break;
    }
  }
}


/*
 * Process the auxiliary equalities:
 * - if substitution is not enabled, then all aux equalities are added to top_eqs
 * - otherwise, cheap substitutions are performed and candidate substitutions
 *   are added to subst_eqs.
 *
 * This function raises an exception via longjmp if a contradiction is detected.
 */
void process_aux_eqs(context_t *ctx) {
  uint32_t i, n;
  ivector_t *aux_eqs;

  aux_eqs = &ctx->aux_eqs;
  n = aux_eqs->size;
  for (i=0; i<n; i++) {
    process_aux_eq(ctx, aux_eqs->data[i]);
  }

  // cleanup
  ivector_reset(&ctx->aux_eqs);
}



/*******************
 *  LEARNED ATOMS  *
 ******************/

/*
 * Process all terms in ctx->aux_atoms:
 */
void process_aux_atoms(context_t *ctx) {
  ivector_t *v;
  uint32_t i, n;
  term_t t, r;
  int32_t code;

  v = &ctx->aux_atoms;
  n = v->size;
  for (i=0; i<n; i++) {
    t = v->data[i];
    r = intern_tbl_get_root(&ctx->intern, t);

    if (intern_tbl_root_is_mapped(&ctx->intern, r)) {
      // already internalized
      code = intern_tbl_map_of_root(&ctx->intern, r);
      if (code == bool2code(false)) {
	// contradiction
	longjmp(ctx->env, TRIVIALLY_UNSAT);
      } else if (code != bool2code(true)) {
	ivector_push(&ctx->top_interns, r);
      }
    } else {
      // not mapped
      intern_tbl_map_root(&ctx->intern, r, bool2code(true));
      ivector_push(&ctx->top_atoms, r);
    }
  }

  ivector_reset(v);
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
  rba_buffer_t *b;

  assert(is_pos_term(t) && is_arithmetic_term(ctx->terms, t));

  b = ctx->arith_buffer;
  assert(b != NULL && rba_buffer_is_zero(b));

  rba_buffer_add_term(b, ctx->terms, t);
  return mk_direct_arith_lt0(ctx->terms, b, true);
}

/*
 * Build a term equivalent to (t > 0)
 */
static term_t gt0_atom(context_t *ctx, term_t t) {
  rba_buffer_t *b;

  assert(is_pos_term(t) && is_arithmetic_term(ctx->terms, t));

  b = ctx->arith_buffer;
  assert(b != NULL && rba_buffer_is_zero(b));

  rba_buffer_add_term(b, ctx->terms, t);
  return mk_direct_arith_gt0(ctx->terms, b, true);
}


/*
 * Build a term equivalent to (t < u)
 */
static term_t lt_atom(context_t *ctx, term_t t, term_t u) {
  rba_buffer_t *b;

  assert(is_pos_term(t) && is_arithmetic_term(ctx->terms, t));
  assert(is_pos_term(u) && is_arithmetic_term(ctx->terms, u));

  // build atom (t - u < 0)
  b = ctx->arith_buffer;
  assert(b != NULL && rba_buffer_is_zero(b));
  rba_buffer_add_term(b, ctx->terms, t);
  rba_buffer_sub_term(b, ctx->terms, u);
  return mk_direct_arith_lt0(ctx->terms, b, true);
}


/*
 * We use a breadth-first approach:
 * - ctx->queue contains all terms to process
 * - v contains the terms that can't be flattened
 * - ctx->small_cache contains all the terms that have been visited
 *   (including all terms in v and in ctx->queue).
 *
 * The term we're building is (or <elements in v> <elements in the queue>)
 */

/*
 * Push t into ctx->queue if it's not been visited yet
 */
static void flatten_or_push_term(context_t *ctx, term_t t) {
  assert(is_boolean_term(ctx->terms, t));

  if (int_hset_add(ctx->small_cache, t)) {
    int_queue_push(&ctx->queue, t);
  }
}

/*
 * Add t to v if it's not been visited yet
 */
static void flatten_or_add_term(context_t *ctx, ivector_t *v, term_t t) {
  assert(is_boolean_term(ctx->terms, t));

  if (int_hset_add(ctx->small_cache, t)) {
    ivector_push(v, t);
  }
}

/*
 * Process all elements in ctx->queue.
 *
 * For every term t in the queue:
 * - if t is already internalized, keep t and add it to v
 * - if t is (or t1 ... t_n), add t1 ... t_n to the queue
 * - if flattening of disequalities is enabled, and t is (NOT (x == 0)) then
 *   we rewrite (NOT (x == 0)) to (OR (< x 0) (> x 0))
 * - otherwise store t into v
 */
static void flatten_or_process_queue(context_t *ctx, ivector_t *v) {
  term_table_t *terms;
  composite_term_t *or;
  composite_term_t *eq;
  uint32_t i, n;
  term_kind_t kind;
  term_t t, x, y;

  terms = ctx->terms;

  while (! int_queue_is_empty(&ctx->queue)) {
    t = int_queue_pop(&ctx->queue);

    // apply substitutions
    t = intern_tbl_get_root(&ctx->intern, t);

    if (intern_tbl_root_is_mapped(&ctx->intern, t)) {
      // t is already internalized: keep it as is
      ivector_push(v, t);
    } else {
      kind = term_kind(terms, t);
      if (is_pos_term(t) && kind == OR_TERM) {
	// add t's children to the queue
	or = or_term_desc(terms, t);
	n = or->arity;
	for (i=0; i<n; i++) {
	  flatten_or_push_term(ctx, or->arg[i]);
	}
      } else if (is_neg_term(t) && context_flatten_diseq_enabled(ctx)) {
	switch (kind) {
	case ARITH_EQ_ATOM:
	  /*
	   * t is (not (eq x 0)): rewrite to (or (x < 0) (x > 0))
	   *
	   * Exception: keep it as an equality if x is an if-then-else term
	   */
	  x = intern_tbl_get_root(&ctx->intern, arith_eq_arg(terms, t));
	  if (is_ite_term(terms, x)) {
	    ivector_push(v, t);
	  } else {
	    flatten_or_add_term(ctx, v, lt0_atom(ctx, x));
	    flatten_or_add_term(ctx, v, gt0_atom(ctx, x));
	  }
	  break;

	case ARITH_BINEQ_ATOM:
	  /*
	   * t is (not (eq x y)): rewrite to (or (x < y) (y < x))
	   *
	   * Exception 1: if x or y is an if-then-else term, then it's
	   * better to keep (eq x y) because the if-lifting
	   * simplifications are more likely to work on
	   *    (ite c a b) = y
	   * than (ite c a b) >= y AND (ite c a b) <= y
	   *
	   * Exception 2: if there's an egraph, then it's better
	   * to keep (eq x y) as is. It will be converted to an
	   * egraph equality.
	   */
	  eq = arith_bineq_atom_desc(terms, t);
	  x = intern_tbl_get_root(&ctx->intern, eq->arg[0]);
	  y = intern_tbl_get_root(&ctx->intern, eq->arg[1]);
	  if (context_has_egraph(ctx) || is_ite_term(terms, x) || is_ite_term(terms, y)) {
	    ivector_push(v, t);
	  } else {
	    flatten_or_add_term(ctx, v, lt_atom(ctx, x, y));
	    flatten_or_add_term(ctx, v, lt_atom(ctx, y, x));
	  }
	  break;

	default:
	  // can't flatten
	  ivector_push(v, t);
	  break;
	}

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

  assert(v->size == 0 && int_queue_is_empty(&ctx->queue));

  (void) context_get_small_cache(ctx); // initialize the cache
  if (context_flatten_diseq_enabled(ctx)) {
    (void) context_get_arith_buffer(ctx);  // allocate the internal buffer
  }

  n = or->arity;
  for (i=0; i<n; i++) {
    flatten_or_push_term(ctx, or->arg[i]);
  }

  flatten_or_process_queue(ctx, v);

  //  context_delete_small_cache(ctx);
  context_reset_small_cache(ctx);
}




/************************
 *  EQUALITY LEARNING   *
 ***********************/

/*
 * Add implied equalities defined by the partition p to the aux_eqs vector
 */
static void add_implied_equalities(context_t *ctx, epartition_t *p) {
  uint32_t i, n;
  term_t *q, x, y;

  n = p->nclasses;
  q = p->data;
  for (i=0; i<n; i++) {
    x = *q++;
    assert(x >= 0);
    y = *q ++;
    while (y >= 0) {
      add_aux_eq(ctx, x, y);
      y = *q ++;
    }
  }
}


/*
 * Attempt to learn global equalities implied
 * by the formulas stored in ctx->top_formulas.
 * Any such equality is added to ctx->aux_eqs
 */
void analyze_uf(context_t *ctx) {
  ivector_t *v;
  uint32_t i, n;
  eq_learner_t eql;
  epartition_t *p;

  init_eq_learner(&eql, ctx->terms);
  v = &ctx->top_formulas;
  n = v->size;

  for (i=0; i<n; i++) {
    p = eq_learner_process(&eql, v->data[i]);
    if (p->nclasses > 0) {
      add_implied_equalities(ctx, p);
    }
  }

  delete_eq_learner(&eql);
}




/*************************************************
 *  ANALYSIS FOR THE DIFFERENCE LOGIC FRAGMENTS  *
 ************************************************/

/*
 * Buffer to store a difference logic term.
 *
 * The difference logic fragment contains terms of the following forms:
 *   a + x - y
 *   a + x
 *   a - y
 *   a
 * where x and y are arithmetic variables and a is a constant (possibly a = 0).
 *
 * In IDL, x and y must be integer variables and a must be an integer constant.
 * In RDL, x and y must be real variables.
 *
 * To encode the four types of terms, we use zero_term when x or y is missing:
 *  a + x  -->  a + x - zero_term
 *  a - y  -->  a + zero_term - y
 *  a      -->  a + zero_term - zero_term
 */
typedef struct dl_term_s {
  term_t x;
  term_t y;
  rational_t a;
} dl_term_t;


/*
 * Initialization and cleanup
 */
static void init_dl_term(dl_term_t *triple) {
  triple->x = zero_term;
  triple->y = zero_term;
  q_init(&triple->a);
}

static void delete_dl_term(dl_term_t *triple) {
  q_clear(&triple->a);
}


/*
 * Check whether the triple is in IDL or RDL.
 */
static bool check_dl_fragment(context_t *ctx, dl_term_t *triple, bool idl) {
  assert(is_arithmetic_term(ctx->terms, triple->x) && is_pos_term(triple->x) && intern_tbl_is_root(&ctx->intern, triple->x));
  assert(is_arithmetic_term(ctx->terms, triple->y) && is_pos_term(triple->y) && intern_tbl_is_root(&ctx->intern, triple->y));

  return (triple->x == zero_term || is_integer_root(ctx, triple->x) == idl)
    && (triple->y == zero_term || is_integer_root(ctx, triple->y) == idl)
    && (!idl || q_is_integer(&triple->a));
}


/*
 * Check whether aux contains a difference logic term. If so store the term in *triple.
 * All terms of aux must be roots in ctx->interm.
 *
 * Return true if aux is in the difference logic fragment, false otherwise.
 */
static bool dl_convert_poly_buffer(context_t *ctx, dl_term_t *triple, poly_buffer_t *aux) {
  uint32_t n;
  monomial_t *q;

  n = poly_buffer_nterms(aux);
  if (n > 3) return false;
  if (n == 0) return true;

  q = poly_buffer_mono(aux);

  // constant
  q_clear(&triple->a);
  if (q[0].var == const_idx) {
    q_set(&triple->a, &q[0].coeff);
    q ++;
    n --;
  }

  // deal with the non-constant terms
  if (n == 2 && q_opposite(&q[0].coeff, &q[1].coeff)) {
    if (q_is_one(&q[0].coeff)) {
      // a_0 + x_1 - x_2
      triple->x = q[0].var; // x_1
      triple->y = q[1].var; // x_2
      return true;
    }

    if (q_is_one(&q[1].coeff)) {
      // a_0 - x_1 + x_2
      triple->x = q[1].var; // x_2
      triple->y = q[0].var; // x_1
      return true;
    }

  } else if (n == 1) {
    if (q_is_one(&q[0].coeff)) {
      // a_0 + x_1
      triple->x = q[0].var; // x_1
      triple->y = zero_term;
      return true;
    }

    if (q_is_minus_one(&q[0].coeff)) {
      // a_0 - x_1
      triple->x = zero_term;
      triple->y = q[0].var; // x_1
      return true;
    }

  } else if (n == 0) {
    triple->x = zero_term;
    triple->y = zero_term;
    return true;
  }

  return false;
}


/*
 * Apply substitutions then check whether p can be converted to a dl term.
 * If so store the result in tiple and return true. Otherwise return false;
 */
static bool dl_convert_poly(context_t *ctx, dl_term_t *triple, polynomial_t *p) {
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

  /*
   * The QF_RDL theory, as defined by SMT-LIB, allows constraints of
   * the form (<= (- (* a x) (* a y)) b) where a and b are integer
   * constants. We allow rationals here and we also allow
   * constraints like that for QF_IDL (provided b/a is an integer).
   */
  if (! poly_buffer_is_zero(aux)) {
    (void) poly_buffer_make_monic(aux);
  }

  return dl_convert_poly_buffer(ctx, triple, aux);
}


/*
 * Check whether (x - y) is a difference logic term. If so, store the result in triple
 * and return true. Otherwise return false.
 */
static bool dl_convert_diff(context_t *ctx, dl_term_t *triple, term_t x, term_t y) {
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

  return dl_convert_poly_buffer(ctx, triple, aux);
}


/*
 * Check whether term t is a difference logic term. If so convert t to a dl_term
 * and store that in triple.
 * Return true if the conversion succeeds, false otherwise.
 */
static bool dl_convert_term(context_t *ctx, dl_term_t *triple, term_t t) {
  term_table_t *terms;

  assert(is_arithmetic_term(ctx->terms, t));

  terms = ctx->terms;

  // apply substitution
  t = intern_tbl_get_root(&ctx->intern, t);

  assert(is_arithmetic_term(terms, t) && is_pos_term(t)
         && intern_tbl_is_root(&ctx->intern, t));

  switch (term_kind(terms, t)) {
  case ARITH_CONSTANT:
    triple->x = zero_term;
    triple->y = zero_term;
    q_set(&triple->a, rational_term_desc(terms, t));
    return true;

  case UNINTERPRETED_TERM:
    return dl_convert_diff(ctx, triple, t, zero_term);

  case ARITH_POLY:
    return dl_convert_poly(ctx, triple, poly_term_desc(terms, t));

  default:
    // TODO: we could accept if-then-else here?
    return false;
  }
}



/*
 * Increment the number of variables if t has not been seen before
 */
static void count_dl_var(context_t *ctx, term_t t) {
  bool new;

  assert(is_pos_term(t) && intern_tbl_is_root(&ctx->intern, t));

  (void) int_rat_hmap_get(ctx->edge_map, t, &new);
  ctx->dl_profile->num_vars += new;
}

/*
 * Update: edge of weight a from source t
 * - in the edge_map, we assign to term t the max weight of all potential
 *   edges of source t. The weight is an absolute value.
 */
static void count_dl_var_and_edge(context_t *ctx, term_t t, rational_t *a) {
  int_rat_hmap_rec_t *d;
  bool new;

  assert(q_is_nonneg(a));
  assert(is_pos_term(t) && intern_tbl_is_root(&ctx->intern, t));

  d = int_rat_hmap_get(ctx->edge_map, t, &new);
  ctx->dl_profile->num_vars += new;
  if (q_gt(a, &d->value)) {
    // increase bound on edges of source t
    q_set(&d->value, a);
  }
}


/*
 * Update the difference logic statistics for atom x - y <= a
 * - this corresponds to an edge x --> y of absolute weight a >= 0
 * - if the atom is true, the dl solver will add an edge from x to y of weight a
 * - if the atom if false, the dl solver will and an edge from y to x of weight
 *    (or - a - 1 in IDL case)
 */
static void update_dl_stats(context_t *ctx, term_t x, term_t y, rational_t *a, bool idl) {
  if (x == y) {
    /*
     * The atom simplifies to true or false but we must count x as a variable,
     * because the diff logic solver will still create a variable for x.
     */
    count_dl_var(ctx, x);
  } else {
    /*
     * We use the absolute value as an upper bound:
     *  x --> y with weight = |a|
     *  y --> x with weight = |a| or |a|+1 if idl
     */
    if (q_is_neg(a)) q_neg(a);
    count_dl_var_and_edge(ctx, x, a);
    if (idl) q_add_one(a);
    count_dl_var_and_edge(ctx, y, a);
    ctx->dl_profile->num_atoms ++;
  }
}


/*
 * Same thing for (x - y == a): the max weight is |a| + 1 for both x and y
 */
static void update_dleq_stats(context_t *ctx, term_t x, term_t y, rational_t *a, bool idl) {
  if (x == y) {
    count_dl_var(ctx, x);
  } else {
    if (q_is_neg(a)) q_neg(a);
    if (idl) q_add_one(a);
    count_dl_var_and_edge(ctx, x, a);
    count_dl_var_and_edge(ctx, y, a);
    ctx->dl_profile->num_eqs ++;
    ctx->dl_profile->num_atoms ++;
  }
}

/*
 * Check atom (t == 0) and update statistics
 * - idl = true to check for IDL, false for RDL
 */
static bool check_dl_eq0_atom(context_t *ctx, term_t t, bool idl) {
  dl_term_t triple;
  bool result;

  init_dl_term(&triple);
  result = dl_convert_term(ctx, &triple, t) && check_dl_fragment(ctx, &triple, idl);
  if (result) {
    // a + x - y = 0 <--> (y - x = a)
    update_dleq_stats(ctx, triple.y, triple.x, &triple.a, idl);
  }
  delete_dl_term(&triple);

  return result;
}

/*
 * Check atom (t >= 0) and update statistics
 */
static bool check_dl_geq0_atom(context_t *ctx, term_t t, bool idl) {
  dl_term_t triple;
  bool result;

  init_dl_term(&triple);
  result = dl_convert_term(ctx, &triple, t) && check_dl_fragment(ctx, &triple, idl);
  if (result) {
    // a + x - y >= 0 <--> (y - x <= -a)
    q_neg(&triple.a);
    update_dl_stats(ctx, triple.y, triple.x, &triple.a, idl);
  }
  delete_dl_term(&triple);

  return result;
}

/*
 * Check atom (t1 == t2) and update statistics
 */
static bool check_dl_eq_atom(context_t *ctx, term_t t1, term_t t2, bool idl) {
  dl_term_t triple;
  bool result;

  init_dl_term(&triple);
  result = dl_convert_diff(ctx, &triple, t1, t2) && check_dl_fragment(ctx, &triple, idl);
  if (result) {
    // a + x - y = 0 <--> (y - x = a)
    update_dleq_stats(ctx, triple.y, triple.x, &triple.a, idl);
  }
  delete_dl_term(&triple);

  return result;
}


/*
 * Check atom (distinct a[0] .... a[n-1]) and update statistics
 */
static bool check_dl_distinct_atom(context_t *ctx, term_t *a, uint32_t n, bool idl) {
  uint32_t i, j;

  assert(n > 2);

  for (i=0; i<n-1; i++) {
    for (j=i+1; j<n; j++) {
      if (! check_dl_eq_atom(ctx, a[i], a[j], idl)) {
	return false;
      }
    }
  }

  return true;
}


/*
 * Analyze all arithmetic atoms in term t and fill ctx->dl_profile
 * - if idl is true, this checks for integer difference logic
 *   otherwise, checks for real difference logic
 * - cache must be initialized and contain all the terms already visited
 */
static void analyze_dl(context_t *ctx, term_t t, bool idl) {
  term_table_t *terms;
  composite_term_t *cmp;
  uint32_t i, n;
  int32_t idx;
  term_t r;
  int32_t code;

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
        analyze_dl(ctx,  r, idl);
      }
      break;

    case ITE_TERM:
    case ITE_SPECIAL:
    case OR_TERM:
    case XOR_TERM:
      cmp = composite_for_idx(terms, idx);
      n = cmp->arity;
      for (i=0; i<n; i++) {
        analyze_dl(ctx, cmp->arg[i], idl);
      }
      break;

    case EQ_TERM:
      cmp = composite_for_idx(terms, idx);
      assert(cmp->arity == 2);
      if (is_boolean_term(terms, cmp->arg[0])) {
        // boolean equality
        analyze_dl(ctx, cmp->arg[0], idl);
        analyze_dl(ctx, cmp->arg[1], idl);
      } else {
        goto abort;
      }
      break;

    case DISTINCT_TERM:
      cmp = composite_for_idx(terms, idx);
      if (! check_dl_distinct_atom(ctx, cmp->arg, cmp->arity, idl)) {
	goto abort;
      }
      break;

    case ARITH_EQ_ATOM:
      // term (x == 0): check whether x is a difference logic term
      if (! check_dl_eq0_atom(ctx, integer_value_for_idx(terms, idx), idl)) {
        goto abort;
      }
      break;

    case ARITH_GE_ATOM:
      // term (x >= 0): check whether x is a difference logic term
      if (! check_dl_geq0_atom(ctx, integer_value_for_idx(terms, idx), idl)) {
        goto abort;
      }
      break;

    case ARITH_BINEQ_ATOM:
      // term (x == y): check whether x - y is a difference logic term
      cmp = composite_for_idx(terms, idx);
      assert(cmp->arity == 2);
      if (! check_dl_eq_atom(ctx, cmp->arg[0], cmp->arg[1], idl)) {
        goto abort;
      }
      break;

    default:
      goto abort;
    }
  }

  return;

 abort:
  code = idl ? FORMULA_NOT_IDL : FORMULA_NOT_RDL;
  longjmp(ctx->env, code);
}


/*
 * Check all terms in vector v
 */
static void analyze_diff_logic_vector(context_t *ctx, ivector_t *v, bool idl) {
  uint32_t i, n;

  n = v->size;
  for (i=0; i<n; i++) {
    analyze_dl(ctx, v->data[i], idl);
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
 * - raise an exception (either FORMULA_NOT_IDL or FORMULA_NOT_RDL) otherwise.
 *
 * This function is used to decide whether to use simplex or a
 * specialized solver when the architecture is CTX_AUTO_IDL or
 * CTX_AUTO_RDL.  Because this function is called before the actual
 * arithmetic solver is created, we assume that no arithmetic term is
 * internalized, and that top_interns is empty.
 */
void analyze_diff_logic(context_t *ctx, bool idl) {
  dl_data_t *stats;
  int_rat_hmap_t *edges;

  assert(ctx->dl_profile == NULL && ctx->edge_map == NULL);

  // allocate and initialize dl_profile, edge_map, and cache
  stats = context_get_dl_profile(ctx);
  edges = context_get_edge_map(ctx);
  (void) context_get_cache(ctx);

  analyze_diff_logic_vector(ctx, &ctx->top_eqs, idl);
  analyze_diff_logic_vector(ctx, &ctx->top_atoms, idl);
  analyze_diff_logic_vector(ctx, &ctx->top_formulas, idl);

  // compute the bound on path length
  int_rat_hmap_sum(edges, &stats->path_bound);

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
  printf("---> path bound = ");
  q_print(stdout, &stats->path_bound);
  printf("\n");
#endif

  context_free_cache(ctx);
  context_free_edge_map(ctx);
}



/*******************
 *  CONDITIONALS   *
 ******************/

/*
 * Allocate a conditional descriptor from the store
 */
static conditional_t *new_conditional(context_t *ctx) {
  conditional_t *d;

  d = objstore_alloc(&ctx->cstore);
  init_conditional(d, ctx->terms);
  return d;
}

/*
 * Free conditional descriptor d
 */
void context_free_conditional(context_t *ctx, conditional_t *d) {
  delete_conditional(d);
  objstore_free(&ctx->cstore, d);
}

/*
 * Attempt to convert an if-then-else term to a conditional
 * - return NULL if the conversion fails
 * - return a conditional descriptor otherwise
 * - if NON-NULL, the result must be freed when no-longer used
 *   by calling context_free_conditional
 */
conditional_t *context_make_conditional(context_t *ctx, composite_term_t *ite) {
  conditional_t *d;

  assert(ite->arity == 3);

  d = new_conditional(ctx);
  convert_ite_to_conditional(d, ite->arg[0], ite->arg[1], ite->arg[2]);
  if (d->nconds <= 1) {
    context_free_conditional(ctx, d);
    d = NULL;
  }

  return d;
}


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
 * - if all c_i's are false, the function returns d
 * - in all other cases, the function returns NULL_TERM
 */
term_t simplify_conditional(context_t *ctx, conditional_t *d) {
  uint32_t i, n;
  bool all_false;
  term_t result;

  n = d->nconds;
  all_false = true;
  result = NULL_TERM;

  for (i=0; i<n; i++) {
    if (term_is_true(ctx, d->pair[i].cond)) {
      result = d->pair[i].val;
      goto done;
    }
    all_false &= term_is_false(ctx, d->pair[i].cond);
  }

  if (all_false) {
    result = d->defval;
  }

 done:
  return result;
}


#if 0

/*
 * FOR TESTING ONLY
 */

/*
 * Print result of conversion of t to a conditional structure
 */
static void print_conditional_conversion(conditional_t *d, term_t t) {
  yices_pp_t pp;
  pp_area_t area;
  uint32_t i, n;

  area.width = 400;
  area.height = 300;
  area.offset = 0;
  area.stretch = false;
  area.truncate = true;
  init_default_yices_pp(&pp, stdout, &area);

  pp_open_block(&pp, PP_OPEN);
  pp_string(&pp, "Conversion to conditional for term");
  pp_term_full(&pp, d->terms, t);
  pp_close_block(&pp, false);
  flush_yices_pp(&pp);

  pp_string(&pp, "result:");
  flush_yices_pp(&pp);

  n = d->nconds;
  for (i=0; i<n; i++) {
    pp_open_block(&pp, PP_OPEN_ITE);
    pp_term_full(&pp, d->terms, d->pair[i].cond);
    pp_term_full(&pp, d->terms, d->pair[i].val);
    pp_close_block(&pp, true);
  }

  pp_open_block(&pp, PP_OPEN_PAR);
  pp_string(&pp, "else");
  pp_term_full(&pp, d->terms, d->defval);
  pp_close_block(&pp, true);

  delete_yices_pp(&pp, true);
}

/*
 * Try to flatten an ite term t into a conditional
 * - if that works print the result
 */
void context_test_conditional_for_ite(context_t *ctx, composite_term_t *ite, term_t t) {
  conditional_t condi;

  init_conditional(&condi, ctx->terms);
  convert_ite_to_conditional(&condi, ite->arg[0], ite->arg[1], ite->arg[2]);

  if (condi.nconds > 1) {
    print_conditional_conversion(&condi, t);
  }

  delete_conditional(&condi);
}


#endif


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

    if (disequal_terms(terms, k, ite->arg[1], true)) {
      // (t == k) is (not c) and (t == b)
      ivector_push(v, opposite_term(ite->arg[0]));
      t = intern_tbl_get_root(&ctx->intern, ite->arg[2]);

    } else if (disequal_terms(terms, k, ite->arg[2], true)) {
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
  rng_record_t **v;
  uint32_t i, n;

  area.width = 150;
  area.height = 30;
  area.offset = 0;
  area.stretch = false;
  area.truncate = true;
  init_default_yices_pp(&pp, stdout, &area);

  v = breaker->sorted_constraints;
  n = breaker->num_constraints;
  for (i=0; i<n; i++) {
    pp_open_block(&pp, PP_OPEN);
    pp_string(&pp, "Range constraints for set: ");
    show_constant_set(&pp, breaker->terms, v[i]);
    pp_close_block(&pp, false);
    flush_yices_pp(&pp);
    flush_yices_pp(&pp);
    pp_constraints(&pp, breaker, v[i]);
  }

  delete_yices_pp(&pp, true);
}

static void print_constant_set(sym_breaker_t *breaker, rng_record_t *r) {
  uint32_t i, n;

  n = r->num_constants;
  for (i=0; i<n; i++) {
    fputc(' ', stdout);
    print_term(stdout, breaker->terms, r->cst[i]);
  }
}

static void print_candidates(sym_breaker_t *breaker, sym_breaker_sets_t *sets) {
  uint32_t i, n;

  printf("--- Candidates ---\n");
  n = sets->num_candidates;
  for (i=0; i<n; i++) {
    printf("   ");
    print_term_full(stdout, breaker->terms, sets->candidates[i]);
    printf("\n");
  }
}

#endif


/*
 * Break symmetries
 */
void break_uf_symmetries(context_t *ctx) {
  sym_breaker_t breaker;
  sym_breaker_sets_t *sets;
  rng_record_t **v;
  uint32_t i, j, n;

  init_sym_breaker(&breaker, ctx);
  collect_range_constraints(&breaker);

#if TRACE_SYM_BREAKING
  show_range_constraints(&breaker);
#endif

  v = breaker.sorted_constraints;
  n = breaker.num_constraints;
  if (n > 0) {
    // test of symmetry breaking
    sets = &breaker.sets;
    for (i=0; i<n; i++) {
      if (check_assertion_invariance(&breaker, v[i])) {
#if TRACE_SYM_BREAKING
	printf("Breaking symmetries using set[%"PRIu32"]:", i);
	print_constant_set(&breaker, v[i]);
	printf("\n");
#endif
	breaker_sets_copy_record(sets, v[i]);
	for (j=i+1; j<n; j++) {
	  if (range_record_subset(v[j], v[i])) {
#if TRACE_SYM_BREAKING
	    printf("Adding set[%"PRIu32"]:", j);
	    print_constant_set(&breaker, v[j]);
	    printf("\n");
#endif
	    breaker_sets_add_record(sets, v[j]);
	  }
	}
#if TRACE_SYM_BREAKING
	print_candidates(&breaker, sets);
	printf("\n");
#endif
	break_symmetries(&breaker, sets);
      } else {
#if TRACE_SYM_BREAKING
	printf("Set[%"PRIu32"]:", i);
	print_constant_set(&breaker, v[i]);
	printf(" not symmetrical\n\n");
#endif
      }
    }

  } else {
#if TRACE_SYM_BREAKING
    printf("\n*** NO SYMMETRY CANDIDATES ***\n\n");
#endif
  }

  delete_sym_breaker(&breaker);
}




/******************************
 *  CONDITIONAL DEFINITIONS   *
 *****************************/

void process_conditional_definitions(context_t *ctx) {
  cond_def_collector_t collect;
  ivector_t *v;
  uint32_t i, n;

  v = &ctx->top_formulas;
  n = v->size;
  if (n > 0) {
    init_cond_def_collector(&collect, ctx);
    for (i=0; i<n; i++) {
      extract_conditional_definitions(&collect, v->data[i]);
    }
    analyze_conditional_definitions(&collect);
    delete_cond_def_collector(&collect);
  }
}
