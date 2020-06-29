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
 * ASSERTION CONTEXT
 */

#include <inttypes.h>

#include "context/context.h"
#include "context/context_simplifier.h"
#include "context/context_utils.h"
#include "context/internalization_codes.h"
#include "context/ite_flattener.h"
#include "solvers/bv/bvsolver.h"
#include "solvers/floyd_warshall/idl_floyd_warshall.h"
#include "solvers/floyd_warshall/rdl_floyd_warshall.h"
#include "solvers/funs/fun_solver.h"
#include "solvers/simplex/simplex.h"
#include "terms/poly_buffer_terms.h"
#include "terms/term_utils.h"
#include "utils/memalloc.h"

#include "mcsat/solver.h"
#include "mt/thread_macros.h"

#include "api/yices_globals.h"

#define TRACE 0

#if TRACE

#include <stdio.h>

#include "io/term_printer.h"
#include "solvers/cdcl/smt_core_printer.h"

#endif





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
    //    u = egraph_make_variable(ctx->egraph, type);
    // it's better to use skolem_term in case type is (tuple ...)
    u = egraph_skolem_term(ctx->egraph, type);
  }
  return u;
}


/*
 * Type of arithmetic variable x
 */
static type_t type_of_arithvar(context_t *ctx, thvar_t x) {
  type_t tau;

  tau = real_type(ctx->types);
  if (ctx->arith.arith_var_is_int(ctx->arith_solver, x)) {
    tau = int_type(ctx->types);
  }

  return tau;
}


/*
 * Convert arithmetic variable x to an egraph term
 */
static occ_t translate_arithvar_to_eterm(context_t *ctx, thvar_t x) {
  eterm_t u;
  type_t tau;

  u = ctx->arith.eterm_of_var(ctx->arith_solver, x);
  if (u == null_eterm) {
    tau = type_of_arithvar(ctx, x);
    u = egraph_thvar2term(ctx->egraph, x, tau);
  }

  return pos_occ(u);
}

/*
 * Convert bit-vector variable x to an egraph term
 * - tau = type of x
 */
static occ_t translate_bvvar_to_eterm(context_t *ctx, thvar_t x, type_t tau) {
  eterm_t u;

  u = ctx->bv.eterm_of_var(ctx->bv_solver, x);
  if (u == null_eterm) {
    u = egraph_thvar2term(ctx->egraph, x, tau);
  }

  return pos_occ(u);
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
    return translate_arithvar_to_eterm(ctx, x);
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
      u = translate_arithvar_to_eterm(ctx, code2thvar(x));
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


/*
 * Internalization error for term t
 * - t can't be processed because there's no egraph
 * - the error code depends on t's type
 */
static int32_t uf_error_code(context_t *ctx, term_t t) {
  int32_t code;

  assert(! context_has_egraph(ctx));

  switch (term_type_kind(ctx->terms, t)) {
  case UNINTERPRETED_TYPE:
    code = UTYPE_NOT_SUPPORTED;
    break;

  case SCALAR_TYPE:
    code = SCALAR_NOT_SUPPORTED;
    break;

  case FUNCTION_TYPE:
    code = UF_NOT_SUPPORTED;
    break;

  case TUPLE_TYPE:
    code = TUPLE_NOT_SUPPORTED;
    break;

  default:
    assert(false);
    code = INTERNAL_ERROR;
    break;
  }

  return code;
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

  //  add_type_constraints(ctx, pos_occ(u), tau);

  return pos_occ(u);
}


/*
 * Build a tuple of same type as t then assert that it's equal to u1
 * - t must be a root in the internalization table
 * - u1 must be equal to t's internalization (as stored in intern_table)
 * This is the skolemization of (exist (x1...x_n) u1 == (tuple x1 ... x_n))
 *
 * - return the eterm u := (tuple x1 ... x_n)
 */
static eterm_t skolem_tuple(context_t *ctx, term_t t, occ_t u1) {
  type_t tau;
  eterm_t u;

  assert(intern_tbl_is_root(&ctx->intern, t) && is_pos_term(t) &&
	 intern_tbl_map_of_root(&ctx->intern, t) == occ2code(u1));

  tau = intern_tbl_type_of_root(&ctx->intern, t);
  u = egraph_skolem_term(ctx->egraph, tau);
  egraph_assert_eq_axiom(ctx->egraph, u1, pos_occ(u));

  return u;
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
 * Convert a conditional expression to an egraph term
 * - c = conditional descriptor
 * - tau = type of c
 */
static occ_t map_conditional_to_eterm(context_t *ctx, conditional_t *c, type_t tau) {
  literal_t *a;
  occ_t u, v;
  uint32_t i, n;
  literal_t l;
  bool all_false;
  term_t t;

#if 0
  printf("---> conditional to eterm\n");
#endif

  t = simplify_conditional(ctx, c);
  if (t != NULL_TERM) {
    return internalize_to_eterm(ctx, t);
  }

  n = c->nconds;
  a = alloc_istack_array(&ctx->istack, n + 1);

  all_false = true;
  u = null_occurrence;

  for (i=0; i<n; i++) {
    a[i] = internalize_to_literal(ctx, c->pair[i].cond);
    if (a[i] == true_literal) {
      /*
       * a[0] ... a[i-1] are all reducible to false
       * but we can't assume that a[0] ... a[i-1] are all false_literals
       * since we don't know how the theory solver internalizes the
       * conditions.
       */
      v = internalize_to_eterm(ctx, c->pair[i].val);
      if (all_false) {
	// all previous conditions a[0 ... i-1] are false
	assert(u == null_occurrence);
	u = v;
      } else {
	// we assert (u == v) as a top-level equality
	egraph_assert_eq_axiom(ctx->egraph, u, v);
      }
      goto done;
    }
    if (a[i] != false_literal) {
      if (all_false) {
	assert(u == null_occurrence);
	u = pos_occ(make_egraph_variable(ctx, tau));
	all_false = false;
      }
      // one clause for a[i] => (u = v[i])
      v = internalize_to_eterm(ctx, c->pair[i].val);
      l = egraph_make_eq(ctx->egraph, u, v);
      add_binary_clause(ctx->core, not(a[i]), l);
    }
  }

  if (all_false) {
    assert(u == null_occurrence);
    u = internalize_to_eterm(ctx, c->defval);
    goto done;
  }

  // clause for the default value
  assert(u != null_occurrence);
  v = internalize_to_eterm(ctx, c->defval);
  l = egraph_make_eq(ctx->egraph, u, v);
  a[n] = l;
  add_clause(ctx->core, n+1, a);

 done:
  free_istack_array(&ctx->istack, a);

  return u;
}


/*
 * Auxiliary function for flattening if-then-else
 * - v contains a conjunction of n literals: l0 /\ ... /\ l_n
 * - we something like (l0 /\ ... /\ l_n implies (x = y))
 *   (i.e., (not l0) \/ ... \/ (not l_n) \/ (x = y)
 * - this function negates all the literals in place
 */
static void ite_prepare_antecedents(ivector_t *v) {
  uint32_t i, n;

  n = v->size;
  for (i=0; i<n; i++) {
    v->data[i] = not(v->data[i]);
  }
}


/*
 * Convert nested if-then-else to  an egraph term
 * - ite = term of the form (ite c1 t1 t2)
 * - c = internalization of c1
 * - tau = type of the term (ite c1 t1 t2)
 */
static occ_t flatten_ite_to_eterm(context_t *ctx, composite_term_t *ite, literal_t c, type_t tau) {
  ite_flattener_t flattener;
  ivector_t *buffer;
  term_t x;
  occ_t u, v;
  literal_t l;

  u = pos_occ(make_egraph_variable(ctx, tau));

  init_ite_flattener(&flattener);
  ite_flattener_push(&flattener, ite, c);

  while (ite_flattener_is_nonempty(&flattener)) {
    if (ite_flattener_last_lit_false(&flattener)) {
      // dead branch
      ite_flattener_next_branch(&flattener);
      continue;
    }
    assert(ite_flattener_branch_is_live(&flattener));

    x = ite_flattener_leaf(&flattener);
    x = intern_tbl_get_root(&ctx->intern, x);

    /*
     * x is the current leaf.
     * If it's (ite ...) then we can expand the tree by pushing x.
     *
     * Heuristic: we don't do it if x is a shared term or if it's
     * already internalized.
     * - we also need a cutoff since the number of branches grows
     *   exponentially.
     */
    if (is_pos_term(x) &&
	is_ite_term(ctx->terms, x) &&
	!intern_tbl_root_is_mapped(&ctx->intern, x) &&
	term_is_not_shared(&ctx->sharing, x)) {
      /*
       * x is of the form (ite c a b) and not internalized already,
       * we push (ite c a b) on the flattener.
       */
      ite = ite_term_desc(ctx->terms, x);
      assert(ite->arity == 3);
      c = internalize_to_literal(ctx, ite->arg[0]);
      ite_flattener_push(&flattener, ite, c);
    } else {
      /*
       * Add the clause [branch conditions => x = u]
       */
      v = internalize_to_eterm(ctx, x);
      l = egraph_make_eq(ctx->egraph, u, v);

      buffer = &ctx->aux_vector;
      assert(buffer->size == 0);
      ite_flattener_get_clause(&flattener, buffer);
      ite_prepare_antecedents(buffer);
      ivector_push(buffer, l);
      add_clause(ctx->core, buffer->size, buffer->data);
      ivector_reset(buffer);

      ite_flattener_next_branch(&flattener);
    }
  }

  delete_ite_flattener(&flattener);

  return u;
}


/*
 * Convert (ite c t1 t2) to an egraph term
 * - tau = type of (ite c t1 t2)
 */
static occ_t map_ite_to_eterm(context_t *ctx, composite_term_t *ite, type_t tau) {
  conditional_t *d;
  eterm_t u;
  occ_t u1, u2, u3;
  literal_t c, l1, l2;


  d = context_make_conditional(ctx, ite);
  if (d != NULL) {
    u1 = map_conditional_to_eterm(ctx, d, tau);
    context_free_conditional(ctx, d);
    return u1;
  }

  c = internalize_to_literal(ctx, ite->arg[0]);
  if (c == true_literal) {
    return internalize_to_eterm(ctx, ite->arg[1]);
  }
  if (c == false_literal) {
    return internalize_to_eterm(ctx, ite->arg[2]);
  }

  if (context_ite_flattening_enabled(ctx)) {
    return flatten_ite_to_eterm(ctx, ite, c, tau);
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

  if (! context_has_arith_solver(ctx)) {
    longjmp(ctx->env, ARITH_NOT_SUPPORTED);
  }

  x = ctx->arith.create_const(ctx->arith_solver, q);
  return translate_arithvar_to_eterm(ctx, x);
}

static occ_t map_bvconst64_to_eterm(context_t *ctx, bvconst64_term_t *c) {
  thvar_t x;
  type_t tau;

  if (! context_has_bv_solver(ctx)) {
    longjmp(ctx->env, BV_NOT_SUPPORTED);
  }

  x = ctx->bv.create_const64(ctx->bv_solver, c);
  tau = bv_type(ctx->types, c->bitsize);

  return translate_bvvar_to_eterm(ctx, x, tau);
}

static occ_t map_bvconst_to_eterm(context_t *ctx, bvconst_term_t *c) {
  thvar_t x;
  type_t tau;

  if (! context_has_bv_solver(ctx)) {
    longjmp(ctx->env, BV_NOT_SUPPORTED);
  }

  x = ctx->bv.create_const(ctx->bv_solver, c);
  tau = bv_type(ctx->types, c->bitsize);

  return translate_bvvar_to_eterm(ctx, x, tau);
}



/***************************************
 *  AXIOMS FOR DIV/MOD/FLOOR/CEIL/ABS  *
 **************************************/

/*
 * Auxiliary function: p and map to represent (x - y)
 * - in polynomial p, only the coefficients are relevant
 * - map[0] stores x and map[1] stores y
 * - both p map must be large enough (at least 2 elements)
 */
static void context_store_diff_poly(polynomial_t *p, thvar_t *map, thvar_t x, thvar_t y) {
  p->nterms = 2;
  p->mono[0].var = 1;
  q_set_one(&p->mono[0].coeff);       // coeff of x = 1
  p->mono[1].var = 2;
  q_set_minus_one(&p->mono[1].coeff); // coeff of y = -1
  p->mono[2].var = max_idx; // end marker

  map[0] = x;
  map[1] = y;
}


/*
 * Same thing for the polynomial (x - y - 1)
 */
static void context_store_diff_minus_one_poly(polynomial_t *p, thvar_t *map, thvar_t x, thvar_t y) {
  p->nterms = 3;
  p->mono[0].var = const_idx;
  q_set_minus_one(&p->mono[0].coeff);  // constant = -1
  p->mono[1].var = 1;
  q_set_one(&p->mono[1].coeff);        // coeff of x = 1
  p->mono[2].var = 2;
  q_set_minus_one(&p->mono[2].coeff);  // coeff of y = -1
  p->mono[3].var = max_idx;

  map[0] = null_thvar; // constant
  map[1] = x;
  map[2] = y;
}


/*
 * Same thing for the polynomial (x + y)
 */
static void context_store_sum_poly(polynomial_t *p, thvar_t *map, thvar_t x, thvar_t y) {
  p->nterms = 2;
  p->mono[0].var = 1;
  q_set_one(&p->mono[0].coeff); // coeff of x = 1
  p->mono[1].var = 2;
  q_set_one(&p->mono[1].coeff); // coeff of y = 1
  p->mono[2].var = max_idx;

  map[0] = x;
  map[1] = y;
}


/*
 * The lower bound on y = (div x k)  is (k * y <= x) or (x - k * y >= 0)
 * We store the polynomial x - k * y
 */
static void context_store_div_lower_bound(polynomial_t *p, thvar_t *map, thvar_t x, thvar_t y, const rational_t *k) {
  p->nterms = 2;
  p->mono[0].var = 1;
  q_set_one(&p->mono[0].coeff);    // coeff of x = 1
  p->mono[1].var = 2;
  q_set_neg(&p->mono[1].coeff, k); // coeff of y = -k
  p->mono[2].var = max_idx;

  map[0] = x;
  map[1] = y;
}


/*
 * For converting (divides k x), we use (divides k x) <=> (x <= k * (div x k))
 * or (k * y - x >= 0) for y = (div x k).
 * We store the polynomial - x + k * y.
 */
static void context_store_divides_constraint(polynomial_t *p, thvar_t *map, thvar_t x, thvar_t y, const rational_t *k) {
  p->nterms = 2;
  p->mono[0].var = 1;
  q_set_minus_one(&p->mono[0].coeff);  // coeff of x = -1
  p->mono[1].var = 2;
  q_set(&p->mono[1].coeff, k);         // coeff of y = k
  p->mono[2].var = max_idx;

  map[0] = x;
  map[1] = y;
}

/*
 * Upper bound on y = (div x k) when both x and y are integer:
 * We have x <= k * y + |k| - 1 or (-x + k y + |k| - 1 >= 0).
 *
 * We store the polynomial - x + k y + |k| - 1
 *
 * NOTE: we don't normalize the constant (|k| - 1) to zero if |k| = 1.
 * This is safe as the simplex solver does not care.
 */
static void context_store_integer_div_upper_bound(polynomial_t *p, thvar_t *map, thvar_t x, thvar_t y, const rational_t *k) {
  p->nterms = 3;
  p->mono[0].var = const_idx;
  q_set_abs(&p->mono[0].coeff, k);
  q_sub_one(&p->mono[0].coeff);        // constant term = |k| - 1
  p->mono[1].var = 1;
  q_set_minus_one(&p->mono[1].coeff);  // coeff of x = -1
  p->mono[2].var = 2;
  q_set(&p->mono[2].coeff, k);         // coeff of y = k
  p->mono[3].var = max_idx;

  map[0] = null_thvar;
  map[1] = x;
  map[2] = y;
}

/*
 * Upper bound on y = (div x k) when x or k is not an integer.
 * We have x < k * y + |k| or x - k*y - |k| < 0 or (not (x - k*y - |k| >= 0))
 *
 * We store the polynomial x - ky - |k|
 */
static void context_store_rational_div_upper_bound(polynomial_t *p, thvar_t *map, thvar_t x, thvar_t y, const rational_t *k) {
  p->nterms = 3;
  p->mono[0].var = const_idx;
  q_set_abs(&p->mono[0].coeff, k);
  q_neg(&p->mono[0].coeff);           // constant term: -|k|
  p->mono[1].var = 1;
  q_set_one(&p->mono[1].coeff);       // coeff of x = +1
  p->mono[2].var = 2;
  q_set_neg(&p->mono[2].coeff, k);    // coeff of y = -k
  p->mono[3].var = max_idx;

  map[0] = null_thvar;
  map[1] = x;
  map[2] = y;
}


/*
 * Polynomial x - y + k d (for asserting y = k * (div y k) + (mod y k)
 * - d is assumed to be (div y k)
 * - x is assumed to be (mod y k)
 */
static void context_store_divmod_eq(polynomial_t *p, thvar_t *map, thvar_t x, thvar_t y, thvar_t d, const rational_t *k) {
  p->nterms = 3;
  p->mono[0].var = 1;
  q_set_one(&p->mono[0].coeff);       // coefficient of x = 1
  p->mono[1].var = 2;
  q_set_minus_one(&p->mono[1].coeff); // coefficient of y = -1
  p->mono[2].var = 3;
  q_set(&p->mono[2].coeff, k);        // coefficient of d = k
  p->mono[3].var = max_idx;

  map[0] = x;
  map[1] = y;
  map[2] = d;
}


/*
 * Bound on x = (mod y k) assuming x and k are integer:
 * - the bound is x <= |k| - 1 (i.e., |k| - 1 - x >= 0)
 *   so we construct |k| - 1 - x
 */
static void context_store_integer_mod_bound(polynomial_t *p, thvar_t *map, thvar_t x, const rational_t *k) {
  p->nterms = 2;
  p->mono[0].var = const_idx;
  q_set_abs(&p->mono[0].coeff, k);
  q_sub_one(&p->mono[0].coeff);        // constant = |k| - 1
  p->mono[1].var = 1;
  q_set_minus_one(&p->mono[1].coeff);  // coeff of x = -1
  p->mono[2].var = max_idx;

  map[0] = null_thvar;
  map[1] = x;
}


/*
 * Bound on x = (mod y k) when x or k are rational
 * - the bound is x < |k| or x - |k| < 0 or (not (x - |k| >= 0))
 *   so we construct x - |k|
 */
static void context_store_rational_mod_bound(polynomial_t *p, thvar_t *map, thvar_t x, const rational_t *k) {
  p->nterms = 2;
  p->mono[0].var = const_idx;
  q_set_abs(&p->mono[0].coeff, k);
  q_neg(&p->mono[0].coeff);            // constant = -|k|
  p->mono[1].var = 1;
  q_set_one(&p->mono[1].coeff);        // coeff of x = +1
  p->mono[2].var = max_idx;

  map[0] = null_thvar;
  map[1] = x;
}


/*
 * Assert constraints for x := floor(y)
 * - both x and y are variables in the arithmetic solver
 * - x has type integer
 *
 * We assert (x <= y && y < x+1)
 */
static void assert_floor_axioms(context_t *ctx, thvar_t x, thvar_t y) {
  polynomial_t *p;
  thvar_t map[3];

  assert(ctx->arith.arith_var_is_int(ctx->arith_solver, x));

  p = context_get_aux_poly(ctx, 4);

  // assert (y - x >= 0)
  context_store_diff_poly(p, map, y, x);
  ctx->arith.assert_poly_ge_axiom(ctx->arith_solver, p, map, true);

  // assert (y - x - 1 < 0) <=> (not (y - x - 1) >= 0)
  context_store_diff_minus_one_poly(p, map, y, x);
  ctx->arith.assert_poly_ge_axiom(ctx->arith_solver, p, map, false);
}


/*
 * Assert constraints for x == ceil(y)
 * - both x and y are variables in the arithmetic solver
 * - x has type integer
 *
 * We assert (x - 1 < y && y <= x)
 */
static void assert_ceil_axioms(context_t *ctx, thvar_t x, thvar_t y) {
  polynomial_t *p;
  thvar_t map[3];

  assert(ctx->arith.arith_var_is_int(ctx->arith_solver, x));

  p = context_get_aux_poly(ctx, 4);

  // assert (x - y >= 0)
  context_store_diff_poly(p, map, x, y);
  ctx->arith.assert_poly_ge_axiom(ctx->arith_solver, p, map, true);

  // assert (x - y - 1 < 0) <=> (not (x - y - 1) >= 0)
  context_store_diff_minus_one_poly(p, map, x, y);
  ctx->arith.assert_poly_ge_axiom(ctx->arith_solver, p, map, false);
}


/*
 * Assert constraints for x == abs(y)
 * - x and y must be variables in the arithmetic solver
 *
 * We assert (x >= 0) AND ((x == y) or (x == -y))
 */
static void assert_abs_axioms(context_t *ctx, thvar_t x, thvar_t y) {
  polynomial_t *p;
  thvar_t map[2];
  literal_t l1, l2;

  // assert (x >= 0)
  ctx->arith.assert_ge_axiom(ctx->arith_solver, x, true);

  // create l1 := (x == y)
  l1 = ctx->arith.create_vareq_atom(ctx->arith_solver, x, y);

  // create l2 := (x == -y) that is (x + y == 0)
  p = context_get_aux_poly(ctx, 3);
  context_store_sum_poly(p, map, x, y);
  l2 = ctx->arith.create_poly_eq_atom(ctx->arith_solver, p, map);

  // assert (or l1 l2)
  add_binary_clause(ctx->core, l1, l2);
}


/*
 * Constraints for x == (div y k)
 * - x and y must be variables in the arithmetic solver
 * - x must be an integer variable
 * - k is a non-zero rational constant
 *
 * If k and y are integer, we assert
 *   k * x <= y <= k * x + |k| - 1
 *
 * Otherwise, we assert
 *   k * x <= y < k * x + |k|
 */
static void assert_div_axioms(context_t *ctx, thvar_t x, thvar_t y, const rational_t *k) {
  polynomial_t *p;
  thvar_t map[3];

  p = context_get_aux_poly(ctx, 4);

  // assert k*x <= y (i.e., y - k*x >= 0)
  context_store_div_lower_bound(p, map, y, x, k);
  ctx->arith.assert_poly_ge_axiom(ctx->arith_solver, p, map, true);

  if (ctx->arith.arith_var_is_int(ctx->arith_solver, y) && q_is_integer(k)) {
    // y and k are both integer
    // assert y <= k*x + |k| - 1 (i.e., - y + k x + |k| - 1 >= 0)
    context_store_integer_div_upper_bound(p, map, y, x, k);
    ctx->arith.assert_poly_ge_axiom(ctx->arith_solver, p, map, true);

  } else {
    // assert y < k*x + |k| (i.e., y - k*x - |k| < 0) or (not (y - k*x - |k| >= 0))
    context_store_rational_div_upper_bound(p, map, y, x, k);
    ctx->arith.assert_poly_ge_axiom(ctx->arith_solver, p, map, false);
  }
}


/*
 * Constraints for x == (mod y k)
 * - d must be the variable equal to (div y k)
 * - x and y must be variables in the arithmetic solver
 * - k is a non-zero rational constant.
 *
 * We assert x = y - k * d (i.e., (mod y k) = x - k * (div y k))
 * and 0 <= x < |k|.
 *
 * NOTE: The 0 <= x < |k| part is redundant. It's implied by the
 * div_axioms for d = (div y k). It's cheap enough that I can't
 * see a problem with adding it anyway (it's just an interval for x).
 */
static void assert_mod_axioms(context_t *ctx, thvar_t x, thvar_t y, thvar_t d, const rational_t *k) {
  polynomial_t *p;
  thvar_t map[3];

  p = context_get_aux_poly(ctx, 4);

  // assert y = k * d + x (i.e., x - y + k *d = 0)
  context_store_divmod_eq(p, map, x, y, d, k);
  ctx->arith.assert_poly_eq_axiom(ctx->arith_solver, p, map, true);

  // assert x >= 0
  ctx->arith.assert_ge_axiom(ctx->arith_solver, x, true);

  if (ctx->arith.arith_var_is_int(ctx->arith_solver, x) && q_is_integer(k)) {
    // both x and |k| are integer
    // assert x <= |k| - 1, i.e., -x + |k| - 1 >= 0
    context_store_integer_mod_bound(p, map, x, k);
    ctx->arith.assert_poly_ge_axiom(ctx->arith_solver, p, map, true);
  } else {
    // assert x < |k|, i.e., x - |k| <0, i.e., (not (x - |k| >= 0))
    context_store_rational_mod_bound(p, map, x, k);
    ctx->arith.assert_poly_ge_axiom(ctx->arith_solver, p, map, false);
  }
}



/******************************************************
 *  CONVERSION OF COMPOSITES TO ARITHMETIC VARIABLES  *
 *****************************************************/

/*
 * Convert a conditional to an arithmetic variable
 * - if is_int is true, the variable is integer otherwise, it's real
 */
static thvar_t map_conditional_to_arith(context_t *ctx, conditional_t *c, bool is_int) {
  literal_t *a;
  uint32_t i, n;
  thvar_t x, v;
  bool all_false;
  term_t t;

#if 0
  printf("---> conditional to arith\n");
#endif

  t = simplify_conditional(ctx, c);
  if (t != NULL_TERM) {
    return internalize_to_arith(ctx, t);
  }

  n = c->nconds;
  a = alloc_istack_array(&ctx->istack, n);

  all_false = true;
  v = null_thvar;

  for (i=0; i<n; i++) {
    a[i] = internalize_to_literal(ctx, c->pair[i].cond);
    if (a[i] == true_literal) {
      /*
       * a[0] ... a[i-1] are all reducible to false
       * but we can't assume v == null_thvar, since
       * we don't know how the theory solver internalizes
       * the conditions (i.e., some of them may not be false_literal).
       */
      x = internalize_to_arith(ctx, c->pair[i].val);
      if (all_false) {
	assert(v == null_thvar);
	v = x;
      } else {
	// assert (v == x) in the arithmetic solver
	ctx->arith.assert_vareq_axiom(ctx->arith_solver, v, x, true);
      }
      goto done;
    }
    if (a[i] != false_literal) {
      if (all_false) {
	assert(v == null_thvar);
	v = ctx->arith.create_var(ctx->arith_solver, is_int);
	all_false = false;
      }
      // clause for a[i] => (v = c->pair[i].val)
      x = internalize_to_arith(ctx, c->pair[i].val);
      ctx->arith.assert_cond_vareq_axiom(ctx->arith_solver, a[i], v, x);
    }
  }

  if (all_false) {
    assert(v == null_thvar);
    v = internalize_to_arith(ctx, c->defval);
    goto done;
  }

  /*
   * last clause (only if some a[i] isn't false):
   * (a[0] \/ ... \/ a[n-1] \/ v == c->defval)
   */
  assert(v != null_thvar);
  x = internalize_to_arith(ctx, c->defval);
  ctx->arith.assert_clause_vareq_axiom(ctx->arith_solver, n, a, v, x);

 done:
  free_istack_array(&ctx->istack, a);
  return v;
}


/*
 * Convert nested if-then-else to  an arithmetic variable
 * - ite = term of the form (ite c1 t1 t2)
 * - c = internalization of c1
 * - is_int = true if the if-then-else term is integer (otherwise it's real)
 */
static thvar_t flatten_ite_to_arith(context_t *ctx, composite_term_t *ite, literal_t c, bool is_int) {
  ite_flattener_t flattener;
  ivector_t *buffer;
  term_t x;
  thvar_t u, v;

  u = ctx->arith.create_var(ctx->arith_solver, is_int);

  init_ite_flattener(&flattener);
  ite_flattener_push(&flattener, ite, c);

  while (ite_flattener_is_nonempty(&flattener)) {
    if (ite_flattener_last_lit_false(&flattener)) {
      // dead branch
      ite_flattener_next_branch(&flattener);
      continue;
    }
    assert(ite_flattener_branch_is_live(&flattener));

    x = ite_flattener_leaf(&flattener);
    x = intern_tbl_get_root(&ctx->intern, x);

    /*
     * x is the current leaf
     * If x is of the form (ite c a b) we can push (ite c a b) on the flattener.
     *
     * Heuristics: don't push the term if x is already internalized or if it's
     * shared.
     */
    if (is_pos_term(x) &&
	is_ite_term(ctx->terms, x) &&
	!intern_tbl_root_is_mapped(&ctx->intern, x) &&
	term_is_not_shared(&ctx->sharing, x)) {
      ite = ite_term_desc(ctx->terms, x);
      assert(ite->arity == 3);
      c = internalize_to_literal(ctx, ite->arg[0]);
      ite_flattener_push(&flattener, ite, c);
    } else {
      /*
       * Add the clause [branch conditions => x = u]
       */
      v = internalize_to_arith(ctx, x);

      buffer = &ctx->aux_vector;
      assert(buffer->size == 0);
      ite_flattener_get_clause(&flattener, buffer);
      ite_prepare_antecedents(buffer);
      // assert [buffer \/ v = u]
      ctx->arith.assert_clause_vareq_axiom(ctx->arith_solver, buffer->size, buffer->data, v, u);
      ivector_reset(buffer);

      ite_flattener_next_branch(&flattener);
    }
  }

  delete_ite_flattener(&flattener);

  return u;
}

/*
 * Convert if-then-else to an arithmetic variable
 * - if is_int is true, the if-then-else term is integer
 * - otherwise, it's real
 */
static thvar_t map_ite_to_arith(context_t *ctx, composite_term_t *ite, bool is_int) {
  conditional_t *d;
  literal_t c;
  thvar_t v, x;

  assert(ite->arity == 3);

  d = context_make_conditional(ctx, ite);
  if (d != NULL) {
    v = map_conditional_to_arith(ctx, d, is_int);
    context_free_conditional(ctx, d);
    return v;
  }

  c = internalize_to_literal(ctx, ite->arg[0]); // condition
  if (c == true_literal) {
    return internalize_to_arith(ctx, ite->arg[1]);
  }
  if (c == false_literal) {
    return internalize_to_arith(ctx, ite->arg[2]);
  }

  if (context_ite_flattening_enabled(ctx)) {
    return flatten_ite_to_arith(ctx, ite, c, is_int);
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
 * Assert the bounds on t when t is an arithmetic, special if-then-else
 * - x = arithmetic variable mapped to t in the arithmetic solver
 */
static void assert_ite_bounds(context_t *ctx, term_t t, thvar_t x) {
  term_table_t *terms;
  polynomial_t *p;
  term_t lb, ub;
  thvar_t map[2];

  terms = ctx->terms;
  assert(is_arithmetic_term(terms, t));

  // get lower and upper bound on t. Both are rational constants
  term_finite_domain_bounds(terms, t, &lb, &ub);

#if 0
  printf("assert ite bound:\n  term: ");
  print_term_name(stdout, terms, t);
  printf("\n");
  printf("  lower bound: ");
  print_term_full(stdout, terms, lb);
  printf("\n");
  printf("  upper bound: ");
  print_term_full(stdout, terms, ub);
  printf("\n");
#endif

  /*
   * prepare polynomial p:
   * first monomial is a constant, second monomial is either +t or -t
   * map[0] = null (what's mapped to const_idx)
   * map[1] = x = (what's mapped to t)
   */
  p = context_get_aux_poly(ctx, 3);
  p->nterms = 2;
  p->mono[0].var = const_idx;
  p->mono[1].var = t;
  p->mono[2].var = max_idx;
  map[0] = null_thvar;
  map[1] = x;


  // first bound: t >= lb
  q_set_neg(&p->mono[0].coeff, rational_term_desc(terms, lb)); // -lb
  q_set_one(&p->mono[1].coeff); // +t
  ctx->arith.assert_poly_ge_axiom(ctx->arith_solver, p, map, true); // assert -lb + t >= 0

  // second bound: t <= ub
  q_set(&p->mono[0].coeff, rational_term_desc(terms, ub));  // +ub
  q_set_minus_one(&p->mono[1].coeff);  // -t
  ctx->arith.assert_poly_ge_axiom(ctx->arith_solver, p, map, true); // assert +ub - t >= 0
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


/*
 * Auxiliary function: return y := (floor x)
 * - check the divmod table first.
 *   If there's a record for (floor x), return the corresponding variable.
 * - Otherwise, create a fresh integer variable y,
 *   assert the axioms for y = (floor x)
 *   add a record to the divmod table and return y.
 */
static thvar_t get_floor(context_t *ctx, thvar_t x) {
  thvar_t y;

  y = context_find_var_for_floor(ctx, x);
  if (y == null_thvar) {
    y = ctx->arith.create_var(ctx->arith_solver, true); // y is an integer variable
    assert_floor_axioms(ctx, y, x); // assert y = floor(x)
    context_record_floor(ctx, x, y); // save the mapping y --> floor(x)
  }

  return y;
}


/*
 * Return y := (div x k)
 * - check the divmod table first
 * - if (div x k) has already been processed, return the corresponding variable
 * - otherwise create a new variable y, assert the axioms for y = (div x k)
 *   add a record in the divmod table, and return y.
 */
static thvar_t get_div(context_t *ctx, thvar_t x, const rational_t *k) {
  thvar_t y;

  y = context_find_var_for_div(ctx, x, k);
  if (y == null_thvar) {
    // create y := (div x k)
    y = ctx->arith.create_var(ctx->arith_solver, true); // y is an integer
    assert_div_axioms(ctx, y, x, k);
    context_record_div(ctx, x, k, y);
  }

  return y;
}



/*
 * Convert (floor t) to an arithmetic variable
 */
static thvar_t map_floor_to_arith(context_t *ctx, term_t t) {
  thvar_t x, y;

  x = internalize_to_arith(ctx, t);
  if (ctx->arith.arith_var_is_int(ctx->arith_solver, x)) {
    // x is integer so (floor x) = x
    y = x;
  } else {
    y = get_floor(ctx, x);
  }

  return y;
}


/*
 * Convert (ceil t) to an arithmetic variable
 */
static thvar_t map_ceil_to_arith(context_t *ctx, term_t t) {
  thvar_t x, y;

  x = internalize_to_arith(ctx, t);
  if (ctx->arith.arith_var_is_int(ctx->arith_solver, x)) {
    // x is integer so (ceil x) = x
    y = x;
  } else {
    y = context_find_var_for_ceil(ctx, x);
    if (y == null_thvar) {
      y = ctx->arith.create_var(ctx->arith_solver, true); // y is an integer variable
      assert_ceil_axioms(ctx, y, x); // assert y = ceil(x)
      context_record_ceil(ctx, x, y); // save the mapping y --> ceil(x)
    }
  }

  return y;
}


/*
 * Convert (abs t) to an arithmetic variable
 */
static thvar_t map_abs_to_arith(context_t *ctx, term_t t) {
  thvar_t x, y;
  bool is_int;

  x = internalize_to_arith(ctx, t);
  is_int = ctx->arith.arith_var_is_int(ctx->arith_solver, x);
  y = ctx->arith.create_var(ctx->arith_solver, is_int); // y := abs(x) has the same type as x
  assert_abs_axioms(ctx, y, x);

  return y;
}


/*
 * Auxiliary function: check whether t is a non-zero arithmetic constant
 * - if so, store t's value in *val
 */
static bool is_non_zero_rational(term_table_t *tbl, term_t t, rational_t *val) {
  assert(is_arithmetic_term(tbl, t));

  if (term_kind(tbl, t) == ARITH_CONSTANT) {
    q_set(val, rational_term_desc(tbl, t));
    return q_is_nonzero(val);
  }
  return false;
}

/*
 * Convert (/ t1 t2) to an arithmetic variable
 * - t2 must be a non-zero arithmetic constant
 */
static thvar_t map_rdiv_to_arith(context_t *ctx, composite_term_t *div) {
  // Could try to evaluate t2 then check whether that's a constant
  assert(div->arity == 2);
  longjmp(ctx->env, FORMULA_NOT_LINEAR);
}


/*
 * Convert (div t1 t2) to an arithmetic variable.
 * - fails if t2 is not an arithmetic constant or if it's zero
 */
static thvar_t map_idiv_to_arith(context_t *ctx, composite_term_t *div) {
  rational_t k;
  thvar_t x, y;

  assert(div->arity == 2);

  q_init(&k);
  if (is_non_zero_rational(ctx->terms, div->arg[1], &k)) { // k := value of t2
    assert(q_is_nonzero(&k));
    x = internalize_to_arith(ctx, div->arg[0]); // t1
    y = get_div(ctx, x, &k);

  } else {
    // division by a non-constant or by zero: not supported by default
    // arithmetic solver for now
    q_clear(&k);
    longjmp(ctx->env, FORMULA_NOT_LINEAR);
  }
  q_clear(&k);

  return y;
}


/*
 * Convert (mod t1 t2) to an arithmetic variable
 * - t2 must be a non-zero constant
 */
static thvar_t map_mod_to_arith(context_t *ctx, composite_term_t *mod) {
  rational_t k;
  thvar_t x, y, r;
  bool is_int;

  assert(mod->arity == 2);

  q_init(&k);
  if (is_non_zero_rational(ctx->terms, mod->arg[1], &k)) { // k := divider
    x = internalize_to_arith(ctx, mod->arg[0]);

    // get y := (div x k)
    assert(q_is_nonzero(&k));
    y = get_div(ctx, x, &k);

    /*
     * r := (mod x k) is x - k * y where y is an integer.
     * If both x and k are integer, then r has integer type. Otherwise,
     * r is a real variable.
     */
    is_int = ctx->arith.arith_var_is_int(ctx->arith_solver, x) && q_is_integer(&k);
    r = ctx->arith.create_var(ctx->arith_solver, is_int);
    assert_mod_axioms(ctx, r, x, y, &k);

  } else {
    // Non-constant or zero divider
    q_clear(&k);
    longjmp(ctx->env, FORMULA_NOT_LINEAR);
  }

  q_clear(&k);

  return r;
}



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

  assert(p->nterms > 0);

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

  assert(p->nterms > 0);

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


#if 0
/*
 * Bvpoly buffer: b must be normalized.
 * - not optimal but this shouldn't be called often.
 */
static thvar_t map_bvpoly_buffer_to_bv(context_t *ctx, bvpoly_buffer_t *b) {
  bvpoly64_t *p;
  bvpoly_t *q;
  uint32_t n;
  thvar_t x;

  n = bvpoly_buffer_bitsize(b);

  if (bvpoly_buffer_is_zero(b)) {
    x = ctx->bv.create_zero(ctx->bv_solver, n);
  } else if (n <= 64) {
    p = bvpoly_buffer_getpoly64(b);
    x = map_bvpoly64_to_bv(ctx, p);
    free_bvpoly64(p);
  } else {
    q = bvpoly_buffer_getpoly(b);
    x = map_bvpoly_to_bv(ctx, q);
    free_bvpoly(q);
  }

  return x;
}

#endif

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

    // try easy simplification
    n = v->size;
    if (disjunct_is_true(ctx, v->data, n)) {
      ivector_reset(v);
      return true_literal;
    }

    // make a copy of v
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
    if (disjunct_is_true(ctx, or->arg, n)) {
      return true_literal;
    }

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
    longjmp(ctx->env, uf_error_code(ctx, distinct->arg[0]));
  }

  free_istack_array(&ctx->istack, a);

  return l;
}



/*
 * Arithmetic atom: p == 0
 */
static literal_t map_poly_eq_to_literal(context_t *ctx, polynomial_t *p) {
  uint32_t i, n;
  thvar_t *a;
  literal_t l;

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

  // build the atom
  l = ctx->arith.create_poly_eq_atom(ctx->arith_solver, p, a);
  free_istack_array(&ctx->istack, a);

  return l;
}


/*
 * Arithmetic atom: (p >= 0)
 */
static literal_t map_poly_ge_to_literal(context_t *ctx, polynomial_t *p) {
  uint32_t i, n;
  thvar_t *a;
  literal_t l;

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

  // build the atom
  l = ctx->arith.create_poly_ge_atom(ctx->arith_solver, p, a);
  free_istack_array(&ctx->istack, a);

  return l;
}


/*
 * Arithmetic atom: (t >= 0)
 */
static literal_t map_arith_geq_to_literal(context_t *ctx, term_t t) {
  term_table_t *terms;
  thvar_t x;
  literal_t l;

  terms = ctx->terms;
  if (term_kind(terms, t) == ARITH_POLY) {
    l = map_poly_ge_to_literal(ctx, poly_term_desc(terms, t));
  } else {
    x = internalize_to_arith(ctx, t);
    l = ctx->arith.create_ge_atom(ctx->arith_solver, x);
  }

  return l;
}



/*
 * Arithmetic equalities (eq t1 t2)
 * 1) try to flatten the if-then-elses
 * 2) also apply cheap lift-if rule: (eq (ite c t1 t2) u1) --> (ite c (eq t1 u1) (eq t2 u1))
 */
static literal_t map_arith_bineq(context_t *ctx, term_t t1, term_t u1);

/*
 * Lift equality: (eq (ite c u1 u2) t) --> (ite c (eq u1 t) (eq u2 t))
 */
static literal_t map_ite_arith_bineq(context_t *ctx, composite_term_t *ite, term_t t) {
  literal_t l1, l2, l3;

  assert(ite->arity == 3);
  l1 = internalize_to_literal(ctx, ite->arg[0]);
  if (l1 == true_literal) {
    // (eq (ite true u1 u2) t) --> (eq u1 t)
    return map_arith_bineq(ctx, ite->arg[1], t);
  }
  if (l1 == false_literal) {
    // (eq (ite true u1 u2) t) --> (eq u2 t)
    return map_arith_bineq(ctx, ite->arg[2], t);
  }

  // apply lift-if here
  l2 = map_arith_bineq(ctx, ite->arg[1], t);
  l3 = map_arith_bineq(ctx, ite->arg[2], t);

  return mk_ite_gate(&ctx->gate_manager, l1, l2, l3);
}

static literal_t map_arith_bineq_aux(context_t *ctx, term_t t1, term_t t2) {
  term_table_t *terms;
  thvar_t x, y;
  occ_t u, v;
  literal_t l;

  /*
   * Try to apply lift-if rule: (eq (ite c u1 u2) t2) --> (ite c (eq u1 t2) (eq u2 t2))
   * do this only if t2 is not an if-then-else term.
   *
   * Otherwise add the atom (eq t1 t2) to the egraph if possible
   * or create (eq t1 t2) in the arithmetic solver.
   */
  terms = ctx->terms;
  if (is_ite_term(terms, t1) && ! is_ite_term(terms, t2)) {
    l = map_ite_arith_bineq(ctx, ite_term_desc(terms, t1), t2);
  } else if (is_ite_term(terms, t2) && !is_ite_term(terms, t1)) {
    l = map_ite_arith_bineq(ctx, ite_term_desc(terms, t2), t1);
  } else if (context_has_egraph(ctx)) {
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

static literal_t map_arith_bineq(context_t *ctx, term_t t1, term_t u1) {
  ivector_t *v;
  int32_t *a;
  uint32_t i, n;
  term_t t2, u2;
  literal_t l;

  t1 = intern_tbl_get_root(&ctx->intern, t1);
  u1 = intern_tbl_get_root(&ctx->intern, u1);

  if (t1 == u1) {
    return true_literal;
  }

  /*
   * Check the cache
   */
  l = find_in_eq_cache(ctx, t1, u1);
  if (l == null_literal) {
    /*
     * The pair (t1, u1) is not mapped already.
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
      l = map_arith_bineq_aux(ctx, t2, u2);

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
      a[n] = map_arith_bineq_aux(ctx, t2, u2);

      // build (and a[0] ... a[n])
      l = mk_and_gate(&ctx->gate_manager, n+1, a);
      free_istack_array(&ctx->istack, a);
    }

    /*
     * Store the mapping (t1, u1) --> l in the cache
     */
    add_to_eq_cache(ctx, t1, u1, l);
  }

  return l;
}


static inline literal_t map_arith_bineq_to_literal(context_t *ctx, composite_term_t *eq) {
  assert(eq->arity == 2);
  return map_arith_bineq(ctx, eq->arg[0], eq->arg[1]);
}



/*
 * Arithmetic atom: (t == 0)
 */
static literal_t map_arith_eq_to_literal(context_t *ctx, term_t t) {
  term_table_t *terms;
  thvar_t x;
  literal_t l;

  terms = ctx->terms;
  if (term_kind(terms, t) == ARITH_POLY) {
    l = map_poly_eq_to_literal(ctx, poly_term_desc(terms, t));
  } else if (is_ite_term(terms, t)) {
    l = map_arith_bineq(ctx, t, zero_term);
  } else {
    x = internalize_to_arith(ctx, t);
    l = ctx->arith.create_eq_atom(ctx->arith_solver, x);
  }
  return l;
}


/*
 * DIVIDES AND IS_INT ATOMS
 */

/*
 * We use the rules
 * - (is_int x)    <=> (x <= floor(x))
 * - (divides k x) <=> (x <= k * div(x, k))
 */

// atom (is_int t)
static literal_t map_arith_is_int_to_literal(context_t *ctx, term_t t) {
  polynomial_t *p;
  thvar_t map[2];
  thvar_t x, y;
  literal_t l;

  x = internalize_to_arith(ctx, t);
  if (ctx->arith.arith_var_is_int(ctx->arith_solver, x)) {
    l = true_literal;
  } else {
    // we convert (is_int x) to (x <= floor(x))
    y = get_floor(ctx, x); // y is floor x
    p = context_get_aux_poly(ctx, 3);
    context_store_diff_poly(p, map, y, x); // (p, map) := (y - x)
    // atom (x <= y) is the same as (p >= 0)
    l = ctx->arith.create_poly_ge_atom(ctx->arith_solver, p, map);
  }

  return l;
}

// atom (divides k t)  we assume k != 0
static literal_t map_arith_divides_to_literal(context_t *ctx, composite_term_t *divides) {
  rational_t k;
  polynomial_t *p;
  thvar_t map[2];
  thvar_t x, y;
  term_t d;
  literal_t l;

  assert(divides->arity == 2);

  d = divides->arg[0];
  if (term_kind(ctx->terms, d) == ARITH_CONSTANT) {
    // make a copy of divides->arg[0] in k
    q_init(&k);
    q_set(&k, rational_term_desc(ctx->terms, d));
    assert(q_is_nonzero(&k));

    x = internalize_to_arith(ctx, divides->arg[1]); // this is t
    y = get_div(ctx, x, &k);  // y := (div x k)
    p = context_get_aux_poly(ctx, 3);
    context_store_divides_constraint(p, map, x, y, &k); // p is (- x + k * y)
    // atom (x <= k * y) is (p >= 0)
    l = ctx->arith.create_poly_ge_atom(ctx->arith_solver, p, map);

    q_clear(&k);

    return l;

  } else {
    // k is not a constant: not supported
    longjmp(ctx->env, FORMULA_NOT_LINEAR);
  }
}


/*
 * BITVECTOR ATOMS
 */

/*
 * Auxiliary function: atom for (t == 0)
 */
static literal_t map_bveq0_to_literal(context_t *ctx, term_t t) {
  uint32_t n;
  thvar_t x, y;

  t = intern_tbl_get_root(&ctx->intern, t);
  n = term_bitsize(ctx->terms, t);
  x = internalize_to_bv(ctx, t);
  y = ctx->bv.create_zero(ctx->bv_solver, n);

  return ctx->bv.create_eq_atom(ctx->bv_solver, x, y);
}

static literal_t map_bveq_to_literal(context_t *ctx, composite_term_t *eq) {
  bveq_simp_t simp;
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
   * More simplifications
   */
  try_arithmetic_bveq_simplification(ctx, &simp, t1, t2);
  switch (simp.code) {
  case BVEQ_CODE_TRUE:
    return true_literal;

  case BVEQ_CODE_FALSE:
    return false_literal;

  case BVEQ_CODE_REDUCED:
    t1 = intern_tbl_get_root(&ctx->intern, simp.left);
    t2 = intern_tbl_get_root(&ctx->intern, simp.right);
    break;

  case BVEQ_CODE_REDUCED0:
    // (t1 == t2) is reduced to (simp.left == 0)
    // we create the atom directly here:
    return map_bveq0_to_literal(ctx, simp.left);

  default:
    break;
  }

  if (equal_bitvector_factors(ctx, t1, t2)) {
    return true_literal;
  }

  /*
   * NOTE: creating (eq t1 t2) in the egraph instead makes things worse
   */
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
    exception = uf_error_code(ctx, t);
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
      intern_tbl_remap_root(&ctx->intern, r, occ2code(u));
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
	//        add_type_constraints(ctx, u, tau);
        break;

      case ARITH_FLOOR:
	assert(is_integer_type(tau));
	x = map_floor_to_arith(ctx, arith_floor_arg(terms, r));
	u = translate_arithvar_to_eterm(ctx, x);
	break;

      case ARITH_CEIL:
	assert(is_integer_type(tau));
	x = map_ceil_to_arith(ctx, arith_ceil_arg(terms, r));
	u = translate_arithvar_to_eterm(ctx, x);
	break;

      case ARITH_ABS:
	x = map_abs_to_arith(ctx, arith_abs_arg(terms, r));
	u = translate_arithvar_to_eterm(ctx, x);
	break;

      case ITE_TERM:
      case ITE_SPECIAL:
        u = map_ite_to_eterm(ctx, ite_term_desc(terms, r), tau);
        break;

      case APP_TERM:
        u = map_apply_to_eterm(ctx, app_term_desc(terms, r), tau);
        break;

      case ARITH_RDIV:
	assert(is_real_type(tau));
	x = map_rdiv_to_arith(ctx, arith_rdiv_term_desc(terms, r));
	u = translate_arithvar_to_eterm(ctx, x);
	break;

      case ARITH_IDIV:
	assert(is_integer_type(tau));
	x = map_idiv_to_arith(ctx, arith_idiv_term_desc(terms, r));
	u = translate_arithvar_to_eterm(ctx, x); // (div t u) has type int
	break;

      case ARITH_MOD:
	x = map_mod_to_arith(ctx, arith_mod_term_desc(terms, r));
	u = translate_arithvar_to_eterm(ctx, x);
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

      case LAMBDA_TERM:
        // not ready for lambda terms yet:
        exception = LAMBDAS_NOT_SUPPORTED;
        goto abort;

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
      //      printf("mapping: %s --> i!%d\n", term_name(ctx->terms, r), (int) x);
      //      fflush(stdout);
      break;

    case ARITH_FLOOR:
      x = map_floor_to_arith(ctx, arith_floor_arg(terms, r));
      intern_tbl_map_root(&ctx->intern, r, thvar2code(x));
      break;

    case ARITH_CEIL:
      x = map_ceil_to_arith(ctx, arith_ceil_arg(terms, r));
      intern_tbl_map_root(&ctx->intern, r, thvar2code(x));
      break;

    case ARITH_ABS:
      x = map_abs_to_arith(ctx, arith_abs_arg(terms, r));
      intern_tbl_map_root(&ctx->intern, r, thvar2code(x));
      break;

    case ITE_TERM:
      x = map_ite_to_arith(ctx, ite_term_desc(terms, r), is_integer_root(ctx, r));
      intern_tbl_map_root(&ctx->intern, r, thvar2code(x));
      break;

    case ITE_SPECIAL:
      x = map_ite_to_arith(ctx, ite_term_desc(terms, r), is_integer_root(ctx, r));
      intern_tbl_map_root(&ctx->intern, r, thvar2code(x));
      if (context_ite_bounds_enabled(ctx)) {
	assert_ite_bounds(ctx, r, x);
      }
      break;

    case APP_TERM:
      u = map_apply_to_eterm(ctx, app_term_desc(terms, r), type_of_root(ctx, r));
      assert(egraph_term_is_arith(ctx->egraph, term_of_occ(u)));
      intern_tbl_map_root(&ctx->intern, r, occ2code(u));
      x = egraph_term_base_thvar(ctx->egraph, term_of_occ(u));
      assert(x != null_thvar);
      break;

    case ARITH_RDIV:
      x = map_rdiv_to_arith(ctx, arith_rdiv_term_desc(terms, r));
      intern_tbl_map_root(&ctx->intern, r, thvar2code(x));
      break;

    case ARITH_IDIV:
      x = map_idiv_to_arith(ctx, arith_idiv_term_desc(terms, r));
      intern_tbl_map_root(&ctx->intern, r, thvar2code(x));
      break;

    case ARITH_MOD:
      x = map_mod_to_arith(ctx, arith_mod_term_desc(terms, r));
      intern_tbl_map_root(&ctx->intern, r, thvar2code(x));
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
  eterm_t u;
  thvar_t v;

  assert(code_is_valid(x));

  if (code_is_eterm(x)) {
    u = code2eterm(x);
    assert(ctx->egraph != NULL && egraph_term_is_bv(ctx->egraph, u));
    v = egraph_term_base_thvar(ctx->egraph, u);
  } else {
    v = code2thvar(x);
  }

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
  occ_t u;
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
    case ITE_SPECIAL:
      x = map_ite_to_bv(ctx, ite_term_desc(terms, r));
      intern_tbl_map_root(&ctx->intern, r, thvar2code(x));
      break;

    case APP_TERM:
      u = map_apply_to_eterm(ctx, app_term_desc(terms, r), type_of_root(ctx, r));
      assert(egraph_term_is_bv(ctx->egraph, term_of_occ(u)));
      intern_tbl_map_root(&ctx->intern, r, occ2code(u));
      x = egraph_term_base_thvar(ctx->egraph, term_of_occ(u));
      assert(x != null_thvar);
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

    case SELECT_TERM:
      u = map_select_to_eterm(ctx, select_term_desc(terms, r), type_of_root(ctx, r));
      assert(egraph_term_is_bv(ctx->egraph, term_of_occ(u)));
      intern_tbl_map_root(&ctx->intern, r, occ2code(u));
      x = egraph_term_base_thvar(ctx->egraph, term_of_occ(u));
      assert(x != null_thvar);
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

    case ARITH_IS_INT_ATOM:
      l = map_arith_is_int_to_literal(ctx, arith_is_int_arg(terms, r));
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

    case ARITH_DIVIDES_ATOM:
      l = map_arith_divides_to_literal(ctx, arith_divides_atom_desc(terms, r));
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
      // lax mode: turn forall into a proposition
      l = pos_lit(create_boolean_variable(ctx->core));
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
 * Replace every variable of t by the root of t in the internalization table
 * - the result is stored in buffer
 */
static void apply_renaming_to_poly(context_t *ctx, polynomial_t *p,  poly_buffer_t *buffer) {
  uint32_t i, n;
  term_t t;

  reset_poly_buffer(buffer);

  assert(poly_buffer_is_zero(buffer));

  n = p->nterms;
  for (i=0; i<n; i++) {
    t = p->mono[i].var;
    if (t == const_idx) {
      poly_buffer_add_const(buffer, &p->mono[i].coeff);
    } else {
      // replace t by its root
      t = intern_tbl_get_root(&ctx->intern, t);
      poly_buffer_addmul_term(ctx->terms, buffer, t, &p->mono[i].coeff);
    }
  }

  normalize_poly_buffer(buffer);
}


/*
 * Auxiliary function: check whether p/a is an integral polynomial
 * assuming all variables and coefficients of p are integer.
 * - check whether all coefficients are multiple of a
 * - a must be non-zero
 */
static bool integralpoly_after_div(poly_buffer_t *buffer, rational_t *a) {
  uint32_t i, n;

  if (q_is_one(a) || q_is_minus_one(a)) {
    return true;
  }

  n = buffer->nterms;
  for (i=0; i<n; i++) {
    if (! q_divides(a, &buffer->mono[i].coeff)) return false;
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
static term_t try_poly_substitution(context_t *ctx, poly_buffer_t *buffer, bool all_int) {
  uint32_t i, n;
  term_t t;

  // check for a free variable in buffer
  n = buffer->nterms;
  for (i=0; i<n; i++) {
    t = buffer->mono[i].var;
    if (t != const_idx && is_elimination_candidate(ctx, t)) {
      if (in_real_class(ctx, t) ||
          (all_int && integralpoly_after_div(buffer, &buffer->mono[i].coeff))) {
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
static polynomial_t *build_poly_substitution(context_t *ctx, poly_buffer_t *buffer, term_t x) {
  polynomial_t *q;
  monomial_t *mono;
  uint32_t i, n;
  term_t y;
  rational_t *a;

  n = buffer->nterms;

  // first get coefficient of x in buffer
  a = NULL; // otherwise GCC complains
  for (i=0; i<n; i++) {
    y = buffer->mono[i].var;
    if (y == x) {
      a = &buffer->mono[i].coeff;
    }
  }
  assert(a != NULL && n > 0);

  q = context_get_aux_poly(ctx, n);
  q->nterms = n-1;
  mono = q->mono;

  // compute - buffer/a (but skip monomial a.x)
  for (i=0; i<n; i++) {
    y = buffer->mono[i].var;
    if (y != x) {
      mono->var = y;
      q_set_neg(&mono->coeff, &buffer->mono[i].coeff);
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
  poly_buffer_t *buffer;
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
   * Apply variable renaming: this is to avoid circularities
   * if p is of the form ... + a x + ... + b y + ...
   * where both x and y are variables in the same class (i.e.,
   * both are elimination candidates).
   */
  buffer = context_get_poly_buffer(ctx);
  apply_renaming_to_poly(ctx, p, buffer);

  /*
   * Search for a variable to substitute
   */
  u = try_poly_substitution(ctx, buffer, all_int);
  if (u == NULL_TERM) {
    return false; // no substitution found
  }

  /*
   * buffer is of the form a.u + p0, we rewrite (buffer == 0) to (u == q)
   * where q = -1/a * p0
   */
  q = build_poly_substitution(ctx, buffer, u); // q is in ctx->aux_poly

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







/******************************************************
 *  TOP-LEVEL ARITHMETIC EQUALITIES OR DISEQUALITIES  *
 *****************************************************/

static void assert_arith_bineq(context_t *ctx, term_t t1, term_t t2, bool tt);

/*
 * Top-level equality: t == (ite c u1 u2) between arithmetic terms
 * - apply lift-if rule: (t == (ite c u1 u2)) --> (ite c (t == u1) (t == u2)
 * - if tt is true: assert the equality otherwise assert the disequality
 */
static void assert_ite_arith_bineq(context_t *ctx, composite_term_t *ite, term_t t, bool tt) {
  literal_t l1, l2, l3;

  assert(ite->arity == 3);

  l1 = internalize_to_literal(ctx, ite->arg[0]);
  if (l1 == true_literal) {
    // (ite c u1 u2) --> u1
    assert_arith_bineq(ctx, ite->arg[1], t, tt);
  } else if (l1 == false_literal) {
    // (ite c u1 u2) --> u2
    assert_arith_bineq(ctx, ite->arg[2], t, tt);
  } else {
    l2 = map_arith_bineq(ctx, ite->arg[1], t); // (u1 == t)
    l3 = map_arith_bineq(ctx, ite->arg[2], t); // (u2 == t)
    assert_ite(&ctx->gate_manager, l1, l2, l3, tt);
  }
}


/*
 * Try substitution t1 := t2
 * - both are arithmetic terms and roots in the internalization table
 */
static void try_arithvar_bineq_elim(context_t *ctx, term_t t1, term_t t2) {
  intern_tbl_t *intern;
  thvar_t x, y;
  int32_t code;

  assert(is_pos_term(t1) && intern_tbl_is_root(&ctx->intern, t1) &&
         intern_tbl_root_is_free(&ctx->intern, t1));

  intern = &ctx->intern;

  if (is_constant_term(ctx->terms, t2)) {
    if (intern_tbl_valid_const_subst(intern, t1, t2)) {
      intern_tbl_add_subst(intern, t1, t2);
    } else {
      // unsat by type incompatibility
      longjmp(ctx->env, TRIVIALLY_UNSAT);
    }

  } else {
    /*
     * Internalize t2 to x.
     * If t1 is still free after that, we can map t1 to x
     * otherwise, t2 depends on t1 so we can't substitute
     */
    x = internalize_to_arith(ctx, t2);
    if (intern_tbl_root_is_free(intern, t1)) {
      intern_tbl_map_root(&ctx->intern, t1, thvar2code(x));
    } else {
      assert(intern_tbl_root_is_mapped(intern, t1));
      code = intern_tbl_map_of_root(intern, t1);
      y = translate_code_to_arith(ctx, code);

      // assert x == y in the arithmetic solver
      ctx->arith.assert_vareq_axiom(ctx->arith_solver, x, y, true);
    }
  }
}


/*
 * Top-level arithmetic equality t1 == t2:
 * - if tt is true: assert t1 == t2 otherwise assert (t1 != t2)
 * - both t1 and t2 are arithmetic terms and roots in the internalization table
 * - the equality (t1 == t2) is not reducible by if-then-else flattening
 */
static void assert_arith_bineq_aux(context_t *ctx, term_t t1, term_t t2, bool tt) {
  term_table_t *terms;
  intern_tbl_t *intern;;
  bool free1, free2;
  thvar_t x, y;
  occ_t u, v;

  assert(is_pos_term(t1) && intern_tbl_is_root(&ctx->intern, t1) &&
         is_pos_term(t2) && intern_tbl_is_root(&ctx->intern, t2));

  terms = ctx->terms;
  if (is_ite_term(terms, t1) && !is_ite_term(terms, t2)) {
    assert_ite_arith_bineq(ctx, ite_term_desc(terms, t1), t2, tt);
    return;
  }

  if (is_ite_term(terms, t2) && !is_ite_term(terms, t1)) {
    assert_ite_arith_bineq(ctx, ite_term_desc(terms, t2), t1, tt);
    return;
  }

  if (tt && context_arith_elim_enabled(ctx)) {
    /*
     * try a substitution
     */
    intern = &ctx->intern;
    free1 = intern_tbl_root_is_free(intern, t1);
    free2 = intern_tbl_root_is_free(intern, t2);

    if (free1 && free2) {
      if (t1 != t2) {
        intern_tbl_merge_classes(intern, t1, t2);
      }
      return;
    }

    if (free1) {
      try_arithvar_bineq_elim(ctx, t1, t2);
      return;
    }

    if (free2) {
      try_arithvar_bineq_elim(ctx, t2, t1);
      return;
    }

  }

  /*
   * Default: assert the constraint in the egraph or in the arithmetic
   * solver if there's no egraph.
   */
  if (context_has_egraph(ctx)) {
    u = internalize_to_eterm(ctx, t1);
    v = internalize_to_eterm(ctx, t2);
    if (tt) {
      egraph_assert_eq_axiom(ctx->egraph, u, v);
    } else {
      egraph_assert_diseq_axiom(ctx->egraph, u, v);
    }
  } else {
    x = internalize_to_arith(ctx, t1);
    y = internalize_to_arith(ctx, t2);
    ctx->arith.assert_vareq_axiom(ctx->arith_solver, x, y, tt);
  }
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
  occ_t u1, u2;

  assert(eq->arity == 2);

  if (is_boolean_term(ctx->terms, eq->arg[0])) {
    assert(is_boolean_term(ctx->terms, eq->arg[1]));
    assert_toplevel_iff(ctx, eq->arg[0], eq->arg[1], tt);
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
    longjmp(ctx->env, uf_error_code(ctx, distinct->arg[0]));
  }

  free_istack_array(&ctx->istack, a);
}



/*
 * Top-level arithmetic equality t1 == u1:
 * - t1 and u1 are arithmetic terms
 * - if tt is true assert (t1 == u1) otherwise assert (t1 != u1)
 * - apply lift-if simplifications and variable elimination
 */
static void assert_arith_bineq(context_t *ctx, term_t t1, term_t u1, bool tt) {
  ivector_t *v;
  int32_t *a;
  uint32_t i, n;
  term_t t2, u2;

  /*
   * Apply substitutions then try if-then-else flattening
   */
  t1 = intern_tbl_get_root(&ctx->intern, t1);
  u1 = intern_tbl_get_root(&ctx->intern, u1);

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
    /*
     * The simple flattening did not work.
     */
    assert(t1 == t2 && u1 == u2);
    assert_arith_bineq_aux(ctx, t2, u2, tt);

  } else {
    // make a copy of v[0 ... n-1]
    // and reserve a[n] for the literal (eq t2 u2)
    a = alloc_istack_array(&ctx->istack, n+1);
    for (i=0; i<n; i++) {
      a[i] = v->data[i];
    }
    ivector_reset(v);

    if (tt) {
      // assert (and a[0] ... a[n-1] (eq t2 u2))
      for (i=0; i<n; i++) {
        assert_term(ctx, a[i], true);
      }

      /*
       * The assertions a[0] ... a[n-1] may have
       * caused roots to be merged. So we must
       * apply term substitution again.
       */
      t2 = intern_tbl_get_root(&ctx->intern, t2);
      u2 = intern_tbl_get_root(&ctx->intern, u2);
      assert_arith_bineq_aux(ctx, t2, u2, true);

    } else {
      // assert (or (not a[0]) ... (not a[n-1]) (not (eq t2 u2)))
      for (i=0; i<n; i++) {
        a[i] = not(internalize_to_literal(ctx, a[i]));
      }
      a[n] = not(map_arith_bineq_aux(ctx, t2, u2));

      add_clause(ctx->core, n+1, a);
    }

    free_istack_array(&ctx->istack, a);
  }
}


/*
 * Top-level arithmetic assertion:
 * - if tt is true, assert p == 0
 * - if tt is false, assert p != 0
 */
static void assert_toplevel_poly_eq(context_t *ctx, polynomial_t *p, bool tt) {
  uint32_t i, n;
  thvar_t *a;

  n = p->nterms;
  a = alloc_istack_array(&ctx->istack, n);;
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

  // assertion
  ctx->arith.assert_poly_eq_axiom(ctx->arith_solver, p, a, tt);
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
  if (term_kind(terms, t) == ARITH_POLY) {
    assert_toplevel_poly_eq(ctx, poly_term_desc(terms, t), tt);
  } else if (is_ite_term(terms, t)) {
    assert_arith_bineq(ctx, t, zero_term, tt);
  } else {
    x = internalize_to_arith(ctx, t);
    ctx->arith.assert_eq_axiom(ctx->arith_solver, x, tt);
  }
}



/*
 * Top-level arithmetic assertion:
 * - if tt is true, assert p >= 0
 * - if tt is false, assert p < 0
 */
static void assert_toplevel_poly_geq(context_t *ctx, polynomial_t *p, bool tt) {
  uint32_t i, n;
  thvar_t *a;

  n = p->nterms;
  a = alloc_istack_array(&ctx->istack, n);;
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

  // assertion
  ctx->arith.assert_poly_ge_axiom(ctx->arith_solver, p, a, tt);
  free_istack_array(&ctx->istack, a);
}



/*
 * Top-level arithmetic inequality:
 * - t is an arithmetic term
 * - if tt is true, assert (t >= 0)
 * - if tt is false, assert (t < 0)
 */
static void assert_toplevel_arith_geq(context_t *ctx, term_t t, bool tt) {
  term_table_t *terms;
  thvar_t x;

  assert(is_arithmetic_term(ctx->terms, t));

  terms = ctx->terms;
  if (term_kind(terms, t) == ARITH_POLY) {
    assert_toplevel_poly_geq(ctx, poly_term_desc(terms, t), tt);
  } else {
    x = internalize_to_arith(ctx, t);
    ctx->arith.assert_ge_axiom(ctx->arith_solver, x, tt);
  }
}


/*
 * Top-level binary equality: (eq t u)
 * - both t and u are arithmetic terms
 * - if tt is true, assert (t == u)
 * - if tt is false, assert (t != u)
 */
static void assert_toplevel_arith_bineq(context_t *ctx, composite_term_t *eq, bool tt) {
  assert(eq->arity == 2);
  assert_arith_bineq(ctx, eq->arg[0], eq->arg[1], tt);
}



/*
 * Top-level (is_int t)
 * - t is an arithmetic term
 * - if tt is true, assert (t <= (floor t))
 * - if tt is false, asssert (t > (floor t))
 *
 * NOTE: instead of asserting (t <= (floor t)) we could create a fresh
 * integer variable z and assert (t = z).
 */
static void assert_toplevel_arith_is_int(context_t *ctx, term_t t, bool tt) {
  polynomial_t *p;
  thvar_t map[2];
  thvar_t x, y;

  x = internalize_to_arith(ctx, t);
  if (ctx->arith.arith_var_is_int(ctx->arith_solver, x)) {
    if (!tt) {
      longjmp(ctx->env, TRIVIALLY_UNSAT);
    }
  } else {
    // x is not an integer variable
    y = get_floor(ctx, x); // y := (floor x)
    p = context_get_aux_poly(ctx, 3);
    context_store_diff_poly(p, map, y, x); // (p, map) stores (y - x)
    // assert either (p >= 0) --> (x <= floor(x))
    // or (p < 0) --> (x > (floor x)
    ctx->arith.assert_poly_ge_axiom(ctx->arith_solver, p, map, tt);
  }
}


/*
 * Top-level (divides k t)
 * - if tt is true, assert (t <= k * (div t k))
 * - if tt is false, assert (t > k * (div t k))
 *
 * We assume (k != 0) since (divides 0 t) is rewritten to (t == 0) by
 * the term manager.
 *
 * NOTE: instead of asserting (t <= k * (div t k)) we could create a fresh
 * integer variable z and assert (t = k * z).
 */
static void assert_toplevel_arith_divides(context_t *ctx, composite_term_t *divides, bool tt) {
  rational_t k;
  polynomial_t *p;
  thvar_t map[2];
  thvar_t x, y;
  term_t d;

  assert(divides->arity == 2);

  d = divides->arg[0];
  if (term_kind(ctx->terms, d) == ARITH_CONSTANT) {
    // copy the divider
    q_init(&k);
    q_set(&k, rational_term_desc(ctx->terms, d));
    assert(q_is_nonzero(&k));

    x = internalize_to_arith(ctx, divides->arg[1]);
    y = get_div(ctx, x, &k);  // y := (div x k);
    p = context_get_aux_poly(ctx, 3);
    context_store_divides_constraint(p, map, x, y, &k); // p is (- x + k * y)

    // if tt, assert (p >= 0) <=> x <= k * y
    // if not tt, assert (p < 0) <=> x > k * y
    ctx->arith.assert_poly_ge_axiom(ctx->arith_solver, p, map, tt);

    q_clear(&k);
  } else {
    // not a constant divider: not supported
    longjmp(ctx->env, FORMULA_NOT_LINEAR);
  }
}






/*
 * Top-level conditional
 * - c = conditional descriptor
 * - if tt is true: assert c otherwise assert not c
 *
 * - c->nconds = number of clauses in the conditional
 * - for each clause i: c->pair[i] = <cond, val>
 * - c->defval = default value
 */
static void assert_toplevel_conditional(context_t *ctx, conditional_t *c, bool tt) {
  uint32_t i, n;
  literal_t *a;
  literal_t l;
  bool all_false;
  term_t t;

#if 0
  printf("---> toplevel conditional\n");
#endif

  t = simplify_conditional(ctx, c);
  if (t != NULL_TERM) {
    assert_term(ctx, t, tt);
    return;
  }


  n = c->nconds;
  a = alloc_istack_array(&ctx->istack, n + 1);

  all_false = true;
  for (i=0; i<n; i++) {
    // a[i] = condition for pair[i]
    a[i] = internalize_to_literal(ctx, c->pair[i].cond);
    if (a[i] == true_literal) {
      // if a[i] is true, all other conditions must be false
      assert_term(ctx, c->pair[i].val, tt);
      goto done;
    }
    if (a[i] != false_literal) {
      // l = value for pair[i]
      l = signed_literal(internalize_to_literal(ctx, c->pair[i].val), tt);
      add_binary_clause(ctx->core, not(a[i]), l); // a[i] => v[i]
      all_false = false;
    }
  }

  if (all_false) {
    // all a[i]s are false: no need for a clause
    assert_term(ctx, c->defval, tt);
    goto done;
  }

  // last clause: (a[0] \/ .... \/ a[n] \/ +/-defval)
  a[n] = signed_literal(internalize_to_literal(ctx, c->defval), tt);
  add_clause(ctx->core, n+1, a);

  // cleanup
 done:
  free_istack_array(&ctx->istack, a);
}



/*
 * Top-level boolean if-then-else (ite c t1 t2)
 * - if tt is true: assert (ite c t1 t2)
 * - if tt is false: assert (not (ite c t1 t2))
 */
static void assert_toplevel_ite(context_t *ctx, composite_term_t *ite, bool tt) {
  conditional_t *d;
  literal_t l1, l2, l3;

  assert(ite->arity == 3);

  d = context_make_conditional(ctx, ite);
  if (d != NULL) {
    assert_toplevel_conditional(ctx, d, tt);
    context_free_conditional(ctx, d);
    return;
  }

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

      // if v contains a true_term, ignore the clause
      n = v->size;
      if (disjunct_is_true(ctx, v->data, n)) {
	ivector_reset(v);
	return;
      }

      // make a copy of v
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
      if (disjunct_is_true(ctx, or->arg, n)) {
	return;
      }

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
// Auxiliary function: assert (t == 0) or (t != 0) depending on tt
static void assert_toplevel_bveq0(context_t *ctx, term_t t, bool tt) {
  uint32_t n;
  thvar_t x, y;

  t = intern_tbl_get_root(&ctx->intern, t);
  n = term_bitsize(ctx->terms, t);
  x = internalize_to_bv(ctx, t);
  y = ctx->bv.create_zero(ctx->bv_solver, n);
  ctx->bv.assert_eq_axiom(ctx->bv_solver, x, y, tt);
}


/*
 * Experimental: when t1 and t2 have a common factor C:
 *   t1 = C * u1
 *   t2 = C * u2
 * then we have (t1 /= t2) implies (u1 /= u2).
 * So we can add (u1 /= u2) when (t1 /= t2) is asserted.
 * This is redundant but it may help solving the problem, especially if C is a
 * complex expression.
 */
static void assert_factored_inequality(context_t *ctx, bvfactoring_t *f) {
  term_t u1, u2;
  thvar_t x, y;

  assert(f->code == BVFACTOR_FOUND);

  //  printf("Asserting factored inequality\n\n");

  u1 = bitvector_factoring_left_term(ctx, f);
  u2 = bitvector_factoring_right_term(ctx, f);
  x = internalize_to_bv(ctx, u1);
  y = internalize_to_bv(ctx, u2);
  ctx->bv.assert_eq_axiom(ctx->bv_solver, x,  y, false);
}

static void assert_toplevel_bveq(context_t *ctx, composite_term_t *eq, bool tt) {
  bveq_simp_t simp;
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
   * Try more simplifications
   */
  try_arithmetic_bveq_simplification(ctx, &simp, t1, t2);
  switch (simp.code) {
  case BVEQ_CODE_TRUE:
    if (!tt) longjmp(ctx->env, TRIVIALLY_UNSAT);
    break;

  case BVEQ_CODE_FALSE:
    if (tt) longjmp(ctx->env, TRIVIALLY_UNSAT);
    break;

  case BVEQ_CODE_REDUCED:
    t1 = intern_tbl_get_root(&ctx->intern, simp.left);
    t2 = intern_tbl_get_root(&ctx->intern, simp.right);
    break;

  case BVEQ_CODE_REDUCED0:
    // reduced to simp.left == 0
    assert_toplevel_bveq0(ctx, simp.left, tt);
    return;

  default:
    break;
  }

  /*
   * Try Factoring
   */
  if (!tt) {
    bvfactoring_t factoring;
    bool eq = false;

    init_bvfactoring(&factoring);
    try_bitvector_factoring(ctx, &factoring, t1, t2);
    switch (factoring.code) {
    case BVFACTOR_EQUAL:
      eq = true;
      break;

    case BVFACTOR_FOUND:
      assert_factored_inequality(ctx, &factoring);
      break;

    default:
      break;
    }
    delete_bvfactoring(&factoring);

    if (eq) {
      longjmp(ctx->env, TRIVIALLY_UNSAT);
    }
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

  case ARITH_IS_INT_ATOM:
    assert_toplevel_arith_is_int(ctx, arith_is_int_arg(terms, t), tt);
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

  case ARITH_DIVIDES_ATOM:
    assert_toplevel_arith_divides(ctx, arith_divides_atom_desc(terms, t), tt);
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

    case ARITH_IS_INT_ATOM:
      assert_toplevel_arith_is_int(ctx, arith_is_int_arg(terms, t), tt);
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

    case ARITH_DIVIDES_ATOM:
      assert_toplevel_arith_divides(ctx, arith_divides_atom_desc(terms, t), tt);
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

  UF_MASK|ARITH_MASK|FUN_MASK  //  CTX_ARCH_MCSAT
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
#define MCSAT  0x40

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

  MCSAT                     //  CTX_ARCH_MCSAT
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






/*
 * SIMPLEX OPTIONS
 */

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
  if (context_has_simplex_solver(ctx)) {
    simplex_enable_eager_lemmas(ctx->arith_solver);
  }
}

void disable_splx_eager_lemmas(context_t *ctx) {
  ctx->options &= ~SPLX_EGRLMAS_OPTION_MASK;
  if (context_has_simplex_solver(ctx)) {
    simplex_disable_eager_lemmas(ctx->arith_solver);
  }
}


void enable_splx_periodic_icheck(context_t *ctx) {
  ctx->options |= SPLX_ICHECK_OPTION_MASK;
  if (context_has_simplex_solver(ctx)) {
    simplex_enable_periodic_icheck(ctx->arith_solver);
  }
}

void disable_splx_periodic_icheck(context_t *ctx) {
  ctx->options &= ~SPLX_ICHECK_OPTION_MASK;
  if (context_has_simplex_solver(ctx)) {
    simplex_disable_periodic_icheck(ctx->arith_solver);
  }
}

void enable_splx_eqprop(context_t *ctx) {
  ctx->options |= SPLX_EQPROP_OPTION_MASK;
  if (context_has_simplex_solver(ctx)) {
    simplex_enable_eqprop(ctx->arith_solver);
  }
}

void disable_splx_eqprop(context_t *ctx) {
  ctx->options &= ~SPLX_EQPROP_OPTION_MASK;
  if (context_has_simplex_solver(ctx)) {
    simplex_disable_eqprop(ctx->arith_solver);
  }
}




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
 * Create and initialize the mcsat solver
 */
static void create_mcsat(context_t *ctx) {
  assert(ctx->mcsat == NULL);
  ctx->mcsat = mcsat_new(ctx);
}



/*
 * Create and initialize the idl solver and attach it to the core
 * - there must be no other solvers and no egraph
 * - if automatic is true, attach the solver to the core, otherwise
 *   initialize the core
 * - copy the solver's internalization interface into arith
 */
static void create_idl_solver(context_t *ctx, bool automatic) {
  idl_solver_t *solver;
  smt_mode_t cmode;

  assert(ctx->egraph == NULL && ctx->arith_solver == NULL && ctx->bv_solver == NULL &&
         ctx->fun_solver == NULL && ctx->core != NULL);

  cmode = core_mode[ctx->mode];
  solver = (idl_solver_t *) safe_malloc(sizeof(idl_solver_t));
  init_idl_solver(solver, ctx->core, &ctx->gate_manager);
  if (automatic) {
    smt_core_reset_thsolver(ctx->core, solver, idl_ctrl_interface(solver),
			    idl_smt_interface(solver));
  } else {
    init_smt_core(ctx->core, CTX_DEFAULT_CORE_SIZE, solver, idl_ctrl_interface(solver),
		  idl_smt_interface(solver), cmode);
  }
  idl_solver_init_jmpbuf(solver, &ctx->env);
  ctx->arith_solver = solver;
  ctx->arith = *idl_arith_interface(solver);
}


/*
 * Create and initialize the rdl solver and attach it to the core.
 * - there must be no other solvers and no egraph
 * - if automatic is true, attach rdl to the core, otherwise
 *   initialize the core
 * - copy the solver's internalization interface in ctx->arith
 */
static void create_rdl_solver(context_t *ctx, bool automatic) {
  rdl_solver_t *solver;
  smt_mode_t cmode;

  assert(ctx->egraph == NULL && ctx->arith_solver == NULL && ctx->bv_solver == NULL &&
         ctx->fun_solver == NULL && ctx->core != NULL);

  cmode = core_mode[ctx->mode];
  solver = (rdl_solver_t *) safe_malloc(sizeof(rdl_solver_t));
  init_rdl_solver(solver, ctx->core, &ctx->gate_manager);
  if (automatic) {
    smt_core_reset_thsolver(ctx->core, solver, rdl_ctrl_interface(solver),
			    rdl_smt_interface(solver));
  } else {
    init_smt_core(ctx->core, CTX_DEFAULT_CORE_SIZE, solver, rdl_ctrl_interface(solver),
		  rdl_smt_interface(solver), cmode);
  }
  rdl_solver_init_jmpbuf(solver, &ctx->env);
  ctx->arith_solver = solver;
  ctx->arith = *rdl_arith_interface(solver);
}


/*
 * Create an initialize the simplex solver and attach it to the core
 * or to the egraph if the egraph exists.
 * - if automatic is true, this is part of auto_idl or auto_rdl. So the
 *   core is already initialized.
 */
static void create_simplex_solver(context_t *ctx, bool automatic) {
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
  if (splx_eqprop_enabled(ctx)) {
    simplex_enable_eqprop(solver);
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
  } else if (!automatic) {
    // attach simplex to the core and initialize the core
    init_smt_core(ctx->core, CTX_DEFAULT_CORE_SIZE, solver, simplex_ctrl_interface(solver),
                  simplex_smt_interface(solver), cmode);
  } else {
    // the core is already initialized: attach simplex
    smt_core_reset_thsolver(ctx->core, solver, simplex_ctrl_interface(solver),
			    simplex_smt_interface(solver));
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
  int32_t bound;
  double atom_density;

  assert(ctx->dl_profile != NULL);
  profile = ctx->dl_profile;

  if (q_is_smallint(&profile->path_bound)) {
    bound = q_get_smallint(&profile->path_bound);
  } else {
    bound = INT32_MAX;
  }

  if (bound >= 1073741824) {
    // simplex required because of arithmetic overflow
    create_simplex_solver(ctx, true);
    ctx->arch = CTX_ARCH_SPLX;
  } else if (profile->num_vars >= 1000) {
    // too many variables for FW
    create_simplex_solver(ctx, true);
    ctx->arch = CTX_ARCH_SPLX;
  } else if (profile->num_vars <= 200 || profile->num_eqs == 0) {
    // use FW for now, until we've tested SIMPLEX more
    // 0 equalities usually means a scheduling problem
    // --flatten works better on IDL/FW
    create_idl_solver(ctx, true);
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
      create_idl_solver(ctx, true);
      ctx->arch = CTX_ARCH_IFW;
      enable_diseq_and_or_flattening(ctx);
    } else {
      create_simplex_solver(ctx, true);
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
    create_simplex_solver(ctx, true);
    ctx->arch = CTX_ARCH_SPLX;
  } else if (profile->num_vars <= 200 || profile->num_eqs == 0) {
    create_rdl_solver(ctx, true);
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
      create_rdl_solver(ctx, true);
      ctx->arch = CTX_ARCH_RFW;
    } else {
      // low-density: use SIMPLEX
      create_simplex_solver(ctx, true);
      ctx->arch = CTX_ARCH_SPLX;
    }
  }
}



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
  init_bv_solver(solver, ctx->core, ctx->egraph);

  if (ctx->egraph != NULL) {
    // attach as a satellite to the egraph
    egraph_attach_bvsolver(ctx->egraph, solver, bv_solver_ctrl_interface(solver),
                           bv_solver_smt_interface(solver), bv_solver_egraph_interface(solver),
                           bv_solver_bv_egraph_interface(solver));
  } else {
    // attach to the core and initialize the core
    init_smt_core(ctx->core, CTX_DEFAULT_CORE_SIZE, solver, bv_solver_ctrl_interface(solver),
                  bv_solver_smt_interface(solver), cmode);
  }

  // EXPERIMENT
  //  smt_core_make_etable(ctx->core);
  // END

  bv_solver_init_jmpbuf(solver, &ctx->env);
  ctx->bv_solver = solver;
  ctx->bv = *bv_solver_bv_interface(solver);
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
 * - if the architecture is either AUTO_IDL or AUTO_RDL, no theory solver
 *   is allocated yet, and the core is initialized for Boolean only
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

  // Create mcsat
  if (solvers & MCSAT) {
    create_mcsat(ctx);
  }

  // Arithmetic solver
  if (solvers & SPLX) {
    create_simplex_solver(ctx, false);
  } else if (solvers & IFW) {
    create_idl_solver(ctx, false);
  } else if (solvers & RFW) {
    create_rdl_solver(ctx, false);
  }

  // Bitvector solver
  if (solvers & BVSLVR) {
    create_bv_solver(ctx);
  }

  // Array solver
  if (solvers & FSLVR) {
    create_fun_solver(ctx);
  }

  /*
   * At this point all solvers are ready and initialized, except the
   * egraph and core if the egraph is present or the core if there are
   * no solvers, or if arch is AUTO_IDL or AUTO_RDL.
   */
  cmode = core_mode[ctx->mode];   // initialization mode for the core
  egraph = ctx->egraph;
  core = ctx->core;
  if (egraph != NULL) {
    init_smt_core(core, CTX_DEFAULT_CORE_SIZE, egraph, egraph_ctrl_interface(egraph),
                  egraph_smt_interface(egraph), cmode);
    egraph_attach_core(egraph, core);

  } else if (solvers == 0) {
    /*
     * Boolean solver only. If arch if AUTO_IDL or AUTO_RDL, the
     * theory solver will be changed later by create_auto_idl_solver
     * or create_auto_rdl_solver.
     */
    assert(ctx->arith_solver == NULL && ctx->bv_solver == NULL && ctx->fun_solver == NULL);
    init_smt_core(core, CTX_DEFAULT_CORE_SIZE, NULL, &null_ctrl, &null_smt, cmode);
  } else if (solvers == MCSAT) {
    /*
     * MCsat solver only, we create the core, but never use it.
     */
    assert(ctx->egraph == NULL && ctx->arith_solver == NULL &&
	   ctx->bv_solver == NULL && ctx->fun_solver == NULL);
    init_smt_core(core, CTX_DEFAULT_CORE_SIZE, NULL, &null_ctrl, &null_smt, cmode);
  }

  /*
   * Optimization: if the arch is NOSOLVERS or BV then we set bool_only in the core
   */
  if (ctx->arch == CTX_ARCH_NOSOLVERS || ctx->arch == CTX_ARCH_BV) {
    smt_core_set_bool_only(core);
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
#ifndef NDEBUG
static inline bool valid_mode(context_mode_t mode) {
  return CTX_MODE_ONECHECK <= mode && mode <= CTX_MODE_INTERACTIVE;
}

static inline bool valid_arch(context_arch_t arch) {
  return CTX_ARCH_NOSOLVERS <= arch && arch <= CTX_ARCH_MCSAT;
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
   *
   * TODO: we could skip this when we use MCSAT (since then the core is
   * not needed).
   */
  ctx->core = (smt_core_t *) safe_malloc(sizeof(smt_core_t));
  ctx->egraph = NULL;
  ctx->mcsat = NULL;
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
  init_assumption_stack(&ctx->assumptions);

  ctx->subst = NULL;
  ctx->marks = NULL;
  ctx->cache = NULL;
  ctx->small_cache = NULL;
  ctx->edge_map = NULL;
  ctx->eq_cache = NULL;
  ctx->divmod_table = NULL;
  ctx->explorer = NULL;

  ctx->dl_profile = NULL;
  ctx->arith_buffer = NULL;
  ctx->poly_buffer = NULL;
  ctx->aux_poly = NULL;
  ctx->aux_poly_size = 0;

  ctx->bvpoly_buffer = NULL;

  q_init(&ctx->aux);
  init_bvconstant(&ctx->bv_buffer);

  ctx->trace = NULL;

  // mcsat options default
  init_mcsat_options(&ctx->mcsat_options);

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
    if (ctx->arch != CTX_ARCH_AUTO_IDL && ctx->arch != CTX_ARCH_AUTO_RDL) {
      delete_smt_core(ctx->core);
    }
    safe_free(ctx->core);
    ctx->core = NULL;
  }

  if (ctx->mcsat != NULL) {
    mcsat_destruct(ctx->mcsat);
    safe_free(ctx->mcsat);
    ctx->mcsat = NULL;
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

  if (ctx->bv_solver != NULL) {
    delete_bv_solver(ctx->bv_solver);
    safe_free(ctx->bv_solver);
    ctx->bv_solver = NULL;
  }

  delete_gate_manager(&ctx->gate_manager);
  /* delete_mcsat_options(&ctx->mcsat_options); // if used then the same memory is freed twice */

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
  delete_assumption_stack(&ctx->assumptions);

  context_free_subst(ctx);
  context_free_marks(ctx);
  context_free_cache(ctx);
  context_free_small_cache(ctx);
  context_free_eq_cache(ctx);
  context_free_divmod_table(ctx);
  context_free_explorer(ctx);

  context_free_dl_profile(ctx);
  context_free_arith_buffer(ctx);
  context_free_poly_buffer(ctx);
  context_free_aux_poly(ctx);

  context_free_bvpoly_buffer(ctx);

  q_clear(&ctx->aux);
  delete_bvconstant(&ctx->bv_buffer);
}



/*
 * Reset: remove all assertions and clear all internalization tables
 */
void reset_context(context_t *ctx) {
  ctx->base_level = 0;

  reset_smt_core(ctx->core); // this propagates reset to all solvers

  if (ctx->mcsat != NULL) {
    mcsat_reset(ctx->mcsat);
  }

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
  reset_assumption_stack(&ctx->assumptions);

  context_free_subst(ctx);
  context_free_marks(ctx);
  context_reset_small_cache(ctx);
  context_reset_eq_cache(ctx);
  context_reset_divmod_table(ctx);
  context_reset_explorer(ctx);

  context_free_arith_buffer(ctx);
  context_reset_poly_buffer(ctx);
  context_free_aux_poly(ctx);
  context_free_dl_profile(ctx);

  context_free_bvpoly_buffer(ctx);

  q_clear(&ctx->aux);
}


/*
 * Add tracer to ctx and ctx->core
 */
void context_set_trace(context_t *ctx, tracer_t *trace) {
  assert(ctx->trace == NULL);
  ctx->trace = trace;
  smt_core_set_trace(ctx->core, trace);
  if (ctx->mcsat != NULL) {
    mcsat_set_tracer(ctx->mcsat, trace);
  }
}


/*
 * Push and pop
 */
void context_push(context_t *ctx) {
  assert(context_supports_pushpop(ctx));
  smt_push(ctx->core);  // propagates to all solvers
  if (ctx->mcsat != NULL) {
    mcsat_push(ctx->mcsat);
  }
  intern_tbl_push(&ctx->intern);
  assumption_stack_push(&ctx->assumptions);
  context_eq_cache_push(ctx);
  context_divmod_table_push(ctx);

  ctx->base_level ++;
}

void context_pop(context_t *ctx) {
  assert(context_supports_pushpop(ctx) && ctx->base_level > 0);
  smt_pop(ctx->core);   // propagates to all solvers
  if (ctx->mcsat != NULL) {
    mcsat_pop(ctx->mcsat);
  }
  intern_tbl_pop(&ctx->intern);
  assumption_stack_pop(&ctx->assumptions);
  context_eq_cache_pop(ctx);
  context_divmod_table_pop(ctx);

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


#if 0
/*
 * PROVISIONAL: SHOW ASSERTIONS
 */
static void context_show_assertions(const context_t *ctx, uint32_t n, const term_t *a) {
  pp_area_t area;
  yices_pp_t printer;
  uint32_t i;

  area.width = 80;
  area.height = UINT32_MAX;
  area.offset = 0;
  area.stretch = false;
  area.truncate = false;
  init_yices_pp(&printer, stdout, &area, PP_VMODE, 0);

  for (i=0; i<n; i++) {
    pp_term_full(&printer, ctx->terms, a[i]);
    flush_yices_pp(&printer);
  }
  delete_yices_pp(&printer, true);
}
#endif

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

    // If using MCSAT, just check and done
    if (ctx->mcsat != NULL) {
      code = mcsat_assert_formulas(ctx->mcsat, n, a);
      goto done;
    }

#if 0
    printf("\n=== Context: process assertions ===\n");
    context_show_assertions(ctx, n, a);
    printf("===\n\n");
#endif

    // flatten
    for (i=0; i<n; i++) {
      flatten_assertion(ctx, a[i]);
    }

    trace_printf(ctx->trace, 6, "(done flattening)\n");

    /*
     * At this point, the assertions are stored into the vectors
     * top_eqs, top_atoms, top_formulas, and top_interns
     * - more top-level equalities may be in subst_eqs
     * - ctx->intern stores the internalized terms and the variable
     *   substitutions.
     */

    switch (ctx->arch) {
    case CTX_ARCH_EG:
      /*
       * UF problem: we must process subst_eqs last since the
       * preprocessing may add new equalities in aux_eqs that may end
       * up in subst_eqs after the call to process_aux_eqs.
       */
      if (context_breaksym_enabled(ctx)) {
        break_uf_symmetries(ctx);
      }
      if (context_eq_abstraction_enabled(ctx)) {
        analyze_uf(ctx);
      }
      if (ctx->aux_eqs.size > 0) {
        process_aux_eqs(ctx);
      }
      if (ctx->subst_eqs.size > 0) {
        context_process_candidate_subst(ctx);
      }
      break;

    case CTX_ARCH_AUTO_IDL:
      /*
       * For difference logic, we must process the subst_eqs first
       * (otherwise analyze_diff_logic may give wrong results).
       */
      if (ctx->subst_eqs.size > 0) {
        context_process_candidate_subst(ctx);
      }
      analyze_diff_logic(ctx, true);
      create_auto_idl_solver(ctx);
      break;

    case CTX_ARCH_AUTO_RDL:
      /*
       * Difference logic, we must process the subst_eqs first
       */
      trace_printf(ctx->trace, 6, "(auto-idl solver)\n");
      if (ctx->subst_eqs.size > 0) {
        context_process_candidate_subst(ctx);
      }
      analyze_diff_logic(ctx, false);
      create_auto_rdl_solver(ctx);
      break;

    case CTX_ARCH_SPLX:
      /*
       * Simplex, like EG, may add aux_atoms so we must process
       * subst_eqs last here.
       */
      trace_printf(ctx->trace, 6, "(Simplex solver)\n");
      // more optional processing
      if (context_cond_def_preprocessing_enabled(ctx)) {
        process_conditional_definitions(ctx);
        if (ctx->aux_eqs.size > 0) {
          process_aux_eqs(ctx);
        }
        if (ctx->aux_atoms.size > 0) {
          process_aux_atoms(ctx);
        }
      }
      if (ctx->subst_eqs.size > 0) {
        context_process_candidate_subst(ctx);
      }
      break;

    default:
      /*
       * Process the candidate variable substitutions if any
       */
      if (ctx->subst_eqs.size > 0) {
        context_process_candidate_subst(ctx);
      }
      break;
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
      trace_printf(ctx->trace, 6, "(asserting  %"PRIu32" existing terms)\n", n);
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
      trace_printf(ctx->trace, 6, "(asserting  %"PRIu32" top-level equalities)\n", n);
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
      trace_printf(ctx->trace, 6, "(asserting  %"PRIu32" top-level atoms)\n", n);
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
      trace_printf(ctx->trace, 6, "(asserting  %"PRIu32" top-level formulas)\n", n);
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
int32_t _o_assert_formulas(context_t *ctx, uint32_t n, const term_t *f) {
  int32_t code;

  assert(ctx->arch == CTX_ARCH_AUTO_IDL ||
         ctx->arch == CTX_ARCH_AUTO_RDL ||
         smt_status(ctx->core) == STATUS_IDLE);

  code = context_process_assertions(ctx, n, f);
  if (code == TRIVIALLY_UNSAT) {
    if (ctx->arch == CTX_ARCH_AUTO_IDL || ctx->arch == CTX_ARCH_AUTO_RDL) {
      // cleanup: reset arch/config to 'no theory'
      assert(ctx->arith_solver == NULL && ctx->bv_solver == NULL && ctx->fun_solver == NULL &&
	     ctx->mode == CTX_MODE_ONECHECK);
      ctx->arch = CTX_ARCH_NOSOLVERS;
      ctx->theories = 0;
      ctx->options = 0;
    }

    if( smt_status(ctx->core) != STATUS_UNSAT) {
      // force UNSAT in the core
      add_empty_clause(ctx->core);
      ctx->core->status = STATUS_UNSAT;
    }
  }

  return code;
}

int32_t assert_formulas(context_t *ctx, uint32_t n, const term_t *f) {
  MT_PROTECT(int32_t, __yices_globals.lock, _o_assert_formulas(ctx, n, f));
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
    // we must call internalization start first
    internalization_start(ctx->core);
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
 * Build an assumption for Boolean term t:
 * - this converts t to a literal l in context ctx
 *   then create an indicator variable x in the core
 *   and add the clause (x => l) in the core.
 * - return a negative code if t can't be internalized
 * - return the literal x otherwise (where x>=0).
 */
int32_t context_add_assumption(context_t *ctx, term_t t) {
  int32_t l, x;

  // check if we already have an assumption literal for t
  x = assumption_literal_for_term(&ctx->assumptions, t);
  if (x < 0) {
    l = context_internalize(ctx, t);
    if (l < 0) return l; // error code

    x = pos_lit(create_boolean_variable(ctx->core));
    add_binary_clause(ctx->core, not(x), l); // clause (x implies l)

    assumption_stack_add(&ctx->assumptions, t, x);
  }

  return x;
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

    switch (ctx->arch) {
    case CTX_ARCH_EG:
      /*
       * UF problem: we must process subst_eqs last since the
       * preprocessing may add new equalities in aux_eqs that may end
       * up in subst_eqs after the call to process_aux_eqs.
       */
      if (context_breaksym_enabled(ctx)) {
	break_uf_symmetries(ctx);
      }
      if (context_eq_abstraction_enabled(ctx)) {
        analyze_uf(ctx);
      }
      if (ctx->aux_eqs.size > 0) {
	process_aux_eqs(ctx);
      }
      if (ctx->subst_eqs.size > 0) {
	context_process_candidate_subst(ctx);
      }
      break;

    case CTX_ARCH_AUTO_IDL:
      /*
       * For difference logic, we must process the subst_eqs first
       * (otherwise analyze_diff_logic may give wrong results).
       */
      if (ctx->subst_eqs.size > 0) {
	context_process_candidate_subst(ctx);
      }
      analyze_diff_logic(ctx, true);
      create_auto_idl_solver(ctx);
      break;

    case CTX_ARCH_AUTO_RDL:
      /*
       * Difference logic, we must process the subst_eqs first
       */
      if (ctx->subst_eqs.size > 0) {
	context_process_candidate_subst(ctx);
      }
      analyze_diff_logic(ctx, false);
      create_auto_rdl_solver(ctx);
      break;

    case CTX_ARCH_SPLX:
      /*
       * Simplex, like EG, may add aux_atoms so we must process
       * subst_eqs last here.
       */
      // more optional processing
      if (context_cond_def_preprocessing_enabled(ctx)) {
	process_conditional_definitions(ctx);
	if (ctx->aux_eqs.size > 0) {
	  process_aux_eqs(ctx);
	}
	if (ctx->aux_atoms.size > 0) {
	  process_aux_atoms(ctx);
	}
      }
      if (ctx->subst_eqs.size > 0) {
	context_process_candidate_subst(ctx);
      }
      break;

    default:
      /*
       * Process the candidate variable substitutions if any
       */
      if (ctx->subst_eqs.size > 0) {
	context_process_candidate_subst(ctx);
      }
      break;
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
 * Interrupt the search.
 */
void context_stop_search(context_t *ctx) {
  if (ctx->mcsat == NULL) {
    stop_search(ctx->core);
    if (context_has_simplex_solver(ctx)) {
      simplex_stop_search(ctx->arith_solver);
    }
  } else {
    mcsat_stop_search(ctx->mcsat);
  }
}



/*
 * Cleanup: restore ctx to a good state after check_context
 * is interrupted.
 */
void context_cleanup(context_t *ctx) {
  // restore the state to IDLE, propagate to all solvers (via pop)
  assert(context_supports_cleaninterrupt(ctx));
  if (ctx->mcsat == NULL) {
    smt_cleanup(ctx->core);
  } else {
    mcsat_clear(ctx->mcsat);
  }
}



/*
 * Clear: prepare for more assertions and checks
 * - free the boolean assignment
 * - reset the status to IDLE
 */
void context_clear(context_t *ctx) {
  assert(context_supports_multichecks(ctx));
  if (ctx->mcsat == NULL) {
    smt_clear(ctx->core);
  } else {
    mcsat_clear(ctx->mcsat);
  }
}



/*
 * Clear_unsat: prepare for pop if the status is UNSAT
 * - remove assumptions if any
 *
 * - if clean interrupt is enabled, then there may be a mismatch between
 *   the context's base_level and the core base_level.
 * - it's possible to have ctx->core.base_level = ctx->base_level + 1
 * - this happens because start_search in smt_core does an internal smt_push
 *   to allow the core to be restored to a clean state if search is interrupted.
 * - if search is not interrupted and the search returns UNSAT, then we're
 *   in a state with core base level = context base level + 1.
 */
void context_clear_unsat(context_t *ctx) {
  if (ctx->mcsat == NULL) {
    smt_clear_unsat(ctx->core);
    assert(smt_base_level(ctx->core) == ctx->base_level);
  }
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
  if (ctx->egraph != NULL) {
    egraph_gc_mark(ctx->egraph);
  }
  if (ctx->fun_solver != NULL) {
    fun_solver_gc_mark(ctx->fun_solver);
  }

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

  if (ctx->mcsat != NULL) {
    mcsat_gc_mark(ctx->mcsat);
  }
}
