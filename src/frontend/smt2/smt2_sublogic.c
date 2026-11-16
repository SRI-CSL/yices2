/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2026 SRI International.
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
 * Detect that a problem belongs to a smaller logic than the declared one.
 */

#include <assert.h>

#include "api/context_config.h"
#include "context/context_types.h"
#include "frontend/smt2/smt2_sublogic.h"
#include "terms/polynomials.h"
#include "terms/power_products.h"
#include "utils/int_hash_sets.h"
#include "utils/int_vectors.h"


/*
 * Theories used by a set of formulas.
 */
typedef struct sublogic_features_s {
  bool uf;           // uninterpreted functions or sorts (needs the egraph)
  bool bv;           // bit-vectors
  bool arith_used;   // some arithmetic term (possibly only constants)
  bool has_int;      // non-constant integer term
  bool has_real;     // non-constant real term or non-integer constant
  bool mixed;        // to_int, is_int: forces mixed arithmetic
  bool nonlinear;    // non-linear arithmetic
  bool unsupported;  // construct we don't analyze: give up
} sublogic_features_t;


/*
 * Arithmetic capabilities of a logic
 */
#define CAP_INT  1u
#define CAP_REAL 2u
#define CAP_NL   4u
#define CAP_DIFF 8u

static uint32_t arith_caps(arith_fragment_t f) {
  switch (f) {
  case ARITH_IDL:  return CAP_INT|CAP_DIFF;
  case ARITH_RDL:  return CAP_REAL|CAP_DIFF;
  case ARITH_LIA:  return CAP_INT;
  case ARITH_LRA:  return CAP_REAL;
  case ARITH_LIRA: return CAP_INT|CAP_REAL;
  case ARITH_NIA:  return CAP_INT|CAP_NL;
  case ARITH_NRA:  return CAP_REAL|CAP_NL;
  case ARITH_NIRA: return CAP_INT|CAP_REAL|CAP_NL;
  case ARITH_FFA:
  case ARITH_NONE:
  default:
    return 0;
  }
}


/*
 * Mark the theories used by the domain and range types of a function type
 * (e.g., an array from bit-vectors to bit-vectors needs the bit-vector solver
 * even if no bit-vector term occurs outside the array).
 */
static void add_component_features(type_table_t *types, type_t tau, sublogic_features_t *f) {
  uint32_t i, n;

  switch (type_kind(types, tau)) {
  case BOOL_TYPE:
    break;

  case INT_TYPE:
    f->arith_used = true;
    f->has_int = true;
    break;

  case REAL_TYPE:
    f->arith_used = true;
    f->has_real = true;
    break;

  case BITVECTOR_TYPE:
    f->bv = true;
    break;

  case SCALAR_TYPE:
  case UNINTERPRETED_TYPE:
    f->uf = true;
    break;

  case FUNCTION_TYPE:
    f->uf = true;
    n = function_type_arity(types, tau);
    for (i=0; i<n; i++) {
      add_component_features(types, function_type_domain(types, tau, i), f);
    }
    add_component_features(types, function_type_range(types, tau), f);
    break;

  default:
    // tuples, finite fields, ...
    f->unsupported = true;
    break;
  }
}


/*
 * Mark the theories used by term t itself (not by its children)
 */
static void add_type_features(term_table_t *terms, term_t t, sublogic_features_t *f) {
  switch (term_type_kind(terms, t)) {
  case BOOL_TYPE:
    break;

  case INT_TYPE:
  case REAL_TYPE:
    f->arith_used = true;
    if (term_kind(terms, t) == ARITH_CONSTANT) {
      if (!is_integer_term(terms, t)) f->has_real = true;
    } else if (is_integer_term(terms, t)) {
      f->has_int = true;
    } else {
      f->has_real = true;
    }
    break;

  case BITVECTOR_TYPE:
    f->bv = true;
    break;

  case SCALAR_TYPE:
  case UNINTERPRETED_TYPE:
    f->uf = true;
    break;

  case FUNCTION_TYPE:
    // function terms are only visited when they are not the head of an application
    f->uf = true;
    add_component_features(terms->types, term_type(terms, t), f);
    break;

  default:
    // tuples, finite fields, ...
    f->unsupported = true;
    break;
  }
}


/*
 * Push all children of a composite term
 */
static void push_composite(ivector_t *stack, composite_term_t *d, uint32_t first) {
  uint32_t i;

  for (i=first; i<d->arity; i++) {
    ivector_push(stack, d->arg[i]);
  }
}

static void push_poly(ivector_t *stack, polynomial_t *p) {
  uint32_t i;

  for (i=0; i<p->nterms; i++) {
    if (p->mono[i].var != const_idx) {
      ivector_push(stack, p->mono[i].var);
    }
  }
}

static void push_bvpoly64(ivector_t *stack, bvpoly64_t *p) {
  uint32_t i;

  for (i=0; i<p->nterms; i++) {
    if (p->mono[i].var != const_idx) {
      ivector_push(stack, p->mono[i].var);
    }
  }
}

static void push_bvpoly(ivector_t *stack, bvpoly_t *p) {
  uint32_t i;

  for (i=0; i<p->nterms; i++) {
    if (p->mono[i].var != const_idx) {
      ivector_push(stack, p->mono[i].var);
    }
  }
}

static bool is_arith_constant(term_table_t *terms, term_t t) {
  return term_kind(terms, unsigned_term(t)) == ARITH_CONSTANT;
}


/*
 * Visit t and add its children to the stack
 */
static void visit_term(term_table_t *terms, term_t t, ivector_t *stack, sublogic_features_t *f) {
  composite_term_t *d;
  pprod_t *p;

  add_type_features(terms, t, f);
  if (f->unsupported) return;

  switch (term_kind(terms, t)) {
  case UNUSED_TERM:
  case RESERVED_TERM:
    f->unsupported = true;
    break;

  case CONSTANT_TERM:
  case VARIABLE:
  case UNINTERPRETED_TERM:
  case ARITH_CONSTANT:
  case BV64_CONSTANT:
  case BV_CONSTANT:
    break;

  case ARITH_FF_CONSTANT:
  case ARITH_FF_EQ_ATOM:
  case ARITH_FF_BINEQ_ATOM:
  case ARITH_FF_POLY:
  case ARITH_ROOT_ATOM:
  case FORALL_TERM:
  case LAMBDA_TERM:
  case TUPLE_TERM:
  case SELECT_TERM:
    f->unsupported = true;
    break;

  case ARITH_EQ_ATOM:
  case ARITH_GE_ATOM:
    ivector_push(stack, arith_atom_arg(terms, t));
    break;

  case ARITH_ABS:
    ivector_push(stack, arith_abs_arg(terms, t));
    break;

  case ARITH_IS_INT_ATOM:
    f->mixed = true;
    ivector_push(stack, arith_is_int_arg(terms, t));
    break;

  case ARITH_FLOOR:
    f->mixed = true;
    ivector_push(stack, arith_floor_arg(terms, t));
    break;

  case ARITH_CEIL:
    f->mixed = true;
    ivector_push(stack, arith_ceil_arg(terms, t));
    break;

  case ARITH_RDIV:
  case ARITH_IDIV:
  case ARITH_MOD:
    // t = (op num den): linear iff den is a constant
    d = composite_term_desc(terms, t);
    if (!is_arith_constant(terms, d->arg[1])) {
      f->nonlinear = true;
    }
    push_composite(stack, d, 0);
    break;

  case ARITH_DIVIDES_ATOM:
    // t = (divides k x): linear iff k is a constant
    d = composite_term_desc(terms, t);
    if (!is_arith_constant(terms, d->arg[0])) {
      f->nonlinear = true;
    }
    push_composite(stack, d, 0);
    break;

  case APP_TERM:
    // arg[0] is the function. If it's a variable, it must not be treated as a
    // function-typed argument.
    d = composite_term_desc(terms, t);
    f->uf = true;
    add_component_features(terms->types, term_type(terms, d->arg[0]), f);
    if (term_kind(terms, unsigned_term(d->arg[0])) == UNINTERPRETED_TERM) {
      push_composite(stack, d, 1);
    } else {
      push_composite(stack, d, 0);
    }
    break;

  case UPDATE_TERM:
    f->uf = true;
    push_composite(stack, composite_term_desc(terms, t), 0);
    break;

  case ITE_TERM:
  case ITE_SPECIAL:
  case EQ_TERM:
  case DISTINCT_TERM:
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
    push_composite(stack, composite_term_desc(terms, t), 0);
    break;

  case BIT_TERM:
    ivector_push(stack, bit_term_arg(terms, t));
    break;

  case POWER_PRODUCT:
    p = pprod_term_desc(terms, t);
    if (is_arithmetic_term(terms, t)) {
      f->nonlinear = true;
    }
    {
      uint32_t i;
      for (i=0; i<p->len; i++) {
        ivector_push(stack, p->prod[i].var);
      }
    }
    break;

  case ARITH_POLY:
    push_poly(stack, poly_term_desc(terms, t));
    break;

  case BV64_POLY:
    push_bvpoly64(stack, bvpoly64_term_desc(terms, t));
    break;

  case BV_POLY:
    push_bvpoly(stack, bvpoly_term_desc(terms, t));
    break;
  }
}


/*
 * Collect the features of formulas a[0 ... n-1]
 */
static void collect_features(term_table_t *terms, const term_t *a, uint32_t n, sublogic_features_t *f) {
  int_hset_t seen;
  ivector_t stack;
  term_t t;
  uint32_t i;

  f->uf = false;
  f->bv = false;
  f->arith_used = false;
  f->has_int = false;
  f->has_real = false;
  f->mixed = false;
  f->nonlinear = false;
  f->unsupported = false;

  init_int_hset(&seen, 64);
  init_ivector(&stack, 64);
  for (i=0; i<n; i++) {
    ivector_push(&stack, a[i]);
  }

  while (stack.size > 0 && !f->unsupported) {
    t = unsigned_term(ivector_pop2(&stack));
    if (int_hset_add(&seen, t)) {
      visit_term(terms, t, &stack, f);
    }
  }

  delete_ivector(&stack);
  delete_int_hset(&seen);
}


/*
 * Check whether logic code c can replace the declared logic
 * - needs = arithmetic capabilities required by the problem
 * - exact_arith = true if the arithmetic fragment must not change
 * Return the cost of c, or -1 if c is not a valid replacement.
 */
static int32_t candidate_cost(smt_logic_t c, smt_logic_t declared, const sublogic_features_t *f,
                              uint32_t needs, bool exact_arith) {
  arith_fragment_t cfrag, dfrag;
  uint32_t ccaps, dcaps;
  bool c_arrays, c_eg, c_bv, d_arrays, d_bv;
  int32_t arch;

  if (c == SMT_ALL || c == NONE || qf_fragment(c) != c) return -1;

  arch = arch_for_logic(c);
  if (arch < 0 || arch == CTX_ARCH_MCSAT) return -1;

  cfrag = arith_fragment(c);
  dfrag = arith_fragment(declared);
  if (cfrag == ARITH_FFA) return -1;
  if (exact_arith && cfrag != dfrag) return -1;

  // difference logic is a restriction that we don't test for
  if ((cfrag == ARITH_IDL || cfrag == ARITH_RDL) && cfrag != dfrag) return -1;

  ccaps = arith_caps(cfrag);
  dcaps = arith_caps(dfrag);
  if ((ccaps & ~dcaps) != 0) return -1;     // c has arithmetic that the declared logic lacks
  if ((needs & ~ccaps) != 0) return -1;     // c lacks arithmetic that we need

  c_arrays = logic_has_arrays(c);
  c_eg = logic_has_uf(c) || c_arrays;
  c_bv = logic_has_bv(c);
  d_arrays = logic_has_arrays(declared);
  d_bv = logic_has_bv(declared);

  if (c_bv && !d_bv) return -1;
  if (f->bv && !c_bv) return -1;

  /*
   * Uninterpreted functions and arrays form one group: Yices terms don't
   * distinguish them and the declared logic decides how models print them.
   * If the problem uses either, we keep exactly the declared combination.
   * Otherwise, we drop both.
   */
  if (f->uf) {
    if (c_arrays != d_arrays || logic_has_uf(c) != logic_has_uf(declared)) return -1;
  } else if (c_eg) {
    return -1;
  }

  return 3 * (int32_t) c_arrays + 2 * (int32_t) logic_has_uf(c) + 2 * (int32_t) c_bv
    + (int32_t) ((ccaps & CAP_INT) != 0) + (int32_t) ((ccaps & CAP_REAL) != 0)
    + 4 * (int32_t) ((ccaps & CAP_NL) != 0);
}


smt_logic_t smt2_smallest_sublogic(term_table_t *terms, smt_logic_t declared,
                                   const term_t *a, uint32_t n) {
  sublogic_features_t f;
  smt_logic_t c, best;
  int32_t cost, best_cost;
  uint32_t needs;
  bool exact_arith;

  if (declared == SMT_UNKNOWN || declared == NONE || qf_fragment(declared) != declared ||
      arith_fragment(declared) == ARITH_FFA) {
    return declared;
  }

  collect_features(terms, a, n, &f);
  if (f.unsupported || f.nonlinear) {
    return declared;
  }

  needs = 0;
  if (f.has_int) needs |= CAP_INT;
  if (f.has_real) needs |= CAP_REAL;
  if (f.mixed) needs |= CAP_INT|CAP_REAL;

  // only constants: we can't tell which arithmetic is required
  exact_arith = f.arith_used && needs == 0;

  best = declared;
  best_cost = -1;
  for (c=0; c<NUM_SMT_LOGICS; c++) {
    cost = candidate_cost(c, declared, &f, needs, exact_arith);
    if (cost >= 0 && (best_cost < 0 || cost < best_cost)) {
      best = c;
      best_cost = cost;
    }
  }

  if (best != declared && arch_for_logic(best) == arch_for_logic(declared)) {
    // same solvers: keep the declared logic
    best = declared;
  }

  return best;
}
