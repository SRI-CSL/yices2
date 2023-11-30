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

#if defined(CYGWIN) || defined(MINGW)
#ifndef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__ __declspec(dllexport)
#endif
#endif

#include "mcsat/preprocessor.h"
#include "mcsat/tracing.h"

#include "terms/term_explorer.h"
#include "terms/bvarith64_buffer_terms.h"
#include "terms/bvarith_buffer_terms.h"

#include "model/models.h"

#include "context/context_types.h"

#include "yices.h"
#include "api/yices_api_lock_free.h"

void preprocessor_construct(preprocessor_t* pre, term_table_t* terms, jmp_buf* handler, const mcsat_options_t* options) {
  pre->terms = terms;
  init_term_manager(&pre->tm, terms);
  init_int_hmap(&pre->preprocess_map, 0);
  init_ivector(&pre->preprocess_map_list, 0);
  init_int_hmap(&pre->purification_map, 0);
  init_ivector(&pre->purification_map_list, 0);
  init_ivector(&pre->preprocessing_stack, 0);
  init_int_hmap(&pre->equalities, 0);
  init_ivector(&pre->equalities_list, 0);
  pre->tracer = NULL;
  pre->exception = handler;
  pre->options = options;
  scope_holder_construct(&pre->scope);
}

void preprocessor_set_tracer(preprocessor_t* pre, tracer_t* tracer) {
  pre->tracer = tracer;
}

void preprocessor_destruct(preprocessor_t* pre) {
  delete_int_hmap(&pre->purification_map);
  delete_ivector(&pre->purification_map_list);
  delete_int_hmap(&pre->preprocess_map);
  delete_ivector(&pre->preprocess_map_list);
  delete_ivector(&pre->preprocessing_stack);
  delete_int_hmap(&pre->equalities);
  delete_ivector(&pre->equalities_list);
  delete_term_manager(&pre->tm);
  scope_holder_destruct(&pre->scope);
}

static
term_t preprocessor_get(preprocessor_t* pre, term_t t) {
  int_hmap_pair_t* find = int_hmap_find(&pre->preprocess_map, t);
  if (find == NULL) {
    return NULL_TERM;
  } else {
    return find->val;
  }
}

static
void preprocessor_set(preprocessor_t* pre, term_t t, term_t t_pre) {
  assert(preprocessor_get(pre, t) == NULL_TERM);
  int_hmap_add(&pre->preprocess_map, t, t_pre);
  ivector_push(&pre->preprocess_map_list, t);
}

typedef struct composite_term1_s {
  uint32_t arity;  // number of subterms
  term_t arg[1];  // real size = arity
} composite_term1_t;

static
composite_term1_t composite_for_noncomposite;

static
composite_term_t* get_composite(term_table_t* terms, term_kind_t kind, term_t t) {
  assert(term_is_composite(terms, t));
  assert(term_kind(terms, t) == kind);
  assert(is_pos_term(t));

  switch (kind) {
  case ITE_TERM:           // if-then-else
  case ITE_SPECIAL:        // special if-then-else term (NEW: EXPERIMENTAL)
    return ite_term_desc(terms, t);
  case EQ_TERM:            // equality
    return eq_term_desc(terms, t);
  case OR_TERM:            // n-ary OR
    return or_term_desc(terms, t);
  case XOR_TERM:           // n-ary XOR
    return xor_term_desc(terms, t);
  case ARITH_BINEQ_ATOM:   // equality: (t1 == t2)  (between two arithmetic terms)
    return arith_bineq_atom_desc(terms, t);
  case ARITH_EQ_ATOM: {
    composite_for_noncomposite.arity = 1;
    composite_for_noncomposite.arg[0] = arith_eq_arg(terms, t);
    return (composite_term_t*)&composite_for_noncomposite;
  }
  case ARITH_GE_ATOM: {
    composite_for_noncomposite.arity = 1;
    composite_for_noncomposite.arg[0] = arith_ge_arg(terms, t);
    return (composite_term_t*)&composite_for_noncomposite;
  }
  case APP_TERM:           // application of an uninterpreted function
    return app_term_desc(terms, t);
  case ARITH_RDIV:          // division: (/ x y)
    return arith_rdiv_term_desc(terms, t);
  case ARITH_IDIV:          // division: (div x y) as defined in SMT-LIB 2
    return arith_idiv_term_desc(terms, t);
  case ARITH_MOD:          // remainder: (mod x y) is y - x * (div x y)
    return arith_mod_term_desc(terms, t);
  case UPDATE_TERM:
    return update_term_desc(terms, t);
  case DISTINCT_TERM:
    return distinct_term_desc(terms, t);
  case BV_ARRAY:
    return bvarray_term_desc(terms, t);
  case BV_DIV:
    return bvdiv_term_desc(terms, t);
  case BV_REM:
    return bvrem_term_desc(terms, t);
  case BV_SDIV:
    return bvsdiv_term_desc(terms, t);
  case BV_SREM:
    return bvsrem_term_desc(terms, t);
  case BV_SMOD:
    return bvsmod_term_desc(terms, t);
  case BV_SHL:
    return bvshl_term_desc(terms, t);
  case BV_LSHR:
    return bvlshr_term_desc(terms, t);
  case BV_ASHR:
    return bvashr_term_desc(terms, t);
  case BV_EQ_ATOM:
    return bveq_atom_desc(terms, t);
  case BV_GE_ATOM:
    return bvge_atom_desc(terms, t);
  case BV_SGE_ATOM:
    return bvsge_atom_desc(terms, t);
  default:
    assert(false);
    return NULL;
  }
}

static
term_t mk_composite(preprocessor_t* pre, term_kind_t kind, uint32_t n, term_t* children) {
  term_manager_t* tm = &pre->tm;
  term_table_t* terms = pre->terms;

  switch (kind) {
  case ITE_TERM:           // if-then-else
  case ITE_SPECIAL:        // special if-then-else term (NEW: EXPERIMENTAL)
  {
    assert(n == 3);
    term_t type = super_type(pre->terms->types, term_type(terms, children[1]), term_type(terms, children[2]));
    assert(type != NULL_TYPE);
    return mk_ite(tm, children[0], children[1], children[2], type);
  }
  case EQ_TERM:            // equality
    assert(n == 2);
    return mk_eq(tm, children[0], children[1]);
  case OR_TERM:            // n-ary OR
    assert(n > 1);
    return mk_or(tm, n, children);
  case XOR_TERM:           // n-ary XOR
    return mk_xor(tm, n, children);
  case ARITH_EQ_ATOM:
    assert(n == 1);
    return mk_arith_eq(tm, children[0], zero_term);
  case ARITH_GE_ATOM:
    assert(n == 1);
    return mk_arith_geq(tm, children[0], zero_term);
  case ARITH_BINEQ_ATOM:   // equality: (t1 == t2)  (between two arithmetic terms)
    assert(n == 2);
    return mk_arith_eq(tm, children[0], children[1]);
  case APP_TERM:           // application of an uninterpreted function
    assert(n > 1);
    return mk_application(tm, children[0], n-1, children + 1);
  case ARITH_RDIV:
    assert(n == 2);
    return mk_arith_rdiv(tm, children[0], children[1]);
  case ARITH_IDIV:          // division: (div x y) as defined in SMT-LIB 2
    assert(n == 2);
    return mk_arith_idiv(tm, children[0], children[1]);
  case ARITH_MOD:          // remainder: (mod x y) is y - x * (div x y)
    assert(n == 2);
    return mk_arith_mod(tm, children[0], children[1]);
  case UPDATE_TERM:
    assert(n > 2);
    return mk_update(tm, children[0], n-2, children + 1, children[n-1]);
  case BV_ARRAY:
    assert(n >= 1);
    return mk_bvarray(tm, n, children);
  case BV_DIV:
    assert(n == 2);
    return mk_bvdiv(tm, children[0], children[1]);
  case BV_REM:
    assert(n == 2);
    return mk_bvrem(tm, children[0], children[1]);
  case BV_SDIV:
    assert(n == 2);
    return mk_bvsdiv(tm, children[0], children[1]);
  case BV_SREM:
    assert(n == 2);
    return mk_bvsrem(tm, children[0], children[1]);
  case BV_SMOD:
    assert(n == 2);
    return mk_bvsmod(tm, children[0], children[1]);
  case BV_SHL:
    assert(n == 2);
    return mk_bvshl(tm, children[0], children[1]);
  case BV_LSHR:
    assert(n == 2);
    return mk_bvlshr(tm, children[0], children[1]);
  case BV_ASHR:
    assert(n == 2);
    return mk_bvashr(tm, children[0], children[1]);
  case BV_EQ_ATOM:
    assert(n == 2);
    return mk_bveq(tm, children[0], children[1]);
  case BV_GE_ATOM:
    assert(n == 2);
    return mk_bvge(tm, children[0], children[1]);
  case BV_SGE_ATOM:
    assert(n == 2);
    return mk_bvsge(tm, children[0], children[1]);
  default:
    assert(false);
    return NULL_TERM;
  }
}

/**
 * Returns true if we should purify t as an argument of a function.
 * Any new equalities are added to output.
 */
static inline
term_t preprocessor_purify(preprocessor_t* pre, term_t t, ivector_t* out) {

  term_table_t* terms = pre->terms;

  // Negated terms must be purified
  if (is_pos_term(t)) {
    // We don't purify variables
    term_kind_t t_kind = term_kind(terms, t);
    switch (t_kind) {
    case UNINTERPRETED_TERM:
      // Variables are already pure
      return t;
    case CONSTANT_TERM:
      return t;
    case ARITH_CONSTANT:
    case BV64_CONSTANT:
    case BV_CONSTANT:
      // Constants are also pure (except for false)
      return t;
    case APP_TERM:
      // Uninterpreted functions are also already purified
      return t;
    case UPDATE_TERM:
      return t;
    default:
      break;
    }
  }

  // Everything else gets purified. Check if in the cache
  int_hmap_pair_t* find = int_hmap_find(&pre->purification_map, t);
  if (find != NULL) {
    return find->val;
  } else {
    // Make the variable
    type_t t_type = term_type(terms, t);
    term_t x = new_uninterpreted_term(terms, t_type);
    // Remember for later
    int_hmap_add(&pre->purification_map, t, x);
    ivector_push(&pre->purification_map_list, t);
    // Also add the variable to the pre-processor
    preprocessor_set(pre, x, x);
    // Add equality to output
    term_t eq = mk_eq(&pre->tm, x, t);
    ivector_push(out, eq);

    if (trace_enabled(pre->tracer, "mcsat::preprocess")) {
      mcsat_trace_printf(pre->tracer, "adding lemma = ");
      trace_term_ln(pre->tracer, terms, eq);
    }

    // Return the purified version
    return x;
  }
}

static inline
term_t mk_bvneg(term_manager_t* tm, term_t t) {
  term_table_t* terms = tm->terms;
  if (term_bitsize(terms,t) <= 64) {
    bvarith64_buffer_t *buffer = term_manager_get_bvarith64_buffer(tm);
    bvarith64_buffer_set_term(buffer, terms, t);
    bvarith64_buffer_negate(buffer);
    return mk_bvarith64_term(tm, buffer);
  } else {
    bvarith_buffer_t *buffer = term_manager_get_bvarith_buffer(tm);
    bvarith_buffer_set_term(buffer, terms, t);
    bvarith_buffer_negate(buffer);
    return mk_bvarith_term(tm, buffer);
  }
}

// Mark equality eq: (var = t) for solving
static
void preprocessor_mark_eq(preprocessor_t* pre, term_t eq, term_t var) {
  assert(is_pos_term(eq));
  assert(is_pos_term(var));
  assert(term_kind(pre->terms, var) == UNINTERPRETED_TERM);

  // Mark the equality
  int_hmap_pair_t* find = int_hmap_get(&pre->equalities, eq);
  assert(find->val == -1);
  find->val = var;
  ivector_push(&pre->equalities_list, eq);
}

static
term_t preprocessor_get_eq_solved_var(const preprocessor_t* pre, term_t eq) {
  assert(is_pos_term(eq));
  int_hmap_pair_t* find = int_hmap_find((int_hmap_t*) &pre->equalities, eq);
  if (find != NULL) {
    return find->val;
  } else {
    return NULL_TERM;
  }
}

term_t preprocessor_apply(preprocessor_t* pre, term_t t, ivector_t* out, bool is_assertion) {

  term_table_t* terms = pre->terms;
  term_manager_t* tm = &pre->tm;

  uint32_t i, j, n;

  // Check if already preprocessed;
  term_t t_pre = preprocessor_get(pre, t);
  if (t_pre != NULL_TERM) {
    return t_pre;
  }

// Note: negative affect on general performance due to solved/substituted
//       terms being to complex for explainers.
//
//  // First, if the assertion is a conjunction, just expand
//  if (is_assertion && is_neg_term(t) && term_kind(terms, t) == OR_TERM) {
//    // !(or t1 ... tn) -> !t1 && ... && !tn
//    composite_term_t* t_desc = composite_term_desc(terms, t);
//    for (i = 0; i < t_desc->arity; ++ i) {
//      ivector_push(out, opposite_term(t_desc->arg[i]));
//    }
//    return true_term;
//  }
//
  // Start
  ivector_t* pre_stack = &pre->preprocessing_stack;
  ivector_reset(pre_stack);
  ivector_push(pre_stack, t);

  // Preprocess
  while (pre_stack->size) {
    // Current term
    term_t current = ivector_last(pre_stack);

    if (trace_enabled(pre->tracer, "mcsat::preprocess")) {
      mcsat_trace_printf(pre->tracer, "current = ");
      trace_term_ln(pre->tracer, terms, current);
    }

    // If preprocessed already, done
    term_t current_pre = preprocessor_get(pre, current);
    if (current_pre != NULL_TERM) {
      ivector_pop(pre_stack);
      continue;
    }

    // Negation
    if (is_neg_term(current)) {
      term_t child = unsigned_term(current);
      term_t child_pre = preprocessor_get(pre, child);
      if (child_pre == NULL_TERM) {
        ivector_push(pre_stack, child);
        continue;
      } else {
        ivector_pop(pre_stack);
        current_pre = opposite_term(child_pre);
        preprocessor_set(pre, current, current_pre);
        continue;
      }
    }

    // Check for supported types
    type_kind_t type = term_type_kind(terms, current);
    switch (type) {
    case BOOL_TYPE:
    case INT_TYPE:
    case REAL_TYPE:
    case UNINTERPRETED_TYPE:
    case FUNCTION_TYPE:
    case BITVECTOR_TYPE:
    case SCALAR_TYPE:
      break;
    default:
      longjmp(*pre->exception, MCSAT_EXCEPTION_UNSUPPORTED_THEORY);
    }

    // Kind of term
    term_kind_t current_kind = term_kind(terms, current);

    switch(current_kind) {
    case CONSTANT_TERM:    // constant of uninterpreted/scalar/boolean types
    case BV64_CONSTANT:    // compact bitvector constant (64 bits at most)
    case BV_CONSTANT:      // generic bitvector constant (more than 64 bits)
    case ARITH_CONSTANT:   // rational constant
      current_pre = current;
      break;
    case UNINTERPRETED_TERM:  // (i.e., global variables, can't be bound).
      current_pre = current;
      // Unless we want special slicing
      if (type == BITVECTOR_TYPE) {
        if (pre->options->bv_var_size > 0) {
          uint32_t size = term_bitsize(terms, current);
          uint32_t var_size = pre->options->bv_var_size;
          if (size > var_size) {
            uint32_t n_vars = (size - 1) / var_size + 1;
            term_t vars[n_vars];
            for (i = n_vars - 1; size > 0; i--) {
              if (size >= var_size) {
                vars[i] = new_uninterpreted_term(terms, bv_type(terms->types, var_size));
                size -= var_size;
              } else {
                vars[i] = new_uninterpreted_term(terms, bv_type(terms->types, size));
                size = 0;
              }
            }
            current_pre = _o_yices_bvconcat(n_vars, vars);
            term_t eq = _o_yices_eq(current, current_pre);
            preprocessor_mark_eq(pre, eq, current);
          }
        }
      }
      break;

    case ITE_TERM:           // if-then-else
    case ITE_SPECIAL:        // special if-then-else term (NEW: EXPERIMENTAL)
    case EQ_TERM:            // equality
    case OR_TERM:            // n-ary OR
    case XOR_TERM:           // n-ary XOR
    case ARITH_EQ_ATOM:      // equality (t == 0)
    case ARITH_BINEQ_ATOM:   // equality: (t1 == t2)  (between two arithmetic terms)
    case ARITH_GE_ATOM:      // inequality (t >= 0)
    case BV_ARRAY:
    case BV_DIV:
    case BV_REM:
    case BV_SMOD:
    case BV_SHL:
    case BV_LSHR:
    case BV_ASHR:
    case BV_EQ_ATOM:
    case BV_GE_ATOM:
    case BV_SGE_ATOM:
    {
      composite_term_t* desc = get_composite(terms, current_kind, current);
      bool children_done = true;
      bool children_same = true;

      n = desc->arity;

      /*
      // Arrays not supported yet
      if (current_kind == EQ_TERM && term_type_kind(terms, desc->arg[0]) == FUNCTION_TYPE) {
        longjmp(*pre->exception, MCSAT_EXCEPTION_UNSUPPORTED_THEORY);
      }
      */
 
      // Is this a top-level equality assertion
      bool is_equality =
          current_kind == EQ_TERM ||
          current_kind == BV_EQ_ATOM ||
          current_kind == ARITH_BINEQ_ATOM ||
          current_kind == ARITH_EQ_ATOM;
      // don't rewrite if the equality is between Boolean terms
      bool is_boolean = is_boolean_type(term_type(pre->terms, desc->arg[0]));

      term_t eq_solve_var = NULL_TERM;
      if (is_assertion && is_equality && !is_boolean) {
	bool is_lhs_rhs_mixed = desc->arity > 1 &&
	  term_type_kind(pre->terms, desc->arg[0]) != term_type_kind(pre->terms, desc->arg[1]);
	// don't rewrite if equality is between mixed terms, e.g. between int and real terms
	if (!is_lhs_rhs_mixed && current == t) {
          eq_solve_var = preprocessor_get_eq_solved_var(pre, t);
          if (eq_solve_var == NULL_TERM) {
            term_t lhs = desc->arg[0];
            term_kind_t lhs_kind = term_kind(terms, lhs);
            // If lhs/rhs is a first-time seen variable, we can solve it
            bool lhs_is_var = lhs_kind == UNINTERPRETED_TERM && is_pos_term(lhs);
            if (lhs_is_var && preprocessor_get(pre, lhs) == NULL_TERM) {
              // First time variable, let's solve
              preprocessor_mark_eq(pre, t, lhs);
              eq_solve_var = lhs;
            } else if (desc->arity > 1) {
              term_t rhs = desc->arg[1];
              term_kind_t rhs_kind = term_kind(terms, rhs);
              bool rhs_is_var = rhs_kind == UNINTERPRETED_TERM && is_pos_term(rhs);
              if (rhs_is_var && preprocessor_get(pre, rhs) == NULL_TERM) {
                // First time variable, let's solve
                preprocessor_mark_eq(pre, t, rhs);
                eq_solve_var = rhs;
              }
            }
          } else {
            // Check that we it's not there already
            if (preprocessor_get(pre, eq_solve_var) != NULL_TERM) {
              eq_solve_var = NULL_TERM;
            }
          }
        }
      }

      ivector_t children;
      init_ivector(&children, n);

      for (i = 0; i < n; ++ i) {
        term_t child = desc->arg[i];
        if (child != eq_solve_var) {
          term_t child_pre = preprocessor_get(pre, child);
          if (child_pre == NULL_TERM) {
            children_done = false;
            ivector_push(pre_stack, child);
          } else if (child_pre != child) {
            children_same = false;
          }
          if (children_done) {
            ivector_push(&children, child_pre);
          }
        }
      }

      if (eq_solve_var != NULL_TERM) {
        // Check again to make sure we don't have something like x = x + 1
        if (preprocessor_get(pre, eq_solve_var) != NULL_TERM) {
          // Do it again
          children_done = false;
        }
      }

      if (children_done) {
        if (eq_solve_var != NULL_TERM) {
          term_t eq_solve_term = zero_term;
          if (children.size > 0) {
            eq_solve_term = children.data[0];
          }
          preprocessor_set(pre, eq_solve_var, eq_solve_term);
          current_pre = true_term;
        } else {
          if (children_same) {
            current_pre = current;
          } else {
            current_pre = mk_composite(pre, current_kind, n, children.data);
          }
        }
      }

      delete_ivector(&children);

      break;
    }

    case ARITH_ABS:
    {
      term_t arg = arith_abs_arg(terms, current);
      term_t arg_pre = preprocessor_get(pre, arg);
      if (arg_pre == NULL_TERM) {
        ivector_push(pre_stack, arg);
      } else {
        type_t arg_pre_type = term_type(pre->terms, arg_pre);
        term_t arg_pre_is_positive = mk_arith_term_geq0(&pre->tm, arg_pre);
        term_t arg_negative = _o_yices_neg(arg_pre);
        current_pre = mk_ite(&pre->tm, arg_pre_is_positive, arg_pre, arg_negative, arg_pre_type);
      }
      break;
    }

    case BV_SDIV:
    {
      composite_term_t* desc = get_composite(terms, current_kind, current);
      assert(desc->arity == 2);
      term_t s = desc->arg[0];
      term_t s_pre = preprocessor_get(pre, s);
      if (s_pre == NULL_TERM) {
        ivector_push(pre_stack, s);
      }
      term_t t = desc->arg[1];
      term_t t_pre = preprocessor_get(pre, t);
      if (t_pre == NULL_TERM) {
        ivector_push(pre_stack, t);
      }
      if (s_pre != NULL_TERM && t_pre != NULL_TERM) {
        type_t tau = term_type(terms, s_pre);
        uint32_t n = term_bitsize(terms, s_pre);
        term_t msb_s = mk_bitextract(tm, s_pre, n-1);
        term_t msb_t = mk_bitextract(tm, t_pre, n-1);
        // if (msb_s) {
        //   if (msb_t) {
        //     t1: udiv(-s, -t)
        //   } else {
        //     t2: -udiv(-s, t)
        //   }
        // } else {
        //   if (msb_t) {
        //     t3: -udiv(s, -t)
        //   } else {
        //     t4: udiv(s, t)
        //   }
        // }
        term_t neg_s = mk_bvneg(tm, s_pre);
        term_t neg_t = mk_bvneg(tm, t_pre);

        term_t t1 = mk_bvdiv(tm, neg_s, neg_t);
        term_t t2 = mk_bvdiv(tm, neg_s, t_pre);
        t2 = mk_bvneg(&pre->tm, t2);
        term_t t3 = mk_bvdiv(tm, s_pre, neg_t);
        t3 = mk_bvneg(&pre->tm, t3);
        term_t t4 = mk_bvdiv(tm, s_pre, t_pre);

        term_t b1 = mk_ite(tm, msb_t, t1, t2, tau);
        term_t b2 = mk_ite(tm, msb_t, t3, t4, tau);

        current_pre = mk_ite(tm, msb_s, b1, b2, tau);
      }
      break;
    }
    case BV_SREM:
    {
      composite_term_t* desc = get_composite(terms, current_kind, current);
      assert(desc->arity == 2);
      term_t s = desc->arg[0];
      term_t s_pre = preprocessor_get(pre, s);
      if (s_pre == NULL_TERM) {
        ivector_push(pre_stack, s);
      }
      term_t t = desc->arg[1];
      term_t t_pre = preprocessor_get(pre, t);
      if (t_pre == NULL_TERM) {
        ivector_push(pre_stack, t);
      }
      if (s_pre != NULL_TERM && t_pre != NULL_TERM) {
        type_t tau = term_type(terms, s_pre);
        uint32_t n = term_bitsize(terms, s_pre);
        term_t msb_s = mk_bitextract(tm, s_pre, n-1);
        term_t msb_t = mk_bitextract(tm, t_pre, n-1);
        // if (msb_s) {
        //   if (msb_t) {
        //     t1: -urem(-s, -t)
        //   } else {
        //     t2: -urem(-s, t)
        //   }
        // } else {
        //   if (msb_t) {
        //     t3: -urem(s, -t)
        //   } else {
        //     t4: urem(s, t)
        //   }
        // }
        term_t neg_s = mk_bvneg(tm, s_pre);
        term_t neg_t = mk_bvneg(tm, t_pre);

        term_t t1 = mk_bvrem(tm, neg_s, neg_t);
        t1 = mk_bvneg(tm, t1);
        term_t t2 = mk_bvrem(tm, neg_s, t_pre);
        t2 = mk_bvneg(tm, t2);
        term_t t3 = mk_bvrem(tm, s_pre, neg_t);
        term_t t4 = mk_bvrem(tm, s_pre, t_pre);

        term_t b1 = mk_ite(tm, msb_t, t1, t2, tau);
        term_t b2 = mk_ite(tm, msb_t, t3, t4, tau);

        current_pre = mk_ite(tm, msb_s, b1, b2, tau);
      }
      break;
    }
    case BIT_TERM: // bit-select current = child[i]
    {
      uint32_t index = bit_term_index(terms, current);
      term_t arg = bit_term_arg(terms, current);
      term_t arg_pre = preprocessor_get(pre, arg);
      if (arg_pre == NULL_TERM) {
        ivector_push(pre_stack, arg);
      } else {
        if (arg_pre == arg) {
          current_pre = current;
        } else {
          if (trace_enabled(pre->tracer, "mcsat::preprocess")) {
            mcsat_trace_printf(pre->tracer, "arg_pre = ");
            trace_term_ln(pre->tracer, terms, arg_pre);
          }
          // For simplification purposes use API
          current_pre = _o_yices_bitextract(arg_pre, index);
          assert(current_pre != NULL_TERM);
        }
      }
      break;
    }
    case BV_POLY:  // polynomial with generic bitvector coefficients
    {
      bvpoly_t* p = bvpoly_term_desc(terms, current);

      bool children_done = true;
      bool children_same = true;

      n = p->nterms;

      ivector_t children;
      init_ivector(&children, n);

      for (i = 0; i < n; ++ i) {
        term_t x = p->mono[i].var;
        term_t x_pre = (x == const_idx ? const_idx : preprocessor_get(pre, x));

        if (x_pre != const_idx) {
          if (x_pre == NULL_TERM) {
            children_done = false;
            ivector_push(pre_stack, x);
          } else if (x_pre != x) {
            children_same = false;
          }
        }

        if (children_done) { ivector_push(&children, x_pre); }
      }

      if (children_done) {
        if (children_same) {
          current_pre = current;
        } else {
          current_pre = mk_bvarith_poly(tm, p, n, children.data);
        }
      }

      delete_ivector(&children);

      break;
    }
    case BV64_POLY: // polynomial with 64bit coefficients
    {
      bvpoly64_t* p = bvpoly64_term_desc(terms, current);

      bool children_done = true;
      bool children_same = true;

      n = p->nterms;

      ivector_t children;
      init_ivector(&children, n);

      for (i = 0; i < n; ++ i) {
        term_t x = p->mono[i].var;
        term_t x_pre = (x == const_idx ? const_idx : preprocessor_get(pre, x));

        if (x_pre != const_idx) {
          if (x_pre == NULL_TERM) {
            children_done = false;
            ivector_push(pre_stack, x);
          } else if (x_pre != x) {
            children_same = false;
          }
        }

        if (children_done) { ivector_push(&children, x_pre); }
      }

      if (children_done) {
        if (children_same) {
          current_pre = current;
        } else {
          current_pre = mk_bvarith64_poly(tm, p, n, children.data);
        }
      }

      delete_ivector(&children);

      break;
    }

    case POWER_PRODUCT:    // power products: (t1^d1 * ... * t_n^d_n)
    {
      pprod_t* pp = pprod_term_desc(terms, current);
      bool children_done = true;
      bool children_same = true;

      n = pp->len;

      ivector_t children;
      init_ivector(&children, n);

      for (i = 0; i < n; ++ i) {
        term_t x = pp->prod[i].var;
        term_t x_pre = preprocessor_get(pre, x);

        if (x_pre == NULL_TERM) {
          children_done = false;
          ivector_push(pre_stack, x);
        } else if (x_pre != x) {
          children_same = false;
        }

        if (children_done) { ivector_push(&children, x_pre); }
      }

      if (children_done) {
        if (children_same) {
          current_pre = current;
        } else {
          // NOTE: it doens't change pp, it just uses it as a frame
          current_pre = mk_pprod(tm, pp, n, children.data);
        }
      }

      delete_ivector(&children);

      break;
    }

    case ARITH_POLY:       // polynomial with rational coefficients
    {
      polynomial_t* p = poly_term_desc(terms, current);

      bool children_done = true;
      bool children_same = true;

      n = p->nterms;

      ivector_t children;
      init_ivector(&children, n);

      for (i = 0; i < n; ++ i) {
        term_t x = p->mono[i].var;
        term_t x_pre = (x == const_idx ? const_idx : preprocessor_get(pre, x));

        if (x_pre != const_idx) {
          if (x_pre == NULL_TERM) {
            children_done = false;
            ivector_push(pre_stack, x);
          } else if (x_pre != x) {
            children_same = false;
          }
        }

        if (children_done) { ivector_push(&children, x_pre); }
      }

      if (children_done) {
        if (children_same) {
          current_pre = current;
        } else {
          current_pre = mk_arith_poly(tm, p, n, children.data);
        }
      }

      delete_ivector(&children);

      break;
    }

    // FOLLOWING ARE UNINTEPRETED, SO WE PURIFY THE ARGUMENTS

    case APP_TERM:           // application of an uninterpreted function
    case ARITH_RDIV:         // regular division (/ x y)
    case ARITH_IDIV:         // division: (div x y) as defined in SMT-LIB 2
    case ARITH_MOD:          // remainder: (mod x y) is y - x * (div x y)
    case UPDATE_TERM:        // update array
    {
      composite_term_t* desc = get_composite(terms, current_kind, current);
      bool children_done = true;
      bool children_same = true;

      n = desc->arity;

      ivector_t children;
      init_ivector(&children, n);

      for (i = 0; i < n; ++ i) {
        term_t child = desc->arg[i];
        term_t child_pre = preprocessor_get(pre, child);

        if (child_pre == NULL_TERM) {
          children_done = false;
          ivector_push(pre_stack, child);
        } else {
          // Purify if needed
          child_pre = preprocessor_purify(pre, child_pre, out);
          // If interpreted terms, we need to purify non-variables
          if (child_pre != child) { children_same = false; }
        }

        if (children_done) { ivector_push(&children, child_pre); }
      }

      if (children_done) {
        if (children_same) {
          current_pre = current;
        } else {
          current_pre = mk_composite(pre, current_kind, n, children.data);
        }
      }

      delete_ivector(&children);

      break;
    }

    case ARITH_IS_INT_ATOM:
    {
      // replace with t <= floor(t)
      term_t child = arith_is_int_arg(terms, current);
      term_t child_pre = preprocessor_get(pre, child);
      if (child_pre != NULL_TERM) {
        child_pre = preprocessor_purify(pre, child_pre, out);
        current_pre = arith_floor(terms, child_pre);
        current_pre = mk_arith_leq(tm, child_pre, current_pre);
      } else {
        ivector_push(pre_stack, child);
      }
      break;
    }

    case ARITH_FLOOR:        // floor: purify, but its interpreted
    {
      term_t child = arith_floor_arg(terms, current);
      term_t child_pre = preprocessor_get(pre, child);

      if (child_pre != NULL_TERM) {
        if (term_kind(terms, child_pre) == ARITH_CONSTANT) {
          rational_t floor;
          q_init(&floor);
          q_set(&floor, rational_term_desc(terms, child_pre));
          q_floor(&floor);
          current_pre = arith_constant(terms, &floor);
          q_clear(&floor);
        } else {
          child_pre = preprocessor_purify(pre, child_pre, out);
          if (child_pre != child) {
            current_pre = arith_floor(terms, child_pre);
          } else {
            current_pre = current;
          }
        }
      } else {
        ivector_push(pre_stack, child);
      }

      break;
    }

    case ARITH_CEIL:        // floor: purify, but its interpreted
    {
      term_t child = arith_ceil_arg(terms, current);
      term_t child_pre = preprocessor_get(pre, child);

      if (child_pre != NULL_TERM) {
        child_pre = preprocessor_purify(pre, child_pre, out);
        if (child_pre != child) {
          current_pre = arith_floor(terms, child_pre);
        } else {
          current_pre = current;
        }
      } else {
        ivector_push(pre_stack, child);
      }

      break;
    }

    case DISTINCT_TERM:
    {
      composite_term_t* desc = get_composite(terms, current_kind, current);

      // Arrays not supported yet
      if (term_type_kind(terms, desc->arg[0]) == FUNCTION_TYPE) {
        longjmp(*pre->exception, MCSAT_EXCEPTION_UNSUPPORTED_THEORY);
      }

      bool children_done = true;
      n = desc->arity;

      ivector_t children;
      init_ivector(&children, n);

      for (i = 0; i < n; ++ i) {
        term_t child = desc->arg[i];
        term_t child_pre = preprocessor_get(pre, child);

        if (child_pre == NULL_TERM) {
          children_done = false;
          ivector_push(pre_stack, child);
        }

        if (children_done) { ivector_push(&children, child_pre); }
      }

      if (children_done) {
        ivector_t distinct;
        init_ivector(&distinct, 0);

        for (i = 0; i < n; ++ i) {
          for (j = i + 1; j < n; ++ j) {
            term_t neq = mk_eq(&pre->tm, children.data[i], children.data[j]);
            neq = opposite_term(neq);
            ivector_push(&distinct, neq);
          }
        }
        current_pre = mk_and(&pre->tm, distinct.size, distinct.data);

        delete_ivector(&distinct);
      }

      delete_ivector(&children);

      break;
    }

    default:
      // UNSUPPORTED TERM/THEORY
      longjmp(*pre->exception, MCSAT_EXCEPTION_UNSUPPORTED_THEORY);
      break;
    }

    if (current_pre != NULL_TERM) {
      preprocessor_set(pre, current, current_pre);
      ivector_pop(pre_stack);
      if (trace_enabled(pre->tracer, "mcsat::preprocess")) {
        mcsat_trace_printf(pre->tracer, "current_pre = ");
        trace_term_ln(pre->tracer, terms, current_pre);
      }
    }

  }

  // Return the result
  t_pre = preprocessor_get(pre, t);
  if (trace_enabled(pre->tracer, "mcsat::preprocess")) {
    mcsat_trace_printf(pre->tracer, "t_pre = ");
    trace_term_ln(pre->tracer, terms, t_pre);
  }

  ivector_reset(pre_stack);

  assert(t_pre != NULL_TERM);
  return t_pre;
}

void preprocessor_set_exception_handler(preprocessor_t* pre, jmp_buf* handler) {
  pre->exception = handler;
}

void preprocessor_push(preprocessor_t* pre) {
  scope_holder_push(&pre->scope,
      &pre->preprocess_map_list.size,
      &pre->purification_map_list.size,
      &pre->equalities_list.size,
      NULL);
}

void preprocessor_pop(preprocessor_t* pre) {

  uint32_t preprocess_map_list_size = 0;
  uint32_t purification_map_list_size = 0;
  uint32_t equalities_list_size = 0;

  scope_holder_pop(&pre->scope,
      &preprocess_map_list_size,
      &purification_map_list_size,
      &equalities_list_size,
      NULL);

  while (pre->preprocess_map_list.size > preprocess_map_list_size) {
    term_t t = ivector_last(&pre->preprocess_map_list);
    ivector_pop(&pre->preprocess_map_list);
    int_hmap_pair_t* find = int_hmap_find(&pre->preprocess_map, t);
    assert(find != NULL);
    int_hmap_erase(&pre->preprocess_map, find);
  }

  while (pre->purification_map_list.size > purification_map_list_size) {
    term_t t = ivector_last(&pre->purification_map_list);
    ivector_pop(&pre->purification_map_list);
    int_hmap_pair_t* find = int_hmap_find(&pre->purification_map, t);
    assert(find != NULL);
    int_hmap_erase(&pre->purification_map, find);
  }

  while (pre->equalities_list.size > equalities_list_size) {
    term_t eq = ivector_last(&pre->equalities_list);
    ivector_pop(&pre->equalities_list);
    int_hmap_pair_t* find = int_hmap_find(&pre->equalities, eq);
    assert(find != NULL);
    int_hmap_erase(&pre->equalities, find);
  }
}

void preprocessor_build_model(preprocessor_t* pre, model_t* model) {
  uint32_t i = 0;
  for (i = 0; i < pre->equalities_list.size; ++ i) {
    term_t eq = pre->equalities_list.data[i];
    term_t eq_var = preprocessor_get_eq_solved_var(pre, eq);
    if (trace_enabled(pre->tracer, "mcsat::preprocess")) {
      mcsat_trace_printf(pre->tracer, "eq = ");
      trace_term_ln(pre->tracer, pre->terms, eq);
      mcsat_trace_printf(pre->tracer, "\neq_var = ");
      trace_term_ln(pre->tracer, pre->terms, eq_var);
      mcsat_trace_printf(pre->tracer, "\n");
    }
    // Some equalities are solved, but then reasserted in the solver
    // these already have a model
    if (model_find_term_value(model, eq_var) != null_value) {
      continue;
    }
    // Some equalities are marked, but not solved. These we skip as they
    // are already set in the model
    if (preprocessor_get(pre, eq_var) == eq_var) {
      continue;
    }
    term_kind_t eq_kind = term_kind(pre->terms, eq);
    composite_term_t* eq_desc = get_composite(pre->terms, eq_kind, eq);
    if (eq_desc->arity > 1) {
      term_t eq_subst = eq_desc->arg[0] == eq_var ? eq_desc->arg[1] : eq_desc->arg[0];
      model_add_substitution(model, eq_var, eq_subst);
    } else {
      model_add_substitution(model, eq_var, zero_term);
    }
  }
}


static inline
void preprocessor_gc_mark_term(preprocessor_t* pre, term_t t) {
  term_table_set_gc_mark(pre->terms, index_of(t));
  type_table_set_gc_mark(pre->terms->types, term_type(pre->terms, t));
}

void preprocessor_gc_mark(preprocessor_t* pre) {
  uint32_t i;

  for (i = 0; i < pre->preprocess_map_list.size; ++ i) {
    term_t t = pre->preprocess_map_list.data[i];
    preprocessor_gc_mark_term(pre, t);
    term_t t_pre = preprocessor_get(pre, t);
    preprocessor_gc_mark_term(pre, t_pre);
  }

  for (i = 0; i < pre->equalities_list.size; ++ i) {
    term_t t = pre->equalities_list.data[i];
    preprocessor_gc_mark_term(pre, t);
  }

  for (i = 0; i < pre->purification_map_list.size; ++ i) {
    term_t t = pre->purification_map_list.data[i];
    preprocessor_gc_mark_term(pre, t);
    term_t t_pure = int_hmap_find(&pre->purification_map, t)->val;
    preprocessor_gc_mark_term(pre, t_pure);
  }
}

