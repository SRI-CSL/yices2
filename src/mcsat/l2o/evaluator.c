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

#include "mcsat/l2o/l2o.h"
#include "mcsat/l2o/l2o_internal.h"
#include "utils/double_hash_map.h"
#include "utils/int_array_sort.h"

#include <math.h>

static inline
bool evaluator_has_cache(const l2o_evaluator_t *evaluator) {
  return evaluator->eval_cache.nelems != 0;
}

static inline
bool evaluator_is_cached(const l2o_evaluator_t *evaluator, term_t t) {
  assert(is_pos_term(t));
  if (!evaluator_has_cache(evaluator)) {
    return false;
  }
  if (double_hmap_find(&evaluator->eval_cache, t) == NULL) {
    return false;
  }
  return !l2o_term_has_variables(evaluator->l2o, t, &evaluator->modified_vars);
}

static inline
double evaluator_get_cache(const l2o_evaluator_t *evaluator, term_t t) {
  assert(is_pos_term(t));
  assert(evaluator_is_cached(evaluator, t));
  double_hmap_pair_t *find = double_hmap_find(&evaluator->eval_cache, t);
  assert(find != NULL);
  return find->val;
}

static inline
double evaluator_get_if_cached(const l2o_evaluator_t *evaluator, term_t t) {
  assert(is_pos_term(t));
  double_hmap_pair_t *find = double_hmap_find(&evaluator->eval_cache, t);
  return find ? find->val : INFINITY;

}

/** Check whether t has been already evaluated */
static inline
bool already_evaluated(const l2o_evaluator_t *evaluator, term_t t) {
  t = unsigned_term(t);
  double_hmap_pair_t *find = double_hmap_find(&evaluator->eval_map, t);
  return find != NULL;
}

/** Get evaluated value of t IF already evaluated. Always to use in combination with already_evaluated */
static inline
double evaluator_get(const l2o_evaluator_t *evaluator, term_t t) {
  assert(is_pos_term(t));
  double_hmap_pair_t *find = double_hmap_find(&evaluator->eval_map, t);
  assert(find != NULL);
  return find->val;
}

static inline
double evaluator_get_if_eval(const l2o_evaluator_t *evaluator, term_t t) {
  assert(is_pos_term(t));
  double_hmap_pair_t *find = double_hmap_find(&evaluator->eval_map, t);
  return find ? find->val : INFINITY;
}

/** Set t_eval as the evaluated value of t */
static inline
void evaluator_set(l2o_evaluator_t *evaluator, term_t t, double t_eval) {
  assert(is_pos_term(t));
  assert(!already_evaluated(evaluator, t) || evaluator_get(evaluator, t) == t_eval);
  double_hmap_pair_t *p = double_hmap_get(&evaluator->eval_map, t);
  p->val = t_eval;
}

/** Results are kept in the order of state. */
static
bool cache_find_changed_variables(const double_hmap_t *eval_cache, const l2o_search_state_t *state, ivector_t *diff) {
  for (int i = 0; i < state->n_var; ++i) {
    term_t t = state->var[i];
    double_hmap_pair_t *p = double_hmap_find(eval_cache, t);
    if (p == NULL) {
      return false;
    } else if (p->val != state->val[i]) {
      ivector_push(diff, t);
    }
  }
  return true;
}

#ifndef NDEBUG
static
bool ensure_cache_values(const l2o_search_state_t *state, const l2o_evaluator_t *evaluator) {
  assert(!l2o_search_state_is_empty(state));
  for (int i = 0; i < state->n_var; ++i) {
    double_hmap_pair_t *p = double_hmap_find(&evaluator->eval_map, state->var[i]);
    if (!p || p->val != state->val[i]) return false;
  }
  return true;
}
#endif

void l2o_evaluator_construct(l2o_t *l2o, l2o_evaluator_t *evaluator) {
  evaluator->l2o = l2o;
  init_double_hmap(&evaluator->eval_map, 0);
  init_double_hmap(&evaluator->eval_cache, 0);
  init_ivector(&evaluator->modified_vars, 0);
}

void l2o_evaluator_destruct(l2o_evaluator_t *evaluator) {
  delete_double_hmap(&evaluator->eval_map);
  delete_double_hmap(&evaluator->eval_cache);
  delete_ivector(&evaluator->modified_vars);
}

void l2o_evaluator_reset(l2o_evaluator_t *evaluator) {
  double_hmap_reset(&evaluator->eval_map);
  double_hmap_reset(&evaluator->eval_cache);
  ivector_reset(&evaluator->modified_vars);
}

void l2o_evaluator_update_cache(l2o_evaluator_t *evaluator) {
  assert(evaluator->eval_map.nelems > 0);
  double_hmap_swap(&evaluator->eval_map, &evaluator->eval_cache);
}

void l2o_evaluator_set_state(l2o_evaluator_t *evaluator, const l2o_search_state_t *state) {
  // reset the evaluation
  double_hmap_reset(&evaluator->eval_map);
  ivector_reset(&evaluator->modified_vars);

  if (evaluator_has_cache(evaluator)) {
    bool diffed = cache_find_changed_variables(&evaluator->eval_cache, state, &evaluator->modified_vars);
    (void) diffed; assert(diffed);
    int_array_sort(evaluator->modified_vars.data, evaluator->modified_vars.size);
  }

  // Each var v[i] is evaluated to its assigned value x[i]
  for (uint32_t i = 0; i < state->n_var; ++i) {
    evaluator_set(evaluator, state->var[i], state->val[i]);
  }

  assert(ensure_cache_values(state, evaluator));
}

static
double evaluator_get_fix_pol(const l2o_evaluator_t *evaluator, term_t term) {
  assert(is_pos_term(term) || term_type_kind(evaluator->l2o->terms, term) == BOOL_TYPE);
  double result = evaluator_get(evaluator, unsigned_term(term));
  if (is_neg_term(term)) {
    // it's boolean
    assert(result == 1.0 || result == 0.0);
    return !result;
  } else {
    return result;
  }
}

static
void evaluator_set_fix_pol(l2o_evaluator_t *evaluator, term_t term, double t_eval) {
  bool is_bool = term_type_kind(evaluator->l2o->terms, term) == BOOL_TYPE;
  (void) is_bool;
  assert(!is_bool || t_eval == 1.0 || t_eval == 0.0);
  if (is_neg_term(term)) {
    assert(is_bool);
    evaluator_set(evaluator, unsigned_term(term), !t_eval);
  } else {
    evaluator_set(evaluator, term, t_eval);
  }
}

double l2o_evaluator_get_value(const l2o_evaluator_t *evaluator, term_t term) {
  assert(already_evaluated(evaluator, term));
  return evaluator_get_fix_pol(evaluator, term);
}

double l2o_evaluator_get_value_if_exists(const l2o_evaluator_t *evaluator, term_t term) {
  if (!already_evaluated(evaluator, term)) return INFINITY;
  return evaluator_get_fix_pol(evaluator, term);
}

double l2o_evaluator_run_term(l2o_evaluator_t *evaluator, term_t term) {
  l2o_t *l2o = evaluator->l2o;
  term_table_t *terms = l2o->terms;

  if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
    printf("\nl2o_evaluate_term_approx\n");
  }

  assert(l2o_is_valid_term(evaluator->l2o, term));

  uint32_t n;
  term_t *args;

  // Start
  ivector_t eval_stack;
  init_ivector(&eval_stack, 0);
  ivector_push(&eval_stack, term);

  while (eval_stack.size > 0) {
    // Current term
    term_t current = ivector_last(&eval_stack);
    type_kind_t current_type = term_type_kind(terms, current);
    term_kind_t current_kind = term_kind(terms, current);
    double current_eval = INFINITY;
    if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
      mcsat_trace_printf(l2o->tracer, "\n\n *  current = ");
      trace_term_ln(l2o->tracer, terms, current);
      printf(" --current id: %d", current);
      printf(" --current type: %d", current_type);
      printf(" --current kind: %d", current_kind);
    }

    // If evaluation already done, continue
    if (already_evaluated(evaluator, current)) {
      ivector_pop(&eval_stack);
      continue;
    }

    if (evaluator_is_cached(evaluator, unsigned_term(current))) {
      ivector_pop(&eval_stack);
      evaluator_set(evaluator, unsigned_term(current), evaluator_get_cache(evaluator, unsigned_term(current)));
      continue;
    }

#ifndef NDEBUG
    if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
      switch (current_type) {
        case BOOL_TYPE:
          printf("\nType is BOOL\n");
          break;
        case INT_TYPE:
          printf("\nType is INT\n");
          break;
        case REAL_TYPE:
          printf("\nType is REAL\n");
          break;
        case UNINTERPRETED_TYPE:
          printf("\nType is UNINTERPRETED\n");
          break;
        case SCALAR_TYPE:
          printf("\nType is SCALAR");
          break;
        default:
          break;
      }
    }
#endif

    switch (current_kind) {
      case CONSTANT_TERM:    // constant of uninterpreted/scalar/boolean types
      {
        if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
          printf("\ncurrent kind is CONSTANT_TERM");
        }
        current_eval = 0;
        break;
      }
      case ARITH_CONSTANT:   // rational constant
      {
        if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
          printf("\ncurrent kind is ARITH_CONSTANT");
        }
        rational_t *desc_rat = rational_term_desc(terms, current);
        // TODO Q how to deal division by zero?
        current_eval = q_get_double(desc_rat);
        break;
      }
      case UNINTERPRETED_TERM:  // (i.e., global variables, can't be bound).
      {
        if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
          printf("\ncurrent kind is UNINTERPRETED_TERM");
        }
        // Otherwise, should already have the value stored
        assert(current_type == BOOL_TYPE && is_neg_term(current));
        term_t current_positive_polarity = opposite_term(current);
        assert(already_evaluated(evaluator, current_positive_polarity));
        double current_pos_eval = evaluator_get(evaluator, current_positive_polarity);
        assert(current_pos_eval == 0.0 || current_pos_eval == 1.0); // arg_i_eval is either FALSE or TRUE
        current_eval = (current_pos_eval == 1.0) ? 0.0 : 1.0;
        break;
      }
      case OR_TERM:
      {
        if (is_pos_term(current)) {
          if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
            printf("\ncurrent kind is OR_TERM (positive polarity)\n");
          }
          composite_term_t *desc = get_composite(terms, current_kind, current);
          n = desc->arity;
          if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
            printf("\n n: %d\n", n);
          }
          args = desc->arg;
          bool args_already_evaluated = true;
          bool one_arg_is_true = false;
          for (uint32_t i = 0; i < n; ++i) {
            term_t arg_i = args[i];
            bool arg_i_already_evaluated = already_evaluated(evaluator, arg_i);
            if (!arg_i_already_evaluated) {
              args_already_evaluated = false;
            } else {
              double arg_i_eval = evaluator_get_fix_pol(evaluator, arg_i);
              assert(arg_i_eval == 0.0 || arg_i_eval == 1.0); // arg_i_eval is either FALSE or TRUE
              if (arg_i_eval == 1.0) {   // arg_i is TRUE
                one_arg_is_true = true;
                break;
              }
            }
          }

          if (one_arg_is_true) {
            current_eval = true;
            break;
          } else {
            if (args_already_evaluated) {
              current_eval = false;
              break;
            } else {
              for (uint32_t i = 0; i < n; ++i) {    // Now we add the non evaluated args to the stack
                term_t arg_i = args[i];
                bool arg_i_already_evaluated = already_evaluated(evaluator, arg_i);
                if (!arg_i_already_evaluated) {
                  ivector_push(&eval_stack, arg_i);
                }
              }
              continue;
            }
          }
        } else { // !is_pos_term(current)
          if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
            printf("\ncurrent kind is AND_TERM (i.e. OR with negative polarity)\n");
          }
          term_t current_unsigned = unsigned_term(current);
          composite_term_t *desc = get_composite(terms, current_kind, current_unsigned);
          n = desc->arity;
          if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
            printf("\n n: %d\n", n);
          }
          args = desc->arg;

          bool args_already_evaluated = true;
          bool one_arg_is_false = false;

          for (uint32_t i = 0; i < n; ++i) {
            term_t arg_i = args[i];
            term_t arg_i_neg = opposite_term(arg_i);

            bool arg_i_neg_already_evaluated = already_evaluated(evaluator, arg_i_neg);
            if (!arg_i_neg_already_evaluated) {
              //ivector_push(eval_stack, arg_i);    // We don't add yet the unevaluated args to the stack: maybe some other arg is false, so there would be no need to evaluate the other args.
              args_already_evaluated = false;
            } else {
              double arg_i_neg_eval = evaluator_get_fix_pol(evaluator, arg_i_neg);
              assert(arg_i_neg_eval == 0.0 || arg_i_neg_eval == 1.0); // arg_i_neg_eval is either FALSE or TRUE
              if (arg_i_neg_eval == 0.0) {   // arg_i is FALSE
                one_arg_is_false = true;
                break;
              }
            }
          }

          if (one_arg_is_false) {
            current_eval = false;
            break;
          } else {
            if (args_already_evaluated) {
              current_eval = true;
              break;
            } else {
              for (uint32_t i = 0; i < n; ++i) {    // Now we add the non evaluated args to the stack
                term_t arg_i = args[i];
                term_t arg_i_neg = opposite_term(arg_i);
                bool arg_i_neg_already_evaluated = already_evaluated(evaluator, arg_i_neg);
                if (!arg_i_neg_already_evaluated) {
                  ivector_push(&eval_stack, arg_i_neg);
                }
              }
              continue;
            }
          }
        }
      }

      case ITE_SPECIAL:
      case ITE_TERM:
      {
        if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
          printf("\ncurrent kind is ITE_TERM or ITE_SPECIAL\n");
        }
        if (is_pos_term(current)) {
          composite_term_t *desc = get_composite(terms, current_kind, current);
          n = desc->arity;
          assert(n == 3);
          args = desc->arg;
          term_t cond = args[0];
          term_t t1 = args[1];
          term_t t2 = args[2];

          bool cond_already_evaluated = already_evaluated(evaluator, cond);

          if (cond_already_evaluated) {
            double cond_eval = evaluator_get_fix_pol(evaluator, cond);
            assert(cond_eval == 0.0 || cond_eval == 1.0); // cond_eval is either FALSE or TRUE
            if (cond_eval == 1.0) {  // cond is TRUE
              bool t1_already_evaluated = already_evaluated(evaluator, t1);
              if (t1_already_evaluated) {
                current_eval = evaluator_get_fix_pol(evaluator, t1);
              } else {
                ivector_push(&eval_stack, t1);
                continue;
              }
            } else {   // cond is FALSE
              bool t2_already_evaluated = already_evaluated(evaluator, t2);
              if (t2_already_evaluated) {
                current_eval = evaluator_get_fix_pol(evaluator, t2);
              } else {
                ivector_push(&eval_stack, t2);
                continue;
              }
            }
            break;
          } else {
            ivector_push(&eval_stack, cond);
            continue;
          }
        } else { // !is_pos_term(current)
          term_t current_unsigned = unsigned_term(current);
          composite_term_t *desc = get_composite(terms, current_kind, current_unsigned);
          assert(desc->arity == 3);
          args = desc->arg;
          term_t cond = args[0];
          term_t t1 = args[1];
          term_t t2 = args[2];
          term_t t1neg = opposite_term(t1);
          term_t t2neg = opposite_term(t2);

          bool cond_already_evaluated = already_evaluated(evaluator, cond);

          if (cond_already_evaluated) {
            double cond_eval = evaluator_get_fix_pol(evaluator, cond);
            assert(cond_eval == 0 || cond_eval == 1); // cond_eval is either FALSE or TRUE
            if (cond_eval == 1) {  // cond is TRUE
              bool t1neg_already_evaluated = already_evaluated(evaluator, t1neg);
              if (t1neg_already_evaluated) {
                current_eval = evaluator_get_fix_pol(evaluator, t1neg);
              } else {
                ivector_push(&eval_stack, t1neg);
                continue;
              }
            } else {   // cond is FALSE
              bool t2neg_already_evaluated = already_evaluated(evaluator, t2neg);
              if (t2neg_already_evaluated) {
                current_eval = evaluator_get_fix_pol(evaluator, t2neg);
              } else {
                ivector_push(&eval_stack, t2neg);
                continue;
              }
            }
            break;
          } else {
            ivector_push(&eval_stack, cond);
            continue;
          }
        }
      }

      case ARITH_EQ_ATOM:      // equality (t == 0)
      {
        if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
          printf("\ncurrent kind is ARITH_EQ_ATOM\n");
        }
        term_t current_unsigned = unsigned_term(current);
        composite_term_t *desc = get_composite(terms, current_kind, current_unsigned);
        assert(desc->arity == 1);
        args = desc->arg;
        term_t t = args[0];

        bool t_already_evaluated = already_evaluated(evaluator, t);

        if (t_already_evaluated) {
          double t_eval = evaluator_get_fix_pol(evaluator, t);
          if (is_pos_term(current)) {   // t == 0
            if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
              printf("\n is positive (t == 0)\n");
            }
            current_eval = t_eval == 0.0;
          } else {                        // t != 0
            current_eval = t_eval != 0.0;
          }
          break;
        } else {
          ivector_push(&eval_stack, t);
          continue;
        }
      }

      case EQ_TERM:      // eq_term
      {
        if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
          printf("\ncurrent kind is EQ_TERM\n");
        }
        term_t current_unsigned = unsigned_term(current);
        composite_term_t *desc = get_composite(terms, current_kind, current_unsigned);
        args = desc->arg;
        assert(desc->arity == 2);

        double args_eval[2];
        bool args_already_evaluated = true;

        for (uint32_t i = 0; i < 2; ++i) {
          term_t arg_i = args[i];
          bool arg_i_already_evaluated = already_evaluated(evaluator, arg_i);
          if (!arg_i_already_evaluated) {
            ivector_push(&eval_stack, arg_i);
            args_already_evaluated = false;
          } else {
            args_eval[i] = evaluator_get_fix_pol(evaluator, arg_i);
          }
        }

        if (!args_already_evaluated) {
          continue;
        } else {
          if (is_pos_term(current)) {   // t1 == t2
            if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
              printf("\n is positive (t1==t2)\n");
            }
            current_eval = args_eval[0] == args_eval[1];
          } else {                        // t1 != t2
            if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
              printf("\n is negative (t1!=t2)\n");
            }
            current_eval = args_eval[0] != args_eval[1];
          }
          break;
        }
      }

      case ARITH_BINEQ_ATOM:      // equality: (t1 == t2)  (between two arithmetic terms)
      {
        if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
          printf("\ncurrent kind is ARITH_BINEQ_ATOM\n");
        }
        term_t current_unsigned = unsigned_term(current);
        composite_term_t *desc = get_composite(terms, current_kind, current_unsigned);
        args = desc->arg;
        assert(desc->arity == 2);

        double args_eval[2];
        bool args_already_evaluated = true;

        for (uint32_t i = 0; i < 2; ++i) {
          term_t arg_i = args[i];
          bool arg_i_already_evaluated = already_evaluated(evaluator, arg_i);
          if (!arg_i_already_evaluated) {
            ivector_push(&eval_stack, arg_i);
            args_already_evaluated = false;
          } else {
            args_eval[i] = evaluator_get_fix_pol(evaluator, arg_i);
          }
        }

        if (!args_already_evaluated) {
          continue;
        } else {
          if (is_pos_term(current)) {   // t1 == t2
            if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
              printf("\n is positive (t1==t2)\n");
            }
            current_eval = args_eval[0] == args_eval[1];
          } else {                        // t1 != t2
            if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
              printf("\n is negative (t1!=t2)\n");
            }
            current_eval = args_eval[0] != args_eval[1];
          }
          break;
        }
      }

      case ARITH_GE_ATOM:      // atom t >= 0
      {
        if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
          printf("\ncurrent kind is ARITH_GE_ATOM\n");
        }
        term_t current_unsigned = unsigned_term(current);
        composite_term_t *desc = get_composite(terms, current_kind, current_unsigned);
        n = desc->arity;
        args = desc->arg;
        term_t t = args[0];

        bool t_already_evaluated = already_evaluated(evaluator, t);

        if (t_already_evaluated) {
          double t_eval = evaluator_get_fix_pol(evaluator, t);
          if (is_pos_term(current)) {   // t >= 0
            if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
              printf("\n is positive (t >= 0)\n");
            }
            current_eval = t_eval >= 0;
          } else {                        // t < 0
            if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
              printf("\n is negative (t < 0)\n");
            }
            current_eval = t_eval < 0;
          }
          break;
        } else {
          ivector_push(&eval_stack, t);
          continue;
        }
      }

      case ARITH_FLOOR: {
        if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
          printf("\ncurrent kind is ARITH_ABS\n");
        }
        term_t subt = arith_floor_arg(terms, current);
        bool subt_already_evaluated = already_evaluated(evaluator, subt);

        if (subt_already_evaluated) {
          double subt_eval = evaluator_get(evaluator, subt);
          if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
            mcsat_trace_printf(l2o->tracer, "\nsubt = ");
            trace_term_ln(l2o->tracer, terms, subt);
          }
          current_eval = floor(subt_eval);
          break;
        } else {
          ivector_push(&eval_stack, subt);
          continue;
        }
      }
      case ARITH_CEIL: {
        if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
          printf("\ncurrent kind is ARITH_CEIL\n");
        }
        term_t subt = arith_ceil_arg(terms, current);
        bool subt_already_evaluated = already_evaluated(evaluator, subt);

        if (subt_already_evaluated) {
          double subt_eval = evaluator_get(evaluator, subt);
          if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
            mcsat_trace_printf(l2o->tracer, "\nsubt = ");
            trace_term_ln(l2o->tracer, terms, subt);
          }
          current_eval = ceil(subt_eval);
          break;
        } else {
          ivector_push(&eval_stack, subt);
          continue;
        }
      }
      case ARITH_ABS: {
        if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
          printf("\ncurrent kind is ARITH_ABS\n");
        }
        term_t subt = arith_abs_arg(terms, current);
        bool subt_already_evaluated = already_evaluated(evaluator, subt);

        if (subt_already_evaluated) {
          double subt_eval = evaluator_get(evaluator, subt);
          if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
            mcsat_trace_printf(l2o->tracer, "\nsubt = ");
            trace_term_ln(l2o->tracer, terms, subt);
          }
          current_eval = fabs(subt_eval);
          break;
        } else {
          ivector_push(&eval_stack, subt);
          continue;
        }
      }
      case POWER_PRODUCT: {
        if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
          printf("\ncurrent kind is POWER_PRODUCT\n");
        }
        pprod_t *ppdesc = pprod_term_desc(terms, current);
        n = ppdesc->len;
        varexp_t *pow_t = ppdesc->prod;
        bool vars_already_evaluated = true;
        for (uint32_t i = 0; i < n; ++i) {
          term_t var = pow_t[i].var;
          if (!already_evaluated(evaluator, var)) {
            ivector_push(&eval_stack, var);
            vars_already_evaluated = false;
          }
        }
        if (!vars_already_evaluated) {
          continue;
        } else {
          current_eval = 1;
          for (uint32_t i = 0; i < n; ++i) {
            double var_eval = evaluator_get(evaluator, pow_t[i].var);
            double pow_eval = pow(var_eval, pow_t[i].exp);
            current_eval = current_eval * pow_eval;
          }
          break;
        }
      }
      case ARITH_POLY: {
        if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
          printf("\ncurrent kind is ARITH_POLY\n");
        }
        polynomial_t *polydesc = poly_term_desc(terms, current);
        n = polydesc->nterms;
        monomial_t *mono = polydesc->mono;
        bool vars_already_evaluated = true;
        for (uint32_t i = 0; i < n; ++i) {
          term_t var = mono[i].var;
          // If monomial has 0 degree then var is UNUSED_TERM (constant term)
          if (good_term(terms, var) && !already_evaluated(evaluator, var)) {
            ivector_push(&eval_stack, var);
            vars_already_evaluated = false;
          }
        }
        if (!vars_already_evaluated) {
          continue;
        } else {
          current_eval = 0;
          for (uint32_t i = 0; i < n; ++i) {
            term_t var = mono[i].var;
            double var_eval = good_term(terms, var) ? evaluator_get(evaluator, var) : 1.0;
            double coeff_eval = q_get_double(&mono[i].coeff);
            current_eval = current_eval + coeff_eval * var_eval;
          }
          break;
        }
      }
      case ARITH_RDIV:      // real division: (/ x y)
      {
        if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
          printf("\ncurrent kind is ARITH_IDIV\n");
        }
        term_t current_unsigned = unsigned_term(current);
        composite_term_t *desc = get_composite(terms, current_kind, current_unsigned);
        n = desc->arity;
        args = desc->arg;
        assert(n == 2);

        double args_eval[2];
        bool args_already_evaluated = true;

        for (uint32_t i = 0; i < 2; ++i) {
          term_t arg_i = args[i];
          bool arg_i_already_evaluated = already_evaluated(evaluator, arg_i);
          if (!arg_i_already_evaluated) {
            ivector_push(&eval_stack, arg_i);
            args_already_evaluated = false;
          } else {
            args_eval[i] = evaluator_get(evaluator, arg_i);
          }
        }

        if (!args_already_evaluated) {
          continue;
        } else {
          double num = args_eval[0];
          double den = args_eval[1];

          if (den == 0) {
            current_eval = 0;
          } else {
            current_eval = num / den;
          }
          break;
        }
      }
      case ARITH_IDIV:      // integer division: (div x y) as defined in SMT-LIB 2
      {
        if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
          printf("\ncurrent kind is ARITH_IDIV\n");
        }
        term_t current_unsigned = unsigned_term(current);
        composite_term_t *desc = get_composite(terms, current_kind, current_unsigned);
        n = desc->arity;
        args = desc->arg;
        assert(n == 2);

        double args_eval[2];
        bool args_already_evaluated = true;

        for (uint32_t i = 0; i < 2; ++i) {
          term_t arg_i = args[i];
          bool arg_i_already_evaluated = already_evaluated(evaluator, arg_i);
          if (!arg_i_already_evaluated) {
            ivector_push(&eval_stack, arg_i);
            args_already_evaluated = false;
          } else {
            args_eval[i] = evaluator_get(evaluator, arg_i);
          }
        }

        if (!args_already_evaluated) {
          continue;
        } else {
          double num = args_eval[0];
          double den = args_eval[1];

          // TODO Q avoid approximation error? E.g if 8 / 2 = 3.999 (that should not happen for int of reasonable size...)
          if (den == 0) {
            current_eval = 0;
          } else if (den > 0) {
            current_eval = floor(num / den);
          } else {
            current_eval = ceil(num / den);
          }
          break;
        }
      }
      case ARITH_MOD:     // remainder:  (mod x y) is x - y * (div x y)
      {
        if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
          printf("\ncurrent kind is ARITH_MOD\n");
        }
        term_t current_unsigned = unsigned_term(current);
        composite_term_t *desc = get_composite(terms, current_kind, current_unsigned);
        n = desc->arity;
        args = desc->arg;
        assert(n == 2);

        double args_eval[2];
        bool args_already_evaluated = true;

        for (uint32_t i = 0; i < 2; ++i) {
          term_t arg_i = args[i];
          bool arg_i_already_evaluated = already_evaluated(evaluator, arg_i);
          if (!arg_i_already_evaluated) {
            ivector_push(&eval_stack, arg_i);
            args_already_evaluated = false;
          } else {
            args_eval[i] = evaluator_get(evaluator, arg_i);
          }
        }

        if (!args_already_evaluated) {
          continue;
        } else {
          double num = args_eval[0];
          double den = args_eval[1];
          double div;

          if (den == 0) {
            div = 0;
          } else if (den > 0) {
            div = floor(num / den);
          } else {
            div = ceil(num / den);
          }

          current_eval = num - den * div;
          break;
        }
      }

      default:    // unsupported kind (XOR_TERM, DISTINCT_TERM, ...): such assertions
                  // are rejected before l2o_run by l2o_term_is_supported, so this is
                  // a defensive path. Free the stack before escaping to avoid a leak.
        if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
          printf("\ncurrent_kind: %d\n", current_kind);
          printf("\ncurrent kind is UNSUPPORTED\n");
        }

        delete_ivector(&eval_stack);
        longjmp(*l2o->exception, INTERNAL_EXCEPTION);
        break;
    }

    if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
      printf("\nsetting...");
      mcsat_trace_printf(l2o->tracer, "\n  current_eval = %f ", current_eval);
      mcsat_trace_printf(l2o->tracer, "\n  current_id = %d ", current);
    }
    ivector_pop(&eval_stack);
    evaluator_set_fix_pol(evaluator, current, current_eval);
  }

  // Get cost of t
  assert(already_evaluated(evaluator, term));
  // TODO or just allow unsigned terms
  double t_eval = evaluator_get_fix_pol(evaluator, term);

  if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
    printf("\nt_eval = %f", t_eval);
  }

  delete_ivector(&eval_stack);

  // Return the result
  return t_eval;
}
