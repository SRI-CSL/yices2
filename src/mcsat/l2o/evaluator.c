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

#include "mcsat/tracing.h"

#include "terms/term_explorer.h"
#include "terms/bvarith64_buffer_terms.h"
#include "terms/bvarith_buffer_terms.h"
#include "terms/free_var_collector.h"

#include "model/models.h"

#include "context/context_types.h"

#include "yices.h"
#include "api/yices_api_lock_free.h"
#include "api/yices_extensions.h"
#include "api/yices_globals.h"

#include "mcsat/l2o/l2o.h"
#include "mcsat/l2o/eval_vectors.h"
#include "mcsat/l2o/eval_hash_map.h"
#include "mcsat/l2o/varset_table.h"

#include <math.h>

#define EVAL_MAXFLOAT __DBL_MAX__;

void evaluator_cache_construct(eval_cache_t *cache) {
  cache->cost = EVAL_MAXFLOAT;
  cache->n_var = 0;
  cache->v = NULL;
  cache->x = NULL;
  init_eval_hmap(&cache->eval_map, 0);
}

void evaluator_cache_destruct(eval_cache_t *cache) {
  delete_eval_hmap(&cache->eval_map);
}

void evaluator_construct(evaluator_t *evaluator) {
  init_eval_hmap(&evaluator->eval_map, 0);
  init_ivector(&evaluator->eval_stack, 0);
  evaluator_cache_construct(&evaluator->cache);
  evaluator->tracer = NULL;
}

void evaluator_set_tracer(evaluator_t *evaluator, tracer_t *tracer) {
  evaluator->tracer = tracer;
}

void evaluator_destruct(evaluator_t *evaluator) {
  delete_eval_hmap(&evaluator->eval_map);
  delete_ivector(&evaluator->eval_stack);
  evaluator_cache_destruct(&evaluator->cache);
}

/** Check whether t has been already evaluated */
static inline
bool already_evaluated(evaluator_t *evaluator, term_t t) {
  eval_hmap_pair_t *find = eval_hmap_find(&evaluator->eval_map, t);
  return find != NULL;
}

/** Get evaluated value of t IF already evaluated. Always to use in combination with already_evaluated */
static inline
double evaluator_get(evaluator_t *evaluator, term_t t) {
  eval_hmap_pair_t *find = eval_hmap_find(&evaluator->eval_map, t);
  assert(find != NULL);
  return find->val;
}

/** Set t_eval as the evaluated value of t */
static inline
void evaluator_set(evaluator_t *evaluator, term_t t, double t_eval) {
  assert(!already_evaluated(evaluator, t));
  eval_hmap_add(&evaluator->eval_map, t, t_eval);
}

static inline
bool evaluator_has_cache(evaluator_t *evaluator) {
  return evaluator->cache.n_var != 0;
}

static
void get_set_of_vars_with_new_value(l2o_t *l2o, uint32_t n_var, const term_t *vars, const double *values, int_hset_t *vars_with_new_value) {
  term_t *cached_vars = l2o->evaluator.cache.v;
  double *cached_values = l2o->evaluator.cache.x;
  uint32_t n_cached_vars = l2o->evaluator.cache.n_var;
  if (n_cached_vars == 0) {
    return;
  } else {
    assert(n_cached_vars == n_var);
    for (uint32_t i = 0; i < n_var; ++i) {
      if (cached_vars[i] != vars[i]) {
        assert(false);
      }
      if (cached_values[i] != values[i]) {
        int_hset_add(vars_with_new_value, vars[i]);
      }
    }
    int_hset_close_and_sort(vars_with_new_value);
    add_varset(&l2o->varset_table, vars_with_new_value);
    if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
      printf("\nvars_with_new_value:");
      for (uint32_t i = 0; i < vars_with_new_value->nelems; ++i) {
        printf("\n\t %d", vars_with_new_value->data[i]);
      }
    }
  }
}

static
bool is_var_member_of_varset(l2o_t *l2o, term_t var, const int_hset_t *varset, int32_t varset_index) {
  //TODO change name &l2o->varset_members_cache
  pmap2_rec_t *rec = pmap2_get(&l2o->varset_members_cache, var, varset_index);
  if (rec->val == -1) {    // not cached yet
    bool var_is_member = false;
    for (uint32_t j = 0; j < varset->nelems; ++j) {
      if (var == varset->data[j]) {
        var_is_member = true;
        break;
      }
    }
    rec->val = var_is_member;
  } else {
    assert(rec->val == true || rec->val == false);
  }
  return rec->val;
}


// Checks whether the intersection between set_of_vars and the free variables in t is empty (0) or not (1)
static
bool varset_intersects_free_vars_of_term(l2o_t *l2o, int_hset_t *set_of_vars, term_t t) {
  int32_t index_vars_in_t = get_freevars_index(l2o, t);
  assert(index_vars_in_t != -1);
  const int_hset_t *vars_in_t = get_freevars_from_index(l2o, index_vars_in_t);

  bool intersection_is_empty = true;

  uint32_t n_vars = set_of_vars->nelems;
  for (uint32_t i = 0; i < n_vars; ++i) {
    bool var_is_member = is_var_member_of_varset(l2o, set_of_vars->data[i], vars_in_t, index_vars_in_t);
    if (var_is_member) {
      intersection_is_empty = false;
      break;
    }
  }
  return !intersection_is_empty;
}

bool can_use_cached_value(l2o_t *l2o, int_hset_t *vars_with_new_val, term_t t) {
  if (!evaluator_has_cache(&l2o->evaluator)) {
    return false;
  }
  if (eval_hmap_find(&l2o->evaluator.cache.eval_map, t) == NULL) {
    return false;
  }
  return !varset_intersects_free_vars_of_term(l2o, vars_with_new_val, t);
}

void evaluator_forget_cache_cost(evaluator_t *evaluator) {
  evaluator->cache.cost = EVAL_MAXFLOAT;
}

double l2o_evaluate_term_approx(l2o_t *l2o, term_t term, uint32_t n_var, const term_t *v, const double *x) {
  if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
    printf("\nl2o_evaluate_term_approx\n");
  }

  term_table_t *terms = l2o->terms;

  uint32_t i, n;
  term_t *args;


  // Start
  ivector_t *eval_stack = &l2o->evaluator.eval_stack;
  ivector_reset(eval_stack);
  ivector_push(eval_stack, term);

  bool cached = evaluator_has_cache(&l2o->evaluator);

  // Set of variables whose values have changed w.r.t. cache assignment. 
  int_hset_t vars_with_new_val;
  init_int_hset(&vars_with_new_val, 0);
  if (cached) {
    get_set_of_vars_with_new_value(l2o, n_var, v, x, &vars_with_new_val);
  }

  // Each var v[i] is evaluated to its assigned value x[i]
  for (i = 0; i < n_var; ++i) {
    evaluator_set(&l2o->evaluator, v[i], x[i]);
  }


  while (eval_stack->size > 0) {
    // Current term
    term_t current = ivector_last(eval_stack);
    type_kind_t current_type = term_type_kind(terms, current);
    term_kind_t current_kind = term_kind(terms, current);
    double current_eval = EVAL_MAXFLOAT;
    if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
      mcsat_trace_printf(l2o->tracer, "\n\n *  current = ");
      trace_term_ln(l2o->tracer, terms, current);
      printf(" --current id: %d", current);
      printf(" --current type: %d", current_type);
      printf(" --current kind: %d", current_kind);
    }

    // If evaluation already done, continue
    bool current_already_evaluated = already_evaluated(&l2o->evaluator, current);
    if (current_already_evaluated) {
      ivector_pop(eval_stack);
      continue;
    }

    // Check whether we can use cached value, i.e. if the values of the variables in current have not changed
    bool use_cached_value = can_use_cached_value(l2o, &vars_with_new_val, current);
    if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
      printf("\nuse_cached_value: %d", use_cached_value);
    }

    if (use_cached_value) {
      current_eval = eval_hmap_find(&l2o->evaluator.cache.eval_map, current)->val;
      if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
        printf("\nusing cached value: %f", current_eval);
      }
    } else {
      switch (current_type) {
        case BOOL_TYPE:
          if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
            printf("\nType is BOOL\n");
          }
          break;
        case INT_TYPE:
          if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
            printf("\nType is INT\n");
          }
          break;
        case REAL_TYPE:
          if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
            printf("\nType is REAL\n");
          }
          break;
        case UNINTERPRETED_TYPE:
          if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
            printf("\nType is UNINTERPRETED\n");
          }
          //l2o_var_set(l2o, current, current);
          break;
        case SCALAR_TYPE:
          if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
            printf("\nType is SCALAR");
          }
          break;
        default:
          longjmp(*l2o->exception, MCSAT_EXCEPTION_UNSUPPORTED_THEORY);
      }

      switch (current_kind) {
        case CONSTANT_TERM:    // constant of uninterpreted/scalar/boolean types
        {
          if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
            printf("\ncurrent kind is CONSTANT_TERM");
          }
          current_eval = 0;
          break;
          //longjmp(*l2o->exception, MCSAT_EXCEPTION_UNSUPPORTED_THEORY);
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
          if (current_type == BOOL_TYPE && is_neg_term(current)) {
            term_t current_positive_polarity = opposite_term(current);
            assert(already_evaluated(&l2o->evaluator, current_positive_polarity));
            double current_pos_eval = evaluator_get(&l2o->evaluator, current_positive_polarity);
            current_eval = (current_pos_eval == true) ? false : true;
            break;
          } else {
            assert(false);  // Should already have the value stored
          }
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
            for (i = 0; i < n; ++i) {
              term_t arg_i = args[i];
              bool arg_i_already_evaluated = already_evaluated(&l2o->evaluator, arg_i);
              if (!arg_i_already_evaluated) {
                //ivector_push(eval_stack, arg_i);    // We don't add yet the unevaluated args to the stack: maybe some other arg is true, so there would be no need to evaluate the other args.
                args_already_evaluated = false;
              } else {
                double arg_i_eval = evaluator_get(&l2o->evaluator, arg_i);
                assert(arg_i_eval == 0 || arg_i_eval == 1); // arg_i_eval is either FALSE or TRUE
                if (arg_i_eval == 1) {   // arg_i is TRUE
                  one_arg_is_true = true;
                  break;
                }
              }
            };

            if (one_arg_is_true) {
              current_eval = true;
              break;
            } else {
              if (args_already_evaluated) {
                current_eval = false;
                break;
              } else {
                for (i = 0; i < n; ++i) {    // Now we add the non evaluated args to the stack
                  term_t arg_i = args[i];
                  bool arg_i_already_evaluated = already_evaluated(&l2o->evaluator, arg_i);
                  if (!arg_i_already_evaluated) {
                    ivector_push(eval_stack, arg_i);
                  }
                };
                continue;
              }
            }

          } else {
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

            for (i = 0; i < n; ++i) {
              term_t arg_i = args[i];
              term_t arg_i_neg = yices_not(arg_i);

              bool arg_i_neg_already_evaluated = already_evaluated(&l2o->evaluator, arg_i_neg);
              if (!arg_i_neg_already_evaluated) {
                //ivector_push(eval_stack, arg_i);    // We don't add yet the unevaluated args to the stack: maybe some other arg is false, so there would be no need to evaluate the other args.
                args_already_evaluated = false;
              } else {
                double arg_i_neg_eval = evaluator_get(&l2o->evaluator, arg_i_neg);
                assert(arg_i_neg_eval == 0 || arg_i_neg_eval == 1); // arg_i_neg_eval is either FALSE or TRUE
                if (arg_i_neg_eval == 0) {   // arg_i is FALSE
                  one_arg_is_false = true;
                  break;
                }
              }
            };

            if (one_arg_is_false) {
              current_eval = false;
              break;
            } else {
              if (args_already_evaluated) {
                current_eval = true;
                break;
              } else {
                for (i = 0; i < n; ++i) {    // Now we add the non evaluated args to the stack
                  term_t arg_i = args[i];
                  term_t arg_i_neg = yices_not(arg_i);
                  bool arg_i_neg_already_evaluated = already_evaluated(&l2o->evaluator, arg_i_neg);
                  if (!arg_i_neg_already_evaluated) {
                    ivector_push(eval_stack, arg_i_neg);
                  }
                };
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

            bool cond_already_evaluated = already_evaluated(&l2o->evaluator, cond);

            if (cond_already_evaluated) {
              double cond_eval = evaluator_get(&l2o->evaluator, cond);
              assert(cond_eval == 0 || cond_eval == 1); // cond_eval is either FALSE or TRUE
              if (cond_eval == 1) {  // cond is TRUE
                bool t1_already_evaluated = already_evaluated(&l2o->evaluator, t1);
                if (t1_already_evaluated) {
                  current_eval = evaluator_get(&l2o->evaluator, t1);
                } else {
                  ivector_push(eval_stack, t1);
                  continue;
                }
              } else {   // cond is FALSE
                bool t2_already_evaluated = already_evaluated(&l2o->evaluator, t2);
                if (t2_already_evaluated) {
                  current_eval = evaluator_get(&l2o->evaluator, t2);
                } else {
                  ivector_push(eval_stack, t2);
                  continue;
                }
              }
              break;
            } else {
              ivector_push(eval_stack, cond);
              continue;
            }
          } else {
            term_t current_unsigned = unsigned_term(current);
            composite_term_t *desc = get_composite(terms, current_kind, current_unsigned);
            assert(desc->arity == 3);
            args = desc->arg;
            term_t cond = args[0];
            term_t t1 = args[1];
            term_t t2 = args[2];
            term_t t1neg = yices_not(t1);
            term_t t2neg = yices_not(t2);

            bool cond_already_evaluated = already_evaluated(&l2o->evaluator, cond);

            if (cond_already_evaluated) {
              double cond_eval = evaluator_get(&l2o->evaluator, cond);
              assert(cond_eval == 0 || cond_eval == 1); // cond_eval is either FALSE or TRUE
              if (cond_eval == 1) {  // cond is TRUE
                bool t1neg_already_evaluated = already_evaluated(&l2o->evaluator, t1neg);
                if (t1neg_already_evaluated) {
                  current_eval = evaluator_get(&l2o->evaluator, t1neg);
                } else {
                  ivector_push(eval_stack, t1neg);
                  continue;
                }
              } else {   // cond is FALSE
                bool t2neg_already_evaluated = already_evaluated(&l2o->evaluator, t2neg);
                if (t2neg_already_evaluated) {
                  current_eval = evaluator_get(&l2o->evaluator, t2neg);
                } else {
                  ivector_push(eval_stack, t2neg);
                  continue;
                }
              }
              break;
            } else {
              ivector_push(eval_stack, cond);
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
          n = desc->arity;
          args = desc->arg;
          term_t t = args[0];

          bool t_already_evaluated = already_evaluated(&l2o->evaluator, t);

          if (t_already_evaluated) {
            double t_eval = evaluator_get(&l2o->evaluator, t);
            if (is_pos_term(current)) {   // t == 0
              if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
                printf("\n is positive (t == 0)\n");
              }
              current_eval = t_eval == 0;
            } else {                        // t != 0
              current_eval = t_eval != 0;
            }
            break;
          } else {
            ivector_push(eval_stack, t);
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
          assert(desc->arity == 2); // TODO what if arity > 2?

          double args_eval[2];
          bool args_already_evaluated = true;

          for (i = 0; i < 2; ++i) {
            term_t arg_i = args[i];
            bool arg_i_already_evaluated = already_evaluated(&l2o->evaluator, arg_i);
            if (!arg_i_already_evaluated) {
              ivector_push(eval_stack, arg_i);
              args_already_evaluated = false;
            } else {
              args_eval[i] = evaluator_get(&l2o->evaluator, arg_i);
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

          for (i = 0; i < 2; ++i) {
            term_t arg_i = args[i];
            bool arg_i_already_evaluated = already_evaluated(&l2o->evaluator, arg_i);
            if (!arg_i_already_evaluated) {
              ivector_push(eval_stack, arg_i);
              args_already_evaluated = false;
            } else {
              args_eval[i] = evaluator_get(&l2o->evaluator, arg_i);
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

          bool t_already_evaluated = already_evaluated(&l2o->evaluator, t);

          if (t_already_evaluated) {
            double t_eval = evaluator_get(&l2o->evaluator, t);
            if (is_pos_term(current)) {   // t == 0
              if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
                printf("\n is positive (t >= 0)\n");
              }
              current_eval = t_eval >= 0;
            } else {                        // t != 0
              if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
                printf("\n is negative (t < 0)\n");
              }
              current_eval = t_eval < 0;
            }
            break;
          } else {
            ivector_push(eval_stack, t);
            continue;
          }
        }

        case ARITH_FLOOR: {
          if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
            printf("\ncurrent kind is ARITH_ABS\n");
          }
          term_t subt = arith_floor_arg(terms, current);
          bool subt_already_evaluated = already_evaluated(&l2o->evaluator, subt);

          if (subt_already_evaluated) {
            double subt_eval = evaluator_get(&l2o->evaluator, subt);
            if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
              mcsat_trace_printf(l2o->tracer, "\nsubt = ");
              trace_term_ln(l2o->tracer, terms, subt);
            }
            current_eval = floor(subt_eval);
            break;
          } else {
            ivector_push(eval_stack, subt);
            continue;
          }
        }
        case ARITH_CEIL: {
          if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
            printf("\ncurrent kind is ARITH_CEIL\n");
          }
          term_t subt = arith_ceil_arg(terms, current);
          bool subt_already_evaluated = already_evaluated(&l2o->evaluator, subt);

          if (subt_already_evaluated) {
            double subt_eval = evaluator_get(&l2o->evaluator, subt);
            if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
              mcsat_trace_printf(l2o->tracer, "\nsubt = ");
              trace_term_ln(l2o->tracer, terms, subt);
            }
            current_eval = ceil(subt_eval);
            break;
          } else {
            ivector_push(eval_stack, subt);
            continue;
          }
        }
        case ARITH_ABS: {
          if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
            printf("\ncurrent kind is ARITH_ABS\n");
          }
          term_t subt = arith_abs_arg(terms, current);
          bool subt_already_evaluated = already_evaluated(&l2o->evaluator, subt);

          if (subt_already_evaluated) {
            double subt_eval = evaluator_get(&l2o->evaluator, subt);
            if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
              mcsat_trace_printf(l2o->tracer, "\nsubt = ");
              trace_term_ln(l2o->tracer, terms, subt);
            }
            current_eval = fabs(subt_eval);
            break;
          } else {
            ivector_push(eval_stack, subt);
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
          double vars_eval[n];
          bool vars_already_evaluated = true;
          for (i = 0; i < n; ++i) {
            varexp_t pow_i = pow_t[i];
            term_t var = pow_i.var;
            bool var_already_evaluated = already_evaluated(&l2o->evaluator, var);
            if (!var_already_evaluated) {
              ivector_push(eval_stack, var);
              vars_already_evaluated = false;
            } else {
              double var_eval = evaluator_get(&l2o->evaluator, var);
              vars_eval[i] = var_eval;
            }
          }
          if (!vars_already_evaluated) {
            continue;
          } else {
            current_eval = 1;
            for (i = 0; i < n; ++i) {
              uint32_t exp = pow_t[i].exp;
              //uint32_t exp = 1;
              double var_eval = vars_eval[i];
              double pow_eval = pow(var_eval, exp);
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
          double vars_eval[n];
          bool vars_already_evaluated = true;
          for (i = 0; i < n; ++i) {
            monomial_t mono_i = mono[i];
            term_t var = mono_i.var;
            if (!good_term(terms, var)) {    // If monomiao has 0 degree then var is UNUSED_TERM
              vars_eval[i] = 1;             // Neutral element of product
              continue;
            }
            bool var_already_evaluated = already_evaluated(&l2o->evaluator, var);
            if (!var_already_evaluated) {
              ivector_push(eval_stack, var);
              vars_already_evaluated = false;
            } else {
              double var_eval = evaluator_get(&l2o->evaluator, var);
              vars_eval[i] = var_eval;
            }
          }
          if (!vars_already_evaluated) {
            continue;
          } else {
            current_eval = 0;
            for (i = 0; i < n; ++i) {
              rational_t coeff = mono[i].coeff;
              double coeff_eval = q_get_double(&coeff);
              double mono_eval = coeff_eval * vars_eval[i];
              current_eval = current_eval + mono_eval;
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

          for (i = 0; i < 2; ++i) {
            term_t arg_i = args[i];
            bool arg_i_already_evaluated = already_evaluated(&l2o->evaluator, arg_i);
            if (!arg_i_already_evaluated) {
              ivector_push(eval_stack, arg_i);
              args_already_evaluated = false;
            } else {
              args_eval[i] = evaluator_get(&l2o->evaluator, arg_i);
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

          for (i = 0; i < 2; ++i) {
            term_t arg_i = args[i];
            bool arg_i_already_evaluated = already_evaluated(&l2o->evaluator, arg_i);
            if (!arg_i_already_evaluated) {
              ivector_push(eval_stack, arg_i);
              args_already_evaluated = false;
            } else {
              args_eval[i] = evaluator_get(&l2o->evaluator, arg_i);
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

          for (i = 0; i < 2; ++i) {
            term_t arg_i = args[i];
            bool arg_i_already_evaluated = already_evaluated(&l2o->evaluator, arg_i);
            if (!arg_i_already_evaluated) {
              ivector_push(eval_stack, arg_i);
              args_already_evaluated = false;
            } else {
              args_eval[i] = evaluator_get(&l2o->evaluator, arg_i);
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

        default:    // TODO consider for example also  EQ_TERM, DISTINCT_TERM, ...
          if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
            printf("\ncurrent_kind: %d\n", current_kind);
            printf("\ncurrent kind is UNSUPPORTED\n");
          }

          // UNSUPPORTED TERM/THEORY
          longjmp(*l2o->exception, MCSAT_EXCEPTION_UNSUPPORTED_THEORY);
          break;
      }
    }

    ivector_pop(eval_stack);
    if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
      printf("\nsetting...");
      mcsat_trace_printf(l2o->tracer, "\n  current_eval = %f ", current_eval);
      mcsat_trace_printf(l2o->tracer, "\n  current_id = %d ", current);
    }
    evaluator_set(&l2o->evaluator, current, current_eval);
  }

  // Get cost of t
  assert(already_evaluated(&l2o->evaluator, term));
  double t_eval = evaluator_get(&l2o->evaluator, term);

  if (trace_enabled(l2o->tracer, "mcsat::evaluator")) {
    printf("\nt_eval = %f", t_eval);
  }

  // Update the cache only if current cost is smaller than cached cost
  if (t_eval < l2o->evaluator.cache.cost) {
    l2o->evaluator.cache.v = (term_t *) safe_malloc(n_var * sizeof(term_t));
    l2o->evaluator.cache.x = (double *) safe_malloc(n_var * sizeof(double));

    l2o->evaluator.cache.cost = t_eval;
    l2o->evaluator.cache.n_var = n_var;
    for (i = 0; i < n_var; ++i) {
      l2o->evaluator.cache.v[i] = v[i];
      l2o->evaluator.cache.x[i] = x[i];
    }

    // TODO Q: Two ways to update the cache. Which one of the following to choose?

    // Hard copy evaluator.eval_map into evaluator.cache.eval_map
    // this way we are losing the cached values of sub-terms of terms for which the cached value have been used (the sub-terms have not been visited)
    eval_hmap_copy(&l2o->evaluator.eval_map, &l2o->evaluator.cache.eval_map);

    // Merge evaluator.eval_map into evaluator.cache.eval_map 
    // this way we update the cache eval_map with all the terms (the merging can be expensive if we have lots of terms)
    //eval_hmap_merge(&l2o->evaluator.eval_map, &l2o->evaluator.cache.eval_map);    
  }

  ivector_reset(eval_stack);
  eval_hmap_reset(&l2o->evaluator.eval_map);
  int_hset_reset(&vars_with_new_val);

  // Return the result
  return t_eval;
}
