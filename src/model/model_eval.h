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
 * COMPUTE THE VALUE OF A TERM IN A MODEL
 */

#ifndef __MODEL_EVAL_H
#define __MODEL_EVAL_H

#include <stdbool.h>
#include <stdint.h>
#include <setjmp.h>

#include "model/models.h"
#include "utils/int_hash_map.h"
#include "utils/int_stack.h"
#include "utils/int_vectors.h"


/*
 * Error codes returned by eval_in_model
 * - all are negative integers
 * - a non-negative value means no error
 * - the null_value is -1 so we start from -2
 */
enum {
  MDL_EVAL_INTERNAL_ERROR = -2,
  MDL_EVAL_UNKNOWN_TERM = -3,
  MDL_EVAL_FREEVAR_IN_TERM = -4,
  MDL_EVAL_QUANTIFIER = -5,
  MDL_EVAL_LAMBDA = -6,
  MDL_EVAL_FAILED = -7, // function equality involved
};



/*
 * Evaluator structure:
 * - pointer to a model + term_table + value_table
 *   (term table and value table are extracted from
 *    model when the evaluator is initialized)
 * - cache: keeps track of the value of evaluated terms
 * - env: jump buffer for error handling
 * - stack of integer arrays
 */
typedef struct evaluator_s {
  model_t *model;
  term_table_t *terms;
  value_table_t *vtbl;
  int_hmap_t cache;
  int_stack_t stack;
  jmp_buf env;
} evaluator_t;




/*
 * Initialization for the given model
 *
 * NOTE: because the evaluator has side effects on model->vtbl,
 * we can't attach several evaluators to the same model.
 */
extern void init_evaluator(evaluator_t *eval, model_t *model);


/*
 * Deletion: free all memory
 */
extern void delete_evaluator(evaluator_t *eval);


/*
 * Reset: empty the cache
 */
extern void reset_evaluator(evaluator_t *eval);


/*
 * Compute the value of term t in the model
 * - t must be a valid term
 * - return a negative code if there's an error
 * - return the id of a concrete objects of eval->model.vtbl otherwise
 *
 * Evaluation may create new objects. All these new objects are
 * permanent in eval->vtbl. So they survive a call to delete_evaluator
 * or reset_evaluator.
 */
extern value_t eval_in_model(evaluator_t *eval, term_t t);


/*
 * Check whether t is true in the model
 * - t must be a valid term
 * - return true if t evaluates to true
 * - return false if t can't be evaluated or
 *   if t's value is not boolean or not true.
 */
extern bool eval_to_true_in_model(evaluator_t *eval, term_t t);


/*
 * Check whether t is false in the model
 * - t must be a valid term
 * - return true if t evaluates to false
 * - return false if t can't be evaluated or it's not a boolean
 *   or if it evaluates to true.
 */
extern bool eval_to_false_in_model(evaluator_t *eval, term_t);


/*
 * Check whether t is zero in the model
 * - t must be a valid term
 * - if t is an arithmetic term, this checks whether value(t) == 0
 * - if t is a bit-vector term, this checks whether value(t) == 0b0000...
 * - return false if t can't be evaluated, or if t is not an arithemtic
 *   term nor a bitvector term, or if t's value is not zero.
 */
extern bool eval_to_zero_in_model(evaluator_t *eval, term_t t);


/*
 * Check whether t evaluates to +/-1 in the model
 * - t must be a valid  term
 * - return false if t can't be evaluated or its value is not a rational
 * - return true if t's value is either +1 or -1
 */
extern bool eval_to_unit_in_model(evaluator_t *eval, term_t t);


/*
 * Compute the values of terms a[0 ... n-1]
 * - don't return anything
 * - the value of a[i] can be queried by using eval_in_model(eval, a[i]) later
 *   (this reads the value from eval->cache so that's cheap).
 */
extern void eval_terms_in_model(evaluator_t *eval, const term_t *a, uint32_t n);


/*
 * Add useful uninterpreted terms to the model.
 *
 * A term t is useful if it's assigned a default value in eval_term. This means
 * that the value of t is useful but was not assigned in the model. It makes
 * sense then to print the value of t in print_model. To do this, we add an
 * entry [t -> value(t)] for every useful term t.
 */
extern void eval_record_useful_terms(evaluator_t *eval);


/*
 * Cached-term collector:
 * - call f(aux, t) for every t that's stored in eval->cache
 *   if f(aux, t) returns true, add t to v
 * - f must not have side effects
 */
// model_filter_t is defined in models.h
extern void evaluator_collect_cached_terms(evaluator_t *eval, void *aux, model_filter_t f, ivector_t *v);


#endif /* __MODEL_EVAL_H */
