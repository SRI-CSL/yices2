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
 * SHOW A MODEL USING THE SMT2 SYNTAX
 */

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>

#include "frontend/smt2/smt2_model_printer.h"
#include "frontend/smt2/smt2_printer.h"
#include "frontend/smt2/smt2_symbol_printer.h"
#include "model/model_eval.h"
#include "utils/int_vectors.h"
#include "utils/int_array_sort.h"


/*
 * The (get-model) command is not officially part of the SMT-LIB 2 standard,
 * but it is useful. To implement it, we print the model as a list of
 * equalities
 *     (= <term-name> <value>)
 * followed by function/array definitions
 */


/*
 * Filter function for collect term:
 * - aux is a term table
 * - return true if t should be printed (i.e., t is uninterpreted and it has a name)
 */
static bool is_named_unint(void *aux, term_t t) {
  return is_pos_term(t) && term_kind(aux, t) == UNINTERPRETED_TERM && term_name(aux, t) != NULL;
}

/*
 * Print (= <term-name> <value>)
 */
static void smt2_pp_term_value(smt2_pp_t *printer, model_t *model, term_t t) {
  char *name;
  value_t v;

  assert(is_named_unint(model->terms, t));
  v = model_find_term_value(model, t);
  name = term_name(model->terms, t);

  assert(v != null_value && name != NULL);

  pp_open_block(&printer->pp, PP_OPEN_EQ);
  smt2_pp_symbol(printer, name);
  smt2_pp_object(printer, &model->vtbl, v);
  pp_close_block(&printer->pp, true);
}


/*
 * Scan array a and print the assignment of all Boolean terms
 * - n = size of the array
 */
static void smt2_pp_bool_assignments(smt2_pp_t *printer, model_t *model, term_t *a, uint32_t n) {
  term_table_t *terms;
  uint32_t i;
  term_t t;

  terms = model->terms;
  for (i=0; i<n; i++) {
    t = a[i];
    if (is_boolean_term(terms, t)) {
      smt2_pp_term_value(printer, model, t);
    }
  }
}

/*
 * Same thing for arithmetic terms
 */
static void smt2_pp_arithmetic_assignments(smt2_pp_t *printer, model_t *model, term_t *a, uint32_t n) {
  term_table_t *terms;
  uint32_t i;
  term_t t;

  terms = model->terms;
  for (i=0; i<n; i++) {
    t = a[i];
    if (is_arithmetic_term(terms, t)) {
      smt2_pp_term_value(printer, model, t);
    }
  }
}

/*
 * Same thing for bitvector terms
 */
static void smt2_pp_bitvector_assignments(smt2_pp_t *printer, model_t *model, term_t *a, uint32_t n) {
  term_table_t *terms;
  uint32_t i;
  term_t t;

  terms = model->terms;
  for (i=0; i<n; i++) {
    t = a[i];
    if (is_bitvector_term(terms, t)) {
      smt2_pp_term_value(printer, model, t);
    }
  }
}

/*
 * Same thing for terms of uninterpreted types
 * (also terms whose types is a instance of an abstract type constructor)
 */
static void smt2_pp_unint_assignments(smt2_pp_t *printer, model_t *model, term_t *a, uint32_t n) {
  term_table_t *terms;
  uint32_t i;
  term_t t;

  terms = model->terms;
  for (i=0; i<n; i++) {
    t = a[i];
    if (is_utype_term(terms, t) || is_itype_term(terms, t)) {
      smt2_pp_term_value(printer, model, t);
    }
  }
}


/*
 * All function terms
 */
static void smt2_pp_function_assignments(smt2_pp_t *printer, model_t *model, term_t *a, uint32_t n) {
  term_table_t *terms;
  uint32_t i;
  term_t t;

  terms = model->terms;
  for (i=0; i<n; i++) {
    t = a[i];
    if (is_function_term(terms, t)) {
      smt2_pp_term_value(printer, model, t);
    }
  }
}


/*
 * Print only terms defined in model->map
 */
void smt2_pp_model(smt2_pp_t *printer, model_t *model) {
  ivector_t v;
  term_t *a;
  uint32_t n;

  init_ivector(&v, 0);
  model_collect_terms(model, false, model->terms, is_named_unint, &v);

  int_array_sort(v.data, v.size);

  n = v.size;
  a = v.data;
  smt2_pp_bool_assignments(printer, model, a, n);
  smt2_pp_arithmetic_assignments(printer, model, a, n);
  smt2_pp_bitvector_assignments(printer, model, a, n);
  smt2_pp_unint_assignments(printer, model, a, n);
  smt2_pp_function_assignments(printer, model, a, n);
  smt2_pp_queued_functions(printer, &model->vtbl, true);
  delete_ivector(&v);
}



/*
 * FULL MODEL PRINTER
 */

/*
 * Evaluate the value of t in eval and print it
 * - print nothing if the evaluator fails to compute a value for t
 */
static void smt2_eval_pp_term_value(smt2_pp_t *printer, evaluator_t *eval, term_t t) {
  model_t *model;
  char *name;
  value_t v;

  model = eval->model;
  assert(is_named_unint(model->terms, t));

  v = eval_in_model(eval, t);
  if (v >= 0) {
    name = term_name(model->terms, t);
    assert(name != NULL);
    pp_open_block(&printer->pp, PP_OPEN_EQ);
    smt2_pp_symbol(printer, name);
    smt2_pp_object(printer, &model->vtbl, v);
    pp_close_block(&printer->pp, true);
  }
}


/*
 * Scan array a and print the assignment of all Boolean terms
 * - n = size of the array
 */
static void smt2_eval_pp_bool_assignments(smt2_pp_t *printer, evaluator_t *eval, term_t *a, uint32_t n) {
  term_table_t *terms;
  uint32_t i;
  term_t t;

  terms = eval->model->terms;
  for (i=0; i<n; i++) {
    t = a[i];
    if (is_boolean_term(terms, t)) {
      smt2_eval_pp_term_value(printer, eval, t);
    }
  }
}

/*
 * Same thing for arithmetic terms
 */
static void smt2_eval_pp_arithmetic_assignments(smt2_pp_t *printer, evaluator_t *eval, term_t *a, uint32_t n) {
  term_table_t *terms;
  uint32_t i;
  term_t t;

  terms = eval->model->terms;
  for (i=0; i<n; i++) {
    t = a[i];
    if (is_arithmetic_term(terms, t)) {
      smt2_eval_pp_term_value(printer, eval, t);
    }
  }
}

/*
 * Same thing for bitvector terms
 */
static void smt2_eval_pp_bitvector_assignments(smt2_pp_t *printer, evaluator_t *eval, term_t *a, uint32_t n) {
  term_table_t *terms;
  uint32_t i;
  term_t t;

  terms = eval->model->terms;
  for (i=0; i<n; i++) {
    t = a[i];
    if (is_bitvector_term(terms, t)) {
      smt2_eval_pp_term_value(printer, eval, t);
    }
  }
}

/*
 * Same thing for terms of uninterpreted types
 */
static void smt2_eval_pp_unint_assignments(smt2_pp_t *printer, evaluator_t *eval, term_t *a, uint32_t n) {
  term_table_t *terms;
  uint32_t i;
  term_t t;

  terms = eval->model->terms;
  for (i=0; i<n; i++) {
    t = a[i];
    if (is_utype_term(terms, t)) {
      smt2_eval_pp_term_value(printer, eval, t);
    }
  }
}


/*
 * All function terms
 */
static void smt2_eval_pp_function_assignments(smt2_pp_t *printer, evaluator_t *eval, term_t *a, uint32_t n) {
  term_table_t *terms;
  uint32_t i;
  term_t t;

  terms = eval->model->terms;
  for (i=0; i<n; i++) {
    t = a[i];
    if (is_function_term(terms, t)) {
      smt2_eval_pp_term_value(printer, eval, t);
    }
  }
}


/*
 * Print all terms
 */
void smt2_pp_full_model(smt2_pp_t *printer, model_t *model) {
  evaluator_t eval;
  ivector_t v;
  term_t *a;
  uint32_t n;

  if (model->has_alias && model->alias_map != NULL) {
    init_evaluator(&eval, model);

    /*
     * We use two passes to find all relevant terms:
     * 1) in the first pass, we compute the value of all terms
     *    in the model's alias table.
     * 2) in the second pass, we collect all terms that have
     *    received a value in the first pass.
     *
     * This is necessary in situations like this:
     *   (assert (= x  (.. y ..)))
     * and y does not occur anywhere else.
     * During model construction, we store [x --> (... y ...)]
     * in the model's alias table (so x is known to be relevant).
     * When we compute x's value in phase 1, we also assign a value
     * to y so y is relevant, and its value must be printed.
     *
     * The second pass makes sure that y is found.
     */

    // first pass: compute term values
    init_ivector(&v, 0);
    model_collect_terms(model, true, model->terms, is_named_unint, &v);
    eval_terms_in_model(&eval, v.data, v.size);

    // second pass: collect all uninterpreted terms that
    // have a value in model or in the evaluator
    ivector_reset(&v);
    model_collect_terms(model, false, model->terms, is_named_unint, &v);
    evaluator_collect_cached_terms(&eval, model->terms, is_named_unint, &v);

    // sort the terms so that we have consistent printouts with different
    // algorithms
    int_array_sort(v.data, v.size);

    // print everything
    n = v.size;
    a = v.data;
    smt2_eval_pp_bool_assignments(printer, &eval, a, n);
    smt2_eval_pp_arithmetic_assignments(printer, &eval, a, n);
    smt2_eval_pp_bitvector_assignments(printer, &eval, a, n);
    smt2_eval_pp_unint_assignments(printer, &eval, a, n);
    smt2_eval_pp_function_assignments(printer, &eval, a, n);
    smt2_pp_queued_functions(printer, &model->vtbl, true);
    delete_ivector(&v);
    delete_evaluator(&eval);
  } else {
    smt2_pp_model(printer, model);
  }
}

