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
 * PRINT A MODEL
 */

#include <assert.h>
#include <inttypes.h>
#include <string.h>

#include "io/concrete_value_printer.h"
#include "io/model_printer.h"
#include "model/model_eval.h"
#include "utils/int_vectors.h"
#include "utils/int_array_sort.h"


/*
 * Print the assignment for t in model
 * - the format is (= <t's name> <value>)
 */
void model_print_term_value(FILE *f, model_t *model, term_t t) {
  char *name;
  value_t v;

  assert(term_kind(model->terms, t) == UNINTERPRETED_TERM);

  name = term_name(model->terms, t);
  if (name == NULL) {
    fprintf(f, "(= t!%"PRId32" ", t);
  } else {
    fprintf(f, "(= %s ", name);
  }

  v = model_find_term_value(model, t);
  if (v == null_value) {
    /*
     * ??) is a C trigraph so "???)" can't be written as is.
     */
    fputs("???"")", f);
  } else {
    vtbl_print_object(f, &model->vtbl, v);
    fputc(')', f);
  }
}


/*
 * Print the assignment for all boolean terms in array a
 * - n = size of the array
 */
static void model_print_bool_assignments(FILE *f, model_t *model, const term_t *a, uint32_t n) {
  term_table_t *terms;
  uint32_t i;
  term_t t;

  terms = model->terms;
  for (i=0; i<n; i++) {
    t = a[i];
    if (is_boolean_term(terms, t)) {
      model_print_term_value(f, model, t);
      fputc('\n', f);
    }
  }
}


/*
 * Print the assignment for all arithmetic terms in array a
 * - n = size of the array
 */
static void model_print_arithmetic_assignments(FILE *f, model_t *model, const term_t *a, uint32_t n) {
  term_table_t *terms;
  uint32_t i;
  term_t t;

  terms = model->terms;
  for (i=0; i<n; i++) {
    t = a[i];
    if (is_arithmetic_term(terms, t)) {
      model_print_term_value(f, model, t);
      fputc('\n', f);
    }
  }
}


/*
 * Print the assignment for all bitvector terms in array a
 * - n = size of the array
 */
static void model_print_bitvector_assignments(FILE *f, model_t *model, const term_t *a, uint32_t n) {
  term_table_t *terms;
  uint32_t i;
  term_t t;

  terms = model->terms;
  for (i=0; i<n; i++) {
    t = a[i];
    if (is_bitvector_term(terms, t)) {
      model_print_term_value(f, model, t);
      fputc('\n', f);
    }
  }
}


/*
 * Print the terms of uninterpreted type in array a
 * - n = size of the array
 */
static void model_print_constant_assignments(FILE *f, model_t *model, const term_t *a, uint32_t n) {
  term_table_t *terms;
  char *name;
  value_unint_t *d;
  uint32_t i;
  term_t t;
  value_t c;
  type_kind_t tau;

  terms = model->terms;
  for (i=0; i<n; i++) {
    t = a[i];
    tau = term_type_kind(terms, t);
    if (tau == UNINTERPRETED_TYPE || tau == SCALAR_TYPE || tau == INSTANCE_TYPE) {
      c = model_find_term_value(model, t);
      d = vtbl_unint(&model->vtbl, c);
      name = term_name(terms, t);
      assert(name != NULL);
      if (d->name == NULL || strcmp(name, d->name) != 0) {
        fprintf(f, "(= %s ", name);
        vtbl_print_object(f, &model->vtbl, c);
        fputs(")\n", f);
      }
    }
  }
}


/*
 * Print the assignment for all tuple terms in array a
 * - n = size of the array
 */
static void model_print_tuple_assignments(FILE *f, model_t *model, const term_t *a, uint32_t n) {
  term_table_t *terms;
  uint32_t i;
  term_t t;

  terms = model->terms;
  for (i=0; i<n; i++) {
    t = a[i];
    if (is_tuple_term(terms, t)) {
      model_print_term_value(f, model, t);
      fputc('\n', f);
    }
  }
}


/*
 * Print the function terms in array a
 * - n = size of the array
 */
static void model_print_function_assignments(FILE *f, model_t *model, const term_t *a, uint32_t n) {
  term_table_t *terms;
  value_fun_t *fun;
  char *name;
  term_t t;
  value_t c;
  uint32_t i;

  terms = model->terms;
  for (i=0; i<n; i++) {
    t = a[i];
    if (is_function_term(terms, t)) {
      /*
       * t is mapped to a function object fun
       * if t and fun have different names, we print
       * (= <t's name> <fun 's name>) otherwise we print nothing
       * and push fun in value_table's queue
       */
      c = model_find_term_value(model, t);
      name = term_name(terms, t);
      assert(name != NULL && c != null_value);
      if (object_is_function(&model->vtbl, c)) {
        fun = vtbl_function(&model->vtbl, c);
        if (fun->name == NULL || strcmp(name, fun->name) != 0) {
          fprintf(f, "(= %s ", name);
          vtbl_print_object(f, &model->vtbl, c);
          fputs(")\n", f);
        } else {
	  vtbl_push_object(&model->vtbl, c);
        }
      }
    }
  }

  /*
   * Second pass: print the update objects
   */
  for (i=0; i<n; i++) {
    t = a[i];
    if (is_function_term(terms, t)) {
      c = model_find_term_value(model, t);
      name = term_name(terms, t);
      assert(name != NULL);
      if (object_is_update(&model->vtbl, c)) {
        vtbl_normalize_and_print_update(f, &model->vtbl, name, c, true);
      }
    }
  }
}




/*
 * Filter function for model_collect_terms
 * - aux is a term table
 * - return true if term t should be printed in the assignments (i.e., t has a name)
 */
static bool term_to_print(void *aux, term_t t) {
  return is_pos_term(t) && term_kind(aux, t) == UNINTERPRETED_TERM && term_name(aux, t) != NULL;
}


/*
 * Print the values of all terms in array a
 * - n = number of terms in a
 */
void model_print_terms(FILE *f, model_t *model, const term_t *a, uint32_t n, pp_lang_t lang) {
  model_print_bool_assignments(f, model, a, n);
  model_print_arithmetic_assignments(f, model, a, n);
  model_print_bitvector_assignments(f, model, a, n);
  model_print_constant_assignments(f, model, a, n);
  model_print_tuple_assignments(f, model, a, n);
  model_print_function_assignments(f, model, a, n);
  vtbl_print_queued_functions(f, &model->vtbl, true);
}


/*
 * Print the model->map table
 */
void model_print(FILE *f, model_t *model, pp_lang_t lang) {
  ivector_t v;

  init_ivector(&v, 0);
  model_collect_terms(model, false, model->terms, term_to_print, &v);
  model_print_terms(f, model, v.data, v.size, lang);
  delete_ivector(&v);
}




/*
 * FULL MODEL: USE EVALUATOR
 */

/*
 * Print the assignment for t as computed by the evaluator
 * - t must be a valid term
 * - if t's value can't be evaluated, we print nothing.
 */
static void eval_print_term_value(FILE *f, evaluator_t *eval, term_t t) {
  model_t *model;
  char *name;
  value_t v;

  model = eval->model;

  v = eval_in_model(eval, t);
  if (v >= 0) {
    // v = good value for t
    name = term_name(model->terms, t);
    if (name == NULL) {
      fprintf(f, "(= t!%"PRId32" ", t);
    } else {
      fprintf(f, "(= %s ", name);
    }
    vtbl_print_object(f, &model->vtbl, v);
    fputc(')', f);
  }
}


/*
 * Variant for a term of uninterpreted or scalar type:
 * - we dont want to print things like (= A A)
 */
static void eval_print_constant_term(FILE *f, evaluator_t *eval, term_t t) {
  value_unint_t *d;
  value_t c;
  char *name;

  c = eval_in_model(eval, t);
  d = vtbl_unint(eval->vtbl, c);
  name = term_name(eval->terms, t);
  if (name == NULL) {
    fprintf(f, "(= t!%"PRId32" ", t);
    vtbl_print_object(f, eval->vtbl, c);
    fputs(")\n", f);
  } else if (d->name == NULL || strcmp(name, d->name) != 0) {
    fprintf(f, "(= %s", name);
    vtbl_print_object(f, eval->vtbl, c);
    fputs(")\n", f);
  }
}


/*
 * Variant for function terms:
 * - if t is mapped to a function object fun and t and fun have different names,
 *   print (= <t's name> <fun's name>)
 */
static void eval_print_function_term(FILE *f, evaluator_t *eval, term_t t) {
  value_fun_t *fun;
  value_t c;
  char *name;

  c = eval_in_model(eval, t);
  name = term_name(eval->terms, t);
  if (object_is_function(eval->vtbl, c)) {
    /*
     * t is mapped to a function object fun
     * if t and fun have different names, we print
     * (= <t's name> <fun 's name>) otherwise we print nothing
     * and store fun in the vtbl's internal queue
     */
    fun = vtbl_function(eval->vtbl, c);
    if (name == NULL) {
      fprintf(f, "(= t%"PRId32" ", t);
      vtbl_print_object(f, eval->vtbl, c);
      fputs(")\n", f);
    } else if (fun->name == NULL || strcmp(name, fun->name) != 0) {
      fprintf(f, "(= %s ", name);
      vtbl_print_object(f, eval->vtbl, c);
      fputs(")\n", f);
    } else {
      vtbl_push_object(eval->vtbl, c);
    }
  } else if (object_is_update(eval->vtbl, c)) {
    /*
     * t is mapped to an update object
     */
    vtbl_normalize_and_print_update(f, eval->vtbl, name, c, true);
  }
}

/*
 * Evaluate then print the value of term t
 */
static void eval_and_print_term(FILE *f, evaluator_t *eval, term_t t) {
  switch (term_type_kind(eval->terms, t)) {
  case UNINTERPRETED_TYPE:
  case SCALAR_TYPE:
  case INSTANCE_TYPE:
    eval_print_constant_term(f, eval, t);
    break;

  case FUNCTION_TYPE:
    eval_print_function_term(f, eval, t);
    break;

  case UNUSED_TYPE:
    assert(false);

  default:
    eval_print_term_value(f, eval, t);
    break;
  }
}

/*
 * Evaluate and print the values of all terms in array a
 * - n = number of terms in a
 * - this is the same as mode_print_terms, except that the function tries
 *   to compute the value of these terms (as in model_print_full).
 */
void model_print_eval_terms(FILE *f, model_t *model, const term_t *a, uint32_t n, pp_lang_t lang) {
  evaluator_t eval;
  uint32_t i;

  init_evaluator(&eval, model);
  for (i=0; i<n; i++) {
    eval_and_print_term(f, &eval, a[i]);
  }
  vtbl_print_queued_functions(f, eval.vtbl, true);
  delete_evaluator(&eval);
}




/*
 * Print the assignment for all boolean terms in array a
 * - n = size of a
 */
static void eval_print_bool_assignments(FILE *f, evaluator_t *eval, const term_t *a, uint32_t n) {
  term_table_t *terms;
  uint32_t i;
  term_t t;

  terms = eval->model->terms;
  for (i=0; i<n; i++) {
    t = a[i];
    if (is_boolean_term(terms, t)) {
      eval_print_term_value(f, eval, t);
      fputc('\n', f);
    }
  }

}

/*
 * Print the assignment for all arithmetic terms in array a
 * - n = size of the array
 */
static void eval_print_arithmetic_assignments(FILE *f, evaluator_t *eval, const term_t *a, uint32_t n) {
  term_table_t *terms;
  uint32_t i;
  term_t t;

  terms = eval->model->terms;
  for (i=0; i<n; i++) {
    t = a[i];
    if (is_arithmetic_term(terms, t)) {
      eval_print_term_value(f, eval, t);
      fputc('\n', f);
    }
  }
}



/*
 * Print the assignment for all bitvector terms in array a
 * - n = size of the array
 */
static void eval_print_bitvector_assignments(FILE *f, evaluator_t *eval, const term_t *a, uint32_t n) {
  term_table_t *terms;
  uint32_t i;
  term_t t;

  terms = eval->model->terms;
  for (i=0; i<n; i++) {
    t = a[i];
    if (is_bitvector_term(terms, t)) {
      eval_print_term_value(f, eval, t);
      fputc('\n', f);
    }
  }
}



/*
 * Print the assignment for all tuple terms in array a
 * - n = size of the array
 */
static void eval_print_tuple_assignments(FILE *f, evaluator_t *eval, const term_t *a, uint32_t n) {
  term_table_t *terms;
  uint32_t i;
  term_t t;

  terms = eval->model->terms;
  for (i=0; i<n; i++) {
    t = a[i];
    if (is_tuple_term(terms, t)) {
      eval_print_term_value(f, eval, t);
      fputc('\n', f);
    }
  }
}


/*
 * Print the terms of uninterpreted type in array a
 * - n = size of the array
 */
static void eval_print_constant_assignments(FILE *f, evaluator_t *eval, const term_t *a, uint32_t n) {
  term_table_t *terms;
  uint32_t i;
  term_t t;
  type_kind_t tau;

  terms = eval->terms;

  for (i=0; i<n; i++) {
    t = a[i];
    tau = term_type_kind(terms, t);
    if (tau == UNINTERPRETED_TYPE || tau == SCALAR_TYPE || tau == INSTANCE_TYPE) {
      eval_print_constant_term(f, eval, t);
    }
  }
}


/*
 * Print the function terms in array a
 * - n = size of the array
 */
static void eval_print_function_assignments(FILE *f, evaluator_t *eval, const term_t *a, uint32_t n) {
  model_t *model;
  term_table_t *terms;
  value_fun_t *fun;
  char *name;
  term_t t;
  value_t c;
  uint32_t i;

  model = eval->model;
  terms = model->terms;

  // first pass: function objects
  for (i=0; i<n; i++) {
    t = a[i];
    if (is_function_term(terms, t)) {
      /*
       * t is mapped to a function object fun
       * if t and fun have different names, we print
       * (= <t's name> <fun 's name>) otherwise we print nothing
       * and store fun in the vtbl's internal queue
       */
      c = eval_in_model(eval, t);
      name = term_name(terms, t);
      assert(name != NULL);
      if (object_is_function(&model->vtbl, c)) {
        fun = vtbl_function(&model->vtbl, c);
        if (fun->name == NULL || strcmp(name, fun->name) != 0) {
          fprintf(f, "(= %s ", name);
          vtbl_print_object(f, &model->vtbl, c);
          fputs(")\n", f);
        } else {
	  vtbl_push_object(&model->vtbl, c);
        }
      }
    }
  }

  /*
   * second pass: deal with update objects
   */
  for (i=0; i<n; i++) {
    t = a[i];
    if (is_function_term(terms, t)) {
      c = eval_in_model(eval, t);
      name = term_name(terms, t);
      assert(name != NULL);
      if (object_is_update(&model->vtbl, c)) {
        vtbl_normalize_and_print_update(f, &model->vtbl, name, c, true);
      }
    }
  }
}


/*
 * Print model, including the aliased terms
 * - one line per term
 * - if model->has_alias is true, then the value of all terms in
 *   the alias table is displayed
 * - if model->has_alias is false, then this is the same as model_print
 */
void model_print_full(FILE *f, model_t *model, pp_lang_t lang) {
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

    // collect all terms that have a name
    init_ivector(&v, 0);
    model_collect_terms(model, true, model->terms, term_to_print, &v);

    // compute their values
    eval_terms_in_model(&eval, v.data, v.size);

    // second pass: collect all uninterpreted terms that
    // have a value in model or in the evaluator.
    ivector_reset(&v);
    model_collect_terms(model, false, model->terms, term_to_print, &v);
    evaluator_collect_cached_terms(&eval, model->terms, term_to_print, &v);

    // print all terms in v
    a = v.data;
    n = v.size;
    eval_print_bool_assignments(f, &eval, a, n);
    eval_print_arithmetic_assignments(f, &eval, a, n);
    eval_print_bitvector_assignments(f, &eval, a, n);
    eval_print_constant_assignments(f, &eval, a, n);
    eval_print_tuple_assignments(f, &eval, a, n);
    eval_print_function_assignments(f, &eval, a, n);
    vtbl_print_queued_functions(f, eval.vtbl, true);

    delete_evaluator(&eval);
    delete_ivector(&v);
  } else {
    model_print(f, model, lang);
  }
}




/*
 * PRETTY PRINTING
 */

/*
 * Print the assignment for t in model
 */
void model_pp_term_value(yices_pp_t *printer, model_t *model, term_t t) {
  char *name;
  value_t v;

  assert(term_kind(model->terms, t) == UNINTERPRETED_TERM);

  pp_open_block(printer, PP_OPEN_EQ);
  name = term_name(model->terms, t);
  if (name == NULL) {
    pp_id(printer, "t!", t);
  } else {
    pp_string(printer, name);
  }

  v = model_find_term_value(model, t);
  if (v == null_value) {
    pp_string(printer, "???");
  } else {
    vtbl_pp_object(printer, &model->vtbl, v);
  }
  pp_close_block(printer, true);
}


/*
 * Print the assignment for all boolean terms in array a
 * - n = size of the array
 */
static void model_pp_bool_assignments(yices_pp_t *printer, model_t *model, const term_t *a, uint32_t n) {
  term_table_t *terms;
  uint32_t i;
  term_t t;

  terms = model->terms;
  for (i=0; i<n; i++) {
    t = a[i];
    if (is_boolean_term(terms, t)) {
      model_pp_term_value(printer, model, t);
    }
  }
}


/*
 * Print the assignment for all arithmetic terms in array a
 * - n = size of the array
 */
static void model_pp_arithmetic_assignments(yices_pp_t *printer, model_t *model, const term_t *a, uint32_t n) {
  term_table_t *terms;
  uint32_t i;
  term_t t;

  terms = model->terms;
  for (i=0; i<n; i++) {
    t = a[i];
    if (is_arithmetic_term(terms, t)) {
      model_pp_term_value(printer, model, t);
    }
  }
}


/*
 * Print the assignment for all bitvector terms in array a
 * - n = size of the array
 */
static void model_pp_bitvector_assignments(yices_pp_t *printer, model_t *model, const term_t *a, uint32_t n) {
  term_table_t *terms;
  uint32_t i;
  term_t t;

  terms = model->terms;
  for (i=0; i<n; i++) {
    t = a[i];
    if (is_bitvector_term(terms, t)) {
      model_pp_term_value(printer, model, t);
    }
  }
}


/*
 * Print the terms of uninterpreted type in array a
 * - n = size of the array
 */
static void model_pp_constant_assignments(yices_pp_t *printer, model_t *model, const term_t *a, uint32_t n) {
  term_table_t *terms;
  char *name;
  value_unint_t *d;
  uint32_t i;
  term_t t;
  value_t c;
  type_kind_t tau;

  terms = model->terms;
  for (i=0; i<n; i++) {
    t = a[i];
    tau = term_type_kind(terms, t);
    if (tau == UNINTERPRETED_TYPE || tau == SCALAR_TYPE || tau == INSTANCE_TYPE) {
      c = model_find_term_value(model, t);
      d = vtbl_unint(&model->vtbl, c);
      name = term_name(terms, t);
      assert(name != NULL);
      if (d->name == NULL || strcmp(name, d->name) != 0) {
        pp_open_block(printer, PP_OPEN_EQ);
        pp_string(printer, name);
        vtbl_pp_object(printer, &model->vtbl, c);
        pp_close_block(printer, true);
      }
    }
  }
}



/*
 * Print the assignment for all tuple terms in array a
 * - n = size of the array
 */
static void model_pp_tuple_assignments(yices_pp_t *printer, model_t *model, const term_t *a, uint32_t n) {
  term_table_t *terms;
  uint32_t i;
  term_t t;

  terms = model->terms;
  for (i=0; i<n; i++) {
    t = a[i];
    if (is_tuple_term(terms, t)) {
      model_pp_term_value(printer, model, t);
    }
  }
}


/*
 * Print the function terms in array a
 * - n = size of the array
 */
static void model_pp_function_assignments(yices_pp_t *printer, model_t *model, const term_t *a, uint32_t n) {
  term_table_t *terms;
  value_fun_t *fun;
  char *name;
  term_t t;
  value_t c;
  uint32_t i;

  terms = model->terms;
  for (i=0; i<n; i++) {
    t = a[i];
    if (is_function_term(terms, t)) {
      /*
       * t is mapped to a function object fun
       * if t and fun have different names, we print
       * (= <t's name> <fun 's name>) otherwise we print nothing
       * and push fun in vtbl's internal queue.
       */
      c = model_find_term_value(model, t);
      name = term_name(terms, t);
      assert(name != NULL);
      if (object_is_function(&model->vtbl, c)) {
        fun = vtbl_function(&model->vtbl, c);
        if (fun->name == NULL || strcmp(name, fun->name) != 0) {
          pp_open_block(printer, PP_OPEN_EQ);
          pp_string(printer, name);
          vtbl_pp_object(printer, &model->vtbl, c);
          pp_close_block(printer, true);
        } else {
	  vtbl_push_object(&model->vtbl, c);
        }
      }
    }
  }

  /*
   * Second pass: print the update objects
   */
  for (i=0; i<n; i++) {
    t = a[i];
    if (is_function_term(terms, t)) {
      c = model_find_term_value(model, t);
      name = term_name(terms, t);
      assert(name != NULL);
      if (object_is_update(&model->vtbl, c)) {
        vtbl_normalize_and_pp_update(printer, &model->vtbl, name, c, true);
      }
    }
  }

}


/*
 * Print the values of all terms in array a
 * - n = number of terms in a
 */
void model_pp_terms(yices_pp_t *printer, model_t *model, const term_t *a, uint32_t n) {
  model_pp_bool_assignments(printer, model, a, n);
  model_pp_arithmetic_assignments(printer, model, a, n);
  model_pp_bitvector_assignments(printer, model, a, n);
  model_pp_constant_assignments(printer, model, a, n);
  model_pp_tuple_assignments(printer, model, a, n);
  model_pp_function_assignments(printer, model, a, n);
  vtbl_pp_queued_functions(printer, &model->vtbl, true);
}


/*
 * Print the model->map table
 */
void model_pp(yices_pp_t *printer, model_t *model) {
  ivector_t v;
  term_t *a;
  uint32_t n;

  init_ivector(&v, 0);
  model_collect_terms(model, false, model->terms, term_to_print, &v);

  n = v.size;
  a = v.data;

  // sort to help make things consistent when we use MCSAT vs. CDCL
  int_array_sort(a, n);
  model_pp_terms(printer, model, a, n);
  delete_ivector(&v);
}



/*
 * USE THE EVALUATOR
 */

/*
 * Print the assignment for t as computed by the evaluator
 * - t must be a valid, uninterpreted term
 */
static void eval_pp_term_value(yices_pp_t *printer, evaluator_t *eval, term_t t) {
  model_t *model;
  char *name;
  value_t v;

  model = eval->model;

  v = eval_in_model(eval, t);
  if (v >= 0) {
    // v = good value for t
    pp_open_block(printer, PP_OPEN_EQ);
    name = term_name(model->terms, t);
    if (name == NULL) {
      pp_id(printer, "t!", t);
    } else {
      pp_string(printer, name);
    }
    vtbl_pp_object(printer, &model->vtbl, v);
    pp_close_block(printer, true);
  }
}


/*
 * Variant for a term of uninterpreted or scalar type
 */
static void eval_pp_constant_term(yices_pp_t *printer, evaluator_t *eval, term_t t) {
  value_unint_t *d;
  value_t c;
  char *name;

  c = eval_in_model(eval, t);
  d = vtbl_unint(eval->vtbl, c);
  name = term_name(eval->terms, t);
  if (name == NULL) {
    pp_open_block(printer, PP_OPEN_EQ);
    pp_id(printer, "t!", t);
    vtbl_pp_object(printer, eval->vtbl, c);
    pp_close_block(printer, true);
  } else if (d->name == NULL || strcmp(name, d->name) != 0) {
    pp_open_block(printer, PP_OPEN_EQ);
    pp_string(printer, name);
    vtbl_pp_object(printer, eval->vtbl, c);
    pp_close_block(printer, true);
  }
}


/*
 * Variant for function terms:
 * - if t is mapped to a function object fun and t and fun have different names,
 *   print (= <t's name> <fun's name>)
 */
static void eval_pp_function_term(yices_pp_t *printer, evaluator_t *eval, term_t t) {
  value_fun_t *fun;
  value_t c;
  char *name;

  c = eval_in_model(eval, t);
  name = term_name(eval->terms, t);
  if (object_is_function(eval->vtbl, c)) {
    /*
     * t is mapped to a function object fun
     * if t and fun have the same name, we don't print anything
     * but we store fun in the vtbl's internal queue.
     *
     * fun will be printed later on by vtbl_pp_queued_functions
     */
    fun = vtbl_function(eval->vtbl, c);
    if (name == NULL) {
      pp_open_block(printer, PP_OPEN_EQ);
      pp_id(printer, "t!", t);
      vtbl_pp_object(printer, eval->vtbl, c);
      pp_close_block(printer, true);
    } else if (fun->name == NULL || strcmp(name, fun->name) != 0) {
      pp_open_block(printer, PP_OPEN_EQ);
      pp_string(printer, name);
      vtbl_pp_object(printer, eval->vtbl, c);
      pp_close_block(printer, true);
    } else {
      vtbl_push_object(eval->vtbl, c);
    }
  } else if (object_is_update(eval->vtbl, c)) {
    /*
     * t is mapped to an update object
     */
    vtbl_normalize_and_pp_update(printer, eval->vtbl, name, c, true);
  }
}

/*
 * Evaluate then print the value of term t
 */
static void eval_and_pp_term(yices_pp_t *printer, evaluator_t *eval, term_t t) {
  switch (term_type_kind(eval->terms, t)) {
  case UNINTERPRETED_TYPE:
  case SCALAR_TYPE:
  case INSTANCE_TYPE:
    eval_pp_constant_term(printer, eval, t);
    break;

  case FUNCTION_TYPE:
    eval_pp_function_term(printer, eval, t);
    break;

  case UNUSED_TYPE:
    assert(false);

  default:
    eval_pp_term_value(printer, eval, t);
    break;
  }
}

/*
 * Evaluate and print the values of all terms in array a
 * - n = number of terms in a
 * - this is the same as mode_pp_terms, except that the function tries
 *   to compute the value of these terms (as in model_print_full).
 */
void model_pp_eval_terms(yices_pp_t *printer, model_t *model, const term_t *a, uint32_t n) {
  evaluator_t eval;
  uint32_t i;

  init_evaluator(&eval, model);
  for (i=0; i<n; i++) {
    eval_and_pp_term(printer, &eval, a[i]);
  }
  vtbl_pp_queued_functions(printer, eval.vtbl, true);
  delete_evaluator(&eval);
}





/*
 * Print the assignment for all boolean terms in array a
 * - n = size of a
 */
static void eval_pp_bool_assignments(yices_pp_t *printer, evaluator_t *eval, const term_t *a, uint32_t n) {
  term_table_t *terms;
  uint32_t i;
  term_t t;

  terms = eval->model->terms;
  for (i=0; i<n; i++) {
    t = a[i];
    if (is_boolean_term(terms, t)) {
      eval_pp_term_value(printer, eval, t);
    }
  }

}

/*
 * Print the assignment for all arithmetic terms in array a
 * - n = size of the array
 */
static void eval_pp_arithmetic_assignments(yices_pp_t *printer, evaluator_t *eval, const term_t *a, uint32_t n) {
  term_table_t *terms;
  uint32_t i;
  term_t t;

  terms = eval->model->terms;
  for (i=0; i<n; i++) {
    t = a[i];
    if (is_arithmetic_term(terms, t)) {
      eval_pp_term_value(printer, eval, t);
    }
  }
}



/*
 * Print the assignment for all bitvector terms in array a
 * - n = size of the array
 */
static void eval_pp_bitvector_assignments(yices_pp_t *printer, evaluator_t *eval, const term_t *a, uint32_t n) {
  term_table_t *terms;
  uint32_t i;
  term_t t;

  terms = eval->model->terms;
  for (i=0; i<n; i++) {
    t = a[i];
    if (is_bitvector_term(terms, t)) {
      eval_pp_term_value(printer, eval, t);
    }
  }
}



/*
 * Print the assignment for all tuple terms in array a
 * - n = size of the array
 */
static void eval_pp_tuple_assignments(yices_pp_t *printer, evaluator_t *eval, const term_t *a, uint32_t n) {
  term_table_t *terms;
  uint32_t i;
  term_t t;

  terms = eval->model->terms;
  for (i=0; i<n; i++) {
    t = a[i];
    if (is_tuple_term(terms, t)) {
      eval_pp_term_value(printer, eval, t);
    }
  }
}


/*
 * Print the terms of uninterpreted type in array a
 * - n = size of the array
 */
static void eval_pp_constant_assignments(yices_pp_t *printer, evaluator_t *eval, const term_t *a, uint32_t n) {
  model_t *model;
  term_table_t *terms;
  char *name;
  value_unint_t *d;
  uint32_t i;
  term_t t;
  value_t c;
  type_kind_t tau;

  model = eval->model;
  terms = model->terms;

  for (i=0; i<n; i++) {
    t = a[i];
    tau = term_type_kind(terms, t);
    if (tau == UNINTERPRETED_TYPE || tau == SCALAR_TYPE || tau == INSTANCE_TYPE) {
      c = eval_in_model(eval, t);
      d = vtbl_unint(&model->vtbl, c);
      name = term_name(terms, t);
      assert(name != NULL);
      if (d->name == NULL || strcmp(name, d->name) != 0) {
        pp_open_block(printer, PP_OPEN_EQ);
        pp_string(printer, name);
        vtbl_pp_object(printer, &model->vtbl, c);
        pp_close_block(printer, true);
      }
    }
  }
}


/*
 * Print the function terms in array a
 * - n = size of the array
 */
static void eval_pp_function_assignments(yices_pp_t *printer, evaluator_t *eval, const term_t *a, uint32_t n) {
  model_t *model;
  term_table_t *terms;
  value_fun_t *fun;
  char *name;
  term_t t;
  value_t c;
  uint32_t i;

  model = eval->model;
  terms = model->terms;

  // first pass: function objects
  for (i=0; i<n; i++) {
    t = a[i];
    if (is_function_term(terms, t)) {
      /*
       * t is mapped to a function object fun if t and fun have
       * different names, we print (= <t's name> <fun 's name>)
       * otherwise we print nothing and store fun in the vtbl's queue
       * (fun's map definition will be printed later).
       */
      c = eval_in_model(eval, t);
      name = term_name(terms, t);
      assert(name != NULL);
      if (object_is_function(&model->vtbl, c)) {
        fun = vtbl_function(&model->vtbl, c);
        if (fun->name == NULL || strcmp(name, fun->name) != 0) {
          pp_open_block(printer, PP_OPEN_EQ);
          pp_string(printer, name);
          vtbl_pp_object(printer, &model->vtbl, c);
          pp_close_block(printer, true);
        } else {
	  vtbl_push_object(&model->vtbl, c);
        }
      }
    }
  }

  /*
   * second pass: deal with update objects
   */
  for (i=0; i<n; i++) {
    t = a[i];
    if (is_function_term(terms, t)) {
      c = eval_in_model(eval, t);
      name = term_name(terms, t);
      assert(name != NULL);
      if (object_is_update(&model->vtbl, c)) {
        vtbl_normalize_and_pp_update(printer, &model->vtbl, name, c, true);
      }
    }
  }
}


/*
 * Print the values of all terms in array a
 * - n = number of terms in a
 */
void eval_pp_terms(yices_pp_t *printer, evaluator_t *eval, const term_t *a, uint32_t n) {
  eval_pp_bool_assignments(printer, eval, a, n);
  eval_pp_arithmetic_assignments(printer, eval, a, n);
  eval_pp_bitvector_assignments(printer, eval, a, n);
  eval_pp_constant_assignments(printer, eval, a, n);
  eval_pp_tuple_assignments(printer, eval, a, n);
  eval_pp_function_assignments(printer, eval, a, n);
  vtbl_pp_queued_functions(printer, eval->vtbl, true);
}


/*
 * Print model, including the aliased terms
 * - one line per term
 * - if model->has_alias is true, then the value of all terms in
 *   the alias table is displayed
 * - if model->has_alias is false, then this is the same as model_pp
 */
void model_pp_full(yices_pp_t *printer, model_t *model) {
  evaluator_t eval;
  ivector_t v;
  term_t *a;
  uint32_t n;

  if (model->has_alias && model->alias_map != NULL) {
    init_evaluator(&eval, model);

    // collect all terms that have a value
    init_ivector(&v, 0);
    model_collect_terms(model, true, model->terms, term_to_print, &v);

    // compute their values
    eval_terms_in_model(&eval, v.data, v.size);

    n = v.size;
    a = v.data;

    // second pass: collect all uninterpreted terms that
    // have a value in model or in the evaluator.
    ivector_reset(&v);
    model_collect_terms(model, false, model->terms, term_to_print, &v);
    evaluator_collect_cached_terms(&eval, model->terms, term_to_print, &v);

    // sort the terms so that we have consistent printouts with different
    // algorithms
    int_array_sort(a, n);

    eval_pp_bool_assignments(printer, &eval, a, n);
    eval_pp_arithmetic_assignments(printer, &eval, a, n);
    eval_pp_bitvector_assignments(printer, &eval, a, n);
    eval_pp_constant_assignments(printer, &eval, a, n);
    eval_pp_tuple_assignments(printer, &eval, a, n);
    eval_pp_function_assignments(printer, &eval, a, n);
    vtbl_pp_queued_functions(printer, eval.vtbl, true);

    delete_evaluator(&eval);
    delete_ivector(&v);
  } else {
    model_pp(printer, model);
  }
}

