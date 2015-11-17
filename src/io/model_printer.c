/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
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
static void model_print_bool_assignments(FILE *f, model_t *model, term_t *a, uint32_t n) {
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
 * Print the assignment for all bitvector terms in array a
 * - n = size of the array
 */
static void model_print_bitvector_assignments(FILE *f, model_t *model, term_t *a, uint32_t n) {
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
 * Filter function for model_collect_terms
 * - aux is a term table
 * - return true if term t should be printed in the assignments (i.e., t has a name)
 */
static bool term_to_print(void *aux, term_t t) {
  return term_kind(aux, t) == UNINTERPRETED_TERM && term_name(aux, t) != NULL;
}


/*
 * Print the model->map table
 */
void model_print(FILE *f, model_t *model) {
  ivector_t v;
  term_t *a;
  uint32_t n;

  init_ivector(&v, 0);
  model_collect_terms(model, false, model->terms, term_to_print, &v);

  n = v.size;
  a = v.data;
  model_print_bool_assignments(f, model, a, n);
  model_print_bitvector_assignments(f, model, a, n);

  delete_ivector(&v);
}




/*
 * FULL MODEL: USE EVALUATOR
 */

/*
 * Print the assignment for t as computed by the evaluator
 * - t must be a valid, uninterpreted term
 */
static void eval_print_term_value(FILE *f, evaluator_t *eval, term_t t) {
  model_t *model;
  char *name;
  value_t v;

  assert(term_kind(eval->model->terms, t) == UNINTERPRETED_TERM);
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
 * Print the assignment for all boolean terms in array a
 * - n = size of a
 */
static void eval_print_bool_assignments(FILE *f, evaluator_t *eval, term_t *a, uint32_t n) {
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
 * Print the assignment for all bitvector terms in array a
 * - n = size of the array
 */
static void eval_print_bitvector_assignments(FILE *f, evaluator_t *eval, term_t *a, uint32_t n) {
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
 * Print model, including the aliased terms
 * - one line per term
 * - if model->has_alias is true, then the value of all terms in
 *   the alias table is displayed
 * - if model->has_alias is false, then this is the same as model_print
 */
void model_print_full(FILE *f, model_t *model) {
  evaluator_t eval;
  ivector_t v;
  term_t *a;
  uint32_t n;

  if (model->has_alias && model->alias_map != NULL) {
    init_evaluator(&eval, model);

    // collect all terms that have a name
    init_ivector(&v, 0);
    model_collect_terms(model, true, model->terms, term_to_print, &v);

    n = v.size;
    a = v.data;
    eval_print_bool_assignments(f, &eval, a, n);
    eval_print_bitvector_assignments(f, &eval, a, n);
    delete_evaluator(&eval);
    delete_ivector(&v);
  } else {
    model_print(f, model);
  }
}




/*
 * PRETTY PRINTING
 */

/*
 * Print the assignment for i in model
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
static void model_pp_bool_assignments(yices_pp_t *printer, model_t *model, term_t *a, uint32_t n) {
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
 * Print the assignment for all bitvector terms in array a
 * - n = size of the array
 */
static void model_pp_bitvector_assignments(yices_pp_t *printer, model_t *model, term_t *a, uint32_t n) {
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
  model_pp_bool_assignments(printer, model, a, n);
  model_pp_bitvector_assignments(printer, model, a, n);
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

  assert(term_kind(eval->model->terms, t) == UNINTERPRETED_TERM);
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
 * Print the assignment for all boolean terms in array a
 * - n = size of a
 */
static void eval_pp_bool_assignments(yices_pp_t *printer, evaluator_t *eval, term_t *a, uint32_t n) {
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
 * Print the assignment for all bitvector terms in array a
 * - n = size of the array
 */
static void eval_pp_bitvector_assignments(yices_pp_t *printer, evaluator_t *eval, term_t *a, uint32_t n) {
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
 * Print model, including the aliased terms
 * - one line per term
 * - if model->has_alias is true, then the value of all terms in
 *   the alias table is displayed
 * - if model->has_alias is false, then this is the same as model_print
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

    n = v.size;
    a = v.data;
    eval_pp_bool_assignments(printer, &eval, a, n);
    eval_pp_bitvector_assignments(printer, &eval, a, n);

    delete_evaluator(&eval);
    delete_ivector(&v);
  } else {
    model_pp(printer, model);
  }
}



