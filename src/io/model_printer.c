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
 * Print the assignment for all arithmetic terms in array a
 * - n = size of the array
 */
static void model_print_arithmetic_assignments(FILE *f, model_t *model, term_t *a, uint32_t n) {
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
 * Print the terms of uninterpreted type in array a
 * - n = size of the array
 */
static void model_print_constant_assignments(FILE *f, model_t *model, term_t *a, uint32_t n) {
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
    if (tau == UNINTERPRETED_TYPE || tau == SCALAR_TYPE) {
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
static void model_print_tuple_assignments(FILE *f, model_t *model, term_t *a, uint32_t n) {
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
static void model_print_function_assignments(FILE *f, model_t *model, term_t *a, uint32_t n) {
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
  model_print_arithmetic_assignments(f, model, a, n);
  model_print_bitvector_assignments(f, model, a, n);
  model_print_constant_assignments(f, model, a, n);
  model_print_tuple_assignments(f, model, a, n);
  model_print_function_assignments(f, model, a, n);
  vtbl_print_queued_functions(f, &model->vtbl, true);
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
 * Print the assignment for all arithmetic terms in array a
 * - n = size of the array
 */
static void eval_print_arithmetic_assignments(FILE *f, evaluator_t *eval, term_t *a, uint32_t n) {
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
 * Print the assignment for all tuple terms in array a
 * - n = size of the array
 */
static void eval_print_tuple_assignments(FILE *f, evaluator_t *eval, term_t *a, uint32_t n) {
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
static void eval_print_constant_assignments(FILE *f, evaluator_t *eval, term_t *a, uint32_t n) {
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
    if (tau == UNINTERPRETED_TYPE || tau == SCALAR_TYPE) {
      c = eval_in_model(eval, t);
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
 * Print the function terms in array a
 * - n = size of the array
 */
static void eval_print_function_assignments(FILE *f, evaluator_t *eval, term_t *a, uint32_t n) {
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
    eval_print_arithmetic_assignments(f, &eval, a, n);
    eval_print_bitvector_assignments(f, &eval, a, n);
    eval_print_constant_assignments(f, &eval, a, n);
    eval_print_tuple_assignments(f, &eval, a, n);
    eval_print_function_assignments(f, &eval, a, n);
    vtbl_print_queued_functions(f, &model->vtbl, true);
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
 * Print the assignment for all arithmetic terms in array a
 * - n = size of the array
 */
static void model_pp_arithmetic_assignments(yices_pp_t *printer, model_t *model, term_t *a, uint32_t n) {
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
 * Print the terms of uninterpreted type in array a
 * - n = size of the array
 */
static void model_pp_constant_assignments(yices_pp_t *printer, model_t *model, term_t *a, uint32_t n) {
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
    if (tau == UNINTERPRETED_TYPE || tau == SCALAR_TYPE) {
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
static void model_pp_tuple_assignments(yices_pp_t *printer, model_t *model, term_t *a, uint32_t n) {
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
static void model_pp_function_assignments(yices_pp_t *printer, model_t *model, term_t *a, uint32_t n) {
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
  model_pp_arithmetic_assignments(printer, model, a, n);
  model_pp_bitvector_assignments(printer, model, a, n);
  model_pp_constant_assignments(printer, model, a, n);
  model_pp_tuple_assignments(printer, model, a, n);
  model_pp_function_assignments(printer, model, a, n);
  vtbl_pp_queued_functions(printer, &model->vtbl, true);
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
 * Print the assignment for all arithmetic terms in array a
 * - n = size of the array
 */
static void eval_pp_arithmetic_assignments(yices_pp_t *printer, evaluator_t *eval, term_t *a, uint32_t n) {
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
 * Print the assignment for all tuple terms in array a
 * - n = size of the array
 */
static void eval_pp_tuple_assignments(yices_pp_t *printer, evaluator_t *eval, term_t *a, uint32_t n) {
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
static void eval_pp_constant_assignments(yices_pp_t *printer, evaluator_t *eval, term_t *a, uint32_t n) {
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
    if (tau == UNINTERPRETED_TYPE || tau == SCALAR_TYPE) {
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
static void eval_pp_function_assignments(yices_pp_t *printer, evaluator_t *eval, term_t *a, uint32_t n) {
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
    eval_pp_arithmetic_assignments(printer, &eval, a, n);
    eval_pp_bitvector_assignments(printer, &eval, a, n);
    eval_pp_constant_assignments(printer, &eval, a, n);
    eval_pp_tuple_assignments(printer, &eval, a, n);
    eval_pp_function_assignments(printer, &eval, a, n);
    vtbl_pp_queued_functions(printer, &model->vtbl, true);
    delete_evaluator(&eval);
    delete_ivector(&v);
  } else {
    model_pp(printer, model);
  }
}



