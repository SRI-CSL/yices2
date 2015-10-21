/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * SUPPORT FOR EXISTS/FORALL SOLVING
 */

#if defined(CYGWIN) || defined(MINGW)
#ifndef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__ __declspec(dllexport)
#endif
#endif

#include <inttypes.h>

#include "context/context.h"
#include "exists_forall/efsolver.h"
#include "model/literal_collector.h"    //get_implicant     (pre qf normalization)
#include "model/projection.h"           //project_literals  (quantifier elimination)
#include "terms/term_substitution.h"
#include "utils/index_vectors.h"

#include "yices.h"


#define EF_VERBOSE 0

/*
 * PRINT STUFF
 */

/*
 * Print solution found by the ef solver
 */
void print_ef_solution(FILE *f, ef_solver_t *solver) {
  ef_prob_t *prob;
  uint32_t i, n;

  prob = solver->prob;
  n = ef_prob_num_evars(prob);

  for (i=0; i<n; i++) {
    fprintf(f, "%s := ", yices_get_term_name(prob->all_evars[i]));
    yices_pp_term(f, solver->evalue[i], 100, 1, 10);
  }
}


/*
 * Show witness found for constraint i
 */
void print_forall_witness(FILE *f, ef_solver_t *solver, uint32_t i) {
  ef_prob_t *prob;
  ef_cnstr_t *cnstr;
  uint32_t j, n;

  prob = solver->prob;
  assert(i < ef_prob_num_constraints(prob));
  cnstr = prob->cnstr + i;

  n = ef_constraint_num_uvars(cnstr);
  for (j=0; j<n; j++) {
    fprintf(f, "%s := ", yices_get_term_name(cnstr->uvars[j]));
    yices_pp_term(f, solver->uvalue_aux.data[j], 100, 1, 10);
  }
}


/*
 * Print the full map:
 * - the variables are in solver->all_vars
 * - their values are in solver->all_values
 */
void print_full_map(FILE *f, ef_solver_t *solver) {
  uint32_t i, n;

  n = solver->all_vars.size;
  assert(n == solver->all_values.size);
  for (i=0; i<n; i++) {
    fprintf(f, "%s := ", yices_get_term_name(solver->all_vars.data[i]));
    yices_pp_term(f, solver->all_values.data[i], 100, 1, 10);
  }
  fprintf(f, "(%"PRIu32" variables)\n", n);
}


/*
 * GLOBAL PROCEDURES
 */

/*
 * Initialize solver:
 * - prob = problem descriptor
 * - logic/arch/parameters = for context initialization and check
 */
void init_ef_solver(ef_solver_t *solver, ef_prob_t *prob, smt_logic_t logic, context_arch_t arch) {
  uint32_t n;

  solver->prob = prob;
  solver->logic = logic;
  solver->arch = arch;
  solver->status = EF_STATUS_IDLE;
  solver->error_code = 0;

  solver->parameters = NULL;
  solver->option = EF_GEN_BY_SUBST_OPTION;
  solver->max_samples = 0;
  solver->max_iters = 0;
  solver->scan_idx = 0;

  solver->exists_context = NULL;
  solver->forall_context = NULL;
  solver->exists_model = NULL;

  n = ef_prob_num_evars(prob);
  assert(n <= UINT32_MAX/sizeof(term_t));
  solver->evalue = (term_t *) safe_malloc(n * sizeof(term_t));

  n = ef_prob_num_uvars(prob);
  assert(n <= UINT32_MAX/sizeof(term_t));
  solver->uvalue = (term_t *) safe_malloc(n * sizeof(term_t));


  solver->full_model = NULL;
  init_ivector(&solver->implicant, 20);
  init_ivector(&solver->projection, 20);

  init_ivector(&solver->evalue_aux, 64);
  init_ivector(&solver->uvalue_aux, 64);
  init_ivector(&solver->all_vars, 64);
  init_ivector(&solver->all_values, 64);

  solver->trace = NULL;
}


/*
 * Delete the whole thing
 */
void delete_ef_solver(ef_solver_t *solver) {
  if (solver->exists_context != NULL) {
    delete_context(solver->exists_context);
    safe_free(solver->exists_context);
    solver->exists_context = NULL;
  }
  if (solver->forall_context != NULL) {
    delete_context(solver->forall_context);
    safe_free(solver->forall_context);
    solver->forall_context = NULL;
  }
  if (solver->exists_model != NULL) {
    yices_free_model(solver->exists_model);
    solver->exists_model = NULL;
  }

  safe_free(solver->evalue);
  safe_free(solver->uvalue);
  solver->evalue = NULL;
  solver->uvalue = NULL;

  if (solver->full_model != NULL) {
    yices_free_model(solver->full_model);
    solver->full_model = NULL;
  }
  delete_ivector(&solver->implicant);
  delete_ivector(&solver->projection);

  delete_ivector(&solver->evalue_aux);
  delete_ivector(&solver->uvalue_aux);
  delete_ivector(&solver->all_vars);
  delete_ivector(&solver->all_values);
}



/*
 * Set the trace:
 * - the current tracer must be NULL.
 */
void ef_solver_set_trace(ef_solver_t *solver, tracer_t *trace) {
  assert(solver->trace == NULL);
  solver->trace = trace;
}




/*
 * OPERATIONS ON THE EXISTS CONTEXT
 */

/*
 * Allocate and initialize the exists context
 */
static void init_exists_context(ef_solver_t *solver) {
  context_t *ctx;

  assert(solver->exists_context == NULL);
  ctx = (context_t *) safe_malloc(sizeof(context_t));
  init_context(ctx, solver->prob->terms, solver->logic, CTX_MODE_MULTICHECKS, solver->arch, false); // qflag is false
  solver->exists_context = ctx;
  if (solver->trace != NULL) {
    context_set_trace(ctx, solver->trace);
  }
}

/*
 * Assert all the conditions from prob into ctx
 * - return the internalization code
 */
static int32_t exists_context_assert_conditions(ef_solver_t *solver) {
  context_t *ctx;
  uint32_t n;

  ctx = solver->exists_context;

  assert(ctx != NULL && context_status(ctx) == STATUS_IDLE);

  n = ef_prob_num_conditions(solver->prob);
  return assert_formulas(ctx, n, solver->prob->conditions);
}


/*
 * Add  assertion f to the exists context
 * - return the internalization code
 * - the exists context must not be UNSAT
 */
static int32_t update_exists_context(ef_solver_t *solver, term_t f) {
  context_t *ctx;
  smt_status_t status;
  int32_t code;

  ctx = solver->exists_context;

  assert(ctx != NULL && is_boolean_term(ctx->terms, f));

  status = context_status(ctx);
  switch (status) {
  case STATUS_SAT:
  case STATUS_UNKNOWN:
    context_clear(ctx);
    assert(context_status(ctx) == STATUS_IDLE);
  case STATUS_IDLE:
    code = assert_formula(ctx, f);
    break;

  default:
    code = INTERNAL_ERROR; // should not happen
    break;
  }

  return code;
}


/*
 * SUBSTITUTION
 */

/*
 * Apply the substitution defined by var and value to term t
 * - n = size of arrays var and value
 * - return code < 0 means that an error occurred during the substitution
 *   (cf. apply_term_subst in term_substitution.h).
 */
static term_t ef_substitution(ef_prob_t *prob, term_t *var, term_t *value, uint32_t n, term_t t) {
  term_subst_t subst;
  term_t g;

  init_term_subst(&subst, prob->manager, n, var, value);
  g = apply_term_subst(&subst, t);
  delete_term_subst(&subst);

  return g;
}





/*
 * FORALL CONTEXT
 */

/*
 * Allocate and initialize it (prior to sampling)
 */
static void init_forall_context(ef_solver_t *solver) {
  context_t *ctx;

  assert(solver->forall_context == NULL);
  ctx = (context_t *) safe_malloc(sizeof(context_t));
  init_context(ctx, solver->prob->terms, solver->logic, CTX_MODE_MULTICHECKS, solver->arch, false);
  solver->forall_context = ctx;
  if (solver->trace != NULL) {
    context_set_trace(ctx, solver->trace);
  }
}


/*
 * Assert (B and not C) in ctx
 * - return the assertion code
 */
static int32_t forall_context_assert(ef_solver_t *solver, term_t b, term_t c) {
  context_t *ctx;
  term_t assertions[2];

  ctx = solver->forall_context;

  assert(ctx != NULL && context_status(ctx) == STATUS_IDLE);
  assert(is_boolean_term(ctx->terms, b) && is_boolean_term(ctx->terms, c));

  assertions[0] = b;
  assertions[1] = opposite_term(c);
  return assert_formulas(ctx, 2, assertions);
}


/*
 * Free or reset the forall_context:
 * - if flag del is true: delete
 * - otherwise, just reset
 */
static void clear_forall_context(ef_solver_t *solver, bool del) {
  assert(solver->forall_context != NULL);
  if (del) {
    delete_context(solver->forall_context);
    safe_free(solver->forall_context);
    solver->forall_context = NULL;
  } else {
    reset_context(solver->forall_context);
  }
}


/*
 * Get the forall_context: return it if it's not NULL
 * allocate and initialize it otherwise.
 */
static context_t *get_forall_context(ef_solver_t *solver) {
  if (solver->forall_context == NULL) {
    init_forall_context(solver);
  }
  return solver->forall_context;
}





/*
 * SAT SOLVING
 */

/*
 * Check satisfiability and get a model
 * - ctx = the context
 * - parameters = heuristic settings (if parameters is NULL, the defaults are used)
 * - var = array of n uninterpreted terms
 * - n = size of array evar and value
 * Output parameters;
 * - value = array of n terms (to receive the value of each var)
 * - model = to export the model (if model is NULL, nothing is exported)
 *
 * The return code is as in check_context:
 * 1) if code = STATUS_SAT then the context is satisfiable
 *    and a model is stored in value[0 ... n-1]
 *    - value[i] = a constant term mapped to evar[i] in the model
 * 2) code = STATUS_UNSAT: not satisfiable
 *
 * 3) other codes report an error of some kind or STATUS_INTERRUPTED
 */
static smt_status_t satisfy_context(context_t *ctx, const param_t *parameters, term_t *var, uint32_t n, term_t *value, model_t **model) {
  smt_status_t stat;
  model_t *mdl;
  int32_t code;

  assert(context_status(ctx) == STATUS_IDLE);

  stat = check_context(ctx, parameters);
  switch (stat) {
  case STATUS_SAT:
  case STATUS_UNKNOWN:
    mdl = yices_get_model(ctx, true);
    code = yices_term_array_value(mdl, n, var, value);
    if (model != NULL) {
      *model = mdl;
    } else {
      yices_free_model(mdl);
    }

    if (code < 0) {
      // can't convert the model to constant terms
      stat = STATUS_ERROR;
    }
    break;

  default:
    // can't build a model
    break;
  }

  return stat;
}



/*
 * Check satisfiability of the exists_context
 * - first free the exists_model if non-NULL
 * - if SAT build a model (in solver->evalue) and store the exists_model
 */
static smt_status_t ef_solver_check_exists(ef_solver_t *solver) {
  term_t *evar;
  uint32_t n;

  if (solver->exists_model != NULL) {
    yices_free_model(solver->exists_model);
    solver->exists_model = NULL;
  }

  evar = solver->prob->all_evars;
  n = iv_len(evar);
  return satisfy_context(solver->exists_context, solver->parameters, evar, n, solver->evalue, &solver->exists_model);
}



/*
 * Test the current exists model using universal constraint i
 * - i must be a valid index (i.e., 0 <= i < solver->prob->num_cnstr)
 * - this checks the assertion B_i and not C_i after replacing existential
 *   variables by their values (stored in evalue)
 * - return code:
 *   if STATUS_SAT (or STATUS_UNKNOWN): a model of (B_i and not C_i)
 *   is found and stored in uvalue_aux
 *   if STATUS_UNSAT: no model found (current exists model is good as
 *   far as constraint i is concerned)
 *   anything else: an error or interruption
 *
 * - if we get an error or interruption, solver->status is updated
 *   otherwise, it is kept as is (should be EF_STATUS_SEARCHING)
 */
static smt_status_t ef_solver_test_exists_model(ef_solver_t *solver, uint32_t i) {
  context_t *forall_ctx;
  ef_cnstr_t *cnstr;
  term_t *value;
  term_t g;
  uint32_t n;
  int32_t code;
  smt_status_t status;

  assert(i < ef_prob_num_constraints(solver->prob));
  cnstr = solver->prob->cnstr + i;

  n = ef_prob_num_evars(solver->prob);
  g = ef_substitution(solver->prob, solver->prob->all_evars, solver->evalue, n, cnstr->guarantee);
  if (g < 0) {
    // error in substitution
    solver->status = EF_STATUS_SUBST_ERROR;
    solver->error_code = g;
    return STATUS_ERROR;
  }

  /*
   * make uvalue_aux large enough
   */
  n = ef_constraint_num_uvars(cnstr);
  resize_ivector(&solver->uvalue_aux, n);
  solver->uvalue_aux.size = n;
  value = solver->uvalue_aux.data;

  forall_ctx = get_forall_context(solver);

  code = forall_context_assert(solver, cnstr->assumption, g); // assert B_i(Y_i) and not g(Y_i)
  if (code == CTX_NO_ERROR) {
    status = satisfy_context(forall_ctx, solver->parameters, cnstr->uvars, n, value, NULL);
    switch (status) {
    case STATUS_SAT:
    case STATUS_UNKNOWN:
    case STATUS_UNSAT:
      break;

    case STATUS_INTERRUPTED:
      solver->status = EF_STATUS_INTERRUPTED;
      break;

    default:
      solver->status = EF_STATUS_CHECK_ERROR;
      solver->error_code = status;
      break;
    }

  } else if (code == TRIVIALLY_UNSAT) {
    assert(context_status(forall_ctx) == STATUS_UNSAT);
    status = STATUS_UNSAT;

  } else {
    // error in assertion
    solver->status = EF_STATUS_ASSERT_ERROR;
    solver->error_code = code;
    status = STATUS_ERROR;
  }

  clear_forall_context(solver, true);

  return status;
}



/*
 * PROJECTION
 */

/*
 * Search for x in sorted array v
 */
static int32_t find_elem(int32_t *v, int32_t x) {
  uint32_t i, j, k;

  i = 0;
  j = iv_len(v);
  while (i < j) {
    k = (i + j) >> 1;
    assert(i <= k && k < j);
    if (v[k] == x) return k;
    if (v[k] < x) {
      i = k+1;
    } else {
      j = k;
    }
  }

  return -1; // not found
}


/*
 * Restrict a model defined by var and value to subvar
 * - the result is stored in subvalue
 * - n = size of arrays subvar and subvalue
 * - preconditions:
 *   var is a sorted index vector
 *   every element of subvar occurs in var
 *   value has the same size as var
 */
static void project_model(int32_t *var, term_t *value, term_t *subvar, term_t *subvalue, uint32_t n) {
  uint32_t i;
  int32_t k;

  for (i=0; i<n; i++) {
    k = find_elem(var, subvar[i]);
    assert(k >= 0 && subvar[i] == var[k]);
    subvalue[i] = value[k];
  }
}


/*
 * Project model onto a subset of the existential variables
 * - value[i] = exist model = array of constant values
 * - evar = an array of n existential variables: every element of evar occurs in ef->all_evars
 * - then this function builds the model restricted to evar into array eval
 *
 * Assumption:
 * - value[i] = value mapped to ef->all_evars[i] for i=0 ... num_evars-1
 * - every x in sub_var occurs somewhere in ef->all_evars
 * - then if evar[i] = x and x is equal to all_evar[k] the function copies
 *   value[k] into eval[i]
 */
static void ef_project_exists_model(ef_prob_t *prob, term_t *value, term_t *evar, term_t *eval, uint32_t n) {
  project_model(prob->all_evars, value, evar, eval, n);
}




/*
 * PRE SAMPLING
 */

/*
 * Sampling for the i-th constraint in solver->prob
 * - search for at most max_samples y's that satisfy the assumption of constraint i in prob
 * - for each such y, add a new constraint to the exist context ctx
 * - max_samples = bound on the number of samples to take (must be positive)
 *
 * Constraint i is of the form
 *    (FORALL Y_i: B_i(Y_i) => C(X_i, Y_i))
 * - every sample is a model y_i that satisfies B_i.
 * - for each sample, we learn that any good candidate X_i must satisfy C(X_i, y_i).
 *   So we add the constraint  C(X_i, y_i) to ctx.
 *
 * Update the solver->status to
 * - EF_STATUS_UNSAT if the exits context is trivially unsat
 * - EF_STATUS_..._ERROR if something goes wrong
 * - EF_STATUS_INTERRUPTED if a call to check/recheck context is interrupted
 * keep it unchanged otherwise (should be EF_STATUS_SEARCHING).
 */
static void ef_sample_constraint(ef_solver_t *solver, uint32_t i) {
  context_t *sampling_ctx;
  ef_cnstr_t *cnstr;
  term_t *value;
  uint32_t nvars, samples;
  int32_t ucode, ecode;
  smt_status_t status;
  term_t cnd;

  assert(i < ef_prob_num_constraints(solver->prob) && solver->max_samples > 0);

  cnstr = solver->prob->cnstr + i;

  /*
   * make uvalue_aux large enough
   * its size = number of universal variables in constraint i
   */
  nvars = ef_constraint_num_uvars(cnstr);
  resize_ivector(&solver->uvalue_aux, nvars);
  solver->uvalue_aux.size = nvars;
  value = solver->uvalue_aux.data;

  samples = solver->max_samples;

  /*
   * assert the assumption in the forall context
   */
  sampling_ctx = get_forall_context(solver);
  ucode = assert_formula(sampling_ctx, cnstr->assumption);
  while (ucode == CTX_NO_ERROR) {
    tprintf(solver->trace, 4, "(EF: start: sampling universal variables)\n");
    status = satisfy_context(sampling_ctx, solver->parameters, cnstr->uvars, nvars, value, NULL);
    switch (status) {
    case STATUS_SAT:
    case STATUS_UNKNOWN:
      // learned condition on X:
      cnd = ef_substitution(solver->prob, cnstr->uvars, value, nvars, cnstr->guarantee);
      if (cnd < 0) {
	solver->status = EF_STATUS_SUBST_ERROR;
	solver->error_code = cnd;
	goto done;
      }
      ecode = update_exists_context(solver, cnd);
      if (ecode < 0) {
	solver->status = EF_STATUS_ASSERT_ERROR;
	solver->error_code = ecode;
	goto done;
      }
      if (ecode == TRIVIALLY_UNSAT) {
	solver->status = EF_STATUS_UNSAT;
	goto done;
      }
      break;

    case STATUS_UNSAT:
      // no more samples for this constraints
      goto done;

    case STATUS_INTERRUPTED:
      solver->status = EF_STATUS_INTERRUPTED;
      goto done;

    default:
      solver->status = EF_STATUS_CHECK_ERROR;
      solver->error_code = status;
      goto done;
    }

    samples --;
    if (samples == 0) goto done;

    ucode = assert_blocking_clause(sampling_ctx);
  }

  /*
   * if ucode < 0, something went wrong in assert_formula
   * or in assert_blocking_clause
   */
  if (ucode < 0) {
    solver->status = EF_STATUS_ASSERT_ERROR;
    solver->error_code = ucode;
  }

 done:
  clear_forall_context(solver, true);
}




/*
 * FIRST EXISTS MODELS
 */

/*
 * Initialize the exists context
 * - asserts all conditions from solver->prob
 * - if max_samples is positive, also apply pre-sampling to all the universal constraints
 *
 * - solver->status is set as follows
 *   EF_STATUS_SEARCHING: means not solved yet
 *   EF_STATUS_UNSAT: if the exists context is trivially UNSAT
 *   EF_STATUS_..._ERROR: if something goes wrong
 *   EF_STATUS_INTERRUPTED if the pre-sampling is interrupted
 */
static void ef_solver_start(ef_solver_t *solver) {
  int32_t code;
  uint32_t i, n;

  assert(solver->status == EF_STATUS_IDLE);

  solver->status = EF_STATUS_SEARCHING;

  init_exists_context(solver);
  code = exists_context_assert_conditions(solver); // add all conditions
  if (code < 0) {
    // assertion error
    solver->status = EF_STATUS_ASSERT_ERROR;
    solver->error_code = code;
  } else if (code == TRIVIALLY_UNSAT) {
    solver->status = EF_STATUS_UNSAT;
  } else if (solver->max_samples > 0) {
    /*
     * run the pre-sampling stuff
     */
    n = ef_prob_num_constraints(solver->prob);
    for (i=0; i<n; i++) {
      ef_sample_constraint(solver, i);
      if (solver->status != EF_STATUS_SEARCHING) break;
    }
  }
}



/*
 * IMPLICANT CONSTRUCTION
 */

/*
 * Merge the exists and forall variables of constraint i
 * - store the variables in solver->all_vars
 * - store their values in solver->all_values
 */
static void ef_build_full_map(ef_solver_t *solver, uint32_t i) {
  ef_cnstr_t *cnstr;
  ivector_t *v;
  uint32_t n;

  assert(i < ef_prob_num_constraints(solver->prob));
  cnstr = solver->prob->cnstr + i;

  // collect all variables of cnstr in solver->all_vars
  v = &solver->all_vars;
  ivector_reset(v);
  n = ef_constraint_num_evars(cnstr);
  ivector_add(v, cnstr->evars, n);
  n = ef_constraint_num_uvars(cnstr);
  ivector_add(v, cnstr->uvars, n);

  // project the evalues onto the exists variable of constraint i
  // store the results in all_values
  v = &solver->all_values;
  n = ef_constraint_num_evars(cnstr);
  resize_ivector(v, n);
  v->size = n;
  ef_project_exists_model(solver->prob, solver->evalue, cnstr->evars, v->data, n);

  // copy the uvalues for constraint i (from uvalue_aux to v)
  n = ef_constraint_num_uvars(cnstr);
  assert(n == solver->uvalue_aux.size);
  ivector_add(v, solver->uvalue_aux.data, n);

#if EF_VERBOSE
  printf("Full map\n");
  print_full_map(stdout, solver);
  fflush(stdout);
#endif
}




/*
 * GENERALIZATION FROM UNIVERSAL MODELS
 */

/*
 * Option 1: don't generalize:
 * - build the formula (or (/= var[0] value[0]) ... (/= var[n-1] value[n-1]))
 */
static term_t ef_generalize1(ef_prob_t *prob, term_t *var, term_t *value, uint32_t n) {
  return mk_array_neq(prob->manager, n, var, value);
}


/*
 * Option 2: generalize by substitution
 * - return (prob->cnstr[i].guarantee with y := value)
 */
static term_t ef_generalize2(ef_prob_t *prob, uint32_t i, term_t *value) {
  ef_cnstr_t *cnstr;
  uint32_t n;
  term_t g;

  assert(i < ef_prob_num_constraints(prob));
  cnstr = prob->cnstr + i;
  n = ef_constraint_num_uvars(cnstr);
  g = ef_substitution(prob, cnstr->uvars, value, n, cnstr->guarantee);
  return g;
}


/*
 * Option 3: generalize by computing an implicant then
 * applying projection.
 */
static term_t ef_generalize3(ef_solver_t *solver, uint32_t i) {
  model_t *mdl;
  ef_cnstr_t *cnstr;
  ivector_t *v, *w;
  term_t a[2];
  uint32_t n;
  int32_t code;
  proj_flag_t pflag;
  term_t result;

  assert(i < ef_prob_num_constraints(solver->prob));

  // free the current full model if any
  if (solver->full_model != NULL) {
    yices_free_model(solver->full_model);
    solver->full_model = NULL;
  }

  // build the full_map and the corresponding model.
  ef_build_full_map(solver, i);
  n = solver->all_vars.size;
  assert(n == solver->all_values.size);
  mdl = yices_model_from_map(n, solver->all_vars.data, solver->all_values.data);
  if (mdl == NULL) {
    // error in the model construction
    solver->status = EF_STATUS_MDL_ERROR;
    solver->error_code = yices_error_code();
    return NULL_TERM;
  }
  solver->full_model = mdl;


  // Constraint
  cnstr = solver->prob->cnstr + i;
  a[0] = cnstr->assumption;                 // B(y)
  a[1] = opposite_term(cnstr->guarantee);   // not C(x, y)


#if EF_VERBOSE
  printf("Constraint:\n");
  yices_pp_term_array(stdout, 2, a, 120, UINT32_MAX, 0, 0);
  printf("(%"PRIu32" literals)\n", 2);
#endif

  // Compute the implicant
  v = &solver->implicant;
  ivector_reset(v);
  code = get_implicant(mdl, solver->prob->manager, LIT_COLLECTOR_ALL_OPTIONS, 2, a, v);
  if (code < 0) {
    solver->status = EF_STATUS_IMPLICANT_ERROR;
    solver->error_code = code;
    return NULL_TERM;
  }

#if EF_VERBOSE
  printf("Implicant:\n");
  yices_pp_term_array(stdout, v->size, v->data, 120, UINT32_MAX, 0, 0);
  printf("(%"PRIu32" literals)\n", v->size);
#endif

  // Projection
  w = &solver->projection;
  ivector_reset(w);
  n = ef_constraint_num_uvars(cnstr);

#if EF_VERBOSE
  printf("(%"PRIu32" universals)\n", n);
  yices_pp_term_array(stdout, n, cnstr->uvars, 120, UINT32_MAX, 0, 0);
#endif

  
  pflag = project_literals(mdl, solver->prob->manager, v->size, v->data, n, cnstr->uvars, w);

  if (pflag != PROJ_NO_ERROR) {
    solver->status = EF_STATUS_PROJECTION_ERROR;
    solver->error_code = pflag;
    return NULL_TERM;
  }

#if EF_VERBOSE
  printf("Projection:\n");
  yices_pp_term_array(stdout, w->size, w->data, 120, UINT32_MAX, 0, 0);
  printf("(%"PRIu32" literals)\n", w->size);
#endif

  switch (w->size) {
  case 0:
    result = true_term;
    break;

  case 1:
    result = w->data[0];
    break;

  default:
    result = mk_and(solver->prob->manager, w->size, w->data);
    break;
  }

  return opposite_term(result);
}


/*
 * Learn a constraint for the exists variable based on the
 * existing forall witness for constraint i:
 * - the witness is defined by the uvars of constraint i
 *   and the values stored in uvalue_aux.
 *
 * This function adds a constraint to the exists_context that will remove the
 * current exists model:
 * - if solver->option is EF_NOGEN_OPTION, the new constraint is
 *   of the form (or (/= var[0] eval[k0]) ... (/= var[k-1] eval[k-1]))
 *   where var[0 ... k-1] are the exist variables of constraint i
 * - if solver->option is EF_GEN_BY_SUBST_OPTION, we build a new
 *   constraint by substitution (option 2)
 *
 * If something goes wrong, then solver->status is updated to EF_STATUS_ERROR.
 * If the new learned assertion makes the exist context trivially unsat
 * then context->status is set to EF_STATUS_UNSAT.
 * Otherwise context->status is kept as is.
 */
static void ef_solver_learn(ef_solver_t *solver, uint32_t i) {
  ef_cnstr_t *cnstr;
  term_t *val;
  term_t new_constraint;
  uint32_t n;
  int32_t code;

  assert(i < ef_prob_num_constraints(solver->prob));
  cnstr = solver->prob->cnstr + i;

  switch (solver->option) {
  case EF_NOGEN_OPTION:
    /*
     * project solver->evalues on the existential
     * variables that occur in constraint i.
     * then build (or (/= evar[0] val[0]) ... (/= evar[n-1] val[n-1]))
     */
    n = ef_constraint_num_evars(cnstr);
    resize_ivector(&solver->evalue_aux, n);
    solver->evalue_aux.size = n;
    val = solver->evalue_aux.data;
    ef_project_exists_model(solver->prob, solver->evalue, cnstr->evars, val, n);
    new_constraint = ef_generalize1(solver->prob, cnstr->evars, val, n);
    break;

  case EF_GEN_BY_SUBST_OPTION:
    val = solver->uvalue_aux.data;
    new_constraint = ef_generalize2(solver->prob, i, val);
    if (new_constraint < 0) {
      // error in substitution
      solver->status = EF_STATUS_SUBST_ERROR;
      solver->error_code = new_constraint;
      return;
    }
    break;

  case EF_GEN_BY_PROJ_OPTION:
  default: // added this to prevent bogus GCC warning
    new_constraint = ef_generalize3(solver, i);
    if (new_constraint < 0) {     
      return;
    }
    break;
  }

  // add the new constraint to the exists context
  code = update_exists_context(solver, new_constraint);
  if (code == TRIVIALLY_UNSAT) {
    solver->status = EF_STATUS_UNSAT;
  } else if (code < 0) {
    solver->status = EF_STATUS_ASSERT_ERROR;
    solver->error_code = code;
  }
}




/*
 * EF SOLVER: INNER LOOP
 */

/*
 * Trace: result of testing candidate
 * - i = constraint id
 */
static void trace_candidate_check(ef_solver_t *solver, uint32_t i, smt_status_t status) {
  switch (status) {
  case STATUS_SAT:
  case STATUS_UNKNOWN:
    tprintf(solver->trace, 4, "(EF: candidate rejected: failed constraint %"PRIu32")\n", i);
    break;

  case STATUS_UNSAT:
    tprintf(solver->trace, 4, "(EF: candidate passed constraint %"PRIu32")\n", i);
    break;

  case STATUS_INTERRUPTED:
    tprintf(solver->trace, 4, "(EF: candidate check was interrupted)\n");
    break;

  default:
    tprintf(solver->trace, 4, "(EF: error in candidate check for constraint %"PRIu32")\n", i);
    break;
  }
}

/*
 * Check whether the current exists_model can be falsified by one
 * of the universal constraints.
 * - scan the universal constraints starting from solver->scan_idx
 * - the current exists model is defined by
 *   the mapping from solver->prob->evars to solver->evalues
 *
 * Update the solver->status as follows:
 * - if no constraint falsifies the model, solver->status = EF_STATUS_SAT
 * - if some constraint falsifies the model, then solver->status may be
 *   updated to EF_STATUS_UNSAT (trivially unsat after learning)
 * - if something goes wrong, solver->status = EF_STATUS_ERROR
 *
 * If constraint i falsifies the model then solver->scan_idx is
 * set to (i+1) modulo num_constraints.
 */
static void  ef_solver_check_exists_model(ef_solver_t *solver) {
  smt_status_t status;
  uint32_t i, n;

  n = ef_prob_num_constraints(solver->prob);

  /*
   * Special case: if there are no universal constraints
   * we return SAT immediately.
   */
  if (n == 0) {
    solver->status = EF_STATUS_SAT;
    return;
  }

  i = solver->scan_idx;
  do {
    tprintf(solver->trace, 4, "(EF: testing candidate against constraint %"PRIu32")\n", i);
    status = ef_solver_test_exists_model(solver, i);
    trace_candidate_check(solver, i, status);

    switch (status) {
    case STATUS_SAT:
    case STATUS_UNKNOWN:
#if EF_VERBOSE
      printf("Counterexample for constraint[%"PRIu32"]\n", i);
      print_forall_witness(stdout, solver, i);
      printf("\n");
      fflush(stdout);
#endif
      ef_solver_learn(solver, i);

    default:
      i ++;
      if (i == n) {
	i = 0;
      }
      break;
    }

  } while (status == STATUS_UNSAT && i != solver->scan_idx);

  solver->scan_idx = i; // prepare for the next call
  if (status == STATUS_UNSAT) {
    // done a full scan
    solver->status = EF_STATUS_SAT;
  }
}



/*
 * EF SOLVER: OUTER LOOP
 */

/*
 * Sample exists models
 * - stop when we find one that's not refuted by the forall constraints
 * - or when we reach the iteration bound
 *
 * Result:
 * - solver->status = EF_STATUS_ERROR if something goes wrong
 * - solver->status = EF_STATUS_INTERRUPTED if one of the calls to
 *   check_context is interrupted
 * - solver->status = EF_STATUS_UNSAT if all efmodels have been tried and none
 *   of them worked
 * - solver->status = EF_STATUS_UNKNOWN if the iteration limit is reached
 * - solver->status = EF_STATUS_SAT if a good model is found
 *
 * In the later case,
 * - the model is stored in solver->exists_model
 * - also it's available as a mapping form solver->prob->evars to solver->evalues
 *
 * Also solver->iters stores the number of iterations used.
 */
static void ef_solver_search(ef_solver_t *solver) {
  smt_status_t stat;
  uint32_t i, max;

  max = solver->max_iters;
  i = 0;

  assert(max > 0);

  tprintf(solver->trace, 2,
	  "(EF search: %"PRIu32" constraints, %"PRIu32" exists vars, %"PRIu32" forall vars)\n",
	  ef_prob_num_constraints(solver->prob),
	  ef_prob_num_evars(solver->prob),
	  ef_prob_num_uvars(solver->prob));
#if EF_VERBOSE
  printf("\nConditions on the exists variables:\n");
  yices_pp_term_array(stdout, ef_prob_num_conditions(solver->prob), solver->prob->conditions, 120, UINT32_MAX, 0, 0);
#endif

  ef_solver_start(solver);
  while (solver->status == EF_STATUS_SEARCHING && i < max) {

    tprintf(solver->trace, 3, "(EF Iteration %"PRIu32", scan_idx = %"PRIu32")\n", i, solver->scan_idx);

    stat = ef_solver_check_exists(solver);
    switch (stat) {
    case STATUS_SAT:
    case STATUS_UNKNOWN:
      // we have a candidate exists model
      // check it and learn what we can

#if EF_VERBOSE
      // FOR DEBUGGING
      printf("Candidate exists model:\n");
      print_ef_solution(stdout, solver);
      printf("\n");
#endif
      tputs(solver->trace, 4, "(EF: Found candidate model)\n");
      ef_solver_check_exists_model(solver);
      break;

    case STATUS_UNSAT:
      tputs(solver->trace, 4, "(EF: No candidate model)\n");
      solver->status = EF_STATUS_UNSAT;
      break;

    case STATUS_INTERRUPTED:
      tputs(solver->trace, 4, "(EF: Interrupted)\n");
      solver->status = EF_STATUS_INTERRUPTED;
      break;

    default:
      solver->status = EF_STATUS_CHECK_ERROR;
      solver->error_code = stat;
      break;
    }

    i ++;
  }

  /*
   * Cleanup and set status if i == max
   */
  if (solver->status != EF_STATUS_SAT && solver->exists_model != NULL) {
    yices_free_model(solver->exists_model);
    solver->exists_model = NULL;
    if (solver->status == EF_STATUS_SEARCHING) {
      assert(i == max);
      solver->status = EF_STATUS_UNKNOWN;
    }
  }

  solver->iters = i;

  tputs(solver->trace, 3, "(EF: done)\n\n");
}


/*
 * Check satisfiability: the result is stored in solver->status
 * - if solver->status is EF_STATUS_SAT then the model is in solver->exists_model
 *   (as in ef_solver_search).
 */
void ef_solver_check(ef_solver_t *solver, const param_t *parameters,
		     ef_gen_option_t gen_mode, uint32_t max_samples, uint32_t max_iters) {
  solver->parameters = parameters;
  solver->option = gen_mode;
  solver->max_samples = max_samples;
  solver->max_iters = max_iters;
  solver->scan_idx = 0;

  // adjust mode
  if (gen_mode == EF_GEN_AUTO_OPTION) {
    solver->option = EF_GEN_BY_SUBST_OPTION;
    if (ef_prob_has_arithmetic_uvars(solver->prob)) {
      solver->option  = EF_GEN_BY_PROJ_OPTION;
    }
  }

  assert(solver->exists_context == NULL &&
	 solver->forall_context == NULL &&
	 solver->exists_model == NULL);

  ef_solver_search(solver);
}


