/*
 * SUPPORT FOR EXISTS/FORALL SOLVING
 */

#include "index_vectors.h"
#include "efsolver.h"
#include "term_substitution.h"
#include "yices.h"


/*
 * Initialize a context from prob
 * - we use the same settings/mode for exists and forall contexts
 */
void init_ef_context(context_t *ctx, ef_prob_t *prob, smt_logic_t logic, context_arch_t arch) {
  init_context(ctx, prob->terms, logic, CTX_MODE_MULTICHECKS, arch, false); // qflag is false
}


/*
 * Assert all the conditions from prob into ctx
 */
int32_t exists_context_assert_conditions(context_t *ctx, ef_prob_t *prob) {
  uint32_t n;
  n = ef_prob_num_conditions(prob);
  return assert_formulas(ctx, n, prob->conditions);
}


/*
 * Add an assertion to an exists context
 */
int32_t update_exists_context(context_t *ctx, term_t f) {
  smt_status_t status;
  int32_t code;

  assert(is_boolean_term(ctx->terms, f));

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
 * Assert (B and not C) in ctx
 */
int32_t forall_context_assert(context_t *ctx, term_t b, term_t c) {
  term_t assertions[2];

  assert(is_boolean_term(ctx->terms, b) && is_boolean_term(ctx->terms, c));
  assertions[0] = b;
  assertions[1] = opposite_term(c);
  return assert_formulas(ctx, 2, assertions);
}



/*
 * Check satisfiability and get a model
 * - ctx = the context
 * - parameters = heuristic settings (if parameters is NULL, the defaults are used)
 * - var = array of n uninterpreted terms
 * - value = array of n terms (to receive the value of each var)
 * - n = size of array evar and value
 *
 * The return code is as in check_context:
 * 1) if code = STATUS_SAT then the context is satisfiable
 *   and a model is stored in value[0 ... n-1]
 * - value[i] = a constant term mapped to evar[i] in the model
 * 2) code = STATUS_UNSAT: not satisfiable
 *
 * 3) other codes report an error of some kind
 */
smt_status_t satisfy_context(context_t *ctx, const param_t *parameters, term_t *var, term_t *value, uint32_t n) {
  smt_status_t stat;
  model_t *model;
  int32_t code;

  assert(context_status(ctx) == STATUS_IDLE);
  stat = check_context(ctx, parameters);
  switch (stat) {
  case STATUS_SAT:
  case STATUS_UNKNOWN:
    model = yices_get_model(ctx, true);
    code = yices_term_array_value(model, n, var, value);
    yices_free_model(model);

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
 * Support for sampling: get another model after adding the blocking clause
 */
smt_status_t recheck_context(context_t *ctx, const param_t *parameters, term_t *var, term_t *value, uint32_t n) {
  int32_t code;

  assert(context_status(ctx) == STATUS_SAT || context_status(ctx) == STATUS_UNKNOWN);

  code = assert_blocking_clause(ctx);
  if (code == TRIVIALLY_UNSAT) {
    return STATUS_UNSAT;
  } else {
    assert(code == CTX_NO_ERROR);
    return satisfy_context(ctx, parameters, var, value, n);
  }
}


/*
 * - apply the substitution defined by var and value to term t
 * - n = size of arrays var and value
 * - return code < 0 means that an error occurred during the substitution
 *   (cf. apply_term_subst in term_substitution.h).
 */
term_t ef_substitution(ef_prob_t *prob, term_t *var, term_t *value, uint32_t n, term_t t) {
  term_subst_t subst;
  term_t g;

  init_term_subst(&subst, prob->manager, n, var, value);
  g = apply_term_subst(&subst, t);
  delete_term_subst(&subst);

  return g;
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
 * Project model to a subset of the existential variables
 * - value[i] = exist model = array of constant values
 * - evar = an array of n existential variables: every element of evar occurs in ef->all_evars
 * - then this function projects builds the model restricted to evar into array eval
 *
 * Assumption:
 * - value[i] = value mapped to ef->all_evars[i] for i=0 ... num_evars-1
 * - every x in sub_var occurs somewhere in ef->all_evars
 * - then if evar[i] = x and x is equal to all_evar[k] the function copies
 *   value[k] into eval[i]
 */
void ef_project_exists_model(ef_prob_t *prob, term_t *value, term_t *evar, term_t *eval, uint32_t n) {
  project_model(prob->all_evars, value, evar, eval, n);
}


/*
 * Same thing for a universal model:
 * - value[i] = model = array of constant value such that value[i] is the value of ef->all_uvar[i]
 * - uvar = subset of the universal variables (of size n)
 * - uval = restriction of value to uvar (as above)
 */
void ef_project_forall_model(ef_prob_t *prob, term_t *value, term_t *uvar, term_t *uval, uint32_t n) {
  project_model(prob->all_uvars, value, uvar, uval, n);
}


/*
 * GENERALIZATION FROM UNIVERSAL MODELS
 */

/*
 * Option 1: don't generalize:
 * - build the formula (or (/= var[0] value[0]) ... (/= var[n-1] value[n-1]))
 */
term_t ef_generalize1(ef_prob_t *prob, term_t *var, term_t *value, uint32_t n) {
  return mk_array_neq(prob->manager, n, var, value);
}


/*
 * Option 2: generalize by substitution
 * - return not (prob->cnstr[i].guarantee with y := value)
 */
term_t ef_generalize2(ef_prob_t *prob, uint32_t i, term_t *value) {
  ef_cnstr_t *cnstr;
  uint32_t n;
  term_t g;

  assert(i < ef_prob_num_constraints(prob));
  cnstr = prob->cnstr + i;
  n = ef_constraint_num_uvars(cnstr);
  g = ef_substitution(prob, cnstr->uvars, value, n, cnstr->guarantee);
  if (g < 0) {
    // substitution error
    return g;
  }

  return opposite_term(g);
}


/*
 * GLOBAL PROCEDURES
 */

/*
 * Initialize solver:
 * - prob = problem descriptor
 * - logic/arch/parameters = for context initialization and check
 * - option = generalization option
 * - max_samples = sampling setting
 */
void init_ef_solver(ef_solver_t *solver, ef_prob_t *prob, const param_t *parameters, smt_logic_t logic,
		    context_arch_t arch, ef_gen_option_t option, uint32_t max_samples) {
  uint32_t n;

  solver->prob = prob;
  solver->parameters = parameters;
  solver->logic = logic;
  solver->arch = arch;
  solver->option = option;
  solver->max_samples = max_samples;
  solver->iters = 0;

  solver->exists_context = NULL;
  solver->forall_context = NULL;

  n = ef_prob_num_evars(prob);
  assert(n <= UINT32_MAX/sizeof(term_t));
  solver->evalue = (term_t *) safe_malloc(n * sizeof(term_t));

  n = ef_prob_num_uvars(prob);
  assert(n <= UINT32_MAX/sizeof(term_t));
  solver->uvalue = (term_t *) safe_malloc(n * sizeof(term_t));

  init_ivector(&solver->evalue_aux, 64);
  init_ivector(&solver->uvalue_aux, 64);
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
  delete_ivector(&solver->evalue_aux);
  delete_ivector(&solver->uvalue_aux);
}


/*
 * Allocate and initialize the exists_context
 */
static void init_exists_context(ef_solver_t *solver) {
  context_t *ctx;

  assert(solver->exists_context == NULL);
  ctx = (context_t *) safe_malloc(sizeof(context_t));
  init_ef_context(ctx, solver->prob, solver->logic, solver->arch);
  solver->exists_context = ctx;
}


/*
 * Allocate an initialize the forall_context
 */
static void init_forall_context(ef_solver_t *solver) {
  context_t *ctx;

  assert(solver->forall_context == NULL);
  ctx = (context_t *) safe_malloc(sizeof(context_t));
  init_ef_context(ctx, solver->prob, solver->logic, solver->arch);
  solver->forall_context = ctx;
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
 * Sampling for the i-th constrain in solver->prob:
 * - search for at most max_samples y's that satisfy the assumption of constraint i in prob
 * - for each such y, add a new constraint to the exist context ctx
 * - max_samples = bound on the number of samples to take
 *
 * Constraint i is of the form
 *    (FORALL Y_i: B_i(Y_i) => C(X_i, Y_i))
 * - every sample is a model y_i that satisfies B_i.
 * - for each sample, we learn that any X_i such that C(X_i, y_i) holds
 *   can't be a good candidate. So we add the constraint not C(X_i, y_i) to ctx.
 */
int32_t ef_sample_constraint(ef_solver_t *solver, uint32_t i) {
  context_t *sampling_ctx;
  ef_cnstr_t *cnstr;
  term_t *value;
  uint32_t nvars, samples;
  int32_t code;
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
  value = solver->uvalue_aux.data;

  samples = solver->max_samples;

  /*
   * assert the assumption in the forall context
   */
  sampling_ctx = get_forall_context(solver);
  code = assert_formula(sampling_ctx, cnstr->assumption);
  while (code == CTX_NO_ERROR) {
    status = satisfy_context(sampling_ctx, solver->parameters, cnstr->uvars, value, nvars);
    switch (status) {
    case STATUS_SAT:
    case STATUS_UNKNOWN:
      // learned condition on X:
      cnd = ef_substitution(solver->prob, cnstr->uvars, value, nvars, cnstr->guarantee);
      if (cnd < 0) {
	code = INTERNAL_ERROR;
	goto done;
      }
      code = update_exists_context(solver->exists_context, opposite_term(cnd));
      break;

    case STATUS_UNSAT:
      goto done;

    default:
      code = INTERNAL_ERROR;
      goto done;
    }

    samples --;
    if (samples == 0) goto done;

    code = assert_blocking_clause(sampling_ctx);
  }

 done:
  clear_forall_context(solver, true);

  return code;
}




/*
 * Initialize the exists context
 * - asserts all conditions from solver->prob
 * - if max_samples is positive, also apply pre-sampling to all the universal constraints
 * - return code:
 *   TRIVIALLY_UNSAT --> exists context is unsat (not ef solution)
 *   CTX_NO_ERROR --> nothing bad happened
 *   negative values --> errors (cf. context.h)
 */
int32_t ef_solver_start(ef_solver_t *solver) {
  context_t *ctx;
  int32_t code;
  uint32_t i, n;

  init_exists_context(solver);
  ctx = solver->exists_context;
  code = exists_context_assert_conditions(ctx, solver->prob); // add all conditions
  if (code == CTX_NO_ERROR && solver->max_samples > 0) {
    // sample: take all constraints in order
    n = ef_prob_num_constraints(solver->prob);
    for (i=0; i<n; i++) {
      code = ef_sample_constraint(solver, i);
      if (code != CTX_NO_ERROR) break;
    }
  }

  return code;
}


/*
 * Check satisfiability of the exists_context
 * - if SAT build a model (in solver->evalue)
 */
smt_status_t ef_solver_check_exists(ef_solver_t *solver) {
  term_t *evar;
  uint32_t n;

  evar = solver->prob->all_evars;
  n = iv_len(evar);
  return satisfy_context(solver->exists_context, solver->parameters, evar, solver->evalue, n);
}


/*
 * Test the current exists model using universal constraint i
 * - i must be a valid index (i.e., 0 <= i < solver->prob->num_cnstr)
 * - this checks the assertion B_i and not C_i after replacing existential
 *   variables by their values (stored in evalue)
 * - return code:
 *   if STATUS_SAT (or STATUS_UNKNOWN): a model of B_i and not C_i
 *   is found and stored in uvalue_aux
 *   if STATUS_UNSAT: not model found (current exists model is good as
 *   far as constraint i is concerned)
 *   anything else: an error
 */
smt_status_t ef_solver_check_forall(ef_solver_t *solver, uint32_t i) {
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
    return STATUS_ERROR;
  }

  /*
   * make uvalue_aux large enough
   */
  n = ef_constraint_num_uvars(cnstr);
  resize_ivector(&solver->uvalue_aux, n);
  value = solver->uvalue_aux.data;

  forall_ctx = get_forall_context(solver);
  code = forall_context_assert(forall_ctx, cnstr->assumption, g); // assert B_i(Y_i) and not g(Y_i)
  if (code == CTX_NO_ERROR) {
    status = satisfy_context(forall_ctx, solver->parameters, cnstr->uvars, value, n);
  } else if (code == TRIVIALLY_UNSAT) {
    assert(context_status(forall_ctx) == STATUS_UNSAT);
    status = STATUS_UNSAT;
  } else {
    // error in assertion
    status = STATUS_ERROR;
  }
  clear_forall_context(solver, true);

  return status;
}


/*
 * Learn a constraint for the exists variable based on the
 * existing forall witness:
 * - i = index of the universal constraint for which we have a witness
 * - the witness is defined by the uvars of constraint i
 * + the values stored in uvalue_aux.
 * - this adds a constraint that will remove the current exists model
 * - if solver->option is EF_NOGEN_OPTION, the new constraint is
 *   of the form (or (/= var[0] eval[k0) ... (/= var[k-1] eval[k-1]))
 *   where var[0 ... k-1] are the exist variables of constraint i
 * - if solver->option is EF_GEN_BY_SUBST_OPTION, we build a new
 *   constraint by substitution (option 2)
 *
 * Return code:
 * - TRIVIALLY_UNSAT: the new constraint make exists_context unsat
 * - CTX_NO_ERROR: nothing bad happened
 * - a negative value --> error
 */
int32_t ef_solver_learn(ef_solver_t *solver, uint32_t i) {
  ef_cnstr_t *cnstr;
  term_t *val;
  term_t new_constraint;
  uint32_t n;

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
    val = solver->evalue_aux.data;
    ef_project_exists_model(solver->prob, solver->evalue, cnstr->evars, val, n);
    new_constraint = ef_generalize1(solver->prob, cnstr->evars, val, n);
    break;

  case EF_GEN_BY_SUBST_OPTION:
  default: // added this to prevent bogus GCC warning
    val = solver->uvalue_aux.data;
    new_constraint = ef_generalize2(solver->prob, i, val);
    if (new_constraint < 0) {
      return INTERNAL_ERROR;
    }
    break;
  }

  return update_exists_context(solver->exists_context, new_constraint);
}
