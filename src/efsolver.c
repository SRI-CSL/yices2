/*
 * SUPPORT FOR EXISTS/FORALL SOLVING
 */

#include "index_vectors.h"
#include "efsolver.h"
#include "term_substitution.h"
#include "yices.h"


/*
 * Initialize and exists_context from prob
 */
void init_exists_context(context_t *ctx, ef_prob_t *prob, smt_logic_t logic, context_arch_t arch) {
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
 * Initialize a forall context:
 */
void init_forall_context(context_t *ctx, ef_prob_t *prob, smt_logic_t logic, context_arch_t arch) {
  init_context(ctx, prob->terms, logic, CTX_MODE_ONECHECK, arch, false); // qflag is false
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
void ef_project_exits_model(ef_prob_t *prob, term_t *value, term_t *evar, term_t *eval, uint32_t n) {
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
