/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#if defined(CYGWIN) || defined(MINGW)
#ifndef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__ __declspec(dllexport)
#endif
#endif

#include <assert.h>
#include <stdio.h>
#include <stdarg.h>
#include <inttypes.h>

#include "api/context_config.h"
#include "api/yices_globals.h"
#include "api/yices_extensions.h"
#include "context/context_utils.h"
#include "utils/string_utils.h"
#include "frontend/common.h"
#include "yices.h"
#include "yices_exit_codes.h"


/*
 * Table to convert  smt_status to a string
 */
const char* const status2string[NUM_SMT_STATUSES] = {
  "idle",
  "searching",
  "unknown",
  "sat",
  "unsat",
  "interrupted",
  "error",
};


/*
 * Conversion of EF preprocessing codes to string
 */
const char * const efcode2error[NUM_EF_CODES] = {
  "no error",
  "assertions contain uninterpreted functions",
  "invalid quantifier nesting (not an exists/forall problem)",
  "non-atomic universal variables",
  "non-atomic existential variables",
  "internal error",
};


/*
 * Table to convert  ef-solver status to a string
 */
const char* const ef_status2string[NUM_EF_STATUSES] = {
  "idle",
  "searching",
  "unknown",
  "sat",
  "unsat",
  "interrupted",
  // error codes:
  "subst error",
  "tval error",
  "check error",
  "assert error",
  "model error",
  "implicant error", 
  "projection error",
  "status error",
};

/*
 * Conversion of internalization code to an error message
 */
const char * const code2error[NUM_INTERNALIZATION_ERRORS] = {
  "no error",
  "internal error",
  "type error",
  "formula contains free variables",
  "logic not supported",
  "the context does not support uninterpreted functions",
  "the context does not support scalar types",
  "the context does not support tuples",
  "the context does not support uninterpreted types",
  "the context does not support arithmetic",
  "the context does not support bitvectors",
  "the context does not support function equalities",
  "the context does not support quantifiers",
  "the context does not support lambdas",
  "not an IDL formula",
  "not an RDL formula",
  "non-linear arithmetic not supported",
  "too many variables for the arithmetic solver",
  "too many atoms for the arithmetic solver",
  "arithmetic solver exception",
  "bitvector solver exception",
};



void __attribute__((noreturn)) freport_bug(FILE *fp, const char *format, ...) {
  va_list p;

  fprintf(fp, "\n*************************************************************\n");
  fprintf(fp, "FATAL ERROR: ");
  va_start(p, format);
  vfprintf(fp, format, p);
  va_end(p);
  fprintf(fp, "\n*************************************************************\n");
  fprintf(fp, "Please report this bug to yices-bugs@csl.sri.com.\n");
  fprintf(fp, "To help us diagnose this problem, please include the\n"
                  "following information in your bug report:\n\n");
  fprintf(fp, "  Yices version: %s\n", yices_version);
  fprintf(fp, "  Build date: %s\n", yices_build_date);
  fprintf(fp, "  Platform: %s (%s)\n", yices_build_arch, yices_build_mode);
  fprintf(fp, "\n");
  fprintf(fp, "Thank you for your help.\n");
  fprintf(fp, "*************************************************************\n\n");
  fflush(fp);

  exit(YICES_EXIT_INTERNAL_ERROR);
}








/***************************************
 *  UTILITIES TO DEAL WITH PARAMETERS  *
 **************************************/

/*
 * Parameter names: using the Yices conventions
 * - for the smt2 front end, you prefix these names with ':yices:'
 */
static const char * const param_names[NUM_PARAMETERS] = {
  "arith-elim",
  "aux-eq-quota",
  "aux-eq-ratio",
  "bland-threshold",
  "branching",
  "bvarith-elim",
  "c-factor",
  "c-threshold",
  "cache-tclauses",
  "clause-decay",
  "d-factor",
  "d-threshold",
  "dyn-ack",
  "dyn-ack-threshold",
  "dyn-bool-ack",
  "dyn-bool-ack-threshold",
  "eager-lemmas",
  "ef-flatten-iff",
  "ef-flatten-ite",
  "ef-gen-mode",
  "ef-max-iters",
  "ef-max-samples",
  "fast-restarts",
  "flatten",
  "icheck",
  "icheck-period",
  "keep-ite",
  "learn-eq",
  "max-ack",
  "max-bool-ack",
  "max-extensionality",
  "max-interface-eqs",
  "max-update-conflicts",
  "mcsat-nra-mgcd",
  "mcsat-nra-nlsat",
  "optimistic-fcheck",
  "prop-threshold",
  "r-factor",
  "r-fraction",
  "r-threshold",
  "random-seed",
  "randomness",
  "simplex-adjust",
  "simplex-prop",
  "tclause-size",
  "var-decay",
  "var-elim",
};

// corresponding parameter codes in order
static const yices_param_t param_code[NUM_PARAMETERS] = {
  PARAM_ARITH_ELIM,
  PARAM_AUX_EQ_QUOTA,
  PARAM_AUX_EQ_RATIO,
  PARAM_BLAND_THRESHOLD,
  PARAM_BRANCHING,
  PARAM_BVARITH_ELIM,
  PARAM_C_FACTOR,
  PARAM_C_THRESHOLD,
  PARAM_CACHE_TCLAUSES,
  PARAM_CLAUSE_DECAY,
  PARAM_D_FACTOR,
  PARAM_D_THRESHOLD,
  PARAM_DYN_ACK,
  PARAM_DYN_ACK_THRESHOLD,
  PARAM_DYN_BOOL_ACK,
  PARAM_DYN_BOOL_ACK_THRESHOLD,
  PARAM_EAGER_LEMMAS,
  PARAM_EF_FLATTEN_IFF,
  PARAM_EF_FLATTEN_ITE,
  PARAM_EF_GEN_MODE,
  PARAM_EF_MAX_ITERS,
  PARAM_EF_MAX_SAMPLES,
  PARAM_FAST_RESTARTS,
  PARAM_FLATTEN,
  PARAM_ICHECK,
  PARAM_ICHECK_PERIOD,
  PARAM_KEEP_ITE,
  PARAM_LEARN_EQ,
  PARAM_MAX_ACK,
  PARAM_MAX_BOOL_ACK,
  PARAM_MAX_EXTENSIONALITY,
  PARAM_MAX_INTERFACE_EQS,
  PARAM_MAX_UPDATE_CONFLICTS,
  PARAM_MCSAT_NRA_MGCD,
  PARAM_MCSAT_NRA_NLSAT,
  PARAM_OPTIMISTIC_FCHECK,
  PARAM_PROP_THRESHOLD,
  PARAM_R_FACTOR,
  PARAM_R_FRACTION,
  PARAM_R_THRESHOLD,
  PARAM_RANDOM_SEED,
  PARAM_RANDOMNESS,
  PARAM_SIMPLEX_ADJUST,
  PARAM_SIMPLEX_PROP,
  PARAM_TCLAUSE_SIZE,
  PARAM_VAR_DECAY,
  PARAM_VAR_ELIM,
};



/*
 * Names of each branching mode (in lexicographic order)
 */
#define NUM_BRANCHING_MODES 6

static const char * const branching_modes[NUM_BRANCHING_MODES] = {
  "default",
  "negative",
  "positive",
  "th-neg",
  "th-pos",
  "theory",
};

static const branch_t branching_code[NUM_BRANCHING_MODES] = {
  BRANCHING_DEFAULT,
  BRANCHING_NEGATIVE,
  BRANCHING_POSITIVE,
  BRANCHING_TH_NEG,
  BRANCHING_TH_POS,
  BRANCHING_THEORY,
};



/*
 * Names of the generalization modes for the EF solver
 */
#define NUM_EF_GEN_MODES 4

static const char * const ef_gen_modes[NUM_EF_GEN_MODES] = {
  "auto",
  "none",
  "projection",
  "substitution",
};

static const ef_gen_option_t ef_gen_code[NUM_EF_GEN_MODES] = {
  EF_GEN_AUTO_OPTION,
  EF_NOGEN_OPTION,
  EF_GEN_BY_PROJ_OPTION,
  EF_GEN_BY_SUBST_OPTION,
};

/*
 * Tables for converting parameter id to parameter name
 * and branching code to branching name. One more table
 * for converting from EF generalization codes to strings.
 */
const char *param2string[NUM_PARAMETERS];

const char *branching2string[NUM_BRANCHING_MODES];

const char *efgen2string[NUM_EF_GEN_MODES];


/*
 * Initialize the table [parameter id --> string]
 * and [branching mode --> string]
 * and [ef gen code --> string]
 */
void init_parameter_name_table(void) {
  uint32_t i, j;
  const char *name;

  for (i=0; i<NUM_PARAMETERS; i++) {
    name = param_names[i];
    j = param_code[i];
    param2string[j] = name;
  }

  for (i=0; i<NUM_BRANCHING_MODES; i++) {
    name = branching_modes[i];
    j = branching_code[i];
    branching2string[j] = name;
  }

  for (i=0; i<NUM_EF_GEN_MODES; i++) {
    name = ef_gen_modes[i];
    j = ef_gen_code[i];
    efgen2string[j] = name;
  }
}


/*
 * Search for a parameter of the given name
 * - use binary search in the param_names table
 * - return PARAM_UNKNOWN if there's no parameter with that name
 */
yices_param_t find_param(const char *name) {
  int32_t i;
  i = binary_search_string(name, param_names, NUM_PARAMETERS);
  if (i >= 0) {
    assert(i < NUM_PARAMETERS);
    return param_code[i];
  } else {
    return PARAM_UNKNOWN;
  }
}


/*
 * Convert a parameter value to boolean, int32, float, etc.
 * - name = parameter name, used for error reporting.
 * - return true if the conversion works
 * - return false otherwise and returns an error message/string in *reason
 */
bool param_val_to_bool(const char *name, const param_val_t *v, bool *value, char **reason) {
  bool code;

  code = true;
  if (v->tag == PARAM_VAL_FALSE) {
    *value = false;
  } else if (v->tag == PARAM_VAL_TRUE) {
    *value = true;
  } else {
    *reason = "boolean required";
    code = false;
  }
  return code;
}

bool param_val_to_int32(const char *name, const param_val_t *v, int32_t *value, char **reason) {
  rational_t *q;

  if (v->tag == PARAM_VAL_RATIONAL) {
    q = v->val.rational;
    if (q_is_smallint(q)) {
      *value = q_get_smallint(q);
      return true;
    } else if (q_is_integer(q)) {
      *reason = "integer overflow";
      return false;
    }
    // if q is a rational: same error as not a number
  }

  *reason = "integer required";

  return false;
}

bool param_val_to_pos32(const char *name, const param_val_t *v, int32_t *value, char **reason) {
  if (param_val_to_int32(name, v, value, reason)) {
    if (*value > 0) return true;
    *reason = "must be positive";
  }
  return false;
}

bool param_val_to_pos16(const char *name, const param_val_t *v, int32_t *value, char **reason) {
  if (param_val_to_int32(name, v, value, reason)) {
    if (1 <= *value && *value <= UINT16_MAX) {
      return true;
    }
    *reason = "must be between 1 and 2^16";
  }
  return false;
}

bool param_val_to_nonneg32(const char *name, const param_val_t *v, int32_t *value, char **reason) {
  if (param_val_to_int32(name, v, value, reason)) {
    if (*value >= 0) return true;
    *reason = "cannot be negative";
  }
  return false;
}

bool param_val_to_float(const char *name, const param_val_t *v, double *value, char **reason) {
  mpq_t aux;

  if (v->tag == PARAM_VAL_RATIONAL) {
    mpq_init(aux);
    q_get_mpq(v->val.rational, aux);
    /*
     * NOTE: the GMP documentation says that conversion to double
     * may raise a hardware trap (overflow, underflow, etc.) on
     * some systems. We ignore this here.
     */
    *value = mpq_get_d(aux);
    mpq_clear(aux);
    return true;
  } else {
    *reason = "number required";
    return false;
  }
}

bool param_val_to_posfloat(const char *name, const param_val_t *v, double *value, char **reason) {
  if (param_val_to_float(name, v, value, reason)) {
    if (*value > 0.0) return true;
    *reason = "must be positive";
  }
  return false;
}

// ratio: number between 0 and 1 (inclusive)
bool param_val_to_ratio(const char *name, const param_val_t *v, double *value, char **reason) {
  if (param_val_to_float(name, v, value, reason)) {
    if (0 <= *value && *value <= 1.0) return true;
    *reason = "must be between 0 and 1";
  }
  return false;
}

// factor: must be at least 1
bool param_val_to_factor(const char *name, const param_val_t *v, double *value, char **reason) {
  if (param_val_to_float(name, v, value, reason)) {
    if (1.0 <= *value) return true;
    *reason = "must be at least 1";
  }
  return false;
}




/*
 * Special case: branching mode
 * - allowed modes are 'default' 'positive' 'negative' 'theory' 'th-neg' 'th-pos'
 */
bool param_val_to_branching(const char *name, const param_val_t *v, branch_t *value, char **reason) {
  int32_t i;

  if (v->tag == PARAM_VAL_SYMBOL) {
    i = binary_search_string(v->val.symbol, branching_modes, NUM_BRANCHING_MODES);
    if (i >= 0) {
      assert(i < NUM_BRANCHING_MODES);
      *value = branching_code[i];
      return true;
    }
  }
  *reason = "must be one of 'default' 'positive' 'negative' 'theory' 'th-neg' 'th-pos";

  return false;
}



/*
 * EF generalization mode
 * - allowed modes are "none" or "substitution" or "projection" or "auto"
 * - we use a general implementation so that we can add more modes later
 */
bool param_val_to_genmode(const char *name, const param_val_t *v, ef_gen_option_t *value, char **reason) {
  int32_t i;

  if (v->tag == PARAM_VAL_SYMBOL) {
    i = binary_search_string(v->val.symbol, ef_gen_modes, NUM_EF_GEN_MODES);
    if (i >= 0) {
      assert(i < NUM_EF_GEN_MODES);
      *value = ef_gen_code[i];
      return true;
    }
  }
  *reason = "must be one of 'none' 'substitution' 'projection' 'auto'";

  return false;
}



/*
 * Set defaults for both ctx_parameters and parameters based on the logic/architecture/mode and iflag/qflag
 * - this tries to give the same settings as 'yices_create_context'
 */
void default_ctx_params(ctx_param_t *ctx_parameters, param_t *parameters, smt_logic_t logic, context_arch_t arch, context_mode_t mode) {
  bool iflag;

  assert(ctx_parameters != NULL);
  ctx_parameters->var_elim = true;
  ctx_parameters->arith_elim = true;
  ctx_parameters->bvarith_elim = true;
  ctx_parameters->flatten_or = true;
  ctx_parameters->eq_abstraction = true;
  ctx_parameters->keep_ite = false;
  ctx_parameters->splx_eager_lemmas = true;
  ctx_parameters->splx_periodic_icheck = false;

  // if the logic is UNKNOWN, integer arithmetic may happen
  iflag = (logic == SMT_UNKNOWN) || iflag_for_logic(logic);
  if (iflag) {
    ctx_parameters->splx_periodic_icheck = true;
    if (logic == QF_LIA || logic == QF_LIRA) {
      ctx_parameters->splx_eager_lemmas = true;
    }
  }

  yices_set_default_params(parameters, logic, arch, mode);
}


/*
 * Export the context's options: store them into ctx_parameters
 * - only the options that can be set in yices_reval or smt2_commands are exported
 */
void save_ctx_params(ctx_param_t *ctx_parameters, context_t *context) {
  assert(ctx_parameters != NULL);
  assert(context != NULL);
  ctx_parameters->var_elim = context_var_elim_enabled(context);
  ctx_parameters->arith_elim = context_arith_elim_enabled(context);
  ctx_parameters->bvarith_elim = context_bvarith_elim_enabled(context);
  ctx_parameters->flatten_or = context_flatten_or_enabled(context);
  ctx_parameters->eq_abstraction = context_eq_abstraction_enabled(context);
  ctx_parameters->keep_ite = context_keep_ite_enabled(context);
  ctx_parameters->splx_eager_lemmas = splx_eager_lemmas_enabled(context);
  ctx_parameters->splx_periodic_icheck = splx_periodic_icheck_enabled(context);
}


