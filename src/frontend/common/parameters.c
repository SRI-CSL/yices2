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

#include <assert.h>

#include "frontend/common/parameters.h"
#include "utils/string_utils.h"

/*
 * Parameter names: using the Yices conventions
 * - for the smt2 front end, you prefix these names with ':yices-'
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
  "ef-max-lemmas-per-round",
  "ef-max-samples",
  "ematch-cnstr-alpha",
  "ematch-cnstr-epsilon",
  "ematch-cnstr-mode",
  "ematch-en",
  "ematch-inst-per-round",
  "ematch-inst-per-search",
  "ematch-inst-total",
  "ematch-rounds-per-search",
  "ematch-search-total",
  "ematch-term-alpha",
  "ematch-term-epsilon",
  "ematch-term-mode",
  "ematch-trial-fapps",
  "ematch-trial-fdepth",
  "ematch-trial-matches",
  "ematch-trial-vdepth",
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
  "mcsat-bv-var-size",
  "mcsat-nra-bound",
  "mcsat-nra-bound-max",
  "mcsat-nra-bound-min",
  "mcsat-nra-mgcd",
  "mcsat-nra-nlsat",
  "mcsat-partial-restart",
  "mcsat-rand-dec-freq",
  "mcsat-rand-dec-seed",
  "mcsat-var-order",
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
  PARAM_EF_MAX_LEMMAS_PER_ROUND,
  PARAM_EF_MAX_SAMPLES,
  PARAM_EMATCH_CNSTR_ALPHA,
  PARAM_EMATCH_CNSTR_EPSILON,
  PARAM_EMATCH_CNSTR_MODE,
  PARAM_EMATCH_EN,
  PARAM_EMATCH_INST_PER_ROUND,
  PARAM_EMATCH_INST_PER_SEARCH,
  PARAM_EMATCH_INST_TOTAL,
  PARAM_EMATCH_ROUNDS_PER_SEARCH,
  PARAM_EMATCH_SEARCH_TOTAL,
  PARAM_EMATCH_TERM_ALPHA,
  PARAM_EMATCH_TERM_EPSILON,
  PARAM_EMATCH_TERM_MODE,
  PARAM_EMATCH_TRIAL_FAPPS,
  PARAM_EMATCH_TRIAL_FDEPTH,
  PARAM_EMATCH_TRIAL_MATCHES,
  PARAM_EMATCH_TRIAL_VDEPTH,
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
  PARAM_MCSAT_BV_VAR_SIZE,
  PARAM_MCSAT_NRA_BOUND,
  PARAM_MCSAT_NRA_BOUND_MAX,
  PARAM_MCSAT_NRA_BOUND_MIN,
  PARAM_MCSAT_NRA_MGCD,
  PARAM_MCSAT_NRA_NLSAT,
  PARAM_MCSAT_PARTIAL_RESTART,
  PARAM_MCSAT_RAND_DEC_FREQ,
  PARAM_MCSAT_RAND_DEC_SEED,
  PARAM_MCSAT_VAR_ORDER,
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
 * Names of the ematch modes for the quant solver
 */
#define NUM_EMATCH_MODES 3

static const char * const ematch_modes[NUM_EMATCH_MODES] = {
  "all",
  "epsilongreedy",
  "random",
};

static const iterate_kind_t ematch_mode_code[NUM_EMATCH_MODES] = {
  ITERATE_ALL,
  ITERATE_EPSILONGREEDY,
  ITERATE_RANDOM,
};


/*
 * Tables for converting parameter id to parameter name
 * and branching code to branching name. One more table
 * for converting from EF generalization codes to strings.
 */
const char *param2string[NUM_PARAMETERS];
const char *branching2string[NUM_BRANCHING_MODES];
const char *efgen2string[NUM_EF_GEN_MODES];
const char *ematchmode2string[NUM_EMATCH_MODES];


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

  for (i=0; i<NUM_EMATCH_MODES; i++) {
    name = ematch_modes[i];
    j = ematch_mode_code[i];
    ematchmode2string[j] = name;
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

// terms
bool param_val_to_terms(const char *name, const param_val_t *v, ivector_t **value, char **reason) {
  if (v->tag == PARAM_VAL_TERMS) {
    *value = v->val.terms;
    return true;
  }
  *reason = "list of variables required";
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
 * EMATCH mode
 * - allowed modes are "all" or "random" or "epsilongreedy"
 * - we use a general implementation so that we can add more modes later
 */
bool param_val_to_ematchmode(const char *name, const param_val_t *v, iterate_kind_t *value, char **reason) {
  int32_t i;

  if (v->tag == PARAM_VAL_SYMBOL) {
    i = binary_search_string(v->val.symbol, ematch_modes, NUM_EMATCH_MODES);
    if (i >= 0) {
      assert(i < NUM_EMATCH_MODES);
      *value = ematch_mode_code[i];
      return true;
    }
  }
  *reason = "must be one of 'all' 'random' 'epsilongreedy'";

  return false;
}
