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
 * SUPPORT FOR READING AND SETTING PARAMETERS
 * USED BY BOTH THE SMT2 AND THE YICES FRONTENDS.
 */
#ifndef __FRONTEND_COMMON_PARAMETERS_H
#define __FRONTEND_COMMON_PARAMETERS_H

#include <stdbool.h>
#include <stdint.h>

#include "solvers/quant/ef_parameters.h"
#include "utils/int_vectors.h"
#include "api/search_parameters.h"
#include "terms/rationals.h"

/*
 * Search parameters and internalization options can be set individually
 * using the command (set-param <name> <value>).
 *
 * We use an integer code to identify the parameters + a table of
 * parameter names in lexicographic order. Each parameter
 * is described in context.h.
 *
 * New: added the EF solver parameters.
 */
typedef enum yices_param {
  // internalization options
  PARAM_VAR_ELIM,
  PARAM_ARITH_ELIM,
  PARAM_BVARITH_ELIM,
  PARAM_FLATTEN,
  PARAM_LEARN_EQ,
  PARAM_KEEP_ITE,
  // restart parameters
  PARAM_FAST_RESTARTS,
  PARAM_C_THRESHOLD,
  PARAM_C_FACTOR,
  PARAM_D_THRESHOLD,
  PARAM_D_FACTOR,
  // clause deletion heuristic
  PARAM_R_INITIAL_THRESHOLD,
  PARAM_R_INTERVAL,
  // branching heuristic
  PARAM_VAR_DECAY,
  PARAM_RANDOMNESS,
  PARAM_RANDOM_SEED,
  PARAM_BRANCHING,
  // learned clauses
  PARAM_CLAUSE_DECAY,
  PARAM_CACHE_TCLAUSES,
  PARAM_TCLAUSE_SIZE,
  // egraph parameters
  PARAM_DYN_ACK,
  PARAM_DYN_BOOL_ACK,
  PARAM_OPTIMISTIC_FCHECK,
  PARAM_MAX_ACK,
  PARAM_MAX_BOOL_ACK,
  PARAM_AUX_EQ_QUOTA,
  PARAM_AUX_EQ_RATIO,
  PARAM_DYN_ACK_THRESHOLD,
  PARAM_DYN_BOOL_ACK_THRESHOLD,
  PARAM_MAX_INTERFACE_EQS,
  // simplex parameters
  PARAM_EAGER_LEMMAS,
  PARAM_SIMPLEX_PROP,
  PARAM_SIMPLEX_ADJUST,
  PARAM_PROP_THRESHOLD,
  PARAM_BLAND_THRESHOLD,
  PARAM_ICHECK,
  PARAM_ICHECK_PERIOD,
  // array solver parameters
  PARAM_MAX_UPDATE_CONFLICTS,
  PARAM_MAX_EXTENSIONALITY,
  // EF solver
  PARAM_EF_FLATTEN_IFF,
  PARAM_EF_FLATTEN_ITE,
  PARAM_EF_GEN_MODE,
  PARAM_EF_MAX_SAMPLES,
  PARAM_EF_MAX_ITERS,
  PARAM_EF_MAX_LEMMAS_PER_ROUND,
  // quant solver
  PARAM_EMATCH_EN,
  PARAM_EMATCH_INST_PER_ROUND,
  PARAM_EMATCH_INST_PER_SEARCH,
  PARAM_EMATCH_INST_TOTAL,
  PARAM_EMATCH_ROUNDS_PER_SEARCH,
  PARAM_EMATCH_SEARCH_TOTAL,
  PARAM_EMATCH_TRIAL_FDEPTH,
  PARAM_EMATCH_TRIAL_VDEPTH,
  PARAM_EMATCH_TRIAL_FAPPS,
  PARAM_EMATCH_TRIAL_MATCHES,
  PARAM_EMATCH_CNSTR_MODE,
  PARAM_EMATCH_CNSTR_EPSILON,
  PARAM_EMATCH_CNSTR_ALPHA,
  PARAM_EMATCH_TERM_MODE,
  PARAM_EMATCH_TERM_EPSILON,
  PARAM_EMATCH_TERM_ALPHA,
  // mcsat options
  PARAM_MCSAT_RAND_DEC_FREQ,
  PARAM_MCSAT_RAND_DEC_SEED,
  PARAM_MCSAT_NRA_MGCD,
  PARAM_MCSAT_NRA_NLSAT,
  PARAM_MCSAT_NRA_BOUND,
  PARAM_MCSAT_NRA_BOUND_MIN,
  PARAM_MCSAT_NRA_BOUND_MAX,
  PARAM_MCSAT_BV_VAR_SIZE,
  PARAM_MCSAT_VAR_ORDER,
  PARAM_MCSAT_PARTIAL_RESTART,
  // error
  PARAM_UNKNOWN
} yices_param_t;


#define NUM_PARAMETERS PARAM_UNKNOWN

/*
 * Argument to the setparam command encodes an immediate value
 * - the tag is given by the enumeration below
 * - PARAM_VAL_ERROR means an unexpected value was passed
 * - the value is either a pointer to rational or a symbol
 */
typedef enum param_val_enum {
  PARAM_VAL_FALSE,
  PARAM_VAL_TRUE,
  PARAM_VAL_RATIONAL,
  PARAM_VAL_SYMBOL,
  PARAM_VAL_TERMS,
  PARAM_VAL_ERROR,
} param_val_enum_t;

typedef struct param_val_s {
  param_val_enum_t tag;
  union {
    rational_t *rational;
    char *symbol;
    ivector_t *terms;
  } val;
} param_val_t;


/*
 * Tables for converting parameter id to parameter name
 * and branching code to branching name. One more table
 * for converting from EF generalization codes to strings.
 *
 * These tables are initialized after a call to
 * init_parameter_name_table.
 */
extern const char *param2string[];
extern const char *branching2string[];
extern const char *efgen2string[];
extern const char *ematchmode2string[];


/*
 * Initialization: setup internal tables
 */
extern void init_parameter_name_table(void);


/*
 * Search for a parameter of the given name
 * - return PARAM_UNKNOWN if there's no parameter with that name
 */
extern yices_param_t find_param(const char *name);

/*
 * Convert a parameter value to boolean, int32, float, etc.
 * - name = parameter name, used for error reporting.
 * - return true if the conversion works
 * - return false otherwise and returns an error message/string in *reason
 *
 * ratio means a floating point number in the interval [0.0 .. 1.0]
 * factor means a floating point number larger than or equal to 1.0
 */
extern bool param_val_to_bool(const char *name, const param_val_t *v, bool *value, char **reason);
extern bool param_val_to_int32(const char *name, const param_val_t *v, int32_t *value, char **reason);
extern bool param_val_to_pos32(const char *name, const param_val_t *v, int32_t *value, char **reason);
extern bool param_val_to_pos16(const char *name, const param_val_t *v, int32_t *value, char **reason);
extern bool param_val_to_nonneg32(const char *name, const param_val_t *v, int32_t *value, char **reason);
extern bool param_val_to_float(const char *name, const param_val_t *v, double *value, char **reason);
extern bool param_val_to_posfloat(const char *name, const param_val_t *v, double *value, char **reason);
extern bool param_val_to_ratio(const char *name, const param_val_t *v, double *value, char **reason);
extern bool param_val_to_factor(const char *name, const param_val_t *v, double *value, char **reason);
extern bool param_val_to_terms(const char *name, const param_val_t *v, ivector_t **value, char **reason);

/*
 * Special case: branching mode
 * - allowed modes are 'default' 'positive' 'negative' 'theory' 'th-neg' 'th-pos'
 */
extern bool param_val_to_branching(const char *name, const param_val_t *v, branch_t *value, char **reason);

/*
 * EF generalization mode
 * - allowed modes are 'none' 'substitution' 'projection' 'auto'
 * - we use a general implementation so that we can add more modes later
 */
extern bool param_val_to_genmode(const char *name, const param_val_t *v, ef_gen_option_t *value, char **reason);

/*
 * EMATCH mode
 * - allowed modes are "all" or "random" or "epsilongreedy"
 * - we use a general implementation so that we can add more modes later
 */
extern bool param_val_to_ematchmode(const char *name, const param_val_t *v, iterate_kind_t *value, char **reason);


#endif /* __FRONTEND_COMMON_PARAMETERS_H */
