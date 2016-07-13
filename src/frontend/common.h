/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Common functions used by both the Yices and SMT2 frontends.
 */
#ifndef __FRONTEND_COMMON_H
#define __FRONTEND_COMMON_H

#include <stdio.h>

#include "exists_forall/ef_client.h"

/*
 * Table to convert  smt_status to a string
 */
extern const char* const status2string[];

/*
 * Conversion of EF preprocessing codes to string
 */
extern const char * const efcode2error[];

/*
 * Table to convert  ef-solver status to a string
 */
extern const char* const ef_status2string[];

/*
 * Conversion of internalization code to an error message
 */
extern const char * const code2error[];



/*
 * Tables for converting parameter id to parameter name
 * and branching code to branching name. One more table
 * for converting from EF generalization codes to strings.
 */
extern const char *param2string[];
extern const char *branching2string[];
extern const char *efgen2string[];

/*
 * Ask for a bug report
 */
extern void __attribute__((noreturn)) freport_bug(FILE *fp, const char *format, ...);


/*
 * SETTING/READING PARAMETERS
 */

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
  PARAM_R_THRESHOLD,
  PARAM_R_FRACTION,
  PARAM_R_FACTOR,
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
  // mcsat options
  PARAM_MCSAT_NRA_MGCD,
  PARAM_MCSAT_NRA_NLSAT,
  // error
  PARAM_UNKNOWN
} yices_param_t;


#define NUM_PARAMETERS PARAM_UNKNOWN

/*
 * Argument to the setparam command encodes an immediate value
 * - the tag is given by the enumeration below
 * - PARAM_VAL_ERROR means an unexpected value was pushed
 * - the value is either a pointer to rational or a symbol
 */
typedef enum param_val_enum {
  PARAM_VAL_FALSE,
  PARAM_VAL_TRUE,
  PARAM_VAL_RATIONAL,
  PARAM_VAL_SYMBOL,
  PARAM_VAL_ERROR,
} param_val_enum_t;

typedef struct param_val_s {
  param_val_enum_t tag;
  union {
    rational_t *rational;
    char *symbol;
  } val;
} param_val_t;


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
 * Preprocessing and simplification options
 * - each boolean flag corresponds to a preprocessing option defined in 
 *   context_types.h. This is not complete. There are more options.
 */
typedef struct ctx_param_s {
  bool var_elim;
  bool arith_elim;
  bool bvarith_elim;
  bool flatten_or;
  bool eq_abstraction;
  bool keep_ite;
  bool splx_eager_lemmas;
  bool splx_periodic_icheck;
} ctx_param_t;


/*
 * Copy the context's parameters into ctx_parameters
 */
extern void save_ctx_params(ctx_param_t *ctx_parameters, context_t *context);

/*
 * Store some defaults for both ctx_parameters and parameters based on the logic, architecture, and mode
 */
extern void default_ctx_params(ctx_param_t *ctx_parameters, param_t *parameters,
			       smt_logic_t logic, context_arch_t arch, context_mode_t mode);


#endif /* __FRONTEND_COMMON_H */
