/*
 * THE SEARCH PARAMETERS/OPTIONS USED BY THE SOLVER
 */

#include <float.h>
#include <assert.h>

#include "string_utils.h"
#include "smt_core.h"

#include "search_parameters.h"



/*******************************
 *  DEFAULT SEARCH PARAMETERS  *
 ******************************/

/*
 * Default restart parameters for SMT solving
 * Minisat-like behavior
 */
#define DEFAULT_FAST_RESTART false
#define DEFAULT_C_THRESHOLD  100
#define DEFAULT_D_THRESHOLD  100
#define DEFAULT_C_FACTOR     1.5
#define DEFAULT_D_FACTOR     1.5

/*
 * Restart parameters if option --fast-restarts is set
 */
#define FAST_RESTART_C_THRESHOLD 100
#define FAST_RESTART_D_THRESHOLD 100
#define FAST_RESTART_C_FACTOR    1.1
#define FAST_RESTART_D_FACTOR    1.1

/*
 * Default clause deletion parameters
 */
#define DEFAULT_R_THRESHOLD   1000
#define DEFAULT_R_FRACTION    0.25
#define DEFAULT_R_FACTOR      1.05


/*
 * The default SMT parameters are copied from smt_core.h
 * - VAR_DECAY_FACTOR  = 0.95
 * - VAR_RANDOM_FACTOR = 0.02
 * - CLAUSE_DECAY_FACTOR = 0.999
 * - clause caching is disabled
 */
#define DEFAULT_VAR_DECAY      VAR_DECAY_FACTOR
#define DEFAULT_RANDOMNESS     VAR_RANDOM_FACTOR
#define DEFAULT_CLAUSE_DECAY   CLAUSE_DECAY_FACTOR
#define DEFAULT_CACHE_TCLAUSES false
#define DEFAULT_TCLAUSE_SIZE   0


/*
 * Default random seed as in smt_core.d
 */
#define DEFAULT_RANDOM_SEED    0xabcdef98

/*
 * Default branching = the smt_core default
 */
#define DEFAULT_BRANCHING  BRANCHING_DEFAULT



/*************************************
 *  GLOBAL TABLES: PARAMETER NAMES   *
 ************************************/

/*
 * Search parameters and options can be set individually.
 *
 * We use an integer code to identify the parameters + a table of
 * parameter names in lexicographic order.
 */
typedef enum param_key {
  // restart parameters
  PARAM_FAST_RESTART,
  PARAM_C_THRESHOLD,
  PARAM_D_THRESHOLD,
  PARAM_C_FACTOR,
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
} param_key_t;

#define NUM_PARAM_KEYS (PARAM_CLAUSE_DECAY+1)

// parameter names in lexicographic ordering
static const char *const param_key_names[NUM_PARAM_KEYS] = {
  "branching",
  "c-factor",
  "c-threshold",
  "clause-decay",
  "d-factor",
  "d-threshold",
  "fast-restarts",
  "r-factor",
  "r-fraction",
  "r-threshold",
  "random-seed",
  "randomness",
  "var-decay",
};

// corresponding parameter codes in order
static const int32_t param_code[NUM_PARAM_KEYS] = {
  PARAM_BRANCHING,
  PARAM_C_FACTOR,
  PARAM_C_THRESHOLD,
  PARAM_CLAUSE_DECAY,
  PARAM_D_FACTOR,
  PARAM_D_THRESHOLD,
  PARAM_FAST_RESTART,
  PARAM_R_FACTOR,
  PARAM_R_FRACTION,
  PARAM_R_THRESHOLD,
  PARAM_RANDOM_SEED,
  PARAM_RANDOMNESS,
  PARAM_VAR_DECAY,
};



/*
 * Names of each branching mode (in lexicographic order)
 */
static const char * const branching_modes[NUM_BRANCHING_MODES] = {
  "default",
  "negative",
  "positive",
  "th-neg",
  "th-pos",
  "theory",
};

static const int32_t branching_code[NUM_BRANCHING_MODES] = {
  BRANCHING_DEFAULT,
  BRANCHING_NEGATIVE,
  BRANCHING_POSITIVE,
  BRANCHING_TH_NEG,
  BRANCHING_TH_POS,
  BRANCHING_THEORY,
};




/****************
 *  FUNCTIONS   *
 ***************/

/*
 * Initialize params with a copy of default_settings
 */

/* replaces the static initializer */
static inline void init_default_settings(param_t *parameters){
  parameters->fast_restart  =  DEFAULT_FAST_RESTART;
  parameters->c_threshold   =  DEFAULT_C_THRESHOLD;
  parameters->d_threshold   =  DEFAULT_D_THRESHOLD;
  parameters->c_factor      =  DEFAULT_C_FACTOR;
  parameters->d_factor      =  DEFAULT_D_FACTOR;

  parameters->r_threshold   =  DEFAULT_R_THRESHOLD;
  parameters->r_fraction    =  DEFAULT_R_FRACTION;
  parameters->r_factor      =  DEFAULT_R_FACTOR;

  parameters->var_decay     =  DEFAULT_VAR_DECAY;
  parameters->randomness    =  DEFAULT_RANDOMNESS;
  parameters->random_seed   =  DEFAULT_RANDOM_SEED;
  parameters->branching     =  DEFAULT_BRANCHING;
  parameters->clause_decay  =  DEFAULT_CLAUSE_DECAY;

};

void init_params_to_defaults(param_t *parameters) {
  init_default_settings(parameters);
}


/*
 * Parse value as a boolean. Store the result in *v
 * - return 0 if this works
 * - return -2 otherwise
 */
static int32_t set_bool_param(const char *value, bool *v) {
  int32_t k;

  k = parse_as_boolean(value, v);
  return (k == valid_boolean) ? 0 : -2;
}


/*
 * Parse value as a branching mode. Store the result in *v
 * - return 0 if this works
 * - return -2 otherwise
 */
static int32_t set_branching_param(const char *value, branch_t *v) {
  int32_t k;

  k = parse_as_keyword(value, branching_modes, branching_code, NUM_BRANCHING_MODES);
  assert(k >= 0 || k == -1);

  if (k >= 0) {
    assert(BRANCHING_DEFAULT <= k && k <= BRANCHING_TH_POS);
    *v = (branch_t) k;
    k = 0;
  } else {
    k = -2;
  }

  return k;
}


/*
 * Parse val as a signed 32bit integer. Check whether
 * the result is in the interval [low, high].
 * - if so, store the result into *v and return 0
 * - if val is not an integer, return -2
 * - if the result is not in the interval, return -2
 */
static int32_t set_int32_param(const char *value, int32_t *v, int32_t low, int32_t high) {
  integer_parse_code_t k;
  int32_t aux;

  k = parse_as_integer(value, &aux);
  switch (k) {
  case valid_integer:
    if (low <= aux && aux <= high) {
      *v = aux;
      aux = 0;
    } else {
      aux = -2;
    }
    break;

  case integer_overflow:
  case invalid_integer:
  default: // prevent GCC warning
    aux = -2;
    break;
  }

  return aux;
}


/*
 * Parse value as an unsigned integer
 * - no interval check
 * - if val is not an unsigned integer, return -2
 */
static int32_t set_uint32_param(const char *value, uint32_t *v) {
  integer_parse_code_t k;
  int32_t code;

  k = parse_as_uint(value, v);
  switch (k) {
  case valid_integer:
    code = 0;
    break;

  case integer_overflow:
  case invalid_integer:
  default:
    code = -2;
    break;
  }

  return code;
}



/*
 * Parse value as a double. Check whether
 * the result is in the interval [low, high].
 * - if so, store the result into *v and return 0
 * - if the string can't be parse as a double, return -1
 * - if the result is not in the interval, return -2
 */
static int32_t set_double_param(const char *value, double *v, double low, double high) {
  double_parse_code_t k;
  double aux;
  int32_t result;

  k = parse_as_double(value, &aux);
  switch (k) {
  case valid_double:
    if (low <= aux && aux <= high) {
      *v = aux;
      result = 0;
    } else {
      result = -2;
    }
    break;

  case double_overflow:
  case invalid_double:
  default: // prevent GCC warning
    result = -1;
    break;
  }

  return result;
}




/*
 * Set a field in the parameter record.
 * - key = field name
 * - value = value for that field
 *
 * Return code:
 *   -1 if the key is not recognized
 *   -2 if the value is not recognized
 *   -3 if the value has the wrong type for the key
 *    0 otherwise (i.e., success)
 */
int32_t params_set_field(param_t *parameters, const char *key, const char *value) {
  int32_t k, r;
  int32_t z;
  double x;

  z = 0; // to prevent GCC warning

  k = parse_as_keyword(key, param_key_names, param_code, NUM_PARAM_KEYS);
  switch (k) {
  case PARAM_FAST_RESTART:
    r = set_bool_param(value, &parameters->fast_restart);
    break;

  case PARAM_C_THRESHOLD:
    r = set_int32_param(value, &z, 1, INT32_MAX);
    if (r == 0) {
      parameters->c_threshold = (uint32_t) z;
    }
    break;

  case PARAM_D_THRESHOLD:
    r = set_int32_param(value, &z, 1, INT32_MAX);
    if (r == 0) {
      parameters->d_threshold = (uint32_t) z;
    }
    break;

  case PARAM_C_FACTOR:
    r = set_double_param(value, &parameters->c_factor, 1.0, DBL_MAX);
    break;

  case PARAM_D_FACTOR:
    r = set_double_param(value, &parameters->d_factor, 1.0, DBL_MAX);
    break;

  case PARAM_R_THRESHOLD:
    r = set_int32_param(value, &z, 1, INT32_MAX);
    if (r == 0) {
      parameters->r_threshold = z;
    }
    break;

  case PARAM_R_FRACTION:
    r = set_double_param(value, &parameters->r_fraction, 0.0, 1.0);
    break;

  case PARAM_R_FACTOR:
    r = set_double_param(value, &parameters->r_factor, 1.0, DBL_MAX);
    break;

  case PARAM_VAR_DECAY:
    r = set_double_param(value, &parameters->var_decay, 0.0, 1.0);
    break;

  case PARAM_RANDOMNESS:
    r = set_double_param(value, &x, 0.0, 1.0);
    if (r == 0) {
      parameters->randomness = (float) x;
    }
    break;

  case PARAM_RANDOM_SEED:
    r = set_uint32_param(value, &parameters->random_seed);
    break;

  case PARAM_BRANCHING:
    r = set_branching_param(value, &parameters->branching);
    break;

  case PARAM_CLAUSE_DECAY:
    r = set_double_param(value, &x, 0.0, 1.0);
    if (r == 0) {
      parameters->clause_decay = (float) x;
    }
    break;

  default:
    assert(k == -1);
    r = -1;
    break;
  }

  return r;
}
