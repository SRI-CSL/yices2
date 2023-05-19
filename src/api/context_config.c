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
 * OBJECT TO STORE CONTEXT CONFIGURATIONS
 */

#include <stdbool.h>
#include <assert.h>

#include "api/context_config.h"
#include "utils/memalloc.h"
#include "utils/string_utils.h"


/*
 * Mapping from strings to context modes (cf. string_utils.h)
 */
static const char * const mode_names[NUM_MODES] = {
  "interactive",
  "multi-checks",
  "one-shot",
  "push-pop",
};

static const int32_t mode[NUM_MODES] = {
  CTX_MODE_INTERACTIVE,
  CTX_MODE_MULTICHECKS,
  CTX_MODE_ONECHECK,
  CTX_MODE_PUSHPOP,
};

static const char * const solver_type_names[NUM_SOLVER_TYPES] = {
  "dpllt",
  "mcsat"
};

static const int32_t solver_type[NUM_SOLVER_TYPES] = {
  CTX_SOLVER_TYPE_DPLLT,
  CTX_SOLVER_TYPE_MCSAT
};

/*
 * Solver codes
 */
static const char * const solver_code_names[NUM_SOLVER_CODES] = {
  "auto",
  "default",
  "ifw",
  "none",
  "rfw",
  "simplex",
};

static const int32_t solver_code[NUM_SOLVER_CODES] = {
  CTX_CONFIG_AUTO,
  CTX_CONFIG_DEFAULT,
  CTX_CONFIG_ARITH_IFW,
  CTX_CONFIG_NONE,
  CTX_CONFIG_ARITH_RFW,
  CTX_CONFIG_ARITH_SIMPLEX,
};


/*
 * Descriptor fields (other than "logic")
 */
typedef enum ctx_config_key {
  CTX_CONFIG_KEY_MODE,
  CTX_CONFIG_KEY_SOLVER_TYPE,
  CTX_CONFIG_KEY_TRACE_TAGS,
  CTX_CONFIG_KEY_ARITH_FRAGMENT,
  CTX_CONFIG_KEY_UF_SOLVER,
  CTX_CONFIG_KEY_ARRAY_SOLVER,
  CTX_CONFIG_KEY_BV_SOLVER,
  CTX_CONFIG_KEY_ARITH_SOLVER,
  CTX_CONFIG_KEY_MODEL_INTERPOLATION,
} ctx_config_key_t;

#define NUM_CONFIG_KEYS (CTX_CONFIG_KEY_MODEL_INTERPOLATION+1)


static const char *const config_key_names[NUM_CONFIG_KEYS] = {
  "arith-fragment",
  "arith-solver",
  "array-solver",
  "bv-solver",
  "mode",
  "model-interpolation",
  "solver-type",
  "trace",
  "uf-solver",
};

static const int32_t config_key[NUM_CONFIG_KEYS] = {
  CTX_CONFIG_KEY_ARITH_FRAGMENT,
  CTX_CONFIG_KEY_ARITH_SOLVER,
  CTX_CONFIG_KEY_ARRAY_SOLVER,
  CTX_CONFIG_KEY_BV_SOLVER,
  CTX_CONFIG_KEY_MODE,
  CTX_CONFIG_KEY_MODEL_INTERPOLATION,
  CTX_CONFIG_KEY_SOLVER_TYPE,
  CTX_CONFIG_KEY_TRACE_TAGS,
  CTX_CONFIG_KEY_UF_SOLVER,
};




/*
 * CONTEXT SETTING FOR A GIVEN LOGIC CODE
 */

/*
 * Conversion of SMT logic code to a default architecture code
 * -1 means not supported
 *
 * We don't use AUTO_IDL, AUTO_RDL, IFW or RFW here since
 * the Floyd-Warshall solvers don't support all use modes.
 *
 * IMPORTANT: this array is used by the API in config_for_logic.
 */
static const int32_t logic2arch[NUM_SMT_LOGICS] = {
  CTX_ARCH_NOSOLVERS,  // NONE

  -1,                  // AX
  -1,                  // BV  (supported by EF)
  -1,                  // IDL (supported by EF)
  -1,                  // LIA (supported by EF)
  -1,                  // LRA (supported by EF)
  -1,                  // LIRA
  -1,                  // NIA
  -1,                  // NRA
  -1,                  // NIRA
  -1,                  // RDL
  -1,                  // UF
  -1,                  // ABV
  -1,                  // ALIA
  -1,                  // ALRA
  -1,                  // ALIRA
  -1,                  // ANIA
  -1,                  // ANRA
  -1,                  // ANIRA
  -1,                  // AUF
  -1,                  // UFBV
  -1,                  // UFBVLIA
  -1,                  // UFIDL
  -1,                  // UFLIA
  -1,                  // UFLRA
  -1,                  // UFLIRA
  -1,                  // UFNIA
  -1,                  // UFNRA
  -1,                  // UFNIRA
  -1,                  // UFRDL
  -1,                  // AUFBV
  -1,                  // AUFLIA
  -1,                  // AUFLRA
  -1,                  // AUFLIRA
  -1,                  // AUFNIA
  -1,                  // AUFNRA
  -1,                  // AUFNIRA

  CTX_ARCH_EGFUN,      // QF_AX
  CTX_ARCH_BV,         // QF_BV
  CTX_ARCH_SPLX,       // QF_IDL
  CTX_ARCH_SPLX,       // QF_LIA
  CTX_ARCH_SPLX,       // QF_LRA
  CTX_ARCH_SPLX,       // QF_LIRA
  CTX_ARCH_MCSAT,      // QF_NIA
  CTX_ARCH_MCSAT,      // QF_NRA
  CTX_ARCH_MCSAT,      // QF_NIRA
  CTX_ARCH_SPLX,       // QF_RDL
  CTX_ARCH_EG,         // QF_UF
  CTX_ARCH_EGFUNBV,    // QF_ABV
  CTX_ARCH_EGFUNSPLX,  // QF_ALIA
  CTX_ARCH_EGFUNSPLX,  // QF_ALRA
  CTX_ARCH_EGFUNSPLX,  // QF_ALIRA
  CTX_ARCH_MCSAT,      // QF_ANIA
  CTX_ARCH_MCSAT,      // QF_ANRA
  CTX_ARCH_MCSAT,      // QF_ANIRA
  CTX_ARCH_EGFUN,      // QF_AUF
  CTX_ARCH_EGBV,       // QF_UFBV
  CTX_ARCH_EGSPLXBV,   // QF_UFBVLIA

  CTX_ARCH_EGSPLX,     // QF_UFIDL
  CTX_ARCH_EGSPLX,     // QF_UFLIA
  CTX_ARCH_EGSPLX,     // QF_UFLRA
  CTX_ARCH_EGSPLX,     // QF_UFLIRA
  CTX_ARCH_MCSAT,      // QF_UFNIA
  CTX_ARCH_MCSAT,      // QF_UFNRA
  CTX_ARCH_MCSAT,      // QF_UFNIRA
  CTX_ARCH_EGSPLX,     // QF_UFRDL
  CTX_ARCH_EGFUNBV,    // QF_AUFBV
  CTX_ARCH_EGFUNSPLX,  // QF_AUFLIA
  CTX_ARCH_EGFUNSPLX,  // QF_AUFLRA
  CTX_ARCH_EGFUNSPLX,  // QF_AUFLIRA
  CTX_ARCH_MCSAT,      // QF_AUFNIA
  CTX_ARCH_MCSAT,      // QF_AUFNRA
  CTX_ARCH_MCSAT,      // QF_AUFNIRA

  CTX_ARCH_EGFUNSPLXBV,  // ALL interpreted as QF_AUFLIRA + QF_BV
};



/*
 * WHICH ARITHMETIC FRAGMENTS REQUIRE THE DIOPHANTINE SUBSOLVER
 */
static const bool fragment2iflag[NUM_ARITH_FRAGMENTS+1] = {
  false,  // IDL
  false,  // RDL
  true,   // LIA
  false,  // LRA
  true,   // LIRA
  true,   // NIA
  false,  // NRA
  true,   // NIRA
  false,  // no arithmetic
};


/*
 * Default configuration:
 * - enable PUSH/POP
 * - solver type = DPLL(T)
 * - no logic specified
 * - arith fragment = LIRA
 * - all solvers set to defaults
 */
static const ctx_config_t default_config = {
  CTX_MODE_PUSHPOP,       // mode
  CTX_SOLVER_TYPE_DPLLT,  // DPLLT solver
  SMT_UNKNOWN,            // logic
  CTX_CONFIG_DEFAULT,     // uf
  CTX_CONFIG_DEFAULT,     // array
  CTX_CONFIG_DEFAULT,     // bv
  CTX_CONFIG_DEFAULT,     // arith
  ARITH_LIRA,             // fragment
  false,                  // model interpolation
  NULL,                   // trace tags
};





/*
 * DIRECT CONFIGURATION
 */
int32_t arch_for_logic(smt_logic_t code) {
  assert(code != SMT_UNKNOWN);
  return logic2arch[code];
}

bool iflag_for_logic(smt_logic_t code) {
  assert(code != SMT_UNKNOWN);
  return fragment2iflag[arith_fragment(code)];
}



/*
 * CONFIG OBJECT
 */

/*
 * Initialize config to the default configuration
 */
void init_config_to_defaults(ctx_config_t *config) {
  *config = default_config;
}



/*
 * Set a default configuration to support the given logic
 * - return -1 if the logic name is not recognized
 * - return -2 if we don't support the logic yet
 * - return 0 otherwise
 *
 * If the function returns 0, the logic field is updated.
 * All other fields are left unchanged.
 */
int32_t config_set_logic(ctx_config_t *config, const char *logic) {
  smt_logic_t code;
  int32_t r;

  code = smt_logic_code(logic);
  if (code == SMT_UNKNOWN) {
    r = -1;
  } else if (logic2arch[code] < 0) {
    r = -2;
  } else {
    config->logic = (smt_logic_t) code;
    r = 0;
  }

  return r;
}


/*
 * Convert value to a solver
 */
static int32_t set_solver_code(const char *value, solver_code_t *dest) {
  int32_t v, r;

  v = parse_as_keyword(value, solver_code_names, solver_code, NUM_SOLVER_CODES);
  if (v < 0) {
    r = -2;
  } else if (v >= CTX_CONFIG_AUTO) {
    r = -3;
  } else {
    assert(v == CTX_CONFIG_DEFAULT || v == CTX_CONFIG_NONE);
    *dest = (solver_code_t) v;
    r = 0;
  }

  return r;
}


/*
 * Set an individual field in config
 * - key = field name
 * - value = value for that field
 *
 * Return code:
 *   -1 if the key is not recognized
 *   -2 if the value is not recognized
 *   -3 if the value is not valid for the key
 *    0 otherwise
 */
int32_t config_set_field(ctx_config_t *config, const char *key, const char *value) {
  int32_t k, v, r;
  arith_fragment_t arith;

  r = 0; // return code

  k = parse_as_keyword(key, config_key_names, config_key, NUM_CONFIG_KEYS);
  switch (k) {
  case CTX_CONFIG_KEY_MODE:
    v = parse_as_keyword(value, mode_names, mode, NUM_MODES);
    if (v < 0) {
      r = -2;
    } else {
      config->mode = v;
    }
    break;

  case CTX_CONFIG_KEY_SOLVER_TYPE:
    v = parse_as_keyword(value, solver_type_names, solver_type, NUM_SOLVER_TYPES);
    if (v < 0) {
      r = -2;
    } else {
      config->solver_type = v;
    }
    break;

  case CTX_CONFIG_KEY_TRACE_TAGS:
    config->trace_tags = safe_strdup(value);
    break;

  case CTX_CONFIG_KEY_ARITH_FRAGMENT:
    arith = arith_fragment_code(value);
    if (arith == ARITH_NONE) {
      r = -2;
    } else {
      config->arith_fragment = arith;
    }
    break;

  case CTX_CONFIG_KEY_UF_SOLVER:
    r = set_solver_code(value, &config->uf_config);
    break;

  case CTX_CONFIG_KEY_ARRAY_SOLVER:
    r = set_solver_code(value, &config->array_config);
    break;

  case CTX_CONFIG_KEY_BV_SOLVER:
    r = set_solver_code(value, &config->bv_config);
    break;

  case CTX_CONFIG_KEY_ARITH_SOLVER:
    v = parse_as_keyword(value, solver_code_names, solver_code, NUM_SOLVER_CODES);
    if (v < 0) {
      r = -2;
    } else {
      assert(0 <= v && v <= NUM_SOLVER_CODES);
      config->arith_config = v;
    }
    break;
  case CTX_CONFIG_KEY_MODEL_INTERPOLATION:
    v = parse_as_boolean(value, &config->model_interpolation);
    if (v < 0) {
      r = -2;
    }
    break;
  default:
    assert(k == -1);
    r = -1;
    break;
  }

  return r;
}



/*
 * Auxiliary functions to build architecture codes incrementally
 * - each function takes an integer a: a is either a valid architecture
 *   code or -1
 * - then the function adds a new solver component to a: this results
 *   in either a new valid code or -1 if the new component is not compatible with a.
 *
 * Important: we assume that the components are added in the following
 * order: egraph, array solver, bitvector solver, arithmetic solver
 */
static inline int32_t arch_add_egraph(int32_t a) {
  if (a == CTX_ARCH_NOSOLVERS) {
    a = CTX_ARCH_EG;
  } else {
    a = -1;
  }
  return a;
}

static int32_t arch_add_array(int32_t a) {
  if (a == CTX_ARCH_EG || a == CTX_ARCH_NOSOLVERS) {
    a = CTX_ARCH_EGFUN; // array requires egraph so we add both implicitly
  } else {
    a = -1;
  }
  return a;
}

static int32_t arch_add_bv(int32_t a) {
  switch (a) {
  case CTX_ARCH_NOSOLVERS:
    a = CTX_ARCH_BV;
    break;

  case CTX_ARCH_EG:
    a = CTX_ARCH_EGBV;
    break;

  case CTX_ARCH_EGFUN:
    a = CTX_ARCH_EGFUNBV;
    break;

  default:
    a = -1;
    break;
  }

  return a;
}

// add the simplex solver
static int32_t arch_add_simplex(int32_t a) {
  switch (a) {
  case CTX_ARCH_NOSOLVERS:
    a = CTX_ARCH_SPLX;
    break;

  case CTX_ARCH_EG:
    a = CTX_ARCH_EGSPLX;
    break;

  case CTX_ARCH_EGFUN:
    a = CTX_ARCH_EGFUNSPLX;
    break;

  case CTX_ARCH_EGBV:
    a = CTX_ARCH_EGSPLXBV;
    break;

  case CTX_ARCH_EGFUNBV:
    a = CTX_ARCH_EGFUNSPLXBV;
    break;

  default:
    a = -1;
    break;
  }

  return a;
}

// add a Floyd-Warshall solver
static int32_t arch_add_ifw(int32_t a) {
  if (a == CTX_ARCH_NOSOLVERS) {
    a = CTX_ARCH_IFW;
  } else {
    a = -1;
  }
  return a;
}

static int32_t arch_add_rfw(int32_t a) {
  if (a == CTX_ARCH_NOSOLVERS) {
    a = CTX_ARCH_RFW;
  } else {
    a = -1;
  }
  return a;
}


// add solver identified by code c to a
static int32_t arch_add_arith(int32_t a, solver_code_t c) {
  switch (c) {
  case CTX_CONFIG_NONE:  // no arithmetic solver
    break;

  case CTX_CONFIG_DEFAULT:  // simplex is the default
  case CTX_CONFIG_AUTO:     // auto = simplex here too
  case CTX_CONFIG_ARITH_SIMPLEX:
    a = arch_add_simplex(a);
    break;

  case CTX_CONFIG_ARITH_IFW:
    a = arch_add_ifw(a);
    break;

  case CTX_CONFIG_ARITH_RFW:
    a = arch_add_rfw(a);
    break;
  }
  return a;
}


/*
 * Check whether the architecture code a is compatible with mode
 * - current restriction: IFW and RFW don't support PUSH/POP or MULTIPLE CHECKS
 */
static bool arch_supports_mode(context_arch_t a, context_mode_t mode) {
  return (a != CTX_ARCH_IFW && a != CTX_ARCH_RFW) || mode == CTX_MODE_ONECHECK;
}


/*
 * Check whether the architecture is supported.
 */
static bool arch_is_supported(context_arch_t a) {
#if HAVE_MCSAT
  return true; // all architectures are supported
#else
  return a != CTX_ARCH_MCSAT;
#endif
}


/*
 * Check whether config is valid (and supported by this version of Yices)
 * and convert it to a tuple (arch, mode, iflag, qflag)
 * - arch = architecture code as defined in context.h
 * - mode = one of the context's modes
 * - iflag = true if the integer solver (in simplex) is required
 * - qflag = true if support for quantifiers is required
 *
 * Return code:
 *   0 if the config is valid and supported
 *  -1 if the config is invalid
 *  -2 if the config is valid but not currently supported
 *  -3 if the solver combination is valid but does not support the specified mode
 */
int32_t decode_config(const ctx_config_t *config, smt_logic_t *logic, context_arch_t *arch, context_mode_t *mode, bool *iflag, bool *qflag) {
  smt_logic_t logic_code;
  int32_t a, r;

  r = 0; // default return code

  logic_code = config->logic;
  if (logic_code != SMT_UNKNOWN) {
    /*
     * The intended logic is specified
     */
    assert(0 <= logic_code && logic_code < NUM_SMT_LOGICS);

    /*
     * Special case: difference logic + mode = ONECHECK + arith_config == AUTO
     */
    if (config->arith_config == CTX_CONFIG_AUTO && config->mode == CTX_MODE_ONECHECK) {
      if (logic_code == QF_IDL) {
	*logic = QF_IDL;
	*arch = CTX_ARCH_AUTO_IDL;
	*mode = CTX_MODE_ONECHECK;
	*iflag = false;
	*qflag = false;
	goto done;
      }

      if (logic_code == QF_RDL) {
	*logic = QF_RDL;
	*arch = CTX_ARCH_AUTO_RDL;
	*mode = CTX_MODE_ONECHECK;
	*iflag = false;
	*qflag = false;
	goto done;
      }
    }

    a = logic2arch[logic_code];
    if (a < 0 || !arch_is_supported(a)) {
      // not supported
      r = -2;
    } else {
      // good configuration
      *logic = logic_code;
      *arch = (context_arch_t) a;
      *iflag = iflag_for_logic(logic_code);
      *qflag = qflag_for_logic(logic_code);
      *mode = config->mode;
    }

  } else if (config->solver_type == CTX_SOLVER_TYPE_MCSAT) {
    if (arch_is_supported(CTX_ARCH_MCSAT)) {
      /*
       * MCSAT solver/no logic specified
       */
      *logic = SMT_UNKNOWN;
      *arch = CTX_ARCH_MCSAT;
      *mode = CTX_MODE_PUSHPOP;
      *iflag = false;
      *qflag = false;
    } else {
      // not compiled with MCSAT support so this is not supported
      r = -2;
    }

  } else {
    /*
     * No logic specified.
     */

    a = CTX_ARCH_NOSOLVERS;
    if (config->uf_config == CTX_CONFIG_DEFAULT) {
      a = arch_add_egraph(a);
    }
    if (config->array_config == CTX_CONFIG_DEFAULT) {
      a = arch_add_array(a);
    }
    if (config->bv_config == CTX_CONFIG_DEFAULT) {
      a = arch_add_bv(a);
    }
    a = arch_add_arith(a, config->arith_config);

    // a is either -1 or an architecture code
    if (a < 0) {
      r = -1; // invalid combination of solvers
    } else if (arch_supports_mode(a, config->mode)) {
      // good configuration
      *logic = SMT_UNKNOWN;
      *arch = (context_arch_t) a;
      *iflag = fragment2iflag[config->arith_fragment];
      *qflag = false;
      *mode = config->mode;
    } else {
      // mode is not supported by the solvers
      r = -3;
    }
  }

 done:
  return r;
}


/*
 * Cleanup a configutation descriptor
 */
void delete_config(ctx_config_t *config) {
  safe_free(config->trace_tags);
}


/*
 * Check whether a logic is supported by the MCSAT solver
 */
bool logic_is_supported_by_mcsat(smt_logic_t code) {
  return code == SMT_ALL || !logic_has_quantifiers(code);
}

/*
 * Check whether a logic requires the MCSAT solver
 */
bool logic_requires_mcsat(smt_logic_t code) {
  return arch_for_logic(code) == CTX_ARCH_MCSAT;
}

/*
 * Check whether a logic is supported by the exists/forall solver
 * - logics with quantifiers and BV or linear arithmetic are supported
 * - logic "NONE" == purely Boolean is supported too
 */
bool logic_is_supported_by_ef(smt_logic_t code) {
  return code == NONE || code == BV || code == IDL || code == LRA || code == RDL || code == LIA || code == UF;
}


/*
 * Context architecture for a logic supported by EF
 */
int32_t ef_arch_for_logic(smt_logic_t code) {
  switch (code) {
  case NONE:
    return CTX_ARCH_NOSOLVERS;

  case UF:
    return CTX_ARCH_EG;

  case BV:
    return CTX_ARCH_BV;

  case IDL:
  case LRA:
  case RDL:
  case LIA:
    return CTX_ARCH_SPLX;

  default:
    return -1;
  }
}
