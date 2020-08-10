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

/*
 * When a context is created, one can specify which solver combination
 * it includes and which features it supports. The context
 * initialization function in context.c currently uses bit masks and
 * integer codes to specify the configuration. We don't want to expose
 * these codes to the official API since they are very likely to
 * change when we extend Yices. Instead, we provide opaque
 * context-configuration objects in the API + functions to allocate
 * and set the configuration.
 *
 * A configuration object includes:
 * - solver_type: either "mcsat" or "dpplt"
 * - logic: which logic to support
 * - mode: which set of operations the context supports
 * - uf_solver: whether to use the Egraph or not
 * - bv_solver: whether to use the bitvector solver or not
 * - array_solver: whether to use the array/function solver or not
 * - arith_solver: which arithmetic solver to use
 * - arith_fragment: which fragment of arithmetic to support
 */

#ifndef __CONTEXT_CONFIG_H
#define __CONTEXT_CONFIG_H

#include <stdint.h>

#include "api/smt_logic_codes.h"
#include "context/context_types.h"



/*
 * The possible logic codes are defined in smt_logic_codes.h
 *
 * The arithmetic codes are also in smt_logic_codes.h:
 *    ARITH_IDL
 *    ARITH_RDL
 *    ARITH_LRA
 *    ARITH_LIA
 *    ARITH_LIRA
 *    ARITH_NRA
 *    ARITH_NIA
 *    ARITH_NIRA
 *
 * The possible modes are defined in context_types.h:
 *    CTX_MODE_ONECHECK
 *    CTX_MODE_MULTICHECKS
 *    CTX_MODE_PUSHPOP
 *    CTX_MODE_INTERACTIVE
 */


/*
 * Codes for each solver
 */
typedef enum solver_code {
  CTX_CONFIG_NONE,            // no solver of that type
  CTX_CONFIG_DEFAULT,         // the default solver of that type

  // special code: if mode=ONECHECK then decide
  // the solver based on the assertions.
  CTX_CONFIG_AUTO,

  // the next codes are for the arithmetic solver only
  CTX_CONFIG_ARITH_SIMPLEX,   // simplex solver
  CTX_CONFIG_ARITH_IFW,       // integer Floyd-Warshall solver
  CTX_CONFIG_ARITH_RFW,       // real Floyd-Warshall solver
} solver_code_t;

#define NUM_SOLVER_CODES (CTX_CONFIG_ARITH_RFW+1)



/*
 * Configuration descriptor
 */
struct ctx_config_s {
  context_mode_t        mode;
  context_solver_type_t solver_type;
  smt_logic_t           logic;
  solver_code_t         uf_config;
  solver_code_t         array_config;
  solver_code_t         bv_config;
  solver_code_t         arith_config;
  arith_fragment_t      arith_fragment;
  char*                 trace_tags;
};



/*
 * Initialize config with the default configuration:
 * - mode = PUSH/POP
 * - logic = UNKNOWN
 * - arith_fragment = LIRA
 * - uf_config    = NONE
 * - array_config = NONE
 * - bv_config    = NONE
 * - arith_config = NONE
 * - trace_tags = NULL
 *
 * In this configuration, a context supports propositional logic only.
 */
extern void init_config_to_defaults(ctx_config_t *config);


/*
 * Set config to support the given logic
 * - return -1 if the logic name is not recognized
 * - return -2 if we don't support the logic yet
 * - return 0 otherwise
 *
 * If the function returns 0, the logic field is updated.
 * All other fields are left unchanged.
 */
extern int32_t config_set_logic(ctx_config_t *config, const char *logic);


/*
 * Set a field in config:
 * - key = field name
 * - value = value for that field
 *
 * This can't be used to set config->logic: key must be one of "mode",
 * "arith-fragment", "uf-solver", "array-solver", "bv-solver",
 * "arith-solver" or "trace".
 *
 * Return code:
 *   -1 if the key is not recognized
 *   -2 if the value is not recognized
 *   -3 if the value is not valid for the key
 *    0 otherwise
 */
extern int32_t config_set_field(ctx_config_t *config, const char *key, const char *value);


/*
 * Check whether config is valid, and supported by this version of Yices,
 * and convert it to a tuple (logic, arch, mode, iflag, qflag)
 * - logic = config->logic
 * - arch = architecture code as defined in context.h
 * - mode = one of the context's modes
 * - iflag = true if the integer solver (in simplex) is required
 * - qflag = true if support for quantifiers is required
 *
 * 1) If config->logic is SMT_UNKNOWN then, the solver codes are
 *    examined. The config is valid if the solver combination matches
 *    one of the supported architectures (cf. context.h) and if
 *    the solvers all support the requested mode.
 *
 * 2) if config->logic is QF_IDL or QF_RDL and mode=ONESHOT
 *     and arith solver core is AUTO then we build a context
 *     with architecture CTX_ARCH_AUTO_IDL or CTX_ARCH_AUTO_RDL.
 *     The actual solver to chosen on the first call to assert_formulas.
 *
 * 3) otherwise, if config->logic is specified, then solver codes and
 *    arithmetic fragments are ignored.
 *
 * Return code:
 *  -1 if the config is invalid
 *  -2 if the config is valid but not currently supported
 *   0 if the config is valid and supported
 */
extern int32_t decode_config(const ctx_config_t *config, smt_logic_t *logic, context_arch_t *arch,
                             context_mode_t *mode, bool *iflag, bool *qflag);



/*
 * Cleanup: this frees config->trace_tags is non-NULL.
 */
extern void delete_config(ctx_config_t *config);


/*
 * DIRECT CONFIGURATION
 */

/*
 * To configure a context, we need:
 * - architecture, iflag, qflag
 * - mode
 *
 * The functions below return arch/iflag/qflag for a given logic code.
 * The code must be a valid logic (not SMT_UNKNOWN).
 *
 * Function arch_for_logic returns -1 if we don't support the logic.
 * For IDL and RDL, arch_for_logic returns CTX_ARCH_SPLX (because the
 * alternative solvers IFW and RFW don't support push and pop).
 */
extern int32_t arch_for_logic(smt_logic_t code);

extern bool iflag_for_logic(smt_logic_t code);

static inline bool qflag_for_logic(smt_logic_t code) {
  return logic_has_quantifiers(code);
}

static inline bool logic_is_supported(smt_logic_t code) {
  return arch_for_logic(code) >= 0;
}

/*
 * Variant for MCSAT
 */
extern bool logic_is_supported_by_mcsat(smt_logic_t code);
extern bool logic_requires_mcsat(smt_logic_t code);


/*
 * Variant for the Exists/Forall solver
 */
extern bool logic_is_supported_by_ef(smt_logic_t code);


/*
 * For a logic supported by the exists/forall solver, this gives the
 * architecture for the two internal contexts used by the ef solver.
 *
 * If the logic is not supported by the exists/forall solver, the
 * function returns -1.
 */
extern int32_t ef_arch_for_logic(smt_logic_t code);


#endif /* __CONTEXT_CONFIG_H */
