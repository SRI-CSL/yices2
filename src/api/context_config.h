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


/*
 * The possible logic codes are defined in smt_logic_codes.h
 *
 * The possible modes are defined in context.h:
 *  CTX_MODE_ONECHECK
 *  CTX_MODE_MULTICHECKS
 *  CTX_MODE_PUSHPOP
 *  CTX_MODE_INTERACTIVE
 */
#include "api/smt_logic_codes.h"
#include "context/context.h"

/*
 * Codes for the arithmetic fragments
 */
typedef enum arith_fragment {
  CTX_CONFIG_ARITH_IDL,       // integer difference logic
  CTX_CONFIG_ARITH_RDL,       // real difference logic
  CTX_CONFIG_ARITH_LRA,       // linear real arithmetic
  CTX_CONFIG_ARITH_LIA,       // linear integer arithmetic
  CTX_CONFIG_ARITH_LIRA,      // mixed linear arithmetic  (default)
  CTX_CONFIG_ARITH_NRA,       // non-linear, real arithmetic
  CTX_CONFIG_ARITH_NIA,       // non-linear, integer arithmetic
  CTX_CONFIG_ARITH_NIRA,      // non-linear, mixed arithmetic
} arith_fragment_t;

#define NUM_ARITH_FRAGMENTS (CTX_CONFIG_ARITH_NIRA+1)


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
  context_mode_t    mode;
  smt_logic_t       logic;
  solver_code_t     uf_config;
  solver_code_t     array_config;
  solver_code_t     bv_config;
  solver_code_t     arith_config;
  arith_fragment_t  arith_fragment;
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
 * "arith-solver".
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



#endif /* __CONTEXT_CONFIG_H */
