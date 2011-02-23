/*
 * OBJECT TO STORE CONTEXT CONFIGURATIONS
 */

/*
 * When a context is created, one can specify which solver combination
 * it includes and which features it supports.  A context configuration
 * is a data structure to store this information. It's used as an opaque
 * object in the Yices API.
 *
 * A configuration includes:
 * - logic: which logic to support. default = NONE
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
#include <stdbool.h>


/*
 * The possible logic codes are defined in smt_logic_codes.h
 *
 * The possible modes are defined in context.h:
 *  CTX_MODE_ONECHECK
 *  CTX_MODE_MULTICHECKS
 *  CTX_MODE_PUSHPOP
 *  CTX_MODE_INTERACTIVE
 */
#include "smt_logic_codes.h"
#include "context.h"

/*
 * Codes for the arithmetic fragments
 */
typedef enum arith_fragment {
  CTX_CONFIG_ARITH_IDL,       // integer difference logic
  CTX_CONFIG_ARITH_RDL,       // real difference logic
  CTX_CONFIG_ARITH_LRA,       // linear real arithmetic
  CTX_CONFIG_ARITH_LIA,       // linear integer arithmetic
  CTX_CONFIG_ARITH_LIRA,      // mixed linear arithmetic
  CTX_CONFIG_ARITH_NRA,       // non-linear, real arithmetic
  CTX_CONFIG_ARITH_NIA,       // non-linear, integer arithmetic
  CTX_CONFIG_ARITH_NIRA,      // non-linear, mixed arithmetic
} arith_fragment_t;


/*
 * Codes for each solver
 */
typedef enum solver_code {
  CTX_CONFIG_NONE,            // no solver of that type
  CTX_CONFIG_DEFAULT,         // the default solver of that type
  CTX_CONFIG_AUTO,            // decide based on the logic + mode

  // the next codes are for the arithmetic solver only
  CTX_CONFIG_ARITH_SIMPLEX,   // simplex solver
  CTX_CONFIG_ARITH_IFW,       // integer Floyd-Warshall solver
  CTX_CONFIG_ARITH_RFW,       // real Floyd-Warshall solver
} solver_code_t;


/*
 * Configuration decriptor
 */
struct ctx_config_s {
  context_mode_t    mode;
  smt_logic_t       logic;
  arith_fragment_t  arith_fragment;
  solver_code_t     uf_config;
  solver_code_t     array_config;
  solver_code_t     bv_config;
  solver_code_t     arith_config;
};



/*
 * Initialize config with the default configuration:
 * - mode = PUSH/POP
 * - logic = UNKNOWN
 * - arith_fragment = LIRA
 * - uf_config = DEFAULT
 * - array_config = DEFAULT
 * - bv_config = DEFAULT
 * - arith_config = DEFAULT
 */
extern void init_config_to_defaults(ctx_config_t *config);


/*
 * Set a default configuration to support the given logic
 * - return -1 if the logic name is not recognized
 * - return -2 if we don't support the logic yet
 * - return 0 otherwise
 *
 * This leaves the mode unchanged and overwrites all the other fields.
 */
extern int32_t default_config_for_logic(ctx_config_t *config, const char *logic);


/*
 * Set a field in config:
 * - key = field name
 * - value = value for that field
 * 
 * Return code:
 *   -1 if the key is not recognized
 *   -2 if the value is not recognized
 *   -3 if the value is not valid for the key
 *    0 otherwise
 */
extern int32_t config_set_field(ctx_config_t *config, const char *key, const char *value);


/*
 * Check whether config is valid (and supported by this version of Yices)
 *
 * If it's valid, then we can build a context with this configuration.
 * This is done by converting config to a tuple (arch, mode, iflag, qflag)
 * - arch = architecture code as defined in context.h
 * - mode = one of the context's modes
 * - iflag = true if the integer solver (in simplex) is required
 * - qflag = true if support for quantifiers is required
 */
extern bool config_is_valid(ctx_config_t *config);


/*
 * Convert config to a context's configuration tuple
 * - config must be valid
 * - arch, mode, iflag, qflag are set 
 */
extern void decode_config(ctx_config_t *config, context_arch_t *arch, context_mode_t *mode, bool *iflag, bool *qflag);


#endif /* __CONTEXT_CONFIG_H */
