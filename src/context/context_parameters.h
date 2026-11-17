/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

#ifndef __CONTEXT_PARAMETERS_H
#define __CONTEXT_PARAMETERS_H

#include <stdbool.h>

#include "context/context_types.h"

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
 * Initialize all parameters to their default
 */
extern void init_ctx_params(ctx_param_t *ctx_parameters);

/*
 * Copy the context's parameters into ctx_parameters
 */
extern void save_ctx_params(ctx_param_t *ctx_parameters, context_t *context);

/*
 * Store some defaults for ctx_parameters based on the logic, architecture, and mode
 */
extern void default_ctx_params(ctx_param_t *ctx_parameters, smt_logic_t logic, context_arch_t arch, context_mode_t mode);


#endif /* __CONTEXT_PARAMETERS */
