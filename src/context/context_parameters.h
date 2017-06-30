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
