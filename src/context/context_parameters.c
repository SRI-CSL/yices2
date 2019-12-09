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

#include "api/context_config.h"
#include "context/context_parameters.h"
#include "context/context_utils.h"

/*
 * Default parameters (these may be overridden by the next function,
 * depending on the logic, architecture, and mode).
 */
void init_ctx_params(ctx_param_t *ctx_parameters) {
  ctx_parameters->var_elim = true;
  ctx_parameters->arith_elim = true;
  ctx_parameters->bvarith_elim = true;
  ctx_parameters->flatten_or = true;
  ctx_parameters->eq_abstraction = true;
  ctx_parameters->keep_ite = false;
  ctx_parameters->splx_eager_lemmas = true;
  ctx_parameters->splx_periodic_icheck = false;
}


/*
 * Set defaults for both based on the logic/architecture/mode and iflag/qflag
 * - this tries to give the same settings as 'yices_create_context'
 */
void default_ctx_params(ctx_param_t *ctx_parameters, smt_logic_t logic, context_arch_t arch, context_mode_t mode) {
  bool iflag;

  assert(ctx_parameters != NULL);
  ctx_parameters->var_elim = true;
  ctx_parameters->arith_elim = true;
  ctx_parameters->bvarith_elim = true;
  ctx_parameters->flatten_or = true;
  ctx_parameters->eq_abstraction = true;
  ctx_parameters->keep_ite = false;
  ctx_parameters->splx_eager_lemmas = true;
  ctx_parameters->splx_periodic_icheck = false;

  // if the logic is UNKNOWN, integer arithmetic may happen
  iflag = (logic == SMT_UNKNOWN) || iflag_for_logic(logic);
  if (iflag) {
    ctx_parameters->splx_periodic_icheck = true;
    if (logic == QF_LIA || logic == QF_LIRA) {
      ctx_parameters->splx_eager_lemmas = true;
    }
  }
}


/*
 * Export the context's options: store them into ctx_parameters
 * - only the options that can be set in yices_reval or smt2_commands are exported
 */
void save_ctx_params(ctx_param_t *ctx_parameters, context_t *context) {
  assert(ctx_parameters != NULL);
  assert(context != NULL);
  ctx_parameters->var_elim = context_var_elim_enabled(context);
  ctx_parameters->arith_elim = context_arith_elim_enabled(context);
  ctx_parameters->bvarith_elim = context_bvarith_elim_enabled(context);
  ctx_parameters->flatten_or = context_flatten_or_enabled(context);
  ctx_parameters->eq_abstraction = context_eq_abstraction_enabled(context);
  ctx_parameters->keep_ite = context_keep_ite_enabled(context);
  ctx_parameters->splx_eager_lemmas = splx_eager_lemmas_enabled(context);
  ctx_parameters->splx_periodic_icheck = splx_periodic_icheck_enabled(context);
}

