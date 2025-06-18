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

#include "options.h"

#include <stddef.h>

extern void init_mcsat_options(mcsat_options_t *opts) {
  opts->model_interpolation = DEFAULT_MCSAT_MODEL_INTERPOLATION;
  opts->nra_mgcd = DEFAULT_MCSAT_NRA_MGCD;
  opts->nra_nlsat = DEFAULT_MCSAT_NRA_NLSAT;
  opts->nra_bound = DEFAULT_MCSAT_NRA_BOUND;
  opts->nra_bound_min = DEFAULT_MCSAT_NRA_BOUND_MIN;
  opts->nra_bound_max = DEFAULT_MCSAT_NRA_BOUND_MAX;
  opts->bv_var_size = DEFAULT_MCSAT_BV_VAR_SIZE;
  opts->l2o = DEFAULT_MCSAT_L2O;
}

void mcsat_options_set_from_params(mcsat_options_t *opts, const param_t *params) {
  if (params != NULL) {
    opts->nra_mgcd = params->mcsat_nra_mgcd;
    opts->nra_nlsat = params->mcsat_nra_nlsat;
    opts->nra_bound = params->mcsat_nra_bound;
    opts->nra_bound_min = params->mcsat_nra_bound_min;
    opts->nra_bound_max = params->mcsat_nra_bound_max;
    opts->bv_var_size = params->mcsat_bv_var_size;
    opts->l2o = params->mcsat_l2o;
  }
}

