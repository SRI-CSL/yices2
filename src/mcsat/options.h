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

#ifndef MCSAT_OPTIONS_H_
#define MCSAT_OPTIONS_H_

#include "utils/int_vectors.h"

#include <stdbool.h>
#include <stdint.h>

/**
 * Options for the mcsat solver.
 */
typedef struct mcsat_options_s {
  bool nra_mgcd;
  bool nra_nlsat;
  bool nra_bound;
  bool l2o;
  int32_t nra_bound_min;
  int32_t nra_bound_max;
  int32_t bv_var_size;
  bool model_interpolation;
} mcsat_options_t;

#define DEFAULT_MCSAT_NRA_MGCD false
#define DEFAULT_MCSAT_NRA_NLSAT false
#define DEFAULT_MCSAT_NRA_BOUND false
#define DEFAULT_MCSAT_L2O false
#define DEFAULT_MCSAT_NRA_BOUND_MIN -1
#define DEFAULT_MCSAT_NRA_BOUND_MAX -1
#define DEFAULT_MCSAT_BV_VAR_SIZE -1
#define DEFAULT_MCSAT_MODEL_INTERPOLATION false

/** Initialize options with default values. */
extern void init_mcsat_options(mcsat_options_t *opts);

#endif /* MCSAT_OPTIONS_H_ */
