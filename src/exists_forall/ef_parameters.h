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
 * Parameters for the EF client.
 */

#ifndef __EF_PARAMETERS_H
#define __EF_PARAMETERS_H

#include <stdbool.h>
#include <stdint.h>

#include "exists_forall/efsolver.h"

/*
 * Parameters for the EF solver
 * - flatten_iff, flatten_ite: control flattening of iff and if-then-else in
 *   ef_analyze
 * - gen_mode = generalization method
 * - max_samples = number of samples (max) used in start (0 means no presampling)
 * - max_iters = bound on the outher iteration in efsolver
 */
typedef struct ef_param_s {
  bool flatten_iff;
  bool flatten_ite;
  ef_gen_option_t gen_mode;
  uint32_t max_samples;
  uint32_t max_iters;
  uint32_t max_numlearnt;
  bool ematching;
} ef_param_t;


/*
 * Initialize p with default values
 */
extern void init_ef_params(ef_param_t *p);


#endif /* __EF_PARAMETERS_H */
