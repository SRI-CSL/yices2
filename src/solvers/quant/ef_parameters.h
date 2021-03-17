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

#include "solvers/quant/quant_parameters.h"

#define DEF_MBQI_MAX_ITERS              10000
#define DEF_MBQI_MAX_LEMMAS_PER_ROUND   5
#define DEF_EMATCH_EN   true

typedef enum ef_gen_option {
  EF_NOGEN_OPTION,        // option 1 above
  EF_GEN_BY_SUBST_OPTION, // option 2 above
  EF_GEN_BY_PROJ_OPTION,  // model-based projection (cheap quantifier elimination)
  EF_GEN_AUTO_OPTION,     // select between PROJ or SUBST depending on variables
} ef_gen_option_t;

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

  uint32_t max_numlearnt_per_round;
  bool ematching;

  /*
   * QUANT SOLVER PARAMETERS
   * - ematch_mode: mode for ematching
   */

  uint32_t ematch_inst_per_round;
  uint32_t ematch_inst_per_search;
  uint32_t ematch_inst_total;
  uint32_t ematch_rounds_per_search;
  uint32_t ematch_search_total;

  uint32_t ematch_exec_max_fdepth;
  uint32_t ematch_exec_max_vdepth;
  uint32_t ematch_exec_max_fapps;
  uint32_t ematch_exec_max_matches;

  uint32_t ematch_cnstr_epsilon;
  double ematch_cnstr_alpha;
  uint32_t ematch_term_epsilon;
  double ematch_term_alpha;

  int32_t ematch_cnstr_mode;
  int32_t ematch_term_mode;

} ef_param_t;


/*
 * Initialize p with default values
 */
extern void init_ef_params(ef_param_t *p);


#endif /* __EF_PARAMETERS_H */
