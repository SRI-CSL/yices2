/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
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
} ef_param_t;


/*
 * Initialize p with default values
 */
extern void init_ef_params(ef_param_t *p);


#endif /* __EF_PARAMETERS_H */
