/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Parameters for the EF client.
 */

#include "exists_forall/ef_parameters.h"

void init_ef_params(ef_param_t *p) {
  p->flatten_iff = false;
  p->flatten_ite = false;
  p->gen_mode = EF_GEN_AUTO_OPTION;
  p->max_samples = 5;
  p->max_iters = 100;
}

