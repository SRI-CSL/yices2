/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 *  The client is one of yices2 or yices-smt2 (i.e. yices_reval.c and smt2_commands.c )
 *
 */


#ifndef __EF_CLIENT_H
#define __EF_CLIENT_H

#include <stdint.h>
#include <stdbool.h>

#include "exists_forall/ef_analyze.h"
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
 * These are essentially the old ef globals found in yices_reval and smt2_command.
 *
 */
typedef struct ef_client_s {
  ef_param_t ef_parameters;
  // problem built from the delayed assertions
  ef_prob_t *efprob;
  // ef solver
  ef_solver_t *efsolver;
  // result from ef_analyze of  the conversion to exists/forall
  ef_code_t efcode;
  // have we solved already?
  bool efdone;
} ef_client_t;


extern void init_ef_client(ef_client_t *ef_client);

extern void delete_ef_client(ef_client_t *ef_client);










#endif /* __EF_CLIENT_H */
