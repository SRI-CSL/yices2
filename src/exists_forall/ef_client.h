/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Top-level support for EF solving
 *
 * This code provides common functions that are used by both the
 * yices2 and yices-smt2 front ends (i.e. yices_reval.c and smt2_commands.c).
 */

#ifndef __EF_CLIENT_H
#define __EF_CLIENT_H

#include <stdint.h>
#include <stdbool.h>

#include "exists_forall/ef_analyze.h"
#include "exists_forall/efsolver.h"
#include "exists_forall/ef_parameters.h"

/*
 * These are essentially the old ef globals found in yices_reval and smt2_command.
 *
 */
typedef struct ef_client_s {
  // the ef parameters
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

/*
 * Build the EF-problem descriptor from the set of delayed assertions
 * - do nothing if efprob exists already
 * - store the internalization code in the global efcode flag
 */
extern void build_ef_problem(ef_client_t *efc, ivector_t *assertions);


extern void ef_solve(ef_client_t *efc, ivector_t *assertions, param_t *parameters,
		     smt_logic_t logic_code, context_arch_t arch, tracer_t *tracer);

/*
 * Code to indicate why ef_get_model returned NULL 
 */
extern const char *const efmodelcode2error[];

/*
 * Model from the ef client; if there is no model, code  will indicate the reason.
 */
extern model_t *ef_get_model(ef_client_t *efc, int32_t *code);


#endif /* __EF_CLIENT_H */
