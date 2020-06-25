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
 * Build the EF-problem descriptor from the set of assertions
 * - n = number of assertions
 * - assertions = array of n Boolean terms
 * - do nothing if efprob exists already
 * - store the internalization code in the global efcode flag
 */
extern void build_ef_problem(ef_client_t *efc, uint32_t n, term_t *assertions, ptr_hmap_t *patterns);

/*
 * Call the exists/forall solver on an array of assertions.
 * - n = number of assertions
 * - assertions =  array of n Boolean terms
 * - parameters = search parameters to be used by the two internal contexts
 * - logic_code = quantifier-free logic for the contexts
 * - arch = context archtitecture
 * - tracer = NULL or an optional tracer for verbose output
 *
 * logic_code and arch are used to initialize the two internal contexts.
 * logic_code must be quantifier free and arch must be a context
 * architecture compatible with this logic.
 */
extern void ef_solve(ef_client_t *efc, uint32_t m, term_t *assertions, param_t *parameters,
		     smt_logic_t logic_code, context_arch_t arch, tracer_t *tracer, ptr_hmap_t *patterns);


/*
 * Code to indicate why ef_get_model returned NULL 
 */
typedef enum {
  EFMODEL_CODE_NO_ERROR,
  EFMODEL_CODE_NO_MODEL,
  EFMODEL_CODE_NOT_SOLVED,
} efmodel_error_code_t;

#define NUM_EFMODEL_ERROR_CODES 3

extern const char *const efmodelcode2error[NUM_EFMODEL_ERROR_CODES];

/*
 * Model from the ef client.
 * Return NULL if there is no model and set code to indicate the error.
 */
extern model_t *ef_get_model(ef_client_t *efc, efmodel_error_code_t *code);


#endif /* __EF_CLIENT_H */
