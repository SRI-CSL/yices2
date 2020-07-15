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
 * Client utilities for EF-solving
 */

#if defined(CYGWIN) || defined(MINGW)
#ifndef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__ __declspec(dllexport)
#endif
#endif

#include <assert.h>
#include <stdint.h>

#include "api/yices_globals.h"

#include "exists_forall/ef_client.h"

#include "yices.h"
#include "yices_exit_codes.h"


void init_ef_client(ef_client_t *efc) {
  init_ef_params(&efc->ef_parameters);
  efc->efprob = NULL;
  efc->efsolver = NULL;
  efc->efcode = EF_NO_ERROR;
  efc->efdone = false;
}

void delete_ef_client(ef_client_t *efc) {
  if (efc->efprob != NULL) {
    delete_ef_prob(efc->efprob);
    safe_free(efc->efprob);
    efc->efprob = NULL;
  }
  if (efc->efsolver != NULL) {
    delete_ef_solver(efc->efsolver);
    safe_free(efc->efsolver);
    efc->efsolver = NULL;
  }
  efc->efdone = false;
}


/*
 * Build the EF-problem descriptor from the set of delayed assertions
 * - n = number of assertions
 * - assertions = array of n Boolean terms
 * - do nothing if efprob exists already
 * - store the internalization code in the global efcode flag
 */
void build_ef_problem(ef_client_t *efc, uint32_t n, term_t *assertions, ptr_hmap_t *patterns) {
  ef_analyzer_t analyzer;

  if (efc->efprob == NULL) {
    efc->efprob = (ef_prob_t *) safe_malloc(sizeof(ef_prob_t));
    init_ef_analyzer(&analyzer, __yices_globals.manager);
    init_ef_prob(efc->efprob, __yices_globals.manager, patterns);
    efc->efcode = ef_analyze(&analyzer, efc->efprob, n, assertions,
			     efc->ef_parameters.flatten_ite,
			     efc->ef_parameters.flatten_iff,
			     efc->ef_parameters.ematching);
    delete_ef_analyzer(&analyzer);
  }
}


const char *const efmodelcode2error[NUM_EFMODEL_ERROR_CODES] = {
  "No error",
  "No model, did not find a solution",
  "Can't build a model. Call the exists forall solver first"
};


/*
 * Model from the ef client; if there is no model, code  will indicate the reason.
 */
model_t *ef_get_model(ef_client_t *efc, efmodel_error_code_t *code){
  ef_solver_t *efsolver;
  model_t *mdl;

  assert(code != NULL);

  mdl = NULL;
  efsolver = efc->efsolver;

  if (efsolver == NULL || !efc->efdone) {
    *code = EFMODEL_CODE_NOT_SOLVED;
  } else if (efsolver->status == EF_STATUS_SAT) {
    *code = EFMODEL_CODE_NO_ERROR;
    mdl = efsolver->exists_model;
    assert(mdl != NULL);
  } else {
    *code = EFMODEL_CODE_NO_MODEL;
  }

  return mdl;
}


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
void ef_solve(ef_client_t *efc, uint32_t n, term_t *assertions, param_t *parameters,
	      smt_logic_t logic_code, context_arch_t arch, tracer_t *tracer, ptr_hmap_t *patterns) {
  build_ef_problem(efc, n, assertions, patterns);

  if (efc->efcode == EF_NO_ERROR){
    if (!efc->efdone) {
      assert(efc->efsolver == NULL);
      efc->efsolver = (ef_solver_t *) safe_malloc(sizeof(ef_solver_t));
      init_ef_solver(efc->efsolver, efc->efprob, logic_code, arch);
      if (tracer != NULL) {
	ef_solver_set_trace(efc->efsolver, tracer);
      }

      /*
       * If the problem has integer or real variables, we force GEN_BY_PROJ
       */
      ef_solver_check(efc->efsolver, parameters, efc->ef_parameters.gen_mode,
		      efc->ef_parameters.max_samples, efc->ef_parameters.max_iters, efc->ef_parameters.max_numlearnt,
		      efc->ef_parameters.ematching);
      efc->efdone = true;
    }
  }
}

