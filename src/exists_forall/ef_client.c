/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
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
 * - do nothing if efprob exists already
 * - store the internalization code in the global efcode flag
 */
void build_ef_problem(ef_client_t *efc, ivector_t *assertions) {
  ef_analyzer_t analyzer;
  ivector_t *v;

  if (efc->efprob == NULL) {
    v = assertions;

    efc->efprob = (ef_prob_t *) safe_malloc(sizeof(ef_prob_t));
    init_ef_analyzer(&analyzer, __yices_globals.manager);
    init_ef_prob(efc->efprob, __yices_globals.manager);
    efc->efcode = ef_analyze(&analyzer, efc->efprob, v->size, v->data,
			     efc->ef_parameters.flatten_ite,
			     efc->ef_parameters.flatten_iff);
    delete_ef_analyzer(&analyzer);
  }
}


const char * const efmodelcode2error[] = {
  "No error.\n"
  "No model, did not find a solution.\n"
  "Can't build a model. Call the exists forall solver first.\n"
};

/*
 * Model from the ef client; if there is no model, code  will indicate the reason.
 */
model_t *ef_get_model(ef_client_t *efc, int32_t* code){
  ef_solver_t *efsolver;

  assert(code != NULL);
    
  if (efc->efdone) {
    efsolver = efc->efsolver;
    assert(efsolver != NULL);
    if (efsolver->status == EF_STATUS_SAT) {
      assert(efsolver->exists_model != NULL);
      return efsolver->exists_model;
    } else {
      *code = 1;
    }
  } else {
    *code = 2;
  }
  return NULL;
}



void ef_solve(ef_client_t *efc, ivector_t *assertions, param_t *parameters,
	      smt_logic_t logic_code, context_arch_t arch, tracer_t *tracer) {
  build_ef_problem(efc, assertions);

  if (efc->efcode == EF_NO_ERROR){
    if(! efc->efdone) {
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
		      efc->ef_parameters.max_samples, efc->ef_parameters.max_iters);
      efc->efdone = true;
    }
  }
}

