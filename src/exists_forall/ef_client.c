/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
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
#include "context/context.h"
#include "exists_forall/ef_client.h"

#include "yices.h"
#include "yices_exit_codes.h"


void init_ef_client(ef_client_t *efc) {
  init_ef_params(&efc->ef_parameters);
  efc->efprob = NULL;
  efc->efsolver = NULL;
  efc->efcode = EF_NO_ERROR;
  efc->has_skolem_functions = false;
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
void build_ef_problem(ef_client_t *efc, uint32_t n, const term_t *assertions, ptr_hmap_t *patterns, param_t *parameters) {
  ef_analyzer_t analyzer;

  if (efc->efprob == NULL) {
    efc->efprob = (ef_prob_t *) safe_malloc(sizeof(ef_prob_t));
    init_ef_analyzer(&analyzer, __yices_globals.manager);
    init_ef_prob(efc->efprob, __yices_globals.manager, patterns, &efc->ef_parameters);
    efc->efcode = ef_analyze(&analyzer, efc->efprob, n, assertions,
			     efc->ef_parameters.flatten_ite,
			     efc->ef_parameters.flatten_iff,
			     efc->ef_parameters.ematching);
    efc->has_skolem_functions = analyzer.num_skolem_funs > 0;
    delete_ef_analyzer(&analyzer);
  }
}



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
 * Same as ef_get_model but also detach the model from efc
 * so that deletion of efc will not delete the model.
 */
model_t *ef_export_model(ef_client_t *efc, efmodel_error_code_t *code) {
  model_t *mdl;

  mdl = ef_get_model(efc, code);
  if (mdl != NULL) {
    assert(mdl == efc->efsolver->exists_model);
    efc->efsolver->exists_model = NULL;
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
void ef_solve(ef_client_t *efc, uint32_t n, const term_t *assertions, param_t *parameters,
	      smt_logic_t logic_code, context_arch_t arch, tracer_t *tracer, ptr_hmap_t *patterns) {
  // disable ematching etc. if we don't have an egraph.
  if (! context_arch_has_egraph(arch)) {
    efc->ef_parameters.ematching = false;
  }
  build_ef_problem(efc, n, assertions, patterns, parameters);

  if (efc->efcode == EF_UNINTERPRETED_FUN) {
    // we have uninterpreted functions as existential variables
    // this is OK if we have an egraph
    // otherwise we check whether some of these exists variables
    // are skolem functions to give a better error report.
    if (context_arch_has_egraph(arch)) {
      // we can try ematching or mbi
      efc->efcode = EF_NO_ERROR;
    } else if (efc->has_skolem_functions) {
      // not an exists/forall problem
      efc->efcode = EF_NESTED_QUANTIFIER;
    }
  }

  if (efc->efcode == EF_NO_ERROR) {
    if (!efc->efdone) {
      assert(efc->efsolver == NULL);
      efc->efsolver = (ef_solver_t *) safe_malloc(sizeof(ef_solver_t));
      init_ef_solver(efc->efsolver, efc->efprob, logic_code, arch);
      if (tracer != NULL) {
	ef_solver_set_trace(efc->efsolver, tracer);
      }
      ef_solver_check(efc->efsolver, parameters, efc->ef_parameters.gen_mode,
			efc->ef_parameters.max_samples, efc->ef_parameters.max_iters,
			efc->ef_parameters.max_numlearnt_per_round,
			efc->ef_parameters.ematching);
      efc->efdone = true;
    }
  }
}

