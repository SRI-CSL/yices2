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

#include "exists_forall/ef_client.h"


/*
 * Initialize the ef_parameters to default values
 * We need to be able to tweak these parameters in a similar fashion to yices_reval.
 */
static inline void init_ef_params(ef_client_t *ef_client){
  ef_client->ef_parameters.flatten_iff = false;
  ef_client->ef_parameters.flatten_ite = false;
  ef_client->ef_parameters.gen_mode = EF_GEN_AUTO_OPTION;
  ef_client->ef_parameters.max_samples = 5;
  ef_client->ef_parameters.max_iters = 100;
}

void init_ef_client(ef_client_t *ef_client) {
  init_ef_params(ef_client);
  ef_client->efprob = NULL;
  ef_client->efsolver = NULL;
  ef_client->efcode = EF_NO_ERROR;
  ef_client->efdone = false;
}

void delete_ef_client(ef_client_t *ef_client) {
  if (ef_client->efprob != NULL) {
    delete_ef_prob(ef_client->efprob);
    safe_free(ef_client->efprob);
    ef_client->efprob = NULL;
  }
  if (ef_client->efsolver != NULL) {
    delete_ef_solver(ef_client->efsolver);
    safe_free(ef_client->efsolver);
    ef_client->efsolver = NULL;
  }
  ef_client->efdone = false;
}
