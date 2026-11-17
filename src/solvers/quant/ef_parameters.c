/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

/*
 * Parameters for the EF client.
 */

#include "solvers/quant/ef_parameters.h"
#include "solvers/quant/quant_parameters.h"

void init_ef_params(ef_param_t *p) {
  p->flatten_iff = false;
  p->flatten_ite = false;
  p->gen_mode = EF_GEN_AUTO_OPTION;
  p->max_samples = 5;

  p->max_iters = DEF_MBQI_MAX_ITERS;
  p->max_numlearnt_per_round = DEF_MBQI_MAX_LEMMAS_PER_ROUND;
  p->ematching = DEF_EMATCH_EN;

  p->ematch_inst_per_round = DEFAULT_MAX_INSTANCES_PER_ROUND;
  p->ematch_inst_per_search = DEFAULT_MAX_INSTANCES_PER_SEARCH;
  p->ematch_inst_total = DEFAULT_MAX_INSTANCES;
  p->ematch_rounds_per_search = DEFAULT_MAX_ROUNDS_PER_SEARCH;
  p->ematch_search_total = DEFAULT_MAX_SEARCH;

  p->ematch_exec_max_fdepth = DEF_MAX_FDEPTH;
  p->ematch_exec_max_vdepth = DEF_MAX_VDEPTH;
  p->ematch_exec_max_fapps = DEF_MAX_FAPPS;
  p->ematch_exec_max_matches = DEF_MAX_MATCHES;

  p->ematch_cnstr_epsilon = CNSTR_RL_EPSILON_MIN;
  p->ematch_cnstr_alpha = CNSTR_RL_ALPHA_DEFAULT;
  p->ematch_term_epsilon = TERM_RL_EPSILON_MIN;
  p->ematch_term_alpha = TERM_RL_ALPHA_DEFAULT;

  p->ematch_cnstr_mode = DEFAULT_EMATCH_MODE;
  p->ematch_term_mode = DEFAULT_EMATCH_MODE;
}

