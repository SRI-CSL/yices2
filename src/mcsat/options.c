/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include "options.h"

#include <stddef.h>

extern void init_mcsat_options(mcsat_options_t *opts) {
  opts->na_nlsat = false;
  opts->na_mgcd = false;
  opts->na_bound = false;
  opts->na_bound_min = -1;
  opts->na_bound_max = -1;
  opts->bv_var_size = -1;
  opts->model_interpolation = false;
  opts->partial_restart = false;
  opts->l2o = false;
}

