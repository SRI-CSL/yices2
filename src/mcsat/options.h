/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

#ifndef MCSAT_OPTIONS_H_
#define MCSAT_OPTIONS_H_

#include "utils/int_vectors.h"

#include <stdbool.h>
#include <stdint.h>

/**
 * Options for the mcsat solver.
 */
typedef struct mcsat_options_s {
  bool na_mgcd;
  bool na_nlsat;
  bool na_bound;
  int32_t na_bound_min;
  int32_t na_bound_max;
  int32_t bv_var_size;
  bool model_interpolation;
  bool partial_restart;
  bool l2o;
} mcsat_options_t;

/** Initialize options with default values. */
extern void init_mcsat_options(mcsat_options_t *opts);

#endif /* MCSAT_OPTIONS_H_ */
