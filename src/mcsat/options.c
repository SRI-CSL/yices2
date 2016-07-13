/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include "options.h"

extern void init_mcsat_options(mcsat_options_t *opts) {
  opts->nra_nlsat = false;
  opts->nra_mgcd = false;
}

