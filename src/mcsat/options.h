/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#ifndef MCSAT_OPTIONS_H_
#define MCSAT_OPTIONS_H_

#include <stdbool.h>
#include <stdint.h>

/**
 * Options for the mcsat solver.
 */
typedef struct mcsat_options_s {
  bool nra_mgcd;
  bool nra_nlsat;
} mcsat_options_t;

/** Initialize options with default values. */
extern void init_mcsat_options(mcsat_options_t *opts);


#endif /* MCSAT_OPTIONS_H_ */
