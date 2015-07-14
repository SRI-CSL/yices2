/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 *  The client is one of yices2 or yices-smt2 (i.e. yices_reval.c and smt2_commands.c )
 *
 */


#ifndef __EF_CLIENT_H
#define __EF_CLIENT_H

#include <stdint.h>
#include <stdbool.h>

#include "exists_forall/ef_analyze.h"
#include "exists_forall/efsolver.h"


/*
 * Table to convert  smt_status to a string
 */
static const char* const status2string[] = {
  "idle",
  "searching",
  "unknown",
  "sat",
  "unsat",
  "interrupted",
};



/*
 * Table to convert  ef-solver status to a string
 */
static const char* const ef_status2string[] = {
  "idle",
  "searching",
  "unknown",
  "sat",
  "unsat",
  "interrupted",
  "subst error",
  "tval error",
  "check error",
  "assert error",
  "error",
};


/*
 * Conversion of EF preprocessing codes to string
 */
static const char * const efcode2error[NUM_EF_CODES] = {
  "no error",
  "assertions contain uninterpreted functions",
  "invalid quantifier nesting (not an exists/forall problem)",
  "non-atomic universal variables",
  "non-atomic existential variables",
  "internal error",
};


/*
 * Parameters for the EF solver
 * - flatten_iff, flatten_ite: control flattening of iff and if-then-else in
 *   ef_analyze
 * - gen_mode = generalization method
 * - max_samples = number of samples (max) used in start (0 means no presampling)
 * - max_iters = bound on the outher iteration in efsolver
 */
typedef struct ef_param_s {
  bool flatten_iff;
  bool flatten_ite;
  ef_gen_option_t gen_mode;
  uint32_t max_samples;
  uint32_t max_iters;
} ef_param_t;

/*
 * These are essentially the old ef globals found in yices_reval and smt2_command.
 *
 */
typedef struct ef_client_s {
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
 * Build the EF-problem descriptor from the set of delayed assertions
 * - do nothing if efprob exists already
 * - store the internalization code in the global efcode flag
 */
extern void build_ef_problem(ef_client_t *efc, ivector_t *assertions);



/* FIXME: things Ian thinks should go here. */

//static void print_ef_analyze_code(ef_code_t code);

//yices_eval_cmd

//print_ef_status

//yices_efsolve_cmd(void)






#endif /* __EF_CLIENT_H */
