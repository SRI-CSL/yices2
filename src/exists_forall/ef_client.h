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

typedef enum frontends { YICES_MAIN, YICES_SMT2 } frontend_t;

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
  //our client frontend 
  frontend_t client;
  // the ef parameters
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


extern void init_ef_client(frontend_t client, ef_client_t *ef_client);

extern void delete_ef_client(ef_client_t *ef_client);

/*
 * Build the EF-problem descriptor from the set of delayed assertions
 * - do nothing if efprob exists already
 * - store the internalization code in the global efcode flag
 */
extern void build_ef_problem(ef_client_t *efc, ivector_t *assertions);

/*
 * Print the translation code returned by assert
 */
extern void print_internalization_code(int32_t code, uint32_t verbosity, frontend_t client);

/*
 * Print the translation code returned by ef_analyze
 */
extern void print_ef_analyze_code(ef_code_t code, frontend_t client);


/*
 * Print the efsolver status
 */
extern void print_ef_status(ef_client_t *efc, uint32_t verbosity, FILE *err);

/*
 * Exists-Forall case. Fetch model.
 */
extern model_t *ef_get_model(ef_client_t *efc);


extern void ef_solve(ef_client_t *efc, ivector_t *assertions, param_t *parameters,
		     smt_logic_t logic_code, context_arch_t arch,
		     uint32_t verbosity, tracer_t *tracer, FILE *err);

/* 
 * FIXME frontend/common.[ch] might be a good place to put things like report_bug print_ok report_success etc.
 * Once we decide what the right names are.
 * Here we should only have things directly related to exists forall.
 *
 */


/*
 * Formatted error: like printf but add the prefix and close (client arg indicates who is calling it yices_reval or yices_smt2).
 */
extern void fprint_error(FILE* fp, frontend_t client, const char *format, ...);


/*
 * bug report
 */

extern void __attribute__((noreturn)) freport_bug(FILE *fp, const char *format, ...);



#endif /* __EF_CLIENT_H */
