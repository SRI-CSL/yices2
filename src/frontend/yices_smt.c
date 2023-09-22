/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */

/*
 * Yices solver for SMT benchmarks
 */

#if defined(CYGWIN) || defined(MINGW)
#ifndef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__ __declspec(dllexport)
#endif
#endif

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <signal.h>
#include <errno.h>
#include <unistd.h>
#include <inttypes.h>
#include <gmp.h>

#include "api/smt_logic_codes.h"
#include "api/yices_globals.h"

#include "context/context.h"
#include "context/context_printer.h"

#include "frontend/smt1/smt_lexer.h"
#include "frontend/smt1/smt_parser.h"
#include "frontend/smt1/smt_term_stack.h"

#include "io/concrete_value_printer.h"
#include "io/model_printer.h"
#include "io/term_printer.h"
#include "io/type_printer.h"

#include "solvers/bv/bvsolver.h"
#include "solvers/bv/bvsolver_printer.h"
#include "solvers/cdcl/smt_core_printer.h"
#include "solvers/egraph/egraph_printer.h"
#include "solvers/floyd_warshall/idl_floyd_warshall.h"
#include "solvers/floyd_warshall/idl_fw_printer.h"
#include "solvers/floyd_warshall/rdl_floyd_warshall.h"
#include "solvers/floyd_warshall/rdl_fw_printer.h"
#include "solvers/funs/fun_solver.h"
#include "solvers/quant/quant_solver.h"
#include "solvers/simplex/simplex.h"
#include "solvers/simplex/simplex_printer.h"

#include "utils/command_line.h"
#include "utils/cputime.h"
#include "utils/memsize.h"
#include "utils/timeout.h"

#include "yices.h"
#include "yices_exit_codes.h"


/*
 * yices_rev is set up at compile time in yices_version.c
 */
extern const char * const yices_rev;


/*
 * GLOBAL OBJECTS
 */
static lexer_t lexer;
static parser_t parser;
static tstack_t stack;
static smt_benchmark_t bench;
static context_t context;
static double construction_time, start_search_time, search_time;


/*
 * Flag for the interrupt handler: true when the context
 * has been initialized
 */
static bool context_exists;


/*
 * Trace
 */
static tracer_t tracer;


/*
 * Conversion of status code in the benchmark header
 */
static const char * const status2string[] = {
  "none", "unsat", "sat", "unknown",
};


/*
 * Conversion of internalization code to an error message
 */
static const char * const code2error[NUM_INTERNALIZATION_ERRORS] = {
  "no error",
  "internal error",
  "type error",
  "formula contains free variables",
  "logic not supported",
  "context does not support UF",
  "context does not support scalar types",
  "context does not support tuples",
  "context does not support uninterpreted types",
  "context does not support arithmetic",
  "context does not support bitvectors",
  "context does not support function equalities",
  "context does not support quantifiers",
  "context does not support lambdas",
  "not an IDL formula",
  "not an RDL formula",
  "non-linear arithmetic not supported",
  "division by zero is not supported",
  "too many variables for the arithmetic solver",
  "too many atoms for the arithmetic solver",
  "arithmetic solver exception",
  "bitvector solver exception",
  "theory not supported by MCSAT",
};



/*
 * COMMAND LINE ARGUMENTS
 */

/*
 * Option flags other than the ones in params_t
 */
static bool var_elim;
static bool flatten_or;
static bool learn_eq;
static bool break_sym;
static bool arith_elim;
static bool bvarith_elim;
static bool keep_ite;
static bool dump_context;
static bool dump_internalization;
static bool show_model;

/*
 * Simplex options not in params_t
 */
static bool eager_lemmas;


/*
 * Which arithmetic solver to use
 */
typedef enum {
  ARITH_SOLVER_AUTOMATIC,
  ARITH_SOLVER_FLOYD_WARSHALL,
  ARITH_SOLVER_SIMPLEX,
} arith_solver_t;

static arith_solver_t arith_solver;


/*
 * Timeout value in seconds (0 means no timeout)
 */
static uint32_t timeout;

static timeout_t *to;

/*
 * Filename given on the command line
 */
static char *filename;

/*
 * If this flag is true, no search parameters was given on the command line,
 * so the default should be used.
 */
static bool use_default_params;

/*
 * Buffer to store the search parameters if the defaults are not used
 */
static param_t params;


/*
 * COMMAND LINE OPTIONS AND FLAGS
 */
typedef enum optid {
  show_version_opt,           // print version and exit
  print_help_opt,             // print help and exit

  // Internalization
  var_elim_opt,               // apply var elimination during internalization
  flatten_opt,                // flatten or and disequality terms
  learneq_opt,                // learn UF equalities
  breaksym_opt,               // break symmetries in UF
  arith_elim_opt,             // eliminate arithmetic variables
  bvarith_elim_opt,           // simplification of bitvector arithmetic expressions
  keep_ite_opt,               // keep term if-then-else in the egraph

  // Debug,
  dump_context_opt,           // dump the solver state (after internalization)
  dump_internalization_opt,   // dump the mapping from terms to solver objects (after internalization)

  // Model
  show_model_opt,             // print the model if SAT

  // Restarts
  fast_restart_opt,           // enable fast restart in smt_core
  c_threshold_opt,            // restart parameter
  c_factor_opt,               // restart parameter
  d_threshold_opt,            // restart parameter (only relevant if fast_restart is true)
  d_factor_opt,               // restart parameter (only relevant if fast_restart is true)

  // Clause database reduction
  r_threshold_opt,            // lower limit on conflict-reduction threshold
  r_fraction_opt,
  r_factor_opt,

  // Branching heuristics
  var_decay_opt,              // decay factor for variable activities
  randomness_opt,             // percent of random decisions
  randomseed_opt,             // prng seed
  neg_branching_opt,          // branching: set decision variable false
  pos_branching_opt,          // branching: set decision variable true
  theory_branching_opt,       // let the theory solver decide
  theory_neg_branching_opt,   // theory solver + neg for non-atom
  theory_pos_branching_opt,   // theory solver + pos for non-atom

  // Clause learning
  clause_decay_opt,           // decay factor for learned clause
  cache_tclause_opt,          // enable autolearn from theory solver
  tclause_size_opt,           // maximal size of clauses learned from the theory solver

  // Egraph parameters
  dyn_ack_opt,                // dynamic ackermann for non-boolean
  dyn_boolack_opt,            // dynamic ackermann for boolean terms
  max_ackermann_opt,          // limit for non-boolean dynamic ackermann trick
  max_boolackermann_opt,      // limit for boolean dynamic ackermann trick
  aux_eq_quota_opt,           // max number of equalities created by ackermann
  aux_eq_ratio_opt,           // increase ratio
  max_interface_eqs_opt,      // max number or interface equalities in each final_check

  // Arithmetic
  use_floyd_warshall,         // IDL or RDL solver
  use_simplex,                // Simplex solver
  simplex_eager_lemmas,       // generate simple lemmas eagerly
  simplex_prop_enabled,       // enable row-based propagation
  simplex_prop_threshold,     // max size of rows in propagation table
  simplex_adjust_model,       // enable optimized model reconciliation (egraph + simplex)
  simplex_bland_threshold,    // threshold that triggers activation of Bland's rule
  simplex_check_period,       // for integer arithmetic: period of calls to integer_check

  // Array solver
  max_update_conflicts,       // max instances of the update axiom per round
  max_extensionality,         // max instances of the extensionality axiom per round

  // Timeout
  timeout_opt,                // give a timeout
} optid_t;

#define NUM_OPTIONS (timeout_opt+1)


/*
 * Option descriptors for the command-line parser
 */
static option_desc_t options[NUM_OPTIONS] = {
  { "version", 'V', FLAG_OPTION, show_version_opt },
  { "help", 'h', FLAG_OPTION, print_help_opt },

  { "var-elim", '\0', FLAG_OPTION, var_elim_opt },
  { "flatten", '\0', FLAG_OPTION, flatten_opt },
  { "learn-eq", '\0', FLAG_OPTION, learneq_opt },
  { "break-symmetries", '\0', FLAG_OPTION, breaksym_opt },
  { "arith-elim", '\0', FLAG_OPTION, arith_elim_opt },
  { "bvarith-elim", '\0', FLAG_OPTION, bvarith_elim_opt },
  { "keep-ite", '\0', FLAG_OPTION, keep_ite_opt },

  { "dump", '\0', FLAG_OPTION, dump_context_opt },
  { "dump-internalization", '\0', FLAG_OPTION, dump_internalization_opt },

  { "show-model", '\0', FLAG_OPTION, show_model_opt },

  { "fast-restarts", '\0', FLAG_OPTION, fast_restart_opt },
  { "c-threshold", '\0', MANDATORY_INT, c_threshold_opt },
  { "c-factor", '\0', MANDATORY_FLOAT, c_factor_opt },
  { "d-threshold", '\0', MANDATORY_INT, d_threshold_opt },
  { "d-factor", '\0', MANDATORY_FLOAT, d_factor_opt },

  { "r-threshold", '\0', MANDATORY_INT, r_threshold_opt },
  { "r-fraction", '\0', MANDATORY_FLOAT, r_fraction_opt },
  { "r-factor", '\0', MANDATORY_FLOAT, r_factor_opt },

  { "var-decay", '\0', MANDATORY_FLOAT, var_decay_opt },
  { "randomness", '\0', MANDATORY_FLOAT, randomness_opt },
  { "random-seed", '\0', MANDATORY_INT, randomseed_opt },
  { "neg-branching", '\0', FLAG_OPTION, neg_branching_opt },
  { "pos-branching", '\0', FLAG_OPTION, pos_branching_opt },
  { "theory-branching", '\0', FLAG_OPTION, theory_branching_opt },
  { "th-neg-branching", '\0', FLAG_OPTION, theory_neg_branching_opt },
  { "th-pos-branching", '\0', FLAG_OPTION, theory_pos_branching_opt },

  { "clause-decay", '\0', MANDATORY_FLOAT, clause_decay_opt },
  { "cache-tclauses", '\0', FLAG_OPTION, cache_tclause_opt },
  { "tclause-size", '\0', MANDATORY_INT, tclause_size_opt },

  { "dyn-ack", '\0', FLAG_OPTION, dyn_ack_opt },
  { "dyn-bool-ack", '\0', FLAG_OPTION, dyn_boolack_opt },
  { "max-ack", '\0', MANDATORY_INT, max_ackermann_opt },
  { "max-bool-ack", '\0', MANDATORY_INT, max_boolackermann_opt },
  { "aux-eq-quota", '\0', MANDATORY_INT, aux_eq_quota_opt },
  { "aux-eq-ratio", '\0', MANDATORY_FLOAT, aux_eq_ratio_opt },
  { "max-interface-eqs", '\0', MANDATORY_INT, max_interface_eqs_opt },

  { "floyd-warshall", '\0', FLAG_OPTION, use_floyd_warshall },
  { "simplex", '\0', FLAG_OPTION, use_simplex },
  { "eager-lemmas", '\0', FLAG_OPTION, simplex_eager_lemmas },
  { "simplex-prop", '\0', FLAG_OPTION, simplex_prop_enabled },
  { "prop-threshold", '\0', MANDATORY_INT, simplex_prop_threshold },
  { "simplex-adjust-model", '\0', FLAG_OPTION, simplex_adjust_model },
  { "bland-threshold", '\0', MANDATORY_INT, simplex_bland_threshold },
  { "icheck-period", '\0', MANDATORY_INT, simplex_check_period },

  { "max-update-conflicts", '\0', MANDATORY_INT, max_update_conflicts },
  { "max-extensionality", '\0', MANDATORY_INT, max_extensionality },

  { "timeout", 't', MANDATORY_INT, timeout_opt },
};


/*
 * Option value = either an integer or a double
 */
typedef union option_val_u {
  int32_t i_value;
  double  d_value;
} option_val_t;


/*
 * Flags to indicate the options given on the command line
 * and for options with a value, what the argument was
 */
static bool opt_set[NUM_OPTIONS];
static option_val_t opt_val[NUM_OPTIONS];


/*
 * Processing of these options
 */
static void print_version(void) {
  printf("Yices %s\n"
	 "Copyright SRI International.\n"
         "Linked with GMP %s\n"
	 "Copyright Free Software Foundation, Inc.\n"
         "Build date: %s\n"
         "Platform: %s (%s)\n",
         yices_version, gmp_version, yices_build_date,
         yices_build_arch, yices_build_mode);
  fflush(stdout);
}

static void yices_help(char *progname) {
  printf("Usage: %s [options] filename\n", progname);
  printf("Option summary:\n"
         "  General:\n"
         "    --version, -V\n"
         "    --help, -h\n"
         "    --timeout, -t\n"
         "  Internalization:\n"
         "    --var-elim\n"
         "    --flatten\n"
         "    --learn-eq\n"
	 "    --break-symmetries\n"
         "    --arith-elim\n"
         "    --keep-ite\n"
         "  Model construction\n"
         "    --show-model\n"
         "  Debugging:\n"
         "    --dump\n"
         "    --dump-internalization\n"
         "  Restart:\n"
         "    --fast-restarts\n"
         "    --c-threshold=<int>\n"
         "    --c-factor=<float>\n"
         "    --d-threshold=<int>\n"
         "    --d-factor=<float>\n"
         "  Learned-clause deletion:\n"
         "    --r-threshold=<int>\n"
         "    --r-fraction=<float>\n"
         "    --r-factor=<float>\n"
         "  Branching heuristic:\n"
         "    --var-decay=<float>\n"
         "    --randomness=<float>\n"
         "    --random-seed=<int>\n"
         "    --neg-branching\n"
         "    --pos-branching\n"
         "    --theory-branching\n"
         "    --th-neg-branching\n"
         "    --th-pos-branching\n"
         "  Clause-learning heuristic\n"
         "    --clause-decay=<float>\n"
         "    --cache-tclauses\n"
         "    --tclause-size\n"
         "  Egraph options:\n"
         "    --dyn-ack\n"
         "    --dyn-bool-ack\n"
         "    --max-ack=<int>\n"
         "    --max-bool-ack=<int>\n"
         "    --aux-eq-quota=<int>\n"
         "    --aux-eq-ratio=<float>\n"
         "    --max-interface-eqs=<int>\n"
         "  Arithmetic:\n"
         "   --floyd-warshall\n"
         "   --simplex\n"
         "   --eager-lemmas\n"
         "   --simplex-prop\n"
         "   --prop-threshold\n"
         "   --simplex-adjust-model\n"
         "   --bland-threshold\n"
         "   --icheck-period\n"
         "  Array solver options:\n"
         "   --max-update-conflicts=<int>\n"
         "   --max-extensionality=<int>\n"
         "\n"
         "For bug reporting and other information, please see http://yices.csl.sri.com/\n");
  fflush(stdout);
}


/*
 * Message for unrecognized options or other errors on the command line.
 */
static void yices_usage(char *progname) {
  fprintf(stderr, "Usage: %s [options] filename\n", progname);
  fprintf(stderr, "Try '%s --help' for more information\n", progname);
}


/*
 * Name of options k in the options table
 */
static inline const char *opt_name(optid_t k) {
  return options[k].name;
}

/*
 * Name of option that select branching mode b
 */
static const char *branching_name(branch_t b) {
  const char *name;

  name = NULL;
  switch (b) {
  case BRANCHING_DEFAULT:
    break;
  case BRANCHING_NEGATIVE:
    name = opt_name(neg_branching_opt);
    break;
  case BRANCHING_POSITIVE:
    name = opt_name(pos_branching_opt);
    break;
  case BRANCHING_THEORY:
    name = opt_name(theory_branching_opt);
    break;
  case BRANCHING_TH_NEG:
    name = opt_name(theory_neg_branching_opt);
    break;
  case BRANCHING_TH_POS:
    name = opt_name(theory_pos_branching_opt);
    break;
  }
  return name;
}




/*
 * Check the search parameters and store them in params
 * - exit and print an error message if they are wrong
 */
static void check_parameters(char *progname) {
  int32_t v;
  double x;

  use_default_params = true;
  init_params_to_defaults(&params);

  // generic flags
  var_elim = opt_set[var_elim_opt];
  flatten_or = opt_set[flatten_opt];
  learn_eq = opt_set[learneq_opt];
  break_sym = opt_set[breaksym_opt];
  arith_elim = opt_set[arith_elim_opt];
  bvarith_elim = opt_set[bvarith_elim_opt];
  keep_ite = opt_set[keep_ite_opt];
  dump_context = opt_set[dump_context_opt];
  dump_internalization = opt_set[dump_internalization_opt];
  show_model = opt_set[show_model_opt];

  // timeout (must be positive)
  if (opt_set[timeout_opt]) {
    v = opt_val[timeout_opt].i_value;
    if (v <= 0) {
      fprintf(stderr, "%s: the timeout must be positive\n", progname);
      goto error;
    }
    timeout = v;
  }


  // specified arithmetic solver: use automatic by default
  arith_solver = ARITH_SOLVER_AUTOMATIC;
  if (opt_set[use_floyd_warshall] && opt_set[use_simplex]) {
    fprintf(stderr, "%s: can't use both Simplex and Floyd-Warshall solvers\n", progname);
    goto error;
  }
  if (opt_set[use_floyd_warshall]) {
    arith_solver = ARITH_SOLVER_FLOYD_WARSHALL;
  }
  if (opt_set[use_simplex]) {
    arith_solver = ARITH_SOLVER_SIMPLEX;
  }

  // simplex-specific options
  eager_lemmas = opt_set[simplex_eager_lemmas];

  // simplex-propagation
  if (opt_set[simplex_prop_enabled]) {
    if (arith_solver == ARITH_SOLVER_FLOYD_WARSHALL) {
      fprintf(stderr, "%s: Simplex option %s not usable if Floyd-Warshall solver is selected\n", progname, opt_name(simplex_prop_enabled));
      goto error;
    }
    params.use_simplex_prop = true;
    use_default_params = false;
  }

  if (opt_set[simplex_prop_threshold]) {
    if (arith_solver == ARITH_SOLVER_FLOYD_WARSHALL) {
      fprintf(stderr, "%s: Simplex option %s not usable if Floyd-Warshall solver is selected\n", progname, opt_name(simplex_prop_threshold));
      goto error;
    }
    if (! params.use_simplex_prop) {
      fprintf(stderr, "%s: %s requires %s to be set\n", progname, opt_name(simplex_prop_threshold), opt_name(simplex_prop_enabled));
      goto error;
    }
    v = opt_val[simplex_prop_threshold].i_value;
    if (v < 0) {
      fprintf(stderr, "%s: %s can't be negative\n", progname, opt_name(simplex_prop_threshold));
      goto error;
    }
    params.max_prop_row_size = v;
    use_default_params = false;
  }

  // Other simplex parameters
  if (opt_set[simplex_bland_threshold]) {
    if (arith_solver == ARITH_SOLVER_FLOYD_WARSHALL) {
      fprintf(stderr, "%s: Simplex option %s not usable if Floyd-Warshall solver is selected\n", progname, opt_name(simplex_bland_threshold));
      goto error;
    }
    v = opt_val[simplex_bland_threshold].i_value;
    if (v <= 0) {
      fprintf(stderr, "%s: %s must be positive\n", progname, opt_name(simplex_prop_threshold));
      goto error;
    }
    params.bland_threshold = v;
    use_default_params = false;
  }

  if (opt_set[simplex_check_period]) {
    if (arith_solver == ARITH_SOLVER_FLOYD_WARSHALL) {
      fprintf(stderr, "%s: Simplex option %s not usable if Floyd-Warshall solver is selected\n", progname, opt_name(simplex_check_period));
      goto error;
    }
    v = opt_val[simplex_check_period].i_value;
    if (v <= 0) {
      fprintf(stderr, "%s: %s must be positive\n", progname, opt_name(simplex_check_period));
      goto error;
    }
    params.integer_check_period = v;
    use_default_params = false;
  }

  if (opt_set[simplex_adjust_model]) {
    if (arith_solver == ARITH_SOLVER_FLOYD_WARSHALL) {
      fprintf(stderr, "%s: Simplex option %s not usable if Floyd-Warshall solver is selected\n", progname, opt_name(simplex_adjust_model));
      goto error;
    }
    params.adjust_simplex_model = true;
    use_default_params = false;
  }


  // Restart parameters
  if (opt_set[fast_restart_opt]) {
    // set fast_restart flags
    // set factors to the default
    params.fast_restart = true;
    params.c_factor = 1.1;
    params.d_factor = 1.1;
    use_default_params = false;
  }

  if (opt_set[c_threshold_opt]) {
    v = opt_val[c_threshold_opt].i_value;
    if (v <= 0) {
      fprintf(stderr, "%s: %s must be positive\n", progname, opt_name(c_threshold_opt));
      goto error;
    }
    params.c_threshold = v;
    params.d_threshold = v;
    use_default_params = false;
  }

  if (opt_set[c_factor_opt]) {
    x = opt_val[c_factor_opt].d_value;
    if (x < 1.0) {
      fprintf(stderr, "%s: %s must be at least 1\n", progname, opt_name(c_factor_opt));
      goto error;
    }
    params.c_factor = x;
    use_default_params = false;
  }

  if (opt_set[d_threshold_opt]) {
    if (params.fast_restart && opt_set[c_threshold_opt]) {
      v = opt_val[d_threshold_opt].i_value;
      if (v < params.c_threshold) {
        fprintf(stderr, "%s: %s must be at least as large as %s\n", progname,
                opt_name(d_threshold_opt), opt_name(c_threshold_opt));
        goto error;
      }
      params.d_threshold = v;
      use_default_params = false;
    } else {
      fprintf(stderr, "%s: option %s requires both %s and %s\n", progname,
              opt_name(d_threshold_opt), opt_name(fast_restart_opt),
              opt_name(c_threshold_opt));
      goto error;
    }
  }

  if (opt_set[d_factor_opt]) {
    if (params.fast_restart) {
      x = opt_val[d_factor_opt].d_value;
      if (x < 1.0) {
        fprintf(stderr, "%s: %s must be at least 1\n", progname, opt_name(d_factor_opt));
        goto error;
      }
      params.d_factor = x;
      use_default_params = false;
    }
  }

  if (opt_set[r_threshold_opt]) {
    v = opt_val[r_threshold_opt].i_value;
    if (v <= 0) {
      fprintf(stderr, "%s: %s must be positive\n", progname, opt_name(r_threshold_opt));
      goto error;
    }
    params.r_threshold = v;
    use_default_params = false;
  }

  if (opt_set[r_fraction_opt]) {
    x = opt_val[r_fraction_opt].d_value;
    if (x < 0) {
      fprintf(stderr, "%s: %s must be positive\n", progname, opt_name(r_fraction_opt));
      goto error;
    }
    params.r_fraction = x;
    use_default_params = false;
  }

  if (opt_set[r_factor_opt]) {
    x = opt_val[r_factor_opt].d_value;
    if (x < 1.0) {
      fprintf(stderr, "%s: %s must be at least 1\n", progname, opt_name(r_factor_opt));
      goto error;
    }
    params.r_factor = x;
    use_default_params = false;
  }

  // Variable activity and randomness
  if (opt_set[var_decay_opt]) {
    x = opt_val[var_decay_opt].d_value;
    if (x < 0 || x > 1.0) {
      fprintf(stderr, "%s: %s must be between 0.0 and 1.0\n", progname, opt_name(var_decay_opt));
      goto error;
    }
    params.var_decay = x;
    use_default_params = false;
  }

  if (opt_set[randomness_opt]) {
    x = opt_val[randomness_opt].d_value;
    if (x < 0 || x > 1.0) {
      fprintf(stderr, "%s: %s must be between 0.0 and 1.0\n", progname, opt_name(randomness_opt));
      goto error;
    }
    params.randomness = x;
    use_default_params = false;
  }

  if (opt_set[randomseed_opt]) {
    v = opt_val[randomseed_opt].i_value;
    params.random_seed = (uint32_t) v;
  }

  // Branching mode
  if (opt_set[theory_neg_branching_opt]) {
    if (params.branching != BRANCHING_DEFAULT) {
      fprintf(stderr, "%s: conflict between branching options %s and %s (pick one)\n", progname,
              opt_name(neg_branching_opt), branching_name(params.branching));
      goto error;
    }
    params.branching = BRANCHING_TH_NEG;
    use_default_params = false;
  }

  if (opt_set[theory_pos_branching_opt]) {
    if (params.branching != BRANCHING_DEFAULT) {
      fprintf(stderr, "%s: conflict between branching options %s and %s (pick one)\n", progname,
              opt_name(neg_branching_opt), branching_name(params.branching));
      goto error;
    }
    params.branching = BRANCHING_TH_POS;
    use_default_params = false;
  }

  if (opt_set[neg_branching_opt]) {
    if (params.branching != BRANCHING_DEFAULT) {
      fprintf(stderr, "%s: conflict between branching options %s and %s (pick one)\n", progname,
              opt_name(neg_branching_opt), branching_name(params.branching));
      goto error;
    }
    params.branching = BRANCHING_NEGATIVE;
    use_default_params = false;
  }

  if (opt_set[pos_branching_opt]) {
    if (params.branching != BRANCHING_DEFAULT) {
      fprintf(stderr, "%s: conflict between branching options %s and %s (pick one)\n", progname,
              opt_name(pos_branching_opt), branching_name(params.branching));
      goto error;
    }
    params.branching = BRANCHING_POSITIVE;
    use_default_params = false;
  }

  if (opt_set[theory_branching_opt]) {
    if (params.branching != BRANCHING_DEFAULT) {
      fprintf(stderr, "%s: conflict between branching options %s and %s (pick one)\n", progname,
              opt_name(theory_branching_opt), branching_name(params.branching));
      goto error;
    }
    params.branching = BRANCHING_THEORY;
    use_default_params = false;
  }

  if (opt_set[clause_decay_opt]) {
    x = opt_val[clause_decay_opt].d_value;
    if (x < 0 || x > 1.0) {
      fprintf(stderr, "%s: %s must be between 0.0 and 1.0\n", progname, opt_name(clause_decay_opt));
      goto error;
    }
    params.clause_decay = x;
    use_default_params = false;
  }

  if (opt_set[cache_tclause_opt]) {
    params.cache_tclauses = true;
    params.tclause_size = 8;
    use_default_params = false;
  }

  if (opt_set[tclause_size_opt]) {
    if (params.cache_tclauses) {
      v = opt_val[tclause_size_opt].i_value;
      if (v < 0) {
        fprintf(stderr, "%s: %s must be positive\n", progname, opt_name(tclause_size_opt));
        goto error;
      }
      params.tclause_size = v;
      use_default_params = false;
    }
  }

  // Egraph options
  if (opt_set[dyn_ack_opt]) {
    params.use_dyn_ack = true;
    // use default max_ackermann, aux_eq_ratio, aux_eq_quota from context_solver.c
    use_default_params = false;
  }

  if (opt_set[dyn_boolack_opt]) {
    params.use_bool_dyn_ack = true;
    use_default_params = false;
  }

  if (opt_set[max_ackermann_opt]) {
    if (params.use_dyn_ack) {
      v = opt_val[max_ackermann_opt].i_value;
      if (v < 0) {
        fprintf(stderr, "%s: %s must be positive\n", progname, opt_name(max_ackermann_opt));
        goto error;
      }
      params.max_ackermann = v;
    } else {
      fprintf(stderr, "%s: %s requires %s\n", progname, opt_name(max_ackermann_opt), opt_name(dyn_ack_opt));
      goto error;
    }
  }

  if (opt_set[max_boolackermann_opt]) {
    if (params.use_bool_dyn_ack) {
      v = opt_val[max_boolackermann_opt].i_value;
      if (v < 0) {
        fprintf(stderr, "%s: %s must be positive\n", progname, opt_name(max_boolackermann_opt));
        goto error;
      }
      params.max_boolackermann = v;
    } else {
      fprintf(stderr, "%s: %s requires %s\n", progname, opt_name(max_boolackermann_opt),
              opt_name(dyn_boolack_opt));
      goto error;
    }
  }

  if (opt_set[aux_eq_quota_opt]) {
    if (params.use_dyn_ack || params.use_bool_dyn_ack) {
      v = opt_val[aux_eq_quota_opt].i_value;
      if (v < 0) {
        fprintf(stderr, "%s: %s must be positive\n", progname, opt_name(aux_eq_quota_opt));
        goto error;
      }
      params.aux_eq_quota = v;
    } else {
      fprintf(stderr, "%s: %s requires %s or %s\n", progname, opt_name(aux_eq_quota_opt),
              opt_name(dyn_ack_opt), opt_name(dyn_boolack_opt));
      goto error;
    }
  }

  if (opt_set[aux_eq_ratio_opt]) {
    if (params.use_dyn_ack || params.use_bool_dyn_ack) {
      x = opt_val[aux_eq_ratio_opt].d_value;
      if (x <= 0.0) {
        fprintf(stderr, "%s: %s must be positive\n", progname, opt_name(aux_eq_ratio_opt));
        goto error;
      }
      params.aux_eq_ratio = x;
    } else {
      fprintf(stderr, "%s: %s requires %s or %s\n", progname, opt_name(aux_eq_ratio_opt),
              opt_name(dyn_ack_opt), opt_name(dyn_boolack_opt));
      goto error;
    }
  }

  if (opt_set[max_interface_eqs_opt]) {
    v = opt_val[max_interface_eqs_opt].i_value;
    if (v < 1) {
      fprintf(stderr, "%s: %s must be at least one\n", progname, opt_name(max_interface_eqs_opt));
      goto error;
    }
    params.max_interface_eqs = v;
    use_default_params = false;
  }


  // Array solver options
  if (opt_set[max_update_conflicts]) {
    v = opt_val[max_update_conflicts].i_value;
    if (v < 1) {
      fprintf(stderr, "%s: %s must be at least one\n", progname, opt_name(max_update_conflicts));
      goto error;
    }
    params.max_update_conflicts = v;
    use_default_params = false;
  }

  if (opt_set[max_extensionality]) {
    v = opt_val[max_extensionality].i_value;
    if (v < 1) {
      fprintf(stderr, "%s: %s must be at least one\n", progname, opt_name(max_update_conflicts));
      goto error;
    }
    params.max_extensionality = v;
    use_default_params = false;
  }

  return;

 error:
  exit(YICES_EXIT_USAGE);
}


/*
 * Parse the command line and fill-in the parameters
 */
static void parse_command_line(int argc, char *argv[]) {
  cmdline_parser_t parser;
  cmdline_elem_t elem;
  uint32_t i;
  optid_t k;

  filename = NULL;
  var_elim = false;
  dump_context = false;
  dump_internalization = false;
  timeout = 0;

  for(i=0; i<NUM_OPTIONS; i++) {
    opt_set[i] = false;
  }

  init_cmdline_parser(&parser, options, NUM_OPTIONS, argv, argc);

  for (;;) {
    cmdline_parse_element(&parser, &elem);
    switch (elem.status) {
    case cmdline_done:
      goto done;

    case cmdline_argument:
      if (filename == NULL) {
        filename = elem.arg;
      } else {
        fprintf(stderr, "%s: too many arguments\n", parser.command_name);
        yices_usage(parser.command_name);
        exit(YICES_EXIT_USAGE);
      }
      break;

    case cmdline_option:
      k = elem.key;
      opt_set[k] = true;
      switch (k) {
      case show_version_opt:
        print_version();
        exit(YICES_EXIT_SUCCESS);

      case print_help_opt:
        yices_help(parser.command_name);
        exit(YICES_EXIT_SUCCESS);

        // boolean options
      case var_elim_opt:
      case flatten_opt:
      case learneq_opt:
      case breaksym_opt:
      case arith_elim_opt:
      case bvarith_elim_opt:
      case keep_ite_opt:
      case dump_context_opt:
      case dump_internalization_opt:
      case show_model_opt:
      case fast_restart_opt:
      case neg_branching_opt:
      case pos_branching_opt:
      case theory_branching_opt:
      case theory_neg_branching_opt:
      case theory_pos_branching_opt:
      case cache_tclause_opt:
      case dyn_ack_opt:
      case dyn_boolack_opt:
      case use_floyd_warshall:
      case use_simplex:
      case simplex_eager_lemmas:
      case simplex_prop_enabled:
      case simplex_adjust_model:
        break;

        // integer parameters
      case c_threshold_opt:
      case d_threshold_opt:
      case r_threshold_opt:
      case randomseed_opt:
      case tclause_size_opt:
      case max_ackermann_opt:
      case max_boolackermann_opt:
      case aux_eq_quota_opt:
      case max_interface_eqs_opt:
      case simplex_prop_threshold:
      case simplex_bland_threshold:
      case simplex_check_period:
      case max_update_conflicts:
      case max_extensionality:
      case timeout_opt:
        opt_val[k].i_value = elem.i_value;
        break;

        // real-valued parameters
      case c_factor_opt:
      case d_factor_opt:
      case r_fraction_opt:
      case r_factor_opt:
      case var_decay_opt:
      case randomness_opt:
      case clause_decay_opt:
      case aux_eq_ratio_opt:
        opt_val[k].d_value = elem.d_value;
        break;
      }
      break;

    case cmdline_error:
      cmdline_print_error(&parser, &elem);
      exit(YICES_EXIT_USAGE);
    }
  }

 done:
  check_parameters(parser.command_name);
}



/**********************************
 *  PRINT STATISTICS AND RESULTS  *
 *********************************/

/*
 * Version header
 */
static void print_yices_header(FILE *f) {
  fprintf(f, "Yices %s, Copyright SRI International.\n", yices_version);
  fprintf(f, "GMP %s, Copyright Free Software Foundation, Inc\n", gmp_version);
  fprintf(f, "Build date: %s\n", yices_build_date);
  fprintf(f, "Platform: %s (%s)\n", yices_build_arch, yices_build_mode);
  fprintf(f, "Revision: %s\n", yices_rev);
  fprintf(f, "----\n");
}


/*
 * Benchmark header
 */
static void print_benchmark(FILE *f, smt_benchmark_t *bench) {
  fprintf(f, "Benchmark: %s\n", bench->name);
  fprintf(f, "Logic: %s\n", bench->logic_name);
  fprintf(f, "Status: %s\n", status2string[bench->status]);
}


/*
 * Statistics in the smt_core
 */
static void show_stats(dpll_stats_t *stat) {
  printf("Core\n");
  printf(" restarts                : %"PRIu32"\n", stat->restarts);
  printf(" simplify db             : %"PRIu32"\n", stat->simplify_calls);
  printf(" reduce db               : %"PRIu32"\n", stat->reduce_calls);
  printf(" remove irrelevant       : %"PRIu32"\n", stat->remove_calls);
  printf(" decisions               : %"PRIu64"\n", stat->decisions);
  printf(" random decisions        : %"PRIu64"\n", stat->random_decisions);
  printf(" propagations            : %"PRIu64"\n", stat->propagations);
  printf(" conflicts               : %"PRIu64"\n", stat->conflicts);
  printf(" theory propagations     : %"PRIu32"\n", stat->th_props);
  printf(" propagation-lemmas      : %"PRIu32"\n", stat->th_prop_lemmas);
  printf(" theory conflicts        : %"PRIu32"\n", stat->th_conflicts);
  printf(" conflict-lemmas         : %"PRIu32"\n", stat->th_conflict_lemmas);

  printf(" lits in pb. clauses     : %"PRIu64"\n", stat->prob_literals);
  printf(" lits in learned clauses : %"PRIu64"\n", stat->learned_literals);
  printf(" total lits. in learned  : %"PRIu64"\n", stat->literals_before_simpl);
  printf(" subsumed lits.          : %"PRIu64"\n", stat->subsumed_literals);
  printf(" deleted pb. clauses     : %"PRIu64"\n", stat->prob_clauses_deleted);
  printf(" deleted learned clauses : %"PRIu64"\n", stat->learned_clauses_deleted);
  printf(" deleted binary clauses  : %"PRIu64"\n", stat->bin_clauses_deleted);
}

/*
 * Egraph statistics
 */
static void show_egraph_stats(egraph_stats_t *stat) {
  printf("Egraph\n");
  printf(" eq from simplex         : %"PRIu32"\n", stat->eq_props);
  printf(" app/update reductions   : %"PRIu32"\n", stat->app_reductions);
  printf(" prop. to core           : %"PRIu32"\n", stat->th_props);
  printf(" conflicts               : %"PRIu32"\n", stat->th_conflicts);
  printf(" non-distinct lemmas     : %"PRIu32"\n", stat->nd_lemmas);
  printf(" auxiliary eqs. created  : %"PRIu32"\n", stat->aux_eqs);
  printf(" dyn boolack. lemmas     : %"PRIu32"\n", stat->boolack_lemmas);
  printf(" other dyn ack.lemmas    : %"PRIu32"\n", stat->ack_lemmas);
  printf(" final checks            : %"PRIu32"\n", stat->final_checks);
  printf(" interface equalities    : %"PRIu32"\n", stat->interface_eqs);
}

/*
 * Array/function solver statistics
 */
static void show_funsolver_stats(fun_solver_stats_t *stat) {
  printf("Arrays\n");
  printf(" init. variables         : %"PRIu32"\n", stat->num_init_vars);
  printf(" init. edges             : %"PRIu32"\n", stat->num_init_edges);
  printf(" update axiom1           : %"PRIu32"\n", stat->num_update_axiom1);
  printf(" update axiom2           : %"PRIu32"\n", stat->num_update_axiom2);
  printf(" extensionality axioms   : %"PRIu32"\n", stat->num_extensionality_axiom);
}

/*
 * Quantifier solver statistics
 */
static void show_quantsolver_stats(quant_solver_stats_t *stat) {
  printf("Quantifiers\n");
  printf(" quantifiers             : %"PRIu32"\n", stat->num_quantifiers);
  printf(" patterns                : %"PRIu32"\n", stat->num_patterns);
  printf(" instances               : %"PRIu32"\n", stat->num_instances);
}

/*
 * Simplex statistics
 */
static void show_simplex_stats(simplex_stats_t *stat) {
  printf("Simplex\n");
  printf(" init. variables         : %"PRIu32"\n", stat->num_init_vars);
  printf(" init. rows              : %"PRIu32"\n", stat->num_init_rows);
  printf(" init. atoms             : %"PRIu32"\n", stat->num_atoms);
  printf(" end atoms               : %"PRIu32"\n", stat->num_end_atoms);
  printf(" elim. candidates        : %"PRIu32"\n", stat->num_elim_candidates);
  printf(" elim. rows              : %"PRIu32"\n", stat->num_elim_rows);
  printf(" fixed vars after simpl. : %"PRIu32"\n", stat->num_simpl_fvars);
  printf(" rows after simpl.       : %"PRIu32"\n", stat->num_simpl_rows);
  printf(" fixed vars              : %"PRIu32"\n", stat->num_fixed_vars);
  printf(" rows in init. tableau   : %"PRIu32"\n", stat->num_rows);
  printf(" rows in final tableau   : %"PRIu32"\n", stat->num_end_rows);
  printf(" calls to make_feasible  : %"PRIu32"\n", stat->num_make_feasible);
  printf(" pivots                  : %"PRIu32"\n", stat->num_pivots);
  printf(" bland-rule activations  : %"PRIu32"\n", stat->num_blands);
  printf(" simple lemmas           : %"PRIu32"\n", stat->num_binary_lemmas);
  //  printf(" propagation lemmas      : %"PRIu32"\n", stat->num_prop_lemmas);  (it's always zero)
  printf(" prop. to core           : %"PRIu32"\n", stat->num_props);
  printf(" derived bounds          : %"PRIu32"\n", stat->num_bound_props);
  printf(" productive propagations : %"PRIu32"\n", stat->num_prop_expl);
  printf(" conflicts               : %"PRIu32"\n", stat->num_conflicts);
  printf(" interface lemmas        : %"PRIu32"\n", stat->num_interface_lemmas);
  printf(" reduced inter. lemmas   : %"PRIu32"\n", stat->num_reduced_inter_lemmas);
  printf(" trichotomy lemmas       : %"PRIu32"\n", stat->num_tricho_lemmas);
  printf(" reduced tricho. lemmas  : %"PRIu32"\n", stat->num_reduced_tricho);
  if (stat->num_make_intfeasible > 0 || stat->num_dioph_checks > 0) {
    printf("Integer arithmetic\n");
    printf(" make integer feasible   : %"PRIu32"\n", stat->num_make_intfeasible);
    printf(" branch atoms            : %"PRIu32"\n", stat->num_branch_atoms);
    printf(" Gomory cuts             : %"PRIu32"\n", stat->num_gomory_cuts);
    printf("bound strengthening\n");
    printf(" conflicts               : %"PRIu32"\n", stat->num_bound_conflicts);
    printf(" recheck conflicts       : %"PRIu32"\n", stat->num_bound_recheck_conflicts);
    printf("integrality tests\n");
    printf(" conflicts               : %"PRIu32"\n", stat->num_itest_conflicts);
    printf(" bound conflicts         : %"PRIu32"\n", stat->num_itest_bound_conflicts);
    printf(" recheck conflicts       : %"PRIu32"\n", stat->num_itest_recheck_conflicts);
    printf("diohpantine solver\n");
    printf(" gcd conflicts           : %"PRIu32"\n", stat->num_dioph_gcd_conflicts);
    printf(" dioph checks            : %"PRIu32"\n", stat->num_dioph_checks);
    printf(" dioph conflicts         : %"PRIu32"\n", stat->num_dioph_conflicts);
    printf(" bound conflicts         : %"PRIu32"\n", stat->num_dioph_bound_conflicts);
    printf(" recheck conflicts       : %"PRIu32"\n", stat->num_dioph_recheck_conflicts);
  }
}


/*
 * Bitvector solver statistics
 */
static void show_bvsolver_stats(bv_solver_t *solver) {
  printf("Bit-vectors\n");
  printf(" variables               : %"PRIu32"\n", bv_solver_num_vars(solver));
  printf(" atoms                   : %"PRIu32"\n", bv_solver_num_atoms(solver));
  printf(" eq. atoms               : %"PRIu32"\n", bv_solver_num_eq_atoms(solver));
  printf(" dyn eq. atoms           : %"PRIu32"\n", solver->stats.on_the_fly_atoms);
  printf(" ge atoms                : %"PRIu32"\n", bv_solver_num_ge_atoms(solver));
  printf(" sge atoms               : %"PRIu32"\n", bv_solver_num_sge_atoms(solver));
  printf(" equiv lemmas            : %"PRIu32"\n", solver->stats.equiv_lemmas);
  printf(" equiv conflicts         : %"PRIu32"\n", solver->stats.equiv_conflicts);
  printf(" semi-equiv lemmas       : %"PRIu32"\n", solver->stats.half_equiv_lemmas);
  printf(" interface lemmas        : %"PRIu32"\n", solver->stats.interface_lemmas);
}



/*
 * Get the arithmetic solver
 */
static inline simplex_solver_t *context_get_simplex_solver(context_t *ctx) {
  assert(context_has_simplex_solver(ctx));
  return (simplex_solver_t *) ctx->arith_solver;
}


/*
 * Statistics + result, after the search
 */
static void print_results(void) {
  smt_core_t *core;
  egraph_t *egraph;
  simplex_solver_t *simplex;
  fun_solver_t *fsolver;
  quant_solver_t *qsolver;
  uint32_t resu;
  double mem_used;

  search_time = get_cpu_time() - start_search_time;
  if (search_time < 0.0) {
    search_time = 0.0;
  }

  core = context.core;
  resu = context.core->status;

  show_stats(&core->stats);
  printf(" boolean variables       : %"PRIu32"\n", core->nvars);
  printf(" atoms                   : %"PRIu32"\n", core->atoms.natoms);

  egraph = context.egraph;
  if (egraph != NULL) {
    show_egraph_stats(&egraph->stats);
    printf(" egraph terms            : %"PRIu32"\n", egraph->terms.nterms);
    if (context_has_fun_solver(&context)) {
      fsolver = context.fun_solver;
      show_funsolver_stats(&fsolver->stats);
    }
    if (context_has_quant_solver(&context)) {
      qsolver = context.quant_solver;
      show_quantsolver_stats(&qsolver->stats);
    }
  }

  if (context_has_simplex_solver(&context)) {
    simplex = context_get_simplex_solver(&context);
    if (simplex != NULL) {
      simplex_collect_statistics(simplex);
      show_simplex_stats(&simplex->stats);
    }
  }

  if (context_has_bv_solver(&context)) {
    show_bvsolver_stats(context.bv_solver);
  }

  printf("\nSearch time             : %.4f s\n", search_time);
  mem_used = mem_size() / (1024 * 1024);
  if (mem_used > 0) {
    printf("Memory used             : %.2f MB\n", mem_used);
  }
  printf("\n\n");

  if (resu == STATUS_SAT) {
    printf("sat\n");
  } else if (resu == STATUS_UNSAT) {
    printf("unsat\n");
  } else {
    printf("unknown\n");
  }

  fflush(stdout);
}


/*
 * Statistics on problem size, before the search
 */
static void print_presearch_stats(void) {
  smt_core_t *core;
  egraph_t *egraph;

  core = context.core;
  egraph = context.egraph;


  printf("boolean variables       : %"PRIu32"\n", core->nvars);
  printf("atoms                   : %"PRIu32"\n", core->atoms.natoms);
  if (egraph != NULL) {
    printf("egraph terms            : %"PRIu32"\n", egraph->terms.nterms);
    printf("app/update reductions   : %"PRIu32"\n", egraph->stats.app_reductions);
  }

  if (context_has_simplex_solver(&context)) {
    printf("arithmetic solver       : Simplex\n");
  } else if (context_has_idl_solver(&context)) {
    printf("arithmetic solver       : IDL Floyd-Warshall\n");
  } else if (context_has_rdl_solver(&context)) {
    printf("arithmetic solver       : RDL Floyd-Warshall\n");
  }

  printf("\n");
  fflush(stdout);
}


/*
 * Print parameters and settings
 */
static void print_options(FILE *f, context_t *ctx) {
  simplex_solver_t *simplex;

  if (context_has_preprocess_options(ctx)) {
    fprintf(f, "Preprocessing:");
    if (context_var_elim_enabled(ctx)) {
      fprintf(f, " --var-elim");
    }
    if (context_flatten_or_enabled(ctx)) {
      fprintf(f, " --flatten-or");
    }
    if (context_flatten_diseq_enabled(ctx)) {
      fprintf(f, " --flatten-diseq");
    }
    if (context_eq_abstraction_enabled(ctx)) {
      fprintf(f, " --learn-eq");
    }
    if (context_breaksym_enabled(ctx)) {
      fprintf(f, " --learn-eq");
    }
    if (context_arith_elim_enabled(ctx)) {
      fprintf(f, " --arith-elim");
    }
    if (context_bvarith_elim_enabled(ctx)) {
      fprintf(f, " --bvarith-elim");
    }
    if (context_keep_ite_enabled(ctx)) {
      fprintf(f, " --keep-ite");
    }
    fprintf(f, "\n");
  }

  if (context_has_arith_solver(ctx)) {
    fprintf(f, "Arithmetic: ");
    if (context_has_simplex_solver(ctx)) {
      fprintf(f, " --simplex");
      simplex = context_get_simplex_solver(ctx);
      if (simplex_option_enabled(simplex, SIMPLEX_EAGER_LEMMAS)) {
        fprintf(f, " --eager-lemmas");
      }
      if (simplex_option_enabled(simplex, SIMPLEX_PROPAGATION) ||
          params.use_simplex_prop) {
        fprintf(f, " --simplex-prop --prop-threshold=%"PRIu32, params.max_prop_row_size);
      }
      if (simplex_option_enabled(simplex, SIMPLEX_ADJUST_MODEL) ||
          params.adjust_simplex_model) {
        fprintf(f, " --simplex-adjust-model");
      }
      fprintf(f, " --bland-threshold=%"PRIu32, params.bland_threshold);
      fprintf(f, " --icheck-period=%"PRId32, params.integer_check_period);
    } else if (context_has_rdl_solver(ctx) || context_has_idl_solver(ctx)) {
      fprintf(f, " --floyd-warshall");
    }
    fprintf(f, "\n");
  }

  if (context_has_egraph(ctx)) {
    fprintf(f, "Egraph: ");
    if (params.use_dyn_ack || params.use_bool_dyn_ack) {
      if (params.use_dyn_ack) {
        fprintf(f, " --dyn-ack --max-ack=%"PRIu32, params.max_ackermann);
      }
      if (params.use_bool_dyn_ack) {
        fprintf(f, " --dyn-bool-ack --max-bool-ack=%"PRIu32, params.max_boolackermann);
      }
      fprintf(f, " --aux-eq-quota=%"PRIu32" --aux-eq-ratio=%.3f", params.aux_eq_quota, params.aux_eq_ratio);
    }
    fprintf(f, " --max-interface-eqs=%"PRIu32"\n", params.max_interface_eqs);
  }

  if (context_has_fun_solver(ctx)) {
    fprintf(f, "Array solver: --max-update-conflicts=%"PRIu32" --max-extensionality=%"PRIu32"\n",
            params.max_update_conflicts, params.max_extensionality);
  }

  if (params.fast_restart || params.cache_tclauses || params.branching != BRANCHING_DEFAULT) {
    fprintf(f, "Core: ");
    if (params.fast_restart) {
      fprintf(f, " --fast-restarts");
    }
    if (params.cache_tclauses) {
      fprintf(f, " --cache-tclauses --tclause-size=%"PRIu32, params.tclause_size);
    }
    switch (params.branching) {
    case BRANCHING_DEFAULT:
      break;
    case BRANCHING_NEGATIVE:
      fprintf(f, " --neg-branching");
      break;
    case BRANCHING_POSITIVE:
      fprintf(f, " --pos-branching");
      break;
    case BRANCHING_THEORY:
      fprintf(f, " --theory-branching");
      break;
    case BRANCHING_TH_NEG:
      fprintf(f, " --th-neg-branching");
      break;
    case BRANCHING_TH_POS:
      fprintf(f, " --th-pos-branching");
      break;
    }
    fprintf(f, "\n");
  }
  fprintf(f, "\n");
}




/*
 * Print the translation code returned by assert
 */
static void print_internalization_code(int32_t code) {
  assert(-NUM_INTERNALIZATION_ERRORS < code && code <= TRIVIALLY_UNSAT);
  if (code == TRIVIALLY_UNSAT) {
    printf("Assertions simplify to false\n\n");
    printf("unsat\n");
    fflush(stdout);
  } else if (code < 0) {
    code = - code;
    printf("unknown\n");
    fprintf(stderr, "Internalization error: %s\n\n", code2error[code]);
  }
}


/*
 * Allocate and initialize a model
 * - set has_alias true
 */
static model_t *new_model(void) {
  model_t *tmp;

  tmp = (model_t *) safe_malloc(sizeof(model_t));
  init_model(tmp, __yices_globals.terms, true);
  return tmp;
}


/*
 * Free model
 */
static void free_model(model_t *model) {
  delete_model(model);
  safe_free(model);
}


/*
 * TEMPORARY FOR TESTING THE EVALUATOR CODE
 */
#include "model/model_eval.h"

#if TEST_EVALUATOR

static void test_evaluator(FILE *f, model_t *model) {
  evaluator_t eval;
  term_table_t *terms;
  uint32_t i, n;
  value_t v;

  init_evaluator(&eval, model);
  terms = __yices_globals.terms;

  n = terms->nelems;
  for (i=0; i<n; i++) {
    if (good_term(terms, i)) {
      fprintf(f, "test eval: term ");
      print_term_id(f, i);
      fprintf(f, " = ");
      print_term_shallow(f, i);
      fflush(f);
      v = eval_in_model(&eval, i);
      fprintf(f, "evaluates to: ");
      if (v >= 0) {
        vtbl_print_object(f, model_get_vtbl(model), v);
        if (object_is_function(model_get_vtbl(model), v)) {
          fprintf(f, "\n");
          vtbl_print_function(f, model_get_vtbl(model), v, true);
        }
        fprintf(f, "\n\n");
      } else {
        fprintf(f, "unknown (code = %"PRId32")\n\n", v);
      }
      fflush(f);
      reset_evaluator(&eval);
    }
  }

  delete_evaluator(&eval);
}
#endif

static void check_model(FILE *f, smt_benchmark_t *bench, model_t *model) {
  evaluator_t eval;
  term_table_t *terms;
  uint32_t i, n;
  term_t t;
  value_t v;

  init_evaluator(&eval, model);
  terms = __yices_globals.terms;

  n = bench->nformulas;
  for (i=0; i<n; i++) {
    t = bench->formulas[i];
    assert(good_term(terms, t));
    v = eval_in_model(&eval, t);
    if (v < 0 || is_false(model_get_vtbl(model), v)) {
      fprintf(f, "\n==== Assertion[%"PRIu32"] ====\n", i);
      print_term_id(f, t);
      fprintf(f, " = ");
      print_term(f, terms, t);
      fprintf(f, "\n");
      fflush(f);
      fprintf(f, "evaluates to: ");
      if (v >= 0) {
        vtbl_print_object(f, model_get_vtbl(model), v);
        fprintf(f, "\n\n");
      } else {
        fprintf(f, "unknown (code = %"PRId32")\n\n", v);
      }
      fflush(f);
    }
    reset_evaluator(&eval);
  }

  delete_evaluator(&eval);
}


/*
 * DUMP SOLVER STATE AFTER INTERNALIZATION
 */

/*
 * Dump the internalization table into file f
 */
static void dump_internalization_table(FILE *f, context_t *ctx) {
  fprintf(f, "--- Substitutions ---\n");
  print_context_intern_subst(f, ctx);
  fprintf(f, "\n--- Internalization ---\n");
  print_context_intern_mapping(f, ctx);
}


/*
 * Dump the initial context + the internalization table (optional)
 */
static void dump_the_context(context_t *context, smt_benchmark_t *bench, char *filename) {
  FILE *dump;
  bv_solver_t *bv;

  dump = fopen(filename, "w");
  if (dump == NULL) return;

  print_benchmark(dump, bench);
  if (dump_internalization) {
    dump_internalization_table(dump, context);
  }

  if (context_has_egraph(context)) {
    fprintf(dump, "\n==== TYPE TABLE ====\n");
    print_type_table(dump, __yices_globals.types);
    fprintf(dump, "\n==== EGRAPH TERMS ====\n");
    print_egraph_terms(dump, context->egraph);
    //    fprintf(dump, "\n==== EGRAPH CLASSES ====\n");
    //    print_egraph_root_classes_details(dump, context->egraph);
    fprintf(dump, "\n==== EGRAPH ATOMS ====\n");
    print_egraph_atoms(dump, context->egraph);

  }

  if (context_has_idl_solver(context)) {
    fprintf(dump, "\n==== IDL ATOMS ====\n");
    print_idl_atoms(dump, context->arith_solver);
  } else if (context_has_rdl_solver(context)) {
    fprintf(dump, "\n==== RDL ATOMS ====\n");
  } else if (context_has_simplex_solver(context)) {
    fprintf(dump, "\n==== SIMPLEX VARIABLES ====\n");
    print_simplex_vars(dump, context->arith_solver);
    fprintf(dump, "\n==== SIMPLEX ATOMS ====\n");
    print_simplex_atoms(dump, context->arith_solver);
    fprintf(dump, "\n==== MATRIX ====\n");
    print_simplex_matrix(dump, context->arith_solver);
    fprintf(dump, "\n==== BOUNDS ====\n");
    print_simplex_bounds(dump, context->arith_solver);
    fprintf(dump, "\n==== ASSIGNMENT ====\n");
    print_simplex_assignment(dump, context->arith_solver);
  }

  if (context_has_bv_solver(context)) {
    bv = context->bv_solver;
    fprintf(dump, "\n==== BVSOLVER PARTITION ====\n");
    print_bv_solver_partition(dump, bv);
    fprintf(dump, "\n==== BVSOLVER TERMS ====\n");
    print_bv_solver_vars(dump, bv);
    fprintf(dump, "\n==== BVSOLVER ATOMS ====\n");
    print_bv_solver_atoms(dump, bv);
  }

  fprintf(dump, "\n==== CLAUSES ====\n");
  print_clauses(dump, context->core);
  fprintf(dump, "\n==== BOOLEAN ASSIGNMENT ====\n");
  print_boolean_assignment(dump, context->core);
  fprintf(dump, "\n");

  fclose(dump);
}



/*
 * TIMEOUT/INTERRUPTS
 */

static const char signum_msg[24] = "\nInterrupted by signal ";
static char signum_buffer[100];

/*
 * Write signal number to file 2 (assumed to be stderr): we can't use
 * fprintf because it's not safe in a signal handler.
 */
static void write_signum(int signum) {
  ssize_t w;
  uint32_t i, n;

  memcpy(signum_buffer, signum_msg, sizeof(signum_msg));

  // force signum to be at most two digits
  signum = signum % 100;
  n = sizeof(signum_msg);
  if (signum > 10) {
    signum_buffer[n] = (char)('0' + signum/10);
    signum_buffer[n + 1] = (char)('0' + signum % 10);
    signum_buffer[n + 2] = '\n';
    n += 3;
  } else {
    signum_buffer[n] = (char)('0' + signum);
    signum_buffer[n + 1] = '\n';
    n += 2;
  }

  // write to file 2
  i = 0;
  do {
    do {
      w = write(2, signum_buffer + i, n);
    } while (w < 0 && errno == EAGAIN);
    if (w < 0) break; // write error, we can't do much about it.
    i += (uint32_t) w;
    n -= (uint32_t) w;
  } while (n > 0);
}

/*
 * Signal handler: call print_results then exit
 */
static void handler(int signum) {
  write_signum(signum);
  if (context_exists) {
    // TODO: Fix this.
    // dump_the_context and print_result can deadlock
    if (dump_context || dump_internalization) {
      dump_the_context(&context, &bench, "yices_exit.dmp");
    }
    print_results();
  }
  _exit(YICES_EXIT_INTERRUPTED);
}


/*
 * Set the signal handler: to print statistics on
 * SIGINT, SIGABRT, SIGXCPU
 */
static void init_handler(void) {
  signal(SIGINT, handler);
  signal(SIGABRT, handler);
#ifndef MINGW
  signal(SIGXCPU, handler);
#endif
}


/*
 * Mask the signals
 */
static void clear_handler(void) {
  signal(SIGINT, SIG_IGN);
  signal(SIGABRT, SIG_IGN);
#ifndef MINGW
  signal(SIGXCPU, SIG_IGN);
#endif
}


/*
 * Timeout handler: p = pointer to the context
 */
static void timeout_handler(void *p) {
  context_t *ctx;

  ctx = p;
  stop_search(ctx->core);
}



/*
 * Temporary test. Check whether one of the input assertion is reduced
 * to false by simplification. This is checked independent of the
 * logic label.
 */
static bool benchmark_reduced_to_false(smt_benchmark_t *bench) {
  uint32_t i, n;
  term_t f;

  n = bench->nformulas;
  for (i=0; i<n; i++) {
    f = bench->formulas[i];
    assert(is_boolean_term(__yices_globals.terms, f));
    if (f == false_term) {
      return true;
    }
  }

  return false;
}


/*
 * MAIN SOLVER FUNCTION
 * - parse input file (assumed to be in SMT-LIB format)
 * - solve benchmark
 * - return an exit code (defined in yices_exit_codes.h)
 */
static int process_benchmark(char *filename) {
  param_t *search_options;
  model_t *model;
  int32_t code;
  double mem_used;
  smt_logic_t logic;
  context_arch_t arch;
  bool need_icheck;   // true if simplex needs integer check

  print_yices_header(stdout);

  if (filename != NULL) {
    // Read from the given file
    if (init_smt_file_lexer(&lexer, filename) < 0) {
      perror(filename);
      return YICES_EXIT_FILE_NOT_FOUND;
    }
  } else {
    // read from stdin
    init_smt_stdin_lexer(&lexer);
  }

  context_exists = false;
  init_handler();

  /*
   * Parse and build the formula
   */
  yices_init();
  init_smt_tstack(&stack);
  init_parser(&parser, &lexer, &stack);
  init_benchmark(&bench);
  code = parse_smt_benchmark(&parser, &bench);
  if (code == 0) {
    construction_time = get_cpu_time();
    mem_used = mem_size() / (1024 * 1024);
    print_benchmark(stdout, &bench);
    printf("Construction time: %.4f s\n", construction_time);
    printf("Memory used: %.2f MB\n", mem_used);
    fflush(stdout);
  }

  delete_parser(&parser);
  close_lexer(&lexer);
  delete_tstack(&stack);

  if (code < 0) {
    code = YICES_EXIT_SYNTAX_ERROR;
    goto cleanup_benchmark;
  }


  /*
   * Check whether the simplifier solved it
   */
  if (benchmark_reduced_to_false(&bench)) {
    printf("\nReduced to false\n\nunsat\n");
    fflush(stdout);
    code = YICES_EXIT_SUCCESS;
    goto cleanup_benchmark;
  }

  /*
   * Select architecture based on the benchmark logic and
   * command-line options
   */
  need_icheck = false;
  arch = CTX_ARCH_NOSOLVERS; // otherwise GCC gives a warning

  if (bench.logic_name != NULL) {
    logic = smt_logic_code(bench.logic_name);
    switch (logic) {
    case QF_ALIA:
    case QF_AUFLIA:
      /*
       * Arrays + uf + simplex
       */
      arch = CTX_ARCH_EGFUNSPLX;
      break;

    case QF_AX:
      /*
       * Egraph + array solver
       */
      arch = CTX_ARCH_EGFUN;
      break;

    case QF_IDL:
      /*
       * Default for QF_IDL: automatic
       * unless --simplex or --floyd-warshall was given on the command line
       */
      switch (arith_solver) {
      case ARITH_SOLVER_AUTOMATIC:
        arch = CTX_ARCH_AUTO_IDL;
        break;
      case ARITH_SOLVER_SIMPLEX:
        arch = CTX_ARCH_SPLX;
        break;
      case ARITH_SOLVER_FLOYD_WARSHALL:
        arch = CTX_ARCH_IFW;
        break;
      }
      break;

    case QF_RDL:
      /*
       * Default for QF_RDL: automatic
       * unless --simplex or --floyd-warshall was given on the command line
       */
      switch (arith_solver) {
      case ARITH_SOLVER_AUTOMATIC:
        arch = CTX_ARCH_AUTO_RDL;
        break;
      case ARITH_SOLVER_SIMPLEX:
        arch = CTX_ARCH_SPLX;
        break;
      case ARITH_SOLVER_FLOYD_WARSHALL:
        arch = CTX_ARCH_RFW;
        break;
      }
      break;

    case QF_UF:
      /*
       * Egraph only
       */
      arch = CTX_ARCH_EG;
      break;


    case QF_LRA:
      /*
       * SIMPLEX only
       */
      arch = CTX_ARCH_SPLX;
      break;

    case QF_LIA:
      /*
       * SIMPLEX only, activate periodic integer checks
       */
      need_icheck = true;
      arch = CTX_ARCH_SPLX;
      break;

    case QF_UFIDL:
      /*
       * Some SMT-LIB benchmarks labeled as QF_UFIDL are actually
       * pure IDL so we allow IDL floyd-warshall here.
       * The default is EGRAPH + SIMPLEX.
       */
      switch (arith_solver) {
      case ARITH_SOLVER_AUTOMATIC:
      case ARITH_SOLVER_SIMPLEX:
        arch = CTX_ARCH_EGSPLX;
        break;
      case ARITH_SOLVER_FLOYD_WARSHALL:
        arch = CTX_ARCH_IFW;
        break;
      }
      break;

    case QF_UFLRA:
      /*
       * EGRAPH + SIMPLEX
       */
      arch = CTX_ARCH_EGSPLX;
      break;

    case QF_UFLIA:
    case QF_UFLIRA:
      /*
       * EGRAPH + SIMPLEX, activate periodic integer checks
       */
      need_icheck = true;
      arch = CTX_ARCH_EGSPLX;
      break;

    case QF_ABV:
    case QF_AUFBV:
      /*
       * EGRAPH + BITVECTOR + ARRAY solver
       */
      arch = CTX_ARCH_EGFUNBV;
      break;

    case QF_UFBV:
      /*
       * EGRAPH + BITVECTOR solver
       */
      arch = CTX_ARCH_EGBV;
      break;

    case QF_BV:
      /*
       * Pure bit-vector problem
       */
      arch = CTX_ARCH_BV;
      //      arch = CTX_ARCH_EGBV;
      break;

    default:
      /*
       * Not supported or unknown logic
       */
      print_internalization_code(LOGIC_NOT_SUPPORTED);
      code = YICES_EXIT_ERROR;
      goto cleanup_benchmark;
    }

  } else {
    fprintf(stderr, "No logic specified\n");
    code = YICES_EXIT_ERROR;
    goto cleanup_benchmark;
  }



  /*
   * Initialize the context and set options
   */
  init_context(&context, __yices_globals.terms, logic, CTX_MODE_ONECHECK, arch, false);
  if (var_elim) {
    enable_variable_elimination(&context);
  }
  if (flatten_or) {
    enable_diseq_and_or_flattening(&context);
  }
  if (learn_eq && arch == CTX_ARCH_EG) {
    enable_eq_abstraction(&context);
  }
  if (break_sym && arch == CTX_ARCH_EG) {
    enable_symmetry_breaking(&context);
  }
  if (arith_elim) {
    enable_arith_elimination(&context);
  }
  if (bvarith_elim) {
    enable_bvarith_elimination(&context);
  }
  if (keep_ite) {
    enable_keep_ite(&context);
  }
  if (eager_lemmas) {
    enable_splx_eager_lemmas(&context);
  }
  if (need_icheck) {
    enable_splx_periodic_icheck(&context);
  }
  if (dump_context) {
    context.options |= DUMP_OPTION_MASK;
  }
  init_trace (&tracer);
  set_trace_vlevel(&tracer, 3);
  context_set_trace(&context, &tracer);
  context_exists = true;

  /*
   * Assert then internalize
   */
  code = assert_formulas(&context, bench.nformulas, bench.formulas);
  print_internalization_code(code);
  if (code < 0) {
    print_results();
    code = YICES_EXIT_ERROR;
    goto cleanup_context;
  }

  if (dump_context || dump_internalization) {
    dump_the_context(&context, &bench, "yices_start.dmp");
  }

  if (code != TRIVIALLY_UNSAT) {
    /*
     * Search
     */
    if (use_default_params) {
      search_options = NULL;
    } else {
      search_options = &params;
    }

    print_options(stdout, &context);
    print_presearch_stats();
    start_search_time = get_cpu_time();

    if (timeout > 0) {
      to = init_timeout();
      start_timeout(to, timeout, timeout_handler, &context);
    }
    code = check_context(&context, search_options);
    clear_handler();

    if (timeout > 0) {
      clear_timeout(to);
      delete_timeout(to);
    }

    print_results();

    if (show_model && (code == STATUS_SAT || code == STATUS_UNKNOWN)) {
      model = new_model();
      context_build_model(model, &context);
      printf("\nMODEL\n");
      model_print(stdout, model);
      printf("----\n");

      // FOR TESTING
#if TEST_EVALUATOR
      test_evaluator(stdout, model);
#endif
      check_model(stdout, &bench, model);
      free_model(model);
    }

  }

  if (dump_context || dump_internalization) {
    dump_the_context(&context, &bench, "yices_end.dmp");
  }

  code = YICES_EXIT_SUCCESS;


  /*
   * Cleanup and return code
   *
   * To cleanup after an error: jump to cleanup_context if the error
   * is detected after the context is initialized or to cleanup_benchmark
   * if the error is detected before the context is initialized.
   */
 cleanup_context:
  delete_context(&context);
  delete_trace(&tracer);
 cleanup_benchmark:
  delete_benchmark(&bench);
  yices_exit();

  return code;
}



int main(int argc, char *argv[]) {
  parse_command_line(argc, argv);
  return process_benchmark(filename);
}

