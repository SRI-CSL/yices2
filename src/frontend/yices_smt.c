/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
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

#include "utils/command_line.h"
#include "utils/cputime.h"
#include "utils/memsize.h"
#include "utils/timeout.h"

#include "yices.h"
#include "yices_exit_codes.h"


/*
 * yices_rev is set up at compile time in yices_version.c
 */
#ifndef NDEBUG
extern const char * const yices_rev;
#endif


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
  "too many variables for the arithmetic solver",
  "too many atoms for the arithmetic solver",
  "arithmetic solver exception",
  "bitvector solver exception",
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
static bool arith_elim;
static bool bvarith_elim;
static bool keep_ite;
static bool dump_context;
static bool dump_internalization;
static bool show_model;

/*
 * Timeout value in seconds (0 means no timeout)
 */
static uint32_t timeout;

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
 * COMMAND-LINE OPTIONS AND FLAGS
 */
typedef enum optid {
  show_version_opt,           // print version and exit
  print_help_opt,             // print help and exit

  // Internalization
  var_elim_opt,               // apply var elimination during internalization
  arith_elim_opt,             // eliminate arithmetic variables
  bvarith_elim_opt,           // simplification of bitvector arithmetic expressions
  flatten_opt,                // flatten or and disequality terms
  learneq_opt,                // learn UF equalities
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
         "    --arith-elim\n"
         "    --bvarith-elim\n"
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
        break;

        // integer parameters
      case c_threshold_opt:
      case d_threshold_opt:
      case r_threshold_opt:
      case randomseed_opt:
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
#ifndef NDEBUG
  fprintf(f, "Revision: %s\n", yices_rev);
#endif
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
 * Statistics + result, after the search
 */
static void print_results(void) {
  smt_core_t *core;
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

  core = context.core;

  printf("boolean variables       : %"PRIu32"\n", core->nvars);
  printf("atoms                   : %"PRIu32"\n", core->atoms.natoms);
  printf("\n");
  fflush(stdout);
}


/*
 * Print parameters and settings
 */
static void print_options(FILE *f, context_t *ctx) {
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

  if (params.fast_restart || params.branching != BRANCHING_DEFAULT) {
    fprintf(f, "Core: ");
    if (params.fast_restart) {
      fprintf(f, " --fast-restarts");
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
    if (code <= BVSOLVER_EXCEPTION) {
      fprintf(stderr, "Internalization error: %s\n\n", code2error[code]);
    } else {
      fprintf(stderr, "%s\n\n", code2error[code]);
    }
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

/*
 * Signal handler: call print_results then exit
 */
static void handler(int signum) {
  printf("Interrupted by signal %d\n\n", signum);
  if (context_exists) {
    if (dump_context || dump_internalization) {
      dump_the_context(&context, &bench, "yices_exit.dmp");
    }
    print_results();
  }
  exit(YICES_EXIT_INTERRUPTED);
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
  arch = CTX_ARCH_NOSOLVERS; // otherwise GCC gives a warning

  if (bench.logic_name != NULL) {
    logic = smt_logic_code(bench.logic_name);
    switch (logic) {
    case QF_BV:
      /*
       * Pure bit-vector problem
       */
      arch = CTX_ARCH_BV;
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
  if (arith_elim) {
    enable_arith_elimination(&context);
  }
  if (bvarith_elim) {
    enable_bvarith_elimination(&context);
  }
  if (keep_ite) {
    enable_keep_ite(&context);
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
      init_timeout();
      start_timeout(timeout, timeout_handler, &context);
    }
    code = check_context(&context, search_options);
    clear_handler();

    if (timeout > 0) {
      clear_timeout();
      delete_timeout();
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

