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

#include "api/context_config.h"
#include "api/smt_logic_codes.h"
#include "api/yices_globals.h"
#include "context/context.h"
#include "frontend/smt1/smt_lexer.h"
#include "frontend/smt1/smt_parser.h"
#include "frontend/smt1/smt_term_stack.h"

#include "yices.h"
#include "yices_exit_codes.h"


/*
 * Define this to nonzero to display statistics
 */
#define SHOW_STATISTICS 1

/*
 * Define this to nonzero to enable command-line options
 */
#define COMMAND_LINE_OPTIONS 1

/*
 * Define this to nonzero to check the model
 * - this has no effect unless COMMAND_LINE_OPTIONS is nonzero
 */
#define CHECK_MODEL 0

#if COMMAND_LINE_OPTIONS
#include "io/model_printer.h"
#include "utils/command_line.h"
#include "utils/timeout.h"
#if CHECK_MODEL
#include "io/term_printer.h"
#include "model/model_eval.h"
#endif
#endif

#if SHOW_STATISTICS || COMMAND_LINE_OPTIONS
#include "utils/cputime.h"
#include "utils/memsize.h"
#endif

#if SHOW_STATISTICS
#include "solvers/bv/bvsolver.h"
#endif


/*
 * GLOBAL OBJECTS
 */
static lexer_t lexer;
static parser_t parser;
static tstack_t stack;
static smt_benchmark_t bench;
static context_t context;
static param_t params;

/*
 * Flag for signal handler
 */
static bool context_exists;


/*
 * Show statistics or not
 */
#if SHOW_STATISTICS
static bool show_statistics;
#endif

/*
 * Runtime statistics: used if statistics are enable
 * or if --verbose is given on the command line
 */
#if SHOW_STATISTICS || COMMAND_LINE_OPTIONS
static double start_search_time, search_time;
#endif

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



/************************************
 *  COMMAND LINE ARGUMENTS/OPTIONS  *
 ***********************************/

#if COMMAND_LINE_OPTIONS

/*
 * Flag: show-model or not
 */
static bool simple_model;
static bool full_model;

/*
 * Verbose or not
 */
static bool verbose;
static double construction_time;

/*
 * Tracer object (for verbose mode)
 */
static tracer_t tracer;

/*
 * Timeout value in seconds (0 means no timeout)
 */
static uint32_t timeout;

/*
 * Input file given on the command line.
 * If this is NULL, we read from stdin.
 */
static char *filename;

/*
 * Internal codes for each option
 */
typedef enum optid {
  show_version_opt,           // print version and exit
  print_help_opt,             // print help and exit
  simple_model_opt,           // print the model if SAT
  full_model_opt,             // full model
  verbose_opt,                // output during search
#if SHOW_STATISTICS
  show_stats_opt,             // show statistics
#endif
  timeout_opt,                // give a timeout
} optid_t;

#define NUM_OPTIONS (timeout_opt+1)

/*
 * Option descriptors for the command-line parser
 */
static option_desc_t options[NUM_OPTIONS] = {
  { "version", 'V', FLAG_OPTION, show_version_opt },
  { "help", 'h', FLAG_OPTION, print_help_opt },
  { "model", 'm', FLAG_OPTION, simple_model_opt },
  { "full-model", 'f', FLAG_OPTION, full_model_opt },
  { "verbose", 'v', FLAG_OPTION, verbose_opt },
#if SHOW_STATISTICS
  { "stats", 's', FLAG_OPTION, show_stats_opt },
#endif
  { "timeout", 't', MANDATORY_INT, timeout_opt },
};



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
         yices_version, gmp_version,
         yices_build_date, yices_build_arch, yices_build_mode);
  fflush(stdout);
}

static void yices_help(char *progname) {
  printf("Usage: %s [options] filename\n", progname);
  printf("Option summary:\n"
         "   --version, -V              Show version and exit\n"
         "   --help, -h                 Print this message and exit\n"
         "   --model, -m                Show a model (some variables may be eliminated)\n"
         "   --full-model, -f           Show a model that includes all variables\n"
         "   --verbose, -v              Print statistics during the search\n"
#if SHOW_STATISTICS
         "   --stats, -s                Show search statistics\n"
#endif
         "   --timeout=<int>, -t <int>  Give a timeout in seconds (default: no timeout)\n"
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
 * Parse the command line and fill-in the parameters
 */
static void parse_command_line(int argc, char *argv[]) {
  cmdline_parser_t parser;
  cmdline_elem_t elem;
  optid_t k;
  int32_t val;

  filename = NULL;
  simple_model = false;
  full_model = false;
  verbose = false;
  timeout = 0;

#if SHOW_STATISTICS
  show_statistics = false;
#endif

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
      switch (k) {
      case show_version_opt:
        print_version();
        exit(YICES_EXIT_SUCCESS);

      case print_help_opt:
        yices_help(parser.command_name);
        exit(YICES_EXIT_SUCCESS);

      case simple_model_opt:
        simple_model = true;
        break;

      case full_model_opt:
        full_model = true;
        break;

      case verbose_opt:
        verbose = true;
        break;

#if SHOW_STATISTICS
      case show_stats_opt:
        show_statistics = true;
        break;
#endif

      case timeout_opt:
        val = elem.i_value;
        if (val <= 0) {
          fprintf(stderr, "%s: the timeout must be positive\n", parser.command_name);
          yices_usage(parser.command_name);
          exit(YICES_EXIT_USAGE);
        }
        timeout = val;
        break;
      }
      break;

    case cmdline_error:
      cmdline_print_error(&parser, &elem);
      fprintf(stderr, "Try '%s --help' for more information\n", parser.command_name);
      exit(YICES_EXIT_USAGE);
    }
  }

 done:
  // nothing to do
  return;
}


#endif




/***********************************
 *  EXTRA OUTPUT FOR VERBOSE MODE  *
 **********************************/

#if COMMAND_LINE_OPTIONS

/*
 * Version header
 */
static void print_yices_header(FILE *f) {
  fprintf(f, "Yices %s, Copyright SRI International.\n", yices_version);
  fprintf(f, "GMP %s, Copyright Free Software Foundation, Inc\n", gmp_version);
  fprintf(f, "Build date: %s\n", yices_build_date);
  fprintf(f, "Platform: %s (%s)\n", yices_build_arch, yices_build_mode);
  fprintf(f, "----\n");
}


/*
 * Benchmark header
 */
static void print_benchmark(FILE *f, smt_benchmark_t *bench) {
  fprintf(f, "Benchmark: %s\n", bench->name);
  fprintf(f, "Logic: %s\n", bench->logic_name);
  fprintf(f, "Status field: %s\n", status2string[bench->status]);
}


/*
 * Statistics on problem size, before the search
 */
static void print_presearch_stats(FILE *f) {
  smt_core_t *core;

  core = context.core;
  fprintf(f, "boolean variables       : %"PRIu32"\n", core->nvars);
  fprintf(f, "atoms                   : %"PRIu32"\n", core->atoms.natoms);
  fprintf(f, "\n");
  fflush(f);
}



/*
 * Print parameters and settings:
 * - disabled this for now: these options can't be set so there's
 *   no reason to print them. Also the meaning of many of them
 *   is mysterious.
 */
static void print_options(FILE *f, context_t *ctx) {
}

#endif


/**********************************
 *  PRINT STATISTICS AND RESULTS  *
 *********************************/

#if SHOW_STATISTICS

/*
 * Statistics in the smt_core
 */
static void show_stats(dpll_stats_t *stat) {
  fprintf(stderr, "Core\n");
  fprintf(stderr, " restarts                : %"PRIu32"\n", stat->restarts);
  fprintf(stderr, " simplify db             : %"PRIu32"\n", stat->simplify_calls);
  fprintf(stderr, " reduce db               : %"PRIu32"\n", stat->reduce_calls);
  fprintf(stderr, " decisions               : %"PRIu64"\n", stat->decisions);
  fprintf(stderr, " random decisions        : %"PRIu64"\n", stat->random_decisions);
  fprintf(stderr, " propagations            : %"PRIu64"\n", stat->propagations);
  fprintf(stderr, " conflicts               : %"PRIu64"\n", stat->conflicts);
  fprintf(stderr, " theory propagations     : %"PRIu32"\n", stat->th_props);
  fprintf(stderr, " propagation-lemmas      : %"PRIu32"\n", stat->th_prop_lemmas);
  fprintf(stderr, " theory conflicts        : %"PRIu32"\n", stat->th_conflicts);
  fprintf(stderr, " conflict-lemmas         : %"PRIu32"\n", stat->th_conflict_lemmas);

  fprintf(stderr, " lits in pb. clauses     : %"PRIu64"\n", stat->prob_literals);
  fprintf(stderr, " lits in learned clauses : %"PRIu64"\n", stat->learned_literals);
  fprintf(stderr, " total lits. in learned  : %"PRIu64"\n", stat->literals_before_simpl);
  fprintf(stderr, " subsumed lits.          : %"PRIu64"\n", stat->subsumed_literals);
  fprintf(stderr, " deleted pb. clauses     : %"PRIu64"\n", stat->prob_clauses_deleted);
  fprintf(stderr, " deleted learned clauses : %"PRIu64"\n", stat->learned_clauses_deleted);
  fprintf(stderr, " deleted binary clauses  : %"PRIu64"\n", stat->bin_clauses_deleted);
}

/*
 * Bitvector solver statistics
 */
static void show_bvsolver_stats(bv_solver_t *solver) {
  fprintf(stderr, "Bit-vectors\n");
  fprintf(stderr, " variables               : %"PRIu32"\n", bv_solver_num_vars(solver));
  fprintf(stderr, " atoms                   : %"PRIu32"\n", bv_solver_num_atoms(solver));
  fprintf(stderr, " eq. atoms               : %"PRIu32"\n", bv_solver_num_eq_atoms(solver));
  fprintf(stderr, " dyn eq. atoms           : %"PRIu32"\n", solver->stats.on_the_fly_atoms);
  fprintf(stderr, " ge atoms                : %"PRIu32"\n", bv_solver_num_ge_atoms(solver));
  fprintf(stderr, " sge atoms               : %"PRIu32"\n", bv_solver_num_sge_atoms(solver));
  fprintf(stderr, " equiv lemmas            : %"PRIu32"\n", solver->stats.equiv_lemmas);
  fprintf(stderr, " equiv conflictss        : %"PRIu32"\n", solver->stats.equiv_conflicts);
  fprintf(stderr, " semi-equiv lemmas       : %"PRIu32"\n", solver->stats.half_equiv_lemmas);
  fprintf(stderr, " interface lemmas        : %"PRIu32"\n", solver->stats.interface_lemmas);
}



/*
 * Statistics + result, after the search
 */
static void print_results(void) {
  smt_core_t *core;
  uint32_t resu;
  double mem_used;

  if (show_statistics) {
    search_time = get_cpu_time() - start_search_time;
    if (search_time < 0.0) {
      search_time = 0.0;
    }

    core = context.core;

    show_stats(&core->stats);
    fprintf(stderr, " boolean variables       : %"PRIu32"\n", core->nvars);
    fprintf(stderr, " atoms                   : %"PRIu32"\n", core->atoms.natoms);

    if (context_has_bv_solver(&context)) {
      show_bvsolver_stats(context.bv_solver);
    }

    fprintf(stderr, "\nSearch time             : %.4f s\n", search_time);
    mem_used = mem_size() / (1024 * 1024);
    if (mem_used > 0) {
      fprintf(stderr, "Memory used             : %.2f MB\n", mem_used);
    }
    fprintf(stderr, "\n\n");
    fflush(stderr);
  }

  resu = context.core->status;
  if (resu == STATUS_SAT) {
    printf("sat\n");
  } else if (resu == STATUS_UNSAT) {
    printf("unsat\n");
  } else {
    printf("unknown\n");
  }

  fflush(stdout);
}


#else

/*
 * STATISTICS DISABLED: JUST PRINT THE RESULT
 */
static void print_results(void) {
  uint32_t resu;

  resu = context.core->status;

  if (resu == STATUS_SAT) {
    printf("sat\n");
  } else if (resu == STATUS_UNSAT) {
    printf("unsat\n");
  } else {
    printf("unknown\n");
  }
  fflush(stdout);

#if COMMAND_LINE_OPTIONS
  if (verbose) {
    fprintf(stderr, "\nSearch time             : %.4f s\n", search_time);
    double mem_used = mem_size() / (1024 * 1024);
    if (mem_used > 0) {
      fprintf(stderr, "Memory used             : %.2f MB\n", mem_used);
    }
    fprintf(stderr, "\n\n");
  }
#endif
}


#endif


/*
 * Print the translation code returned by assert
 */
static void print_internalization_code(int32_t code) {
  assert(-NUM_INTERNALIZATION_ERRORS < code && code <= TRIVIALLY_UNSAT);
  if (code == TRIVIALLY_UNSAT) {
    printf("unsat\n");
    //    printf("Assertions simplify to false\n\n");
  } else if (code < 0) {
    printf("unknown\n");
    code = - code;
    if (code <= BVSOLVER_EXCEPTION) {
      printf("Internalization error: %s\n\n", code2error[code]);
    } else {
      printf("%s\n\n", code2error[code]);
    }
  }
  fflush(stdout);
}



/***************************
 *  OPTIONAL: CHECK MODEL  *
 **************************/

#if COMMAND_LINE_OPTIONS && CHECK_MODEL

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
      //      print_term(f, __yices_globals.terms, t);
      pretty_print_term_exp(f, NULL, __yices_globals.terms, t);
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

#endif


/****************************
 *  TIMEOUT AND INTERRUPTS  *
 ***************************/

/*
 * Signal handler: call print_results then exit
 */
static void handler(int signum) {
  if (context_exists) {
    print_results();
  }
  fprintf(stderr, "Interrupted by signal %d\n\n", signum);
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


#if COMMAND_LINE_OPTIONS
/*
 * Timeout handler
 * - p = pointer to the context
 */
static void timeout_handler(void *p) {
  context_t *ctx;
  ctx = p;
  stop_search(ctx->core);
}

#endif



/*
 * MAIN SOLVER FUNCTION
 * - parse input file (assumed to be in SMT-LIB format)
 * - solve benchmark
 * - return an exit code (defined in yices_exit_codes.h)
 */
static int process_benchmark(void) {
  int32_t code;
  smt_logic_t logic;  // logic code read from the file
#if COMMAND_LINE_OPTIONS
  double mem_used;
#endif

#if COMMAND_LINE_OPTIONS
  if (verbose) {
    print_yices_header(stderr);
  }

  // open input file if given or stdin
  if (filename != NULL) {
    if (init_smt_file_lexer(&lexer, filename) < 0) {
      perror(filename);
      return YICES_EXIT_FILE_NOT_FOUND;
    }
  } else {
    init_smt_stdin_lexer(&lexer);
  }
#else
  // no command line option so read from stdin
  init_smt_stdin_lexer(&lexer);
#endif

  // initialize the signal handler
  context_exists = false;
  init_handler();

  /*
   * Parse and build the formula
   */
  yices_init();
  init_smt_tstack(&stack);

  init_parser(&parser, &lexer, &stack);
  init_benchmark(&bench);
  code = parse_smt_benchmark(&parser, &bench); // code < 0 means syntax error, 0 means OK

#if COMMAND_LINE_OPTIONS
  if (verbose && code == 0) {
    construction_time = get_cpu_time();
    mem_used = mem_size() / (1024 * 1024);
    print_benchmark(stderr, &bench);
    fprintf(stderr, "Construction time: %.4f s\n", construction_time);
    fprintf(stderr, "Memory used: %.2f MB\n\n", mem_used);
    fflush(stderr);
  }
#endif

  delete_parser(&parser);
  close_lexer(&lexer);
  delete_tstack(&stack);

  if (code < 0) {
    code = YICES_EXIT_SYNTAX_ERROR;
    goto cleanup_benchmark;
  }


  /*
   * Select architecture based on the benchmark logic
   */
  if (bench.logic_name != NULL) {
    logic = smt_logic_code(bench.logic_name);
    if (logic != QF_BV) {
      print_internalization_code(LOGIC_NOT_SUPPORTED);
      code = YICES_EXIT_ERROR;
      goto cleanup_benchmark;
    }
  } else {
    printf("unknown\n");
    printf("No logic specified\n");
    code = YICES_EXIT_ERROR;
    goto cleanup_benchmark;
  }

  /*
   * Initialize the context and set internalization options
   * and global search options
   */

  // QF_BV options: --var-elim --fast-restarts --randomness=0 --bvarith-elim
  //    enable_diseq_and_or_flattening(&context);  flatten makes things worse
  init_params_to_defaults(&params);
  init_context(&context, __yices_globals.terms, logic, CTX_MODE_ONECHECK, CTX_ARCH_BV, false);
  enable_variable_elimination(&context);
  enable_bvarith_elimination(&context);
  params.fast_restart = true;
  params.randomness = 0.0;
  params.c_factor = 1.05;
  params.d_factor = 1.05;

#if COMMAND_LINE_OPTIONS
  if (verbose) {
    init_trace(&tracer);
    set_trace_vlevel(&tracer, 2);
    context_set_trace(&context, &tracer);
  }
#endif

  context_exists = true;

  /*
   * Assert and internalize
   */
  code = assert_formulas(&context, bench.nformulas, bench.formulas);
  print_internalization_code(code);
  if (code < 0) {
    code = YICES_EXIT_ERROR;
    goto cleanup_context;
  }

  if (code != TRIVIALLY_UNSAT) {

#if COMMAND_LINE_OPTIONS
    /*
     * Deal with verbosity, timeout, model, and statistics
     */
    if (verbose) {
      print_options(stderr, &context);
      print_presearch_stats(stderr);
    }

    start_search_time = get_cpu_time();

    if (timeout > 0) {
      init_timeout();
      start_timeout(timeout, timeout_handler, &context);
    }
    code = check_context(&context, &params);
    clear_handler();
    if (timeout > 0) {
      clear_timeout();
      delete_timeout();
    }
    print_results();

    if ((simple_model || full_model) && (code == STATUS_SAT || code == STATUS_UNKNOWN)) {
      model_t *model;

      /*
       * if full_model is true, keep substitutions in the model
       * and print everything
       * otherwise, print a simple model (don't worry about eliminated variables)
       */
      model = (model_t *) safe_malloc(sizeof(model_t));
      init_model(model, __yices_globals.terms, full_model);
      context_build_model(model, &context);
      printf("\n");
      if (full_model) {
        model_print_full(stdout, model);
      } else {
        model_print(stdout, model);
      }
      printf("\n");
#if CHECK_MODEL
      check_model(stdout, &bench, model);
#endif
      delete_model(model);
      safe_free(model);
    }

#else
    /*
     * no command-line options:
     */
#if SHOW_STATISTICS
    start_search_time = get_cpu_time();
#endif
    code = check_context(&context, &params);
    clear_handler();
    print_results();
#endif
  }

  code = YICES_EXIT_SUCCESS;

  /*
   * Cleanup and return code
   */
 cleanup_context:
  delete_context(&context);
#if COMMAND_LINE_OPTIONS
  if (verbose) {
    delete_trace(&tracer);
  }
#endif

 cleanup_benchmark:
  delete_benchmark(&bench);
  yices_exit();

  return code;
}



int main(int argc, char *argv[]) {
#if SHOW_STATISTICS
  show_statistics = true; // can be overridden by parse_command_line if enabled
#endif

#if COMMAND_LINE_OPTIONS
  parse_command_line(argc, argv);
#endif

  return process_benchmark();
}

