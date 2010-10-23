/*
 * Yices solver for SMT benchmarks
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <signal.h>
#include <inttypes.h>
#include <gmp.h>

#include "cputime.h"
#include "memsize.h"
#include "smt_lexer.h"
#include "smt_parser.h"
#include "term_stack.h"
#include "context.h"
#include "smt_logic_codes.h"

#include "simplex.h"
#include "idl_floyd_warshall.h"
#include "rdl_floyd_warshall.h"
#include "fun_solver.h"
// #include "bvsolver.h"
// #include "model_printer.h"
#include "command_line.h"

#include "yices.h"
#include "yices_globals.h"
#include "yices_exit_codes.h"


/*
 * Define this to nonzero to display statistics
 */
#define SHOW_STATISTICS 1

/*
 * Define this to nonzero to enable command-line options
 */
#define COMMAND_LINE_OPTIONS 0



/*
 * GLOBAL OBJECTS
 */
static lexer_t lexer;
static parser_t parser;
static tstack_t stack;
static smt_benchmark_t bench;
static context_t context;
static param_t params;

#if SHOW_STATISTICS
static double construction_time, start_search_time, search_time;
#endif

/*
 * Flag for signal handler
 */
static bool context_exists;


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
  "context does not support arithmetic",
  "context does not support bitvectors",
  "context does not support function equalities",
  "context does not support quantifiers",
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
} optid_t;

#define NUM_OPTIONS (full_model_opt+1)

/*
 * Option descriptors for the command-line parser
 */
static option_desc_t options[NUM_OPTIONS] = {
  { "version", 'V', FLAG_OPTION, show_version_opt },
  { "help", 'h', FLAG_OPTION, print_help_opt },
  { "model", 'm', FLAG_OPTION, simple_model_opt },
  { "full-model", 'f', FLAG_OPTION, full_model_opt },
};



/*
 * Processing of these options
 */
static void print_version(void) {
  printf("Yices %s. Copyright SRI International.\n"
	 "GMP %s. Copyright Free Software Foundation, Inc.\n"
	 "Build date: %s\n"
	 "Platform: %s (%s)\n",
	 yices_version, gmp_version, 
	 yices_build_date, yices_build_arch, yices_build_mode);
  fflush(stdout);
}

static void yices_help(char *progname) {
  printf("Usage: %s [options] filename\n", progname);
  printf("Option summary:\n"
	 "   --version, -V         Show version and exit\n"
	 "   --help, -h            Print this message and exit\n"
	 "   --model, -m           Show a model (some variables may be eliminated)\n"
	 "   --full-model, -f      Show a model that includes all variables\n"
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

  filename = NULL;
  simple_model = false;
  full_model = false;

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






/**********************************
 *  PRINT STATISTICS AND RESULTS  *
 *********************************/


#if SHOW_STATISTICS

extern const char * const yices_svn_url;
extern const char * const yices_svn_rev;

/*
 * Version header
 */
static void print_yices_header(FILE *f) {
  fprintf(f, "Yices %s\n", yices_version);
  fprintf(f, "%s\n", yices_svn_url);
  fprintf(f, "Revision: %s\n", yices_svn_rev);
  fprintf(f, "Build date: %s\n", yices_build_date);
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
 * Statistics in the smt_core
 */
static void show_stats(dpll_stats_t *stat) {
  printf("Core\n");
  printf(" restarts                : %"PRIu32"\n", stat->restarts);
  printf(" simplify db             : %"PRIu32"\n", stat->simplify_calls);
  printf(" reduce db               : %"PRIu32"\n", stat->reduce_calls);
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
  printf(" prop. to core           : %"PRIu32"\n", stat->num_props);
  printf(" derived bounds          : %"PRIu32"\n", stat->num_bound_props);
  printf(" productive propagations : %"PRIu32"\n", stat->num_prop_expl);
  printf(" conflicts               : %"PRIu32"\n", stat->num_conflicts);
  if (stat->num_make_intfeasible > 0 || stat->num_dioph_checks > 0) {
    printf("Integer arithmetic\n");
    printf(" make integer feasible   : %"PRIu32"\n", stat->num_make_intfeasible);
    printf(" branch & bound          : %"PRIu32"\n", stat->num_branch_atoms);
    printf(" gcd conflicts           : %"PRIu32"\n", stat->num_gcd_conflicts);
    printf(" dioph checks            : %"PRIu32"\n", stat->num_dioph_checks);
    printf(" dioph conflicts         : %"PRIu32"\n", stat->num_dioph_conflicts);
    printf(" bound conflicts         : %"PRIu32"\n", stat->num_bound_conflicts);
    printf(" recheck conflicts       : %"PRIu32"\n", stat->num_recheck_conflicts);
  }
}


#if 0
/*
 * Bitvector solver statistics
 */
static void show_bvsolver_stats(bv_solver_t *solver) {
  printf("Bit-vectors\n");
  printf(" variables               : %"PRIu32"\n", bv_solver_num_vars(solver));
  printf(" atoms                   : %"PRIu32"\n", bv_solver_num_atoms(solver));
  printf(" eq. atoms               : %"PRIu32"\n", bv_solver_num_eq_atoms(solver));
  printf(" ge atoms                : %"PRIu32"\n", bv_solver_num_ge_atoms(solver));
  printf(" sge atoms               : %"PRIu32"\n", bv_solver_num_sge_atoms(solver));
}

#endif

/*
 * Get the arithmetic solver
 */
static inline simplex_solver_t *context_get_simplex_solver(context_t *ctx) {
  assert(context_has_simplex_solver(ctx));
  return (simplex_solver_t *) ctx->arith_solver;
}

static inline idl_solver_t *context_get_idl_solver(context_t *ctx) {
  assert(context_has_idl_solver(ctx));
  return (idl_solver_t *) ctx->arith_solver;
}

static inline rdl_solver_t *context_get_rdl_solver(context_t *ctx) {
  assert(context_has_rdl_solver(ctx));
  return (rdl_solver_t *) ctx->arith_solver;
}


/*
 * Statistics + result, after the search
 */
static void print_results() {
  smt_core_t *core;
  egraph_t *egraph;
  simplex_solver_t *simplex;
  fun_solver_t *fsolver;
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
  }

  if (context_has_simplex_solver(&context)) {
    simplex = context_get_simplex_solver(&context);
    if (simplex != NULL) {
      simplex_collect_statistics(simplex);
      show_simplex_stats(&simplex->stats);
    }
  }

#if 0
  if (context_has_bv_solver(&context)) {
    show_bvsolver_stats(context.bv_solver);
  }
#endif

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
static void print_presearch_stats() {
  smt_core_t *core;
  egraph_t *egraph;

  core = context.core;
  egraph = context.egraph;


  printf("boolean variables       : %"PRIu32"\n", core->nvars);
  printf("atoms                   : %"PRIu32"\n", core->atoms.natoms);
  if (egraph != NULL) {
    printf("egraph terms            : %"PRIu32"\n", egraph->terms.nterms);
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
      fprintf(f, " --aux-eq-quota=%"PRIu32" --aux-eq-ratio=%.3f\n", params.aux_eq_quota, params.aux_eq_ratio); 
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
    case BRANCHING_BV:
      fprintf(f, " --bv-branching");
      break;
    }
    fprintf(f, "\n");
  }
  fprintf(f, "\n");
}

#else

/*
 * NON-VERBOSE: JUST PRINT THE RESULT
 */
static void print_results() {
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



/*
 * SIGNAL PROCESSING
 */

/*
 * Signal handler: call print_results then exit
 */
static void handler(int signum) {
  if (context_exists) {
    print_results();
  }
  printf("Interrupted by signal %d\n\n", signum);
  exit(YICES_EXIT_INTERRUPTED);
}

/*
 * Set the signal handler: to print statistics on
 * SIGINT, SIGABRT, SIGXCPU
 */
static void init_handler() {
  signal(SIGINT, handler);
  signal(SIGABRT, handler);
#ifndef MINGW
  signal(SIGXCPU, handler);
#endif
}







/*
 * MAIN SOLVER FUNCTION
 * - parse input file (assumed to be in SMT-LIB format)
 * - solve bechmark
 * - return an exit code (defined in yices_exit_codes.h)
 */
static int process_benchmark(void) {
  int32_t code;
  context_arch_t arch;
  bool need_icheck;   // true if simplex needs integer check
  smt_logic_t logic;  // logic code read from the file
#if SHOW_STATISTICS
  double mem_used;
#endif


#if SHOW_STATISTICS
  print_yices_header(stdout);
#endif

#if COMMAND_LINE_OPTIONS
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
  tstack_set_smt_mode();
  init_tstack(&stack);
  init_parser(&parser, &lexer, &stack);
  init_benchmark(&bench);
  code = parse_smt_benchmark(&parser, &bench);
  if (code < 0) {
    return YICES_EXIT_SYNTAX_ERROR;
  }

#if SHOW_STATISTICS
  construction_time = get_cpu_time();
  mem_used = mem_size() / (1024 * 1024);
  print_benchmark(stdout, &bench);
  printf("Construction time: %.4f s\n", construction_time);
  printf("Memory used: %.2f MB\n", mem_used);
  fflush(stdout);
#endif

  delete_parser(&parser);
  close_lexer(&lexer);
  delete_tstack(&stack);

  /*
   * Select architecture based on the benchmark logic
   */
  need_icheck = false;
  
  if (bench.logic_name != NULL) {
    logic = smt_logic_code(bench.logic_name);
    switch (logic) {
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
       */
      arch = CTX_ARCH_AUTO_IDL;
      break;

    case QF_RDL:
      /*
       * Default for QF_RDL: automatic 
       */
      arch = CTX_ARCH_AUTO_RDL;
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
       * The default is EGRAPH + SIMPLEX.
       */
      arch = CTX_ARCH_EGSPLX;
      break;

    case QF_UFLRA:
      /*
       * EGRAPH + SIMPLEX
       */
      arch = CTX_ARCH_EGSPLX;
      break;

    case QF_UFLIA:
      /*
       * EGRAPH + SIMPLEX, activate periodic integer checks
       */
      need_icheck = true;
      arch = CTX_ARCH_EGSPLX;
      break;

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
      //      arch = CTX_ARCH_BV;
      arch = CTX_ARCH_NOSOLVERS; 
      // Hack: replace BV by empty solver (to exercise the internalization functions).
      break;

    default:
      /*
       * Not supported yet
       */
      print_internalization_code(LOGIC_NOT_SUPPORTED);
      return YICES_EXIT_ERROR;
    }

  } else {
    printf("unknown\n");
    printf("No logic specified\n");
    return YICES_EXIT_ERROR;
  }

  /*
   * Initialize the context and set internalization options
   * and global search options
   */
  init_params_to_defaults(&params);
  init_context(&context, __yices_globals.terms, CTX_MODE_ONECHECK, arch, false);
  switch (arch) {
  case CTX_ARCH_EG:
    // QF_UF options: --var-elim --cache-tclauses --learn-eq --dyn-bool-ack
    enable_variable_elimination(&context);
    enable_eq_abstraction(&context);
    params.use_bool_dyn_ack = true;
    params.cache_tclauses = true;
    params.tclause_size = 8;
    break;

  case CTX_ARCH_SPLX: 
    // options: --flatten --theory-branching --cache-tclauses --arith-elim --var-elim
    enable_variable_elimination(&context);
    enable_arith_elimination(&context);
    enable_diseq_and_or_flattening(&context);
    params.branching = BRANCHING_THEORY;
    params.cache_tclauses = true;
    params.tclause_size = 8;
    if (need_icheck) {
      enable_splx_periodic_icheck(&context);
      if (logic == QF_LIA) {
	// TESTS for yices_smtcomp8 on QF_LIA
	enable_splx_eager_lemmas(&context);
	params.use_simplex_prop = true;
	params.tclause_size = 20;
      }
    }
    break;

  case CTX_ARCH_BV:
    // QF_BV options: --flatten --var-elim --fast-restarts --randomness=0 --bvarith-elim
    enable_diseq_and_or_flattening(&context);
    enable_variable_elimination(&context);
    enable_bvarith_elimination(&context);
    params.fast_restart = true;
    params.c_factor = 1.1;  
    params.d_factor = 1.1; 
    params.randomness = 0.0;
    break;

  case CTX_ARCH_EGFUN:        // egraph+array/function theory 
    enable_diseq_and_or_flattening(&context);
    enable_variable_elimination(&context);
    break;
    
  case CTX_ARCH_EGSPLX:       // egraph+simplex
  case CTX_ARCH_EGFUNSPLX:    // egraph+fun+simplex
    enable_variable_elimination(&context);
    enable_arith_elimination(&context);
    enable_diseq_and_or_flattening(&context);
    params.use_dyn_ack = true;
    params.use_bool_dyn_ack = true;
    params.use_simplex_prop = true;
    params.cache_tclauses = true;
    params.tclause_size = 8;
    params.max_interface_eqs = 30;
    if (logic == QF_UFLIA) {
      params.branching = BRANCHING_NEGATIVE;
    } else {
      params.branching = BRANCHING_THEORY;
    }
    if (need_icheck) {
      enable_splx_periodic_icheck(&context);
      params.max_interface_eqs = 15;
    }
    break;

  case CTX_ARCH_EGBV:         // egraph+bitvector solver
  case CTX_ARCH_EGFUNBV:      // egraph+fun+bitvector
    // QF_BV options: --flatten --var-elim --fast-restarts --randomness=0 --bvarith-elim
    enable_diseq_and_or_flattening(&context);
    enable_variable_elimination(&context);
    enable_bvarith_elimination(&context);
    params.fast_restart = true;
    params.c_factor = 1.1;  
    params.d_factor = 1.1; 
    params.randomness = 0.0;
    // TEST: default --> 200
    //       r1263b/r1268b--> 40
    //       r1263c/r1268c --> 60
    //       r1263d --> 80
    //       r1268e --> 10
    //       r1268f --> 1
    //       r1268g --> 20
    //       r1268h --> 30
    //       r1268i --> 15
    params.max_interface_eqs = 15;
    break;

  case CTX_ARCH_AUTO_IDL:
    // nothing required
    break;

  case CTX_ARCH_AUTO_RDL:
    // preprocessing option: --flatten is used by both FW and SPLX
    enable_diseq_and_or_flattening(&context);
    break;

  default:
    enable_variable_elimination(&context);
    enable_diseq_and_or_flattening(&context);
    break;
  }

  /*
   * Assert and internalize
   */
  code = assert_formulas(&context, bench.nformulas, bench.formulas);
  print_internalization_code(code);
  if (code < 0) {
    return YICES_EXIT_ERROR;
  }

  if (code != TRIVIALLY_UNSAT) {

    /*
     * Adjust the search parameters for AUTO_IDL or AUTO_RDL
     */
    switch (arch) {
    case CTX_ARCH_AUTO_IDL:
      if (context_has_idl_solver(&context)) {
	// IDL/Floyd-Warshall: --flatten --cache-tclauses --fast-restarts
	params.cache_tclauses = true;
	params.tclause_size = 8;
	params.fast_restart = true;
      
      } else {
	assert(context_has_simplex_solver(&context));
	// SIMPLEX: --split-eqs --theory-branching --cache-tclauses
	params.branching = BRANCHING_THEORY;
	params.cache_tclauses = true;
	params.tclause_size = 8;
	// if equalities are present also enable --simplex-prop
	if (get_diff_logic_profile(&context)->num_eqs >= 10) {
	  params.use_simplex_prop = true;
	}
      }
      break;

    case CTX_ARCH_AUTO_RDL:
      if (context_has_rdl_solver(&context)) {
	// RDL/Floyd-Warshall: --cache-tclauses --fast-restarts --tclause-size=20
	params.cache_tclauses = true;
	params.tclause_size = 20;
	params.fast_restart = true;
      } else {
	assert(context_has_simplex_solver(&context));
	// SIMPLEX: --theory-branching  --flatten --split-eqs
	params.branching = BRANCHING_THEORY;
      }
      break;

    default:
      break;
    }

#if SHOW_STATISTICS
    print_options(stdout, &context);
    print_presearch_stats();
    start_search_time = get_cpu_time();
#endif

    code = check_context(&context, &params, true);
    print_results();

#if COMMAND_LINE_OPTIONS
    if ((simple_model || full_model) && (code == STATUS_SAT || code == STATUS_UNKNOWN)) {
      model_t *model;

      // if full_model is true, keep substitutions in the model
      // and print everything
      // otherwise, print a simple model (don't worry about eliminated variables)
      model = context_build_model(&context, full_model);
      printf("\nMODEL\n");
      if (full_model) {
	model_print_full(stdout, model);
      } else {
	model_print(stdout, model);
      }
      printf("----\n");
      free_model(model);
    }
#endif

  }

  /*
   * Cleanup
   */
  delete_context(&context);
  delete_benchmark(&bench);
  yices_exit();

  return YICES_EXIT_SUCCESS;
}



int main(int argc, char *argv[]) {
#if COMMAND_LINE_OPTIONS
  parse_command_line(argc, argv);
#endif
  return process_benchmark();
}

