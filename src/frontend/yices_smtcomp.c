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
#include <inttypes.h>
#include <errno.h>
#include <unistd.h>
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
#include "solvers/simplex/simplex.h"
#include "utils/cputime.h"
#include "utils/memsize.h"
#endif

#if SHOW_STATISTICS
#include "solvers/bv/bvsolver.h"
#include "solvers/funs/fun_solver.h"
#include "solvers/quant/quant_solver.h"
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
  "division by zero is not supported",
  "too many variables for the arithmetic solver",
  "too many atoms for the arithmetic solver",
  "arithmetic solver exception",
  "bitvector solver exception",
  "theory not supported by MCSAT",
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

#if COMMAND_LINE_OPTIONS || SHOW_STATISTICS
/*
 * Get the arithmetic solver
 */
static inline simplex_solver_t *context_get_simplex_solver(context_t *ctx) {
  assert(context_has_simplex_solver(ctx));
  return (simplex_solver_t *) ctx->arith_solver;
}

#endif

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
  egraph_t *egraph;

  core = context.core;
  egraph = context.egraph;

  fprintf(f, "boolean variables       : %"PRIu32"\n", core->nvars);
  fprintf(f, "atoms                   : %"PRIu32"\n", core->atoms.natoms);
  if (egraph != NULL) {
    fprintf(f, "egraph terms            : %"PRIu32"\n", egraph->terms.nterms);
    fprintf(f, "app/update reductions   : %"PRIu32"\n", egraph->stats.app_reductions);
  }

  if (context_has_simplex_solver(&context)) {
    fprintf(f, "arithmetic solver       : Simplex\n");
  } else if (context_has_idl_solver(&context)) {
    fprintf(f, "arithmetic solver       : IDL Floyd-Warshall\n");
  } else if (context_has_rdl_solver(&context)) {
    fprintf(f, "arithmetic solver       : RDL Floyd-Warshall\n");
  }
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
#if 0
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
      fprintf(f, " --break-symmetries");
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
        fprintf(f, " --simplex-ajust-model");
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
        fprintf(f, " --dyn-ack --max-ack=%"PRIu32" --dyn-ack-threshold=%"PRIu32,
                params.max_ackermann, (uint32_t) params.dyn_ack_threshold);
      }
      if (params.use_bool_dyn_ack) {
        fprintf(f, " --dyn-bool-ack --max-bool-ack=%"PRIu32" --dyn-bool-ack-threshold=%"PRIu32,
                params.max_boolackermann, (uint32_t) params.dyn_bool_ack_threshold);
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
    }
    fprintf(f, "\n");
  }
  fprintf(f, "\n");
#endif
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
 * Egraph statistics
 */
static void show_egraph_stats(egraph_stats_t *stat) {
  fprintf(stderr, "Egraph\n");
  fprintf(stderr, " eq from simplex         : %"PRIu32"\n", stat->eq_props);
  fprintf(stderr, " prop. to core           : %"PRIu32"\n", stat->th_props);
  fprintf(stderr, " conflicts               : %"PRIu32"\n", stat->th_conflicts);
  fprintf(stderr, " non-distinct lemmas     : %"PRIu32"\n", stat->nd_lemmas);
  fprintf(stderr, " auxiliary eqs. created  : %"PRIu32"\n", stat->aux_eqs);
  fprintf(stderr, " dyn boolack. lemmas     : %"PRIu32"\n", stat->boolack_lemmas);
  fprintf(stderr, " other dyn ack.lemmas    : %"PRIu32"\n", stat->ack_lemmas);
  fprintf(stderr, " final checks            : %"PRIu32"\n", stat->final_checks);
  fprintf(stderr, " interface equalities    : %"PRIu32"\n", stat->interface_eqs);
}


/*
 * Array/function solver statistics
 */
static void show_funsolver_stats(fun_solver_stats_t *stat) {
  fprintf(stderr, "Arrays\n");
  fprintf(stderr, " init. variables         : %"PRIu32"\n", stat->num_init_vars);
  fprintf(stderr, " init. edges             : %"PRIu32"\n", stat->num_init_edges);
  fprintf(stderr, " update axiom1           : %"PRIu32"\n", stat->num_update_axiom1);
  fprintf(stderr, " update axiom2           : %"PRIu32"\n", stat->num_update_axiom2);
  fprintf(stderr, " extensionality axioms   : %"PRIu32"\n", stat->num_extensionality_axiom);
}

/*
 * Quantifier solver statistics
 */
static void show_quantsolver_stats(quant_solver_stats_t *stat) {
  fprintf(stderr, "Quantifiers\n");
  fprintf(stderr, " quantifiers             : %"PRIu32"\n", stat->num_quantifiers);
  fprintf(stderr, " patterns                : %"PRIu32"\n", stat->num_patterns);
  fprintf(stderr, " instances               : %"PRIu32"\n", stat->num_instances);
}


/*
 * Simplex statistics
 */
static void show_simplex_stats(simplex_stats_t *stat) {
  fprintf(stderr, "Simplex\n");
  fprintf(stderr, " init. variables         : %"PRIu32"\n", stat->num_init_vars);
  fprintf(stderr, " init. rows              : %"PRIu32"\n", stat->num_init_rows);
  fprintf(stderr, " init. atoms             : %"PRIu32"\n", stat->num_atoms);
  fprintf(stderr, " end atoms               : %"PRIu32"\n", stat->num_end_atoms);
  fprintf(stderr, " elim. candidates        : %"PRIu32"\n", stat->num_elim_candidates);
  fprintf(stderr, " elim. rows              : %"PRIu32"\n", stat->num_elim_rows);
  fprintf(stderr, " fixed vars after simpl. : %"PRIu32"\n", stat->num_simpl_fvars);
  fprintf(stderr, " rows after simpl.       : %"PRIu32"\n", stat->num_simpl_rows);
  fprintf(stderr, " fixed vars              : %"PRIu32"\n", stat->num_fixed_vars);
  fprintf(stderr, " rows in init. tableau   : %"PRIu32"\n", stat->num_rows);
  fprintf(stderr, " rows in final tableau   : %"PRIu32"\n", stat->num_end_rows);
  fprintf(stderr, " calls to make_feasible  : %"PRIu32"\n", stat->num_make_feasible);
  fprintf(stderr, " pivots                  : %"PRIu32"\n", stat->num_pivots);
  fprintf(stderr, " bland-rule activations  : %"PRIu32"\n", stat->num_blands);
  fprintf(stderr, " simple lemmas           : %"PRIu32"\n", stat->num_binary_lemmas);
  fprintf(stderr, " prop. to core           : %"PRIu32"\n", stat->num_props);
  fprintf(stderr, " derived bounds          : %"PRIu32"\n", stat->num_bound_props);
  fprintf(stderr, " productive propagations : %"PRIu32"\n", stat->num_prop_expl);
  fprintf(stderr, " conflicts               : %"PRIu32"\n", stat->num_conflicts);
  fprintf(stderr, " interface lemmas        : %"PRIu32"\n", stat->num_interface_lemmas);
  fprintf(stderr, " reduced inter. lemmas   : %"PRIu32"\n", stat->num_reduced_inter_lemmas);
  fprintf(stderr, " trichotomy lemmas       : %"PRIu32"\n", stat->num_tricho_lemmas);
  fprintf(stderr, " reduced tricho. lemmas  : %"PRIu32"\n", stat->num_reduced_tricho);
  if (stat->num_make_intfeasible > 0 || stat->num_dioph_checks > 0) {
    fprintf(stderr, "Integer arithmetic\n");
    fprintf(stderr, " make integer feasible   : %"PRIu32"\n", stat->num_make_intfeasible);
    fprintf(stderr, " branch atoms            : %"PRIu32"\n", stat->num_branch_atoms);
    fprintf(stderr, " Gomory cuts             : %"PRIu32"\n", stat->num_gomory_cuts);
    fprintf(stderr, "bound strengthening\n");
    fprintf(stderr, " conflicts               : %"PRIu32"\n", stat->num_bound_conflicts);
    fprintf(stderr, " recheck conflicts       : %"PRIu32"\n", stat->num_bound_recheck_conflicts);
    fprintf(stderr, "integrality tests\n");
    fprintf(stderr, " conflicts               : %"PRIu32"\n", stat->num_itest_conflicts);
    fprintf(stderr, " bound conflicts         : %"PRIu32"\n", stat->num_itest_bound_conflicts);
    fprintf(stderr, " recheck conflicts       : %"PRIu32"\n", stat->num_itest_recheck_conflicts);
    fprintf(stderr, "diohpantine solver\n");
    fprintf(stderr, " gcd conflicts           : %"PRIu32"\n", stat->num_dioph_gcd_conflicts);
    fprintf(stderr, " dioph checks            : %"PRIu32"\n", stat->num_dioph_checks);
    fprintf(stderr, " dioph conflicts         : %"PRIu32"\n", stat->num_dioph_conflicts);
    fprintf(stderr, " bound conflicts         : %"PRIu32"\n", stat->num_dioph_bound_conflicts);
    fprintf(stderr, " recheck conflicts       : %"PRIu32"\n", stat->num_dioph_recheck_conflicts);
  }
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
  egraph_t *egraph;
  simplex_solver_t *simplex;
  fun_solver_t *fsolver;
  quant_solver_t *qsolver;
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

    egraph = context.egraph;
    if (egraph != NULL) {
      show_egraph_stats(&egraph->stats);
      fprintf(stderr, " egraph terms            : %"PRIu32"\n", egraph->terms.nterms);
      fprintf(stderr, " egraph eq_quota         : %"PRIu32"\n", egraph->aux_eq_quota);
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
    printf("Internalization error: %s\n\n", code2error[-code]);
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
  if (context_exists) {
    print_results();
  }
  write_signum(signum);
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
 * PROVISIONAL: FOR TESTING OF IMPLICANT CONSTRUCTION
 */
static void show_implicant(FILE *f, model_t *mdl, smt_benchmark_t *bench) {
  term_vector_t v;
  int32_t code;

  yices_init_term_vector(&v);
  code = yices_implicant_for_formulas(mdl, bench->nformulas, bench->formulas, &v);
  if (code < 0) {
    fprintf(f, "\n*** GET IMPLICANT FAILED ***\n");
    yices_print_error(f);
    fflush(f);
  } else {
    fprintf(f, "\nIMPLICANT:\n");
    yices_pp_term_array(f, v.size, v.data, 120, UINT32_MAX, 0, 0);
    fflush(f);
  }

  yices_delete_term_vector(&v);
}


/*
 * MAIN SOLVER FUNCTION
 * - parse input file (assumed to be in SMT-LIB format)
 * - solve benchmark
 * - return an exit code (defined in yices_exit_codes.h)
 */
static int process_benchmark(void) {
  int32_t code;
  context_arch_t arch;
  bool need_icheck;   // true if simplex needs integer check
  bool qflag;         // true if quantifier support is needed
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

    // HACK: fix incorrect logic labels (for QF_UFIDL)
    if (logic == QF_UFIDL && !bench.has_uf) {
      fprintf(stderr, "Warning: logic should be QF_IDL\n");
      logic = QF_IDL;
    }

    code = arch_for_logic(logic);
    if (code < 0) {
      print_internalization_code(LOGIC_NOT_SUPPORTED);
      code = YICES_EXIT_ERROR;
      goto cleanup_benchmark;
    }

    switch (logic) {
    case QF_IDL:
      arch = CTX_ARCH_AUTO_IDL;
      need_icheck = false;
      qflag = false;
      break;

    case QF_RDL:
      arch = CTX_ARCH_AUTO_RDL;
      need_icheck = false;
      qflag = false;
      break;

    default:
      arch = (context_arch_t) code;
      need_icheck = iflag_for_logic(logic);
      qflag = qflag_for_logic(logic);
      break;
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
  init_params_to_defaults(&params);
  init_context(&context, __yices_globals.terms, logic, CTX_MODE_ONECHECK, arch, qflag);

#if COMMAND_LINE_OPTIONS
  if (verbose) {
    init_trace(&tracer);
    set_trace_vlevel(&tracer, 2);
    context_set_trace(&context, &tracer);
  }
#endif

  context_exists = true;
  switch (arch) {
  case CTX_ARCH_EG:
    // QF_UF options: --var-elim --cache-tclauses --learn-eq --dyn-bool-ack
    //    enable_variable_elimination(&context); // this helps if symmetry breaking is used
    enable_eq_abstraction(&context);
    enable_symmetry_breaking(&context);
    params.use_bool_dyn_ack = true;
    params.use_dyn_ack = true;
    //    params.max_ackermann = 100;
    params.cache_tclauses = true;
    params.tclause_size = 12;
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
    // QF_BV options: --var-elim --fast-restarts --randomness=0 --bvarith-elim
    //    enable_diseq_and_or_flattening(&context);  flatten makes things worse
    enable_variable_elimination(&context);
    enable_bvarith_elimination(&context);
    params.fast_restart = true;
    params.c_factor = 1.1;
    params.d_factor = 1.1;
    params.randomness = 0.0;
    // EXPERIMENT: faster restarts
    params.c_factor = 1.05;
    params.d_factor = 1.05;
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
    params.adjust_simplex_model = true;
    params.cache_tclauses = true;
    params.tclause_size = 8;
    if (logic == QF_UFLIA || logic == QF_UFLIRA || logic == QF_AUFLIA || logic == QF_ALIA) {
      params.branching = BRANCHING_NEGATIVE;
      params.max_interface_eqs = 15;
    } else {
      params.branching = BRANCHING_THEORY;
      params.max_interface_eqs = 30;
    }
    if (need_icheck) {
      enable_splx_periodic_icheck(&context);
    }
    if (logic == QF_UFLIA || logic == QF_UFLIRA) {
      params.use_optimistic_fcheck = false;
    }
    enable_splx_eqprop(&context);
    break;

  case CTX_ARCH_EGBV:         // egraph+bitvector solver
  case CTX_ARCH_EGFUNBV:      // egraph+fun+bitvector
    // QF_BV options: --var-elim --fast-restarts --randomness=0 --bvarith-elim
    enable_diseq_and_or_flattening(&context);
    enable_variable_elimination(&context);
    enable_bvarith_elimination(&context);
    params.fast_restart = true;
    params.c_factor = 1.1;
    params.d_factor = 1.1;
    params.randomness = 0.0;
    params.max_interface_eqs = 15;
    // TESTING: 2012/09/13
    params.max_update_conflicts = 50;
    break;

  case CTX_ARCH_AUTO_IDL:
    // nothing required
    break;

  case CTX_ARCH_AUTO_RDL:
    // preprocessing option: --flatten is used by both FW and SPLX
    enable_diseq_and_or_flattening(&context);
    enable_variable_elimination(&context);
    enable_arith_elimination(&context);
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
    code = YICES_EXIT_ERROR;
    goto cleanup_context;
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
        // test for version 1826
        params.cache_tclauses = true;
        params.tclause_size = 20;
        params.use_simplex_prop = true;
      }
      break;

    default:
      break;
    }

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
	show_implicant(stdout, model, &bench);
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

