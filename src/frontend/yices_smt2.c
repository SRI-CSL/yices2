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
 * Yices solver: input in the SMT-LIB 2.0 language
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

#if defined(MINGW)
/*
 * We call isatty(STDIN_FILENO) to check whether stdin is a terminal.
 *
 * On Windows/MINGW, isatty is called _isatty. The macro STDIN_FILENO
 * appears to be defined in mingw/include/stdio.h. Not clear whether
 * it exists in Windows?  There is a function isatty declared in io.h,
 * but it is deprecated.
 *
 * NOTE: the windows function _isatty doesn't have the same behavior
 * as isatty on Unix. It returns a non-zero value if the file
 * descriptor is associated with a character device (which is true of
 * terminals but of other files too).
 */
#include <io.h>
#ifndef STDIN_FILENO
#define STDIN_FILENO (_fileno(stdin))
#endif
#define isatty _isatty

#else
// Should work on all Unix variants
#include <unistd.h>
#endif

#include "frontend/common/parameters.h"
#include "frontend/smt2/smt2_commands.h"
#include "frontend/smt2/smt2_lexer.h"
#include "frontend/smt2/smt2_parser.h"
#include "frontend/smt2/smt2_term_stack.h"
#include "io/simple_printf.h"
#include "solvers/cdcl/delegate.h"
#include "utils/command_line.h"
#include "solvers/quant/quant_parameters.h"

#include "yices.h"
#include "yices_exit_codes.h"

/*
 * yices_rev is set up at compile time in yices_version.c
 */
extern const char * const yices_rev;

/*
 * Global objects:
 * - lexer/parser/stack: for processing the SMT2 input
 * - incremental: if this flag is true, support for push/pop
 *   and multiple check_sat is enabled. Otherwise, the solver
 *   is configured to handle a set of declarations/assertions
 *   followed by a single call to (check_sat).
 * - interactive: set option :print-success to true.
 *   and  print a prompt before parsing commands if stdin is a terminal.
 * - timeout: command-line option
 *
 * - filename = name of the input file (NULL means read stdin)
 */
static lexer_t lexer;
static parser_t parser;
static tstack_t stack;

static bool incremental;
static bool interactive;
static bool smt2_model_format;
static bool bvdecimal;
static bool show_stats;
static int32_t verbosity;
static uint32_t timeout;
static char *filename;
static char *delegate;
static char *dimacsfile;

// mcsat options
static bool mcsat;
static bool mcsat_nra_mgcd;
static bool mcsat_nra_nlsat;
static bool mcsat_nra_bound;
static int32_t mcsat_nra_bound_min;
static int32_t mcsat_nra_bound_max;
static int32_t mcsat_bv_var_size;

static pvector_t trace_tags;

// ef solver options
static bool ef_en_ematch;
static int32_t ef_mbqi_max_iter;
static int32_t ef_mbqi_max_lemma_per_round;

static int32_t ef_ematch_inst_per_round;
static int32_t ef_ematch_inst_per_search;
static int32_t ef_ematch_inst_total;
static int32_t ef_ematch_rounds_per_search;
static int32_t ef_ematch_search_total;

static int32_t ef_ematch_trial_fdepth;
static int32_t ef_ematch_trial_vdepth;
static int32_t ef_ematch_trial_fapps;
static int32_t ef_ematch_trial_matches;

static int32_t ef_ematch_cnstr_epsilon;
static double ef_ematch_cnstr_alpha;
static int32_t ef_ematch_term_epsilon;
static double ef_ematch_term_alpha;

static int32_t ef_ematch_cnstr_mode;
static int32_t ef_ematch_term_mode;


/****************************
 *  COMMAND-LINE ARGUMENTS  *
 ***************************/

typedef enum optid {
  show_version_opt,        // print version and exit
  show_help_opt,           // print help and exit
  show_mcsat_help_opt,     // print help about the mcsat options
  show_stats_opt,          // show statistics after all commands are processed
  verbosity_opt,           // set verbosity on the command line
  incremental_opt,         // enable incremental mode
  interactive_opt,         // enable interactive mode
  smt2format_opt,          // use SMT-LIB2 format for models
  bvdecimal_opt,           // use (_ bv<xxx> n) for bit-vector constants
  timeout_opt,             // give a timeout
  delegate_opt,            // use an external sat solver
  dimacs_opt,              // bitblast then export to DIMACS
  mcsat_opt,               // enable mcsat
  mcsat_nra_mgcd_opt,      // use the mgcd instead psc in projection
  mcsat_nra_nlsat_opt,     // use the nlsat projection instead of brown single-cell
  mcsat_nra_bound_opt,     // search by increasing bound
  mcsat_nra_bound_min_opt, // set initial bound
  mcsat_nra_bound_max_opt, // set maximal bound
  mcsat_bv_var_size_opt,   // set size of bitvector variables
  trace_opt,               // enable a trace tag
  show_ef_help_opt,        // print help about the ef options
  ematch_en_opt,                    // enable ematching
  mbqi_max_iter_opt,                // set max mbqi iterations
  mbqi_lemmas_per_round_opt,        // set max mbqi lemmas per round
  ematch_inst_per_round_opt,        // set max ematch instances per round
  ematch_inst_per_search_opt,       // set max ematch instances per search
  ematch_inst_total_opt,            // set max ematch instances
  ematch_rounds_per_search_opt,     // set max ematch rounds per search
  ematch_search_total_opt,          // set max ematch rounds per search
  ematch_trial_fdepth_opt,          // set max function depth in each ematch trial
  ematch_trial_vdepth_opt,          // set max variable depth in each ematch trial
  ematch_trial_fapps_opt,           // set max function apps in each ematch trial
  ematch_trial_matches_opt,         // set max matches in each ematch trial
  ematch_cnstr_epsilon_opt,         // set ematch constraint learner epsilon
  ematch_cnstr_alpha_opt,           // set ematch constraint learner learning rate
  ematch_term_epsilon_opt,          // set ematch term learner epsilon
  ematch_term_alpha_opt,            // set ematch term learner learning rate
  ematch_cnstr_mode_opt,            // set cnstr mode in ematching
  ematch_term_mode_opt,             // set term mode in ematching
} optid_t;

#define NUM_OPTIONS (ematch_term_mode_opt+1)

/*
 * Option descriptors
 */
static option_desc_t options[NUM_OPTIONS] = {
  { "version", 'V', FLAG_OPTION, show_version_opt },
  { "help", 'h', FLAG_OPTION, show_help_opt },
  { "mcsat-help", '0', FLAG_OPTION, show_mcsat_help_opt },
  { "stats", 's', FLAG_OPTION, show_stats_opt },
  { "verbosity", 'v', MANDATORY_INT, verbosity_opt },
  { "timeout", 't', MANDATORY_INT, timeout_opt },
  { "incremental", '\0', FLAG_OPTION, incremental_opt },
  { "interactive", '\0', FLAG_OPTION, interactive_opt },
  { "smt2-model-format", '\0', FLAG_OPTION, smt2format_opt },
  { "bvconst-in-decimal", '\0', FLAG_OPTION, bvdecimal_opt },
  { "delegate", '\0', MANDATORY_STRING, delegate_opt },
  { "dimacs", '\0', MANDATORY_STRING, dimacs_opt },
  { "mcsat", '\0', FLAG_OPTION, mcsat_opt },
  { "mcsat-nra-mgcd", '\0', FLAG_OPTION, mcsat_nra_mgcd_opt },
  { "mcsat-nra-nlsat", '\0', FLAG_OPTION, mcsat_nra_nlsat_opt },
  { "mcsat-nra-bound", '\0', FLAG_OPTION, mcsat_nra_bound_opt },
  { "mcsat-nra-bound-min", '\0', MANDATORY_INT, mcsat_nra_bound_min_opt },
  { "mcsat-nra-bound-max", '\0', MANDATORY_INT, mcsat_nra_bound_max_opt },
  { "mcsat-bv-var-size", '\0', MANDATORY_INT, mcsat_bv_var_size_opt },
  { "trace", 't', MANDATORY_STRING, trace_opt },
  { "ef-help", '0', FLAG_OPTION, show_ef_help_opt },
  { "ematch", '\0', FLAG_OPTION, ematch_en_opt },
  { "mbqi-max-iter", '\0', MANDATORY_INT, mbqi_max_iter_opt },
  { "mbqi-lemmas-per-round", '\0', MANDATORY_INT, mbqi_lemmas_per_round_opt },
  { "ematch-inst-per-round", '\0', MANDATORY_INT, ematch_inst_per_round_opt },
  { "ematch-inst-per-search", '\0', MANDATORY_INT, ematch_inst_per_search_opt },
  { "ematch-inst-total", '\0', MANDATORY_INT, ematch_inst_total_opt },
  { "ematch-rounds-per-search", '\0', MANDATORY_INT, ematch_rounds_per_search_opt },
  { "ematch-search-total", '\0', MANDATORY_INT, ematch_search_total_opt },
  { "ematch-trial-fdepth", '\0', MANDATORY_INT, ematch_trial_fdepth_opt },
  { "ematch-trial-vdepth", '\0', MANDATORY_INT, ematch_trial_vdepth_opt },
  { "ematch-trial-fapps", '\0', MANDATORY_INT, ematch_trial_fapps_opt },
  { "ematch-trial-matches", '\0', MANDATORY_INT, ematch_trial_matches_opt },
  { "ematch-cnstr-epsilon", '\0', MANDATORY_INT, ematch_cnstr_epsilon_opt },
  { "ematch-cnstr-alpha", '\0', MANDATORY_FLOAT, ematch_cnstr_alpha_opt },
  { "ematch-term-epsilon", '\0', MANDATORY_INT, ematch_term_epsilon_opt },
  { "ematch-term-alpha", '\0', MANDATORY_FLOAT, ematch_term_alpha_opt },
  { "ematch-cnstr-mode", '\0', MANDATORY_STRING, ematch_cnstr_mode_opt },
  { "ematch-term-mode", '\0', MANDATORY_STRING, ematch_term_mode_opt },
};


/*
 * Processing of command-line
 */
static void print_version(void) {
  printf("Yices %s\n"
   "Copyright SRI International.\n"
         "Linked with GMP %s\n"
   "Copyright Free Software Foundation, Inc.\n"
         "Build date: %s\n"
         "Platform: %s (%s)\n"
         "Revision: %s\n",
         yices_version, gmp_version,
         yices_build_date, yices_build_arch, yices_build_mode, yices_rev);
  fflush(stdout);
}

static void print_help(const char *progname) {
  printf("Usage: %s [option] filename\n"
         "    or %s [option]\n\n", progname, progname);
  printf("Option summary:\n"
         "    --version, -V             Show version and exit\n"
         "    --help, -h                Print this message and exit\n"
         "    --verbosity=<level>       Set verbosity level (default = 0)\n"
         "             -v <level>\n"
         "    --timeout=<timeout>       Set a timeout in seconds (default = no timeout)\n"
         "           -t <timeout>\n"
         "    --stats, -s               Print statistics once all commands have been processed\n"
         "    --incremental             Enable support for push/pop\n"
         "    --interactive             Run in interactive mode (ignored if a filename is given)\n"
         "    --smt2-model-format       Display models in the SMT-LIB 2 format (default = false)\n"
         "    --bvconst-in-decimal      Display bit-vector constants as decimal numbers (default = false)\n"
         "    --delegate=<satsolver>    Use an external SAT solver (can be cadical, cryptominisat, kissat, or y2sat)\n"
         "    --dimacs=<filename>       Bitblast and export to a file (in DIMACS format)\n"
         "    --mcsat                   Use the MCSat solver\n"
         "    --mcsat-help              Show the MCSat options\n"
         "    --ef-help                 Show the EF options\n"
         "\n"
         "For bug reports and other information, please see http://yices.csl.sri.com/\n");
  fflush(stdout);
}

static void print_mcsat_help(const char *progname) {
  printf("Usage: %s [option] filename\n"
         "    or %s [option]\n\n", progname, progname);
  printf("MCSat options:\n"
         "    --mcsat-nra-mgcd          Use model-based GCD instead of PSC for projection\n"
         "    --mcsat-nra-nlsat         Use NLSAT projection instead of Brown's single-cell construction\n"
         "    --mcsat-nra-bound         Search by increasing the bound on variable magnitude\n"
         "    --mcsat-nra-bound-min=<B> Set initial lower bound\n"
         "    --mcsat-nra-bound-max=<B> Set maximal bound for search\n"
         "    --mcsat-bv-var-size=<B>   Set size of bit-vector variables in MCSAT search"
         "\n");
  fflush(stdout);
}

static void print_ef_help(const char *progname) {
  printf("Usage: %s [option] filename\n"
         "    or %s [option]\n\n", progname, progname);
  printf("EF options:\n");
  printf("    --ematch                        Toggle enabling/disabling ematching (default: %s)\n", (DEF_EMATCH_EN?"true":"false"));
  printf("    --ematch-cnstr-mode=<M>         Set the ematching constraint mode (can be epsilongreedy, random, all) (default: epsilongreedy)\n");
  printf("    --ematch-term-mode=<M>          Set the ematching term mode (can be epsilongreedy, random, all) (default: epsilongreedy)\n");
  printf("\n");
  printf("  Learner options\n");
  printf("    --ematch-cnstr-epsilon=<M>      Set the minimum epsilon for ematch constraint learner (between 0-%d) (default: %d)\n", CNSTR_RL_EPSILON_MAX, CNSTR_RL_EPSILON_MIN);
  printf("    --ematch-cnstr-alpha=<M>        Set the learning rate for ematch constraint learner (between 0-1) (default: %.2f)\n", CNSTR_RL_ALPHA_DEFAULT);
  printf("    --ematch-term-epsilon=<M>       Set the minimum epsilon for ematch term learner (between 0-%d) (default: %d)\n", TERM_RL_EPSILON_MAX, TERM_RL_EPSILON_MIN);
  printf("    --ematch-term-alpha=<M>         Set the learning rate for ematch term learner (between 0-1) (default: %.2f)\n", TERM_RL_ALPHA_DEFAULT);
  printf("\n");
  printf("  Fine-grained options\n");
  printf("   (mbqi)\n");
  printf("    --mbqi-max-iter=<M>             Set the max number of mbqi iterations (default: %d)\n", DEF_MBQI_MAX_ITERS);
  printf("    --mbqi-lemmas-per-round=<M>     Set the max number of lemmas per mbqi round (default: %d)\n", DEF_MBQI_MAX_LEMMAS_PER_ROUND);
  printf("   (ematch)\n");
  printf("    --ematch-inst-per-round=<M>     Set the max number of instances per ematch round (default: %d)\n", DEFAULT_MAX_INSTANCES_PER_ROUND);
  printf("    --ematch-inst-per-search=<M>    Set the max number of instances per ematch seach (default: %d)\n", DEFAULT_MAX_INSTANCES_PER_SEARCH);
  printf("    --ematch-inst-total=<M>         Set the max number of ematch instances total (default: %d)\n", DEFAULT_MAX_INSTANCES);
  printf("    --ematch-rounds-per-search=<M>  Set the max number of rounds per ematch seach (default: %d)\n", DEFAULT_MAX_ROUNDS_PER_SEARCH);
  printf("    --ematch-search-total=<M>       Set the max number of ematch searches total (default: %d)\n", DEFAULT_MAX_SEARCH);
  printf("   (ematch trial)\n");
  printf("    --ematch-trial-matches=<M>      Set the max matches allowed in each ematch trial (default: %d)\n", DEF_MAX_MATCHES);
  printf("    --ematch-trial-fapps=<M>        Set the max function apps considered in each ematch trial (default: %d)\n", DEF_MAX_FAPPS);
  printf("    --ematch-trial-fdepth=<M>       Set the max function depth allowed in each fapp considered during ematch trial (default: %d)\n", DEF_MAX_FDEPTH);
  printf("    --ematch-trial-vdepth=<M>       Set the max function depth allowed in each match considered during ematch trial (default: %d)\n", DEF_MAX_VDEPTH);
  fflush(stdout);
}

/*
 * Message for unrecognized options or other errors on the command line.
 */
static void print_usage(const char *progname) {
  fprintf(stderr, "Usage: %s [options] filename\n", progname);
  fprintf(stderr, "Try '%s --help' for more information\n", progname);
}

/*
 * Utility: make a copy of string s
 * - we limit the copy to MAX_STRING_COPY_LEN characters
 * - return NULL if that fails
 *
 * 16000 bytes should be more than enough in practice for a filename.
 * For example on Linux/ext4 filesystem: PATH_MAX=4096 bytes.
 * We produce an error if somebody tries a name longer than that.
 */
#define MAX_STRING_COPY_LEN 16000

static char *copy_string(const char *s) {
  size_t len;
  char *c;

  c = NULL;
  len = strlen(s);
  if (len <= MAX_STRING_COPY_LEN) {
    c = (char *) safe_malloc(len + 1);
    strcpy(c, s);
  }
  return c;
}


/*
 * Parse the command line and process options
 */
static void parse_command_line(int argc, char *argv[]) {
  cmdline_parser_t parser;
  cmdline_elem_t elem;
  optid_t k;
  int32_t v;
  int code;
  bool unknown_delegate;

  filename = NULL;
  incremental = false;
  interactive = false;
  smt2_model_format = false;
  bvdecimal = false;
  show_stats = false;
  verbosity = 0;
  timeout = 0;
  delegate = NULL;
  dimacsfile = NULL;

  mcsat = false;
  mcsat_nra_mgcd = false;
  mcsat_nra_nlsat = false;
  mcsat_nra_bound = false;
  mcsat_nra_bound_min = -1;
  mcsat_nra_bound_max = -1;
  mcsat_bv_var_size = -1;

  init_pvector(&trace_tags, 5);

  ef_en_ematch = DEF_EMATCH_EN;
  ef_mbqi_max_iter = -1;
  ef_mbqi_max_lemma_per_round = -1;
  ef_ematch_inst_per_round = -1;
  ef_ematch_inst_per_search = -1;
  ef_ematch_inst_total = -1;
  ef_ematch_rounds_per_search = -1;
  ef_ematch_search_total = -1;
  ef_ematch_trial_fdepth = -1;
  ef_ematch_trial_vdepth = -1;
  ef_ematch_trial_fapps = -1;
  ef_ematch_trial_matches = -1;
  ef_ematch_cnstr_epsilon = -1;
  ef_ematch_cnstr_alpha = -1;
  ef_ematch_term_epsilon = -1;
  ef_ematch_term_alpha = -1;
  ef_ematch_cnstr_mode = -1;
  ef_ematch_term_mode = -1;

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
        goto bad_usage;
      }
      break;

    case cmdline_option:
      k = elem.key;
      switch (k) {
      case show_version_opt:
        print_version();
        code = YICES_EXIT_SUCCESS;
        goto exit;

      case show_help_opt:
        print_help(parser.command_name);
        code = YICES_EXIT_SUCCESS;
        goto exit;

      case show_mcsat_help_opt:
        print_mcsat_help(parser.command_name);
        code = YICES_EXIT_SUCCESS;
        goto exit;

      case show_stats_opt:
        show_stats = true;
        break;

      case verbosity_opt:
        v = elem.i_value;
        if (v < 0) {
          fprintf(stderr, "%s: the verbosity level must be non-negative\n", parser.command_name);
          goto bad_usage;
        }
        verbosity = v;
        break;

      case timeout_opt:
        v = elem.i_value;
        if (v < 0) {
          fprintf(stderr, "%s: the timeout must be non-negative\n", parser.command_name);
          goto bad_usage;
        }
        timeout = v;
        break;

      case incremental_opt:
        incremental = true;
        break;

      case interactive_opt:
        interactive = true;
        break;

      case delegate_opt:
        if (delegate == NULL) {
          unknown_delegate = true;
          if (supported_delegate(elem.s_value, &unknown_delegate)) {
          delegate = copy_string(elem.s_value);
        } else if (unknown_delegate) {
          fprintf(stderr, "%s: unknown delegate: %s (choices are 'y2sat' or 'cadical' or 'kissat' or 'cryptominisat')\n",
          parser.command_name, elem.s_value);
          goto bad_usage;
        } else {
          fprintf(stderr, "%s: unsupported delegate: this version was not compiled to support %s\n", parser.command_name, elem.s_value);
          goto bad_usage;
        }
      } else if (strcmp(elem.s_value, delegate) != 0) {
        fprintf(stderr, "%s: can't have several delegates\n", parser.command_name);
        goto bad_usage;
      }
      break;

      case dimacs_opt:
        if (dimacsfile == NULL) {
          dimacsfile = copy_string(elem.s_value);
          if (dimacsfile == NULL) {
            // copy_string failed
            fprintf(stderr, "%s: file-name %s is too long\n", parser.command_name, elem.s_value);
            code = YICES_EXIT_USAGE;
            goto exit;
         }
        } else {
          fprintf(stderr, "%s: can't give more than one dimacs file\n", parser.command_name);
          goto bad_usage;
        }
        break;

      case smt2format_opt:
        smt2_model_format = true;
        break;

      case bvdecimal_opt:
        bvdecimal = true;
        break;

      case mcsat_opt:
        if (! yices_has_mcsat()) goto no_mcsat;
        mcsat  = true;
        break;

      case mcsat_nra_mgcd_opt:
        if (! yices_has_mcsat()) goto no_mcsat;
        mcsat_nra_mgcd = true;
        break;

      case mcsat_nra_nlsat_opt:
        if (! yices_has_mcsat()) goto no_mcsat;
        mcsat_nra_nlsat = true;
        break;

      case mcsat_nra_bound_opt:
        if (! yices_has_mcsat()) goto no_mcsat;
        mcsat_nra_bound = true;
        break;

      case mcsat_nra_bound_min_opt:
        if (! yices_has_mcsat()) goto no_mcsat;
        if (! validate_integer_option(&parser, &elem, 0, INT32_MAX)) goto bad_usage;
        mcsat_nra_bound_min = elem.i_value;
        break;

      case mcsat_nra_bound_max_opt:
        if (! yices_has_mcsat()) goto no_mcsat;
        if (! validate_integer_option(&parser, &elem, 0, INT32_MAX)) goto bad_usage;
        mcsat_nra_bound_max = elem.i_value;
        break;

      case mcsat_bv_var_size_opt:
        if (! yices_has_mcsat()) goto no_mcsat;
        if (! validate_integer_option(&parser, &elem, 0, INT32_MAX)) goto bad_usage;
        mcsat_bv_var_size = elem.i_value;
        break;

      case show_ef_help_opt:
        print_ef_help(parser.command_name);
        code = YICES_EXIT_SUCCESS;
        goto exit;

      case ematch_en_opt:
        ef_en_ematch = !ef_en_ematch;
        break;

      case mbqi_max_iter_opt:
        if (! validate_integer_option(&parser, &elem, 0, INT32_MAX)) goto bad_usage;
        ef_mbqi_max_iter = elem.i_value;
        break;

      case mbqi_lemmas_per_round_opt:
        if (! validate_integer_option(&parser, &elem, 0, INT32_MAX)) goto bad_usage;
        ef_mbqi_max_lemma_per_round = elem.i_value;
        break;

      case ematch_inst_per_round_opt:
        if (! validate_integer_option(&parser, &elem, 0, INT32_MAX)) goto bad_usage;
        ef_ematch_inst_per_round = elem.i_value;
        break;

      case ematch_inst_per_search_opt:
        if (! validate_integer_option(&parser, &elem, 0, INT32_MAX)) goto bad_usage;
        ef_ematch_inst_per_search = elem.i_value;
        break;

      case ematch_inst_total_opt:
        if (! validate_integer_option(&parser, &elem, 0, INT32_MAX)) goto bad_usage;
        ef_ematch_inst_total = elem.i_value;
        break;

      case ematch_rounds_per_search_opt:
        if (! validate_integer_option(&parser, &elem, 0, INT32_MAX)) goto bad_usage;
        ef_ematch_rounds_per_search = elem.i_value;
        break;

      case ematch_search_total_opt:
        if (! validate_integer_option(&parser, &elem, 0, INT32_MAX)) goto bad_usage;
        ef_ematch_search_total = elem.i_value;
        break;

      case ematch_trial_fdepth_opt:
        if (! validate_integer_option(&parser, &elem, 0, INT32_MAX)) goto bad_usage;
        ef_ematch_trial_fdepth = elem.i_value;
        break;

      case ematch_trial_vdepth_opt:
        if (! validate_integer_option(&parser, &elem, 0, INT32_MAX)) goto bad_usage;
        ef_ematch_trial_vdepth = elem.i_value;
        break;

      case ematch_trial_fapps_opt:
        if (! validate_integer_option(&parser, &elem, 0, INT32_MAX)) goto bad_usage;
        ef_ematch_trial_fapps = elem.i_value;
        break;

      case ematch_trial_matches_opt:
        if (! validate_integer_option(&parser, &elem, 0, INT32_MAX)) goto bad_usage;
        ef_ematch_trial_matches = elem.i_value;
        break;

      case ematch_cnstr_epsilon_opt:
        if (! validate_integer_option(&parser, &elem, 0, CNSTR_RL_EPSILON_MAX)) goto bad_usage;
        ef_ematch_cnstr_epsilon = elem.i_value;
        break;

      case ematch_cnstr_alpha_opt:
        if (! validate_double_option(&parser, &elem, 0.0, false, 1.0, false)) goto bad_usage;
        ef_ematch_cnstr_alpha = elem.d_value;
        break;

      case ematch_term_epsilon_opt:
        if (! validate_integer_option(&parser, &elem, 0, TERM_RL_EPSILON_MAX)) goto bad_usage;
        ef_ematch_term_epsilon = elem.i_value;
        break;

      case ematch_term_alpha_opt:
        if (! validate_double_option(&parser, &elem, 0.0, false, 1.0, false)) goto bad_usage;
        ef_ematch_term_alpha = elem.d_value;
        break;

      case ematch_cnstr_mode_opt:
        ef_ematch_cnstr_mode = supported_ematch_mode(elem.s_value);
        if (ef_ematch_cnstr_mode < 0) {
          fprintf(stderr, "%s: unsupported ematching constraint mode: %s\n", parser.command_name, elem.s_value);
          goto bad_usage;
        }
        break;

      case ematch_term_mode_opt:
        ef_ematch_term_mode = supported_ematch_mode(elem.s_value);
        if (ef_ematch_term_mode < 0) {
          fprintf(stderr, "%s: unsupported ematching term mode: %s\n", parser.command_name, elem.s_value);
          goto bad_usage;
        }
        break;

      case trace_opt:
        pvector_push(&trace_tags, elem.s_value);
        break;
      }
      break;

    case cmdline_error:
      cmdline_print_error(&parser, &elem);
      fprintf(stderr, "Try %s --help for more information\n", parser.command_name);
      code = YICES_EXIT_USAGE;
      goto exit;
    }
  }

 done:
  if (incremental && delegate != NULL) {
    fprintf(stderr, "%s: delegate %s does not support incremental mode\n", parser.command_name, delegate);
    code = YICES_EXIT_USAGE;
    goto exit;
  }

  if (incremental && dimacsfile != NULL) {
    fprintf(stderr, "%s: export to DIMACS is not supported in incremental mode\n", parser.command_name);
    code = YICES_EXIT_USAGE;
    goto exit;
  }

  // force interactive to false if there's a filename
  if (filename != NULL) {
    interactive = false;
  }
  return;

  /*
   * Error conditions
   */
 no_mcsat:
  fprintf(stderr, "mcsat is not supported: %s was not compiled with mcsat support\n", parser.command_name);
  code = YICES_EXIT_USAGE;
  goto exit;

 bad_usage:
  print_usage(parser.command_name);
  code = YICES_EXIT_USAGE;

 exit:
  // cleanup then exit
  // code is either YICES_EXIT_SUCCESS or YICES_EXIT_USAGE.
  delete_pvector(&trace_tags);
  exit(code);
}

static void setup_mcsat(void) {
  aval_t aval_true;

  if (mcsat) {
    smt2_enable_mcsat();
  }

  aval_true = attr_vtbl_symbol(__smt2_globals.avtbl, "true");

  if (mcsat_nra_mgcd) {
    smt2_set_option(":yices-mcsat-nra-mgcd", aval_true);
  }

  if (mcsat_nra_nlsat) {
    smt2_set_option(":yices-mcsat-nra-nlsat", aval_true);
  }

  if (mcsat_nra_bound) {
    smt2_set_option(":yices-mcsat-nra-bound", aval_true);
  }

  if (mcsat_nra_bound_min >= 0) {
    aval_t aval_bound_min;
    rational_t q;
    q_init(&q);
    q_set32(&q, mcsat_nra_bound_min);
    aval_bound_min = attr_vtbl_rational(__smt2_globals.avtbl, &q);
    smt2_set_option(":yices-mcsat-nra-bound-min", aval_bound_min);
    q_clear(&q);
  }

  if (mcsat_nra_bound_max >= 0) {
    aval_t aval_bound_max;
    rational_t q;
    q_init(&q);
    q_set32(&q, mcsat_nra_bound_max);
    aval_bound_max = attr_vtbl_rational(__smt2_globals.avtbl, &q);
    smt2_set_option(":yices-mcsat-nra-bound-max", aval_bound_max);
    q_clear(&q);
  }

  if (mcsat_bv_var_size > 0) {
    aval_t aval_bv_var_size;
    rational_t q;
    q_init(&q);
    q_set32(&q, mcsat_bv_var_size);
    aval_bv_var_size = attr_vtbl_rational(__smt2_globals.avtbl, &q);
    smt2_set_option(":yices-mcsat-bv-var-size", aval_bv_var_size);
    q_clear(&q);
  }
}

static void setup_ef(void) {
  aval_t aval_true, aval_false;

  aval_true = attr_vtbl_symbol(__smt2_globals.avtbl, "true");
  aval_false = attr_vtbl_symbol(__smt2_globals.avtbl, "false");

  if (ef_en_ematch != DEF_EMATCH_EN) {
    smt2_set_option(":yices-ematch-en", (ef_en_ematch?aval_true:aval_false));
  }

  if (ef_mbqi_max_iter >= 0) {
    aval_t aval_max;
    rational_t q;
    q_init(&q);
    q_set32(&q, ef_mbqi_max_iter);
    aval_max = attr_vtbl_rational(__smt2_globals.avtbl, &q);
    smt2_set_option(":yices-ef-max-iters", aval_max);
    q_clear(&q);
  }

  if (ef_mbqi_max_lemma_per_round >= 0) {
    aval_t aval_max;
    rational_t q;
    q_init(&q);
    q_set32(&q, ef_mbqi_max_lemma_per_round);
    aval_max = attr_vtbl_rational(__smt2_globals.avtbl, &q);
    smt2_set_option(":yices-ef-max-lemmas-per-round", aval_max);
    q_clear(&q);
  }

  if (ef_ematch_inst_per_round >= 0) {
    aval_t aval_max;
    rational_t q;
    q_init(&q);
    q_set32(&q, ef_ematch_inst_per_round);
    aval_max = attr_vtbl_rational(__smt2_globals.avtbl, &q);
    smt2_set_option(":yices-ematch-inst-per-round", aval_max);
    q_clear(&q);
  }

  if (ef_ematch_inst_per_search >= 0) {
    aval_t aval_max;
    rational_t q;
    q_init(&q);
    q_set32(&q, ef_ematch_inst_per_search);
    aval_max = attr_vtbl_rational(__smt2_globals.avtbl, &q);
    smt2_set_option(":yices-ematch-inst-per-search", aval_max);
    q_clear(&q);
  }

  if (ef_ematch_inst_total >= 0) {
    aval_t aval_max;
    rational_t q;
    q_init(&q);
    q_set32(&q, ef_ematch_inst_total);
    aval_max = attr_vtbl_rational(__smt2_globals.avtbl, &q);
    smt2_set_option(":yices-ematch-inst-total", aval_max);
    q_clear(&q);
  }

  if (ef_ematch_rounds_per_search >= 0) {
    aval_t aval_max;
    rational_t q;
    q_init(&q);
    q_set32(&q, ef_ematch_rounds_per_search);
    aval_max = attr_vtbl_rational(__smt2_globals.avtbl, &q);
    smt2_set_option(":yices-ematch-rounds-per-search", aval_max);
    q_clear(&q);
  }

  if (ef_ematch_search_total >= 0) {
    aval_t aval_max;
    rational_t q;
    q_init(&q);
    q_set32(&q, ef_ematch_search_total);
    aval_max = attr_vtbl_rational(__smt2_globals.avtbl, &q);
    smt2_set_option(":yices-ematch-search-total", aval_max);
    q_clear(&q);
  }

  if (ef_ematch_trial_fdepth >= 0) {
    aval_t aval_max;
    rational_t q;
    q_init(&q);
    q_set32(&q, ef_ematch_trial_fdepth);
    aval_max = attr_vtbl_rational(__smt2_globals.avtbl, &q);
    smt2_set_option(":yices-ematch-trial-fdepth", aval_max);
    q_clear(&q);
  }

  if (ef_ematch_trial_vdepth >= 0) {
    aval_t aval_max;
    rational_t q;
    q_init(&q);
    q_set32(&q, ef_ematch_trial_vdepth);
    aval_max = attr_vtbl_rational(__smt2_globals.avtbl, &q);
    smt2_set_option(":yices-ematch-trial-vdepth", aval_max);
    q_clear(&q);
  }

  if (ef_ematch_trial_fapps >= 0) {
    aval_t aval_max;
    rational_t q;
    q_init(&q);
    q_set32(&q, ef_ematch_trial_fapps);
    aval_max = attr_vtbl_rational(__smt2_globals.avtbl, &q);
    smt2_set_option(":yices-ematch-trial-fapps", aval_max);
    q_clear(&q);
  }

  if (ef_ematch_trial_matches >= 0) {
    aval_t aval_max;
    rational_t q;
    q_init(&q);
    q_set32(&q, ef_ematch_trial_matches);
    aval_max = attr_vtbl_rational(__smt2_globals.avtbl, &q);
    smt2_set_option(":yices-ematch-trial-matches", aval_max);
    q_clear(&q);
  }

  if (ef_ematch_cnstr_epsilon >= 0) {
    aval_t aval_max;
    rational_t q;
    q_init(&q);
    q_set32(&q, ef_ematch_cnstr_epsilon);
    aval_max = attr_vtbl_rational(__smt2_globals.avtbl, &q);
    smt2_set_option(":yices-ematch-cnstr-epsilon", aval_max);
    q_clear(&q);
  }

  if (ef_ematch_cnstr_alpha >= 0) {
    aval_t aval_max;
    rational_t q;
    q_init(&q);
    // accurate upto 3 decimal places
    q_set_int32(&q, (int32_t)(ef_ematch_cnstr_alpha*1000), 1000);
    aval_max = attr_vtbl_rational(__smt2_globals.avtbl, &q);
    smt2_set_option(":yices-ematch-cnstr-alpha", aval_max);
    q_clear(&q);
  }

  if (ef_ematch_term_epsilon >= 0) {
    aval_t aval_max;
    rational_t q;
    q_init(&q);
    q_set32(&q, ef_ematch_term_epsilon);
    aval_max = attr_vtbl_rational(__smt2_globals.avtbl, &q);
    smt2_set_option(":yices-ematch-term-epsilon", aval_max);
    q_clear(&q);
  }

  if (ef_ematch_term_alpha >= 0) {
    aval_t aval_max;
    rational_t q;
    q_init(&q);
    // accurate upto 3 decimal places
    q_set_int32(&q, (int32_t)(ef_ematch_term_alpha*1000), 1000);
    aval_max = attr_vtbl_rational(__smt2_globals.avtbl, &q);
    smt2_set_option(":yices-ematch-term-alpha", aval_max);
    q_clear(&q);
  }

  if (ef_ematch_cnstr_mode >= 0) {
    aval_t aval_mode = attr_vtbl_symbol(__smt2_globals.avtbl, ematchmode2string[ef_ematch_cnstr_mode]);
    smt2_set_option(":yices-ematch-cnstr-mode", aval_mode);
  }

  if (ef_ematch_term_mode >= 0) {
    aval_t aval_mode = attr_vtbl_symbol(__smt2_globals.avtbl, ematchmode2string[ef_ematch_term_mode]);
    smt2_set_option(":yices-ematch-term-mode", aval_mode);
  }

}


/********************
 *  SIGNAL HANDLER  *
 *******************/

static const char *signum_msg = "\nInterrupted by signal ";

/*
 * Write signal number of file 2 (assumed to be stderr): we can't use
 * fprintf because it's not safe in a signal handler.
 */
static void write_signum(int signum) {
  print_buffer_t b;

  reset_print_buffer(&b);
  print_buffer_append_string(&b, signum_msg);
  print_buffer_append_int32(&b, (int32_t) signum);
  print_buffer_append_char(&b, '\n');
  (void) write_buffer(2, &b);
}

/*
 * We call exit on SIGINT/ABORT and XCPU
 * - we could try to handle SIGINT more gracefully in interactive mode
 * - this will do for now.
 */
static void default_handler(int signum) {
  if (verbosity > 0) {
    write_signum(signum);
  }
  if (show_stats) {
    smt2_show_stats();
  }
  _exit(YICES_EXIT_INTERRUPTED);
}


/*
 * Initialize the signal handlers
 */
static void init_handlers(void) {
  signal(SIGINT, default_handler);
  signal(SIGABRT, default_handler);
#ifndef MINGW
  signal(SIGXCPU, default_handler);
#endif
}


/*
 * Reset the default handlers
 */
static void reset_handlers(void) {
  signal(SIGINT, SIG_DFL);
  signal(SIGABRT, SIG_DFL);
#ifndef MINGW
  signal(SIGXCPU, SIG_DFL);
#endif
}



/**********
 *  MAIN  *
 *********/

#define HACK_FOR_UTF 0

#if HACK_FOR_UTF

/*
 * List of locales to try
 */
#define NUM_LOCALES 3

static const char *const locales[NUM_LOCALES] = {
  "C.UTF-8", "en_US.utf8", "en_US.UTF-8",
};

// HACK TO FORCE UTF8
static void force_utf8(void) {
  uint32_t i;

  for (i=0; i<NUM_LOCALES; i++) {
    if (setlocale(LC_CTYPE, locales[i]) != NULL) {
      if (verbosity > 1) {
	fprintf(stderr, "Switched to locale '%s'\n", setlocale(LC_CTYPE, NULL));
	fflush(stderr);
      }
      return;
    }
  }

  fprintf(stderr, "Failed to switch locale to UTF-8. Current locale is '%s'\n", setlocale(LC_CTYPE, NULL));
  fflush(stderr);
}

#else

static void force_utf8(void) {
  // Do nothing
}

#endif


int main(int argc, char *argv[]) {
  int32_t code;
  uint32_t i;
  bool prompt;

  prompt = false;
  parse_command_line(argc, argv);
  force_utf8();

  if (filename != NULL) {
    // read from file
    if (init_smt2_file_lexer(&lexer, filename) < 0) {
      perror(filename);
      exit(YICES_EXIT_FILE_NOT_FOUND);
    }
  } else {
    // read from stdin
    init_smt2_stdin_lexer(&lexer);
    prompt = interactive && isatty(STDIN_FILENO);
  }

  init_handlers();

  yices_init();
  init_smt2(!incremental, timeout, interactive);
  if (smt2_model_format) smt2_force_smt2_model_format();
  if (bvdecimal) smt2_force_bvdecimal_format();
  if (dimacsfile != NULL && delegate == NULL) smt2_export_to_dimacs(dimacsfile);
  if (delegate != NULL) {
    smt2_set_delegate(delegate);
    if (dimacsfile != NULL) smt2_set_dimacs_file(dimacsfile);
  }

  init_smt2_tstack(&stack);
  init_parser(&parser, &lexer, &stack);

  init_parameter_name_table();

  if (verbosity > 0) {
    smt2_set_verbosity(verbosity);
  }
  if (trace_tags.size > 0) {
    for (i = 0; i < trace_tags.size; ++ i) {
      smt2_enable_trace_tag(trace_tags.data[i]);
    }
  }

  setup_mcsat();
  setup_ef();

  while (smt2_active()) {
    if (prompt) {
      // prompt
      fputs("yices> ", stdout);
      fflush(stdout);
    }
    code = parse_smt2_command(&parser);
    if (code < 0) {
      // syntax error
      if (interactive) {
	flush_lexer(&lexer);
      } else {
	break; // exit
      }
    }
  }

  if (show_stats) {
    smt2_show_stats();
  }

  if (dimacsfile != NULL) {
    safe_free(dimacsfile);
    dimacsfile = NULL;
  }
  if (delegate != NULL) {
    safe_free(delegate);
    delegate = NULL;
  }

  delete_pvector(&trace_tags);
  delete_parser(&parser);
  close_lexer(&lexer);
  delete_tstack(&stack);
  delete_smt2();
  yices_exit();

  reset_handlers();

  return YICES_EXIT_SUCCESS;
}

