/*
 * Yices solver: using the Yices language
 * - read-eval loop
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <signal.h>
#include <inttypes.h>

#include "yices_lexer.h"
#include "yices_parser.h"
#include "term_stack.h"
#include "memsize.h"
#include "command_line.h"
#include "rationals.h"
#include "yices_exit_codes.h"

// Need PRNG_DEFAULT_SEED in show-params
#include "prng.h"

// FOR DUMP
#include "term_printer.h"
#include "type_printer.h"
#include "solver_printer.h"
#include "context_printer.h"

// TODO: should need only yices.h
#include "context.h"
#include "yices.h"
#include "yices_globals.h"
#include "yices_reval.h"



/********************
 *  GLOBAL OBJECTS  *
 *******************/

/*
 * PARSING/TERM CONSTRUCTION
 * - input_filename: name of the input file.
 *   If input_filename is NULL, we run in interactive mode and get input from stdin.
 * - lexer, parser, term_stack: to process the input commands
 * - include_depth = number of nested (include ...) commands being processed
 *
 * GLOBAL FLAGS:
 * - interactive: true if no input file is given on the command line
 * - verbose: boolean flag for now (could use a verbosity level??)
 * - done: set to true when exit is called, or if there's an error and
 *   interactive is false (i.e., we exit on the first error unless we're
 *   in the interactive mode).
 */
static bool interactive;
static bool done;
static bool verbose;
static uint32_t include_depth;
static char *input_filename;
static lexer_t lexer;
static parser_t parser;
static tstack_t stack;


/*
 * Context, model, and solver parameters
 */
static context_t *context;
static param_t parameters;


/*
 * Random seed: we keep a copy here for (show-params ...)
 */
static uint32_t the_seed;


/*
 * Search parameters and internalization options can be set individually
 * using the command (set-param <name> <value>).
 *
 * We use an integer code to identify the parameters + a table of
 * parameter names in lexicographic order. Each parameter 
 * is described in context.h
 */
typedef enum yices_param {
  // internalization options
  PARAM_VAR_ELIM,
  PARAM_ARITH_ELIM,
  PARAM_FLATTEN,
  PARAM_LEARN_EQ,
  PARAM_KEEP_ITE,
  // restart parameters 
  PARAM_FAST_RESTARTS,
  PARAM_C_THRESHOLD,
  PARAM_C_FACTOR,
  PARAM_D_THRESHOLD,
  PARAM_D_FACTOR,
  // clause deletion heuristic
  PARAM_R_THRESHOLD,
  PARAM_R_FRACTION,
  PARAM_R_FACTOR,
  // branching heuristic
  PARAM_VAR_DECAY,
  PARAM_RANDOMNESS,
  PARAM_RANDOM_SEED,
  PARAM_BRANCHING,
  // learned clauses
  PARAM_CLAUSE_DECAY,
  PARAM_CACHE_TCLAUSES,
  PARAM_TCLAUSE_SIZE,
  // egraph parameters
  PARAM_DYN_ACK,
  PARAM_DYN_BOOL_ACK,
  PARAM_MAX_ACK,
  PARAM_MAX_BOOL_ACK,
  PARAM_AUX_EQ_QUOTA,
  PARAM_AUX_EQ_RATIO,
  PARAM_MAX_INTERFACE_EQS,
  // simplex parameters
  PARAM_EAGER_LEMMAS,
  PARAM_SIMPLEX_PROP,
  PARAM_PROP_THRESHOLD,
  PARAM_BLAND_THRESHOLD,
  PARAM_ICHECK,
  PARAM_ICHECK_PERIOD,
  // error
  PARAM_UNKNOWN
} yices_param_t;


#define NUM_PARAMETERS PARAM_UNKNOWN

static const char * const param_names[NUM_PARAMETERS] = {
  "arith-elim",
  "aux-eq-quota",
  "aux-eq-ratio",
  "bland-threshold",
  "branching",
  "c-factor",
  "c-threshold",
  "cache-tclauses",
  "clause-decay",
  "d-factor",
  "d-threshold",
  "dyn-ack",
  "dyn-bool-ack",
  "eager-lemmas",
  "fast-restarts",
  "flatten",
  "icheck",
  "icheck-period",
  "keep-ite",
  "learn-eq",
  "max-ack",
  "max-bool-ack",
  "max-interface-eqs",
  "prop-threshold",
  "r-factor",
  "r-fraction",
  "r-threshold",
  "random-seed",
  "randomness",
  "simplex-prop",
  "tclause-size",
  "var-decay",
  "var-elim",
};

// corresponding parameter codes in order
static const yices_param_t param_code[NUM_PARAMETERS] = {
  PARAM_ARITH_ELIM,
  PARAM_AUX_EQ_QUOTA,
  PARAM_AUX_EQ_RATIO,
  PARAM_BLAND_THRESHOLD,
  PARAM_BRANCHING,
  PARAM_C_FACTOR,
  PARAM_C_THRESHOLD,
  PARAM_CACHE_TCLAUSES,
  PARAM_CLAUSE_DECAY,
  PARAM_D_FACTOR,
  PARAM_D_THRESHOLD,
  PARAM_DYN_ACK,
  PARAM_DYN_BOOL_ACK,
  PARAM_EAGER_LEMMAS,
  PARAM_FAST_RESTARTS,
  PARAM_FLATTEN,
  PARAM_ICHECK,
  PARAM_ICHECK_PERIOD,
  PARAM_KEEP_ITE,
  PARAM_LEARN_EQ,
  PARAM_MAX_ACK,
  PARAM_MAX_BOOL_ACK,
  PARAM_MAX_INTERFACE_EQS,
  PARAM_PROP_THRESHOLD,
  PARAM_R_FACTOR,
  PARAM_R_FRACTION,
  PARAM_R_THRESHOLD,
  PARAM_RANDOM_SEED,
  PARAM_RANDOMNESS,
  PARAM_SIMPLEX_PROP,
  PARAM_TCLAUSE_SIZE,
  PARAM_VAR_DECAY,
  PARAM_VAR_ELIM,
};



/*
 * Names of each branching mode (in lexicographic order)
 */
#define NUM_BRANCHING_MODES 6

static const char * const branching_modes[NUM_BRANCHING_MODES] = {
  "default",
  "negative",
  "positive",
  "th-neg",
  "th-pos",
  "theory",
};

static const branch_t branching_code[NUM_BRANCHING_MODES] = {
  BRANCHING_DEFAULT,
  BRANCHING_NEGATIVE,
  BRANCHING_POSITIVE,
  BRANCHING_TH_NEG,
  BRANCHING_TH_POS,
  BRANCHING_THEORY,
};



/*
 * smt_status --> string
 */
static const char * const status2string[] = {
  "idle",
  "searching",
  "unknown",
  "sat",
  "unsat",
  "interrupted",
};



/*
 * Tables for converting parameter id to parameter name
 * and branching code to branching name.
 */
static const char *param2string[NUM_PARAMETERS];
static const char *branching2string[NUM_BRANCHING_MODES];




/**************************
 *  COMMAND-LINE OPTIONS  *
 *************************/

enum {
  version_flag,
  help_flag,
  verbose_flag,
};

#define NUM_OPTIONS (verbose_flag+1)

static option_desc_t options[NUM_OPTIONS] = {
  { "version", 'V', FLAG_OPTION, version_flag },
  { "help", 'h', FLAG_OPTION, help_flag },
  { "verbose", 'v', FLAG_OPTION, verbose_flag },
};


/*
 * Base options
 */
static void print_version(void) {
  printf("Yices %s. Copyright SRI International, 2009\n"
	 "GMP %s. Copyright Free Software Foundation, Inc.\n"
	 "Build date: %s\n"
	 "Platform: %s (%s)\n",
	 yices_version,
	 gmp_version,
	 yices_build_date,
	 yices_build_arch,
	 yices_build_mode);
  fflush(stdout);
}

static void print_help(char *progname) {
  printf("Usage: %s [options] filename\n", progname);
  printf("Options:\n"
	 "  --version, -V           Display version and exit\n"
	 "  --help, -h              Display this information\n"
	 "  --verbose, -v           Run in verbose mode\n"
	 "\n"
	 "For bug reporting and other information, please see http://yices.csl.sri.com/\n");
  fflush(stdout);
}

static void print_usage(char *progname) {
  fprintf(stderr, "Usage: %s [options] <input_file>\n", progname);
  fprintf(stderr, "Try '%s --help' for more information\n", progname);  
}


/*
 * Processing of the command-line flags
 * - set the global variable input_filename
 * - input_filename = NULL means no filename on the command lineo
 * - deal with --help, --version or with errors
 */
static void process_command_line(int argc, char *argv[]) {
  cmdline_parser_t parser;
  cmdline_elem_t elem;

  input_filename = NULL;
  verbose = false;

  init_cmdline_parser(&parser, options, NUM_OPTIONS, argv, argc);

  for (;;) {
    cmdline_parse_element(&parser, &elem);
    switch (elem.status) {
    case cmdline_done:
      goto done;

    case cmdline_argument:
      if (input_filename == NULL) {
	input_filename = elem.arg;	
      } else {
	fprintf(stderr, "%s: can't have several input files\n", parser.command_name);
	goto bad_usage;
      }
      break;

    case cmdline_option:
      switch (elem.key) {
      case version_flag:
	print_version();
	goto quick_exit;

      case help_flag:
	print_help(parser.command_name);
	goto quick_exit;

      case verbose_flag:
	verbose = true;
	break;

      default:
	assert(false);
	break;
      }
      break;

    case cmdline_error:
      cmdline_print_error(&parser, &elem);
      goto bad_usage;
    }
  }

 quick_exit:
  exit(YICES_EXIT_SUCCESS);
  
 bad_usage:
  print_usage(parser.command_name);
  exit(YICES_EXIT_USAGE);

 done:
  return;
}




/********************
 *  SIGNAL HANDLER  *
 *******************/

/*
 * On SIGINT: call stop_search if the context is SEARCHING
 */
static void sigint_handler(int signum) {
  assert(context != NULL);
  if (verbose) {
    printf("\nInterrupted by signal %d\n", signum);
    fflush(stdout);
  }
  //  if (context_status(context) == STATUS_SEARCHING) {
  //    context_stop_search(context);
  //  }
}


/*
 * Other interrupts: exit with code INTERRUPTED
 */
static void default_handler(int signum) {
  if (verbose) {
    printf("\nInterrupted by signal %d\n", signum);
    fflush(stdout);
  }
  exit(YICES_EXIT_INTERRUPTED);
}


/*
 * Initialize the signal handlers
 */
static void init_handlers(void) {
  signal(SIGINT, sigint_handler);
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





/********************
 *  ERROR MESSAGES  *
 *******************/

/*
 * Error in the input: print an error message + location
 * - force exit if we're not in interactive mode
 */
static void report_error(const char *s) {
  reader_t *rd;

  rd = &parser.lex->reader;
  if (rd->name != NULL) {
    fprintf(stderr, "%s: ", rd->name);
  }
  fprintf(stderr, "%s (line %"PRId32", column %"PRId32")\n", s, reader_line(rd), reader_column(rd));
  done = !interactive;
}


/*
 * System error: call perror + print location
 * - force exit if we're not in interactive mode
 */
static void report_system_error(const char *s) {
  reader_t *rd;

  rd = &parser.lex->reader;
  if (rd->name != NULL) {
    fprintf(stderr, "%s: ", rd->name);
  }
  fprintf(stderr, "error at line %"PRId32": ", reader_line(rd));
  perror(s);

  done = !interactive;  
}


/*
 * Error in parameter assignment:
 * - name = parameter name
 * - reason = more explanation
 */
static void report_invalid_param(const char *name) {
  reader_t *rd;

  rd = &parser.lex->reader;
  if (rd->name != NULL) {
    fprintf(stderr, "%s: ", rd->name);
  }
  fprintf(stderr, "invalid parameter %s (line %"PRId32", column %"PRId32")\n", 
	  name, reader_line(rd), reader_column(rd));
  done = !interactive;
}

static void report_invalid_param_value(const char *name, const char *reason) {
  reader_t *rd;

  rd = &parser.lex->reader;
  if (rd->name != NULL) {
    fprintf(stderr, "%s: ", rd->name);
  }
  fprintf(stderr, "invalid value for parameter %s: %s (line %"PRId32", column %"PRId32")\n", 
	  name, reason, reader_line(rd), reader_column(rd));
  done = !interactive;
}



/*
 * BUG in Yices: Print an error message then exit
 */
static void report_bug(const char *s) {
  fprintf(stderr, "\n*************************************************************\n");
  fprintf(stderr, "FATAL ERROR: %s\n\n", s);
  fprintf(stderr, "Please report this bug to yices-bugs@csl.sri.com.\n");
  fprintf(stderr, "To help us diagnose this problem, please include the\n"
                  "following information in your bug report:\n\n");
  fprintf(stderr, "  Yices version: %s\n", yices_version);
  fprintf(stderr, "  Build date: %s\n", yices_build_date);
  fprintf(stderr, "  Platform: %s (%s)\n", yices_build_arch, yices_build_mode);
  fprintf(stderr, "\n");
  fprintf(stderr, "Thank you for your help.\n");
  fprintf(stderr, "*************************************************************\n\n");
  fflush(stderr);

  exit(YICES_EXIT_INTERNAL_ERROR);
}


/*
 * Conversion of internalization code to an error message
 */
static const char * const code2error[NUM_INTERNALIZATION_ERRORS] = {
  "no error", 
  "internal error",
  "type error",
  "formula contains free-variables",
  "logic not supported",
  "context does not support UF",
  "context does not support arithmetic",
  "context does not support bitvectors",
  "context does not support function equalities",
  "context does not support quantifiers",
  "not an IDL formula",
  "not an RDL formula",
  "non-linear arithmetic not supported",
  "arithmetic solver exception",
  "bitvector solver exception",
};



/*
 * Print the translation code returned by assert
 */
static void print_internalization_code(int32_t code) {
  assert(-NUM_INTERNALIZATION_ERRORS < code && code <= TRIVIALLY_UNSAT);
  if (code == TRIVIALLY_UNSAT) {
    printf("unsat\n");
    fflush(stdout);
  } else if (verbose && code == CTX_NO_ERROR) {
    printf("ok\n");
    fflush(stdout);
  } else if (code < 0) {
    code = - code;
    report_error(code2error[code]);
  }
}



/*
 * Report that previous command was executed (if verbose)
 */
static void print_ok(void) {
  if (verbose) {
    printf("ok\n");
    fflush(stdout);
  }
}



/****************************
 *  CONTEXT INITIALIZATION  *  
 ***************************/

/*
 * Placeholder: initialize the parameters
 */
static void init_params_to_defaults(param_t *p) {
  p->fast_restart = false;
  p->c_threshold = 100;
  p->d_threshold = 100;
  p->c_factor = 1.5;
  p->d_factor = 1.5;
  p->r_threshold = 1000;
  p->r_fraction = 0.25;
  p->r_factor = 1.05;
  p->var_decay = 0.95;
  p->randomness = 0.02;
  p->branching = BRANCHING_DEFAULT;
  p->clause_decay  = 0.999;
  p->cache_tclauses = false;
  p->tclause_size = 0;
  p->use_dyn_ack = false;
  p->use_bool_dyn_ack = false;
  p->max_ackermann = 1000;
  p->max_boolackermann = 600000;
  p->aux_eq_quota = 100;
  p->aux_eq_ratio = 0.3;
  p->max_interface_eqs = 200;
  p->use_simplex_prop = false;
  p->max_prop_row_size = 30;
  p->bland_threshold = 1000;
  p->integer_check_period = 99999999;
  p->max_update_conflicts = 20;
  p->max_extensionality = 1;
}

/*
 * Allocate and initialize the global context and model.
 * Initialize the parameter table with default values.
 * Set the signal handlers.
 */
static void init_ctx(void) {
  context = (context_t *) safe_malloc(sizeof(context_t));
  init_context(context, __yices_globals.terms, CTX_MODE_INTERACTIVE, CTX_ARCH_EG, false);
  enable_variable_elimination(context);
  enable_eq_abstraction(context);

  init_params_to_defaults(&parameters);
  init_handlers();
}


/*
 * On exit: cleanup
 */
static void delete_ctx(void) {
  assert(context != NULL);
  reset_handlers();
  delete_context(context);
  safe_free(context);
  context = NULL;
}




/***************************************
 *  UTILITIES TO DEAL WITH PARAMETERS  *
 **************************************/

/*
 * Initialize the table [parameter id --> string]
 * and [branching mode --> string]
 */
static void init_parameter_name_table(void) {
  uint32_t i, j;
  const char *name;

  for (i=0; i<NUM_PARAMETERS; i++) {
    name = param_names[i];
    j = param_code[i];
    param2string[j] = name;
  }

  for (i=0; i<NUM_BRANCHING_MODES; i++) {
    name = branching_modes[i];
    j = branching_code[i];
    branching2string[j] = name;
  }
}


/*
 * Binary search in a sorted array of strings.
 * - n = size of the array (n must be positive)
 * - s = string to search for
 * Return the index i between 0 and n-1 such that a[i] == s,
 * or -1 if s is not present in the array.
 */
static int32_t binary_search_string(const char *s, const char * const *a, int32_t n) {
  uint32_t l, h, k;
  int cmp;

  assert(n > 0);

  l = 0;
  h = (uint32_t) n;
  for (;;) {
    k = (l + h)/2;
    assert(l <= k && k < h);
    cmp = strcmp(s, a[k]);
    if (cmp == 0) return k;
    if (k == l) return -1;
    if (cmp < 0) {
      h = k;
    } else {
      assert(cmp > 0);
      l = k;
    }
  }
}

/*
 * Search for a parameter of the given name
 * - use binary search in the param_names table
 * - return PARAM_UNKNOWN if there's no parameter with that name
 */
static yices_param_t find_param(const char *name) {
  int32_t i;

  i = binary_search_string(name, param_names, NUM_PARAMETERS);
  if (i >= 0) {
    assert(i < NUM_PARAMETERS);
    return param_code[i];
  } else {
    return PARAM_UNKNOWN;
  }
}


/*
 * Convert a parameter value to boolean, int32, float, etc.
 * - name = parameter name, used for error reporting.
 * - return true if the conversion works
 * - return false otherwise (and print an error message)
 */
static bool param_val_to_bool(const char *name, param_val_t *v, bool *value) {
  bool code;

  code = true;
  if (v->tag == PARAM_VAL_FALSE) {
    *value = false;
  } else if (v->tag == PARAM_VAL_TRUE) {
    *value = true;
  } else {
    report_invalid_param_value(name, "boolean required");
    code = false;
  }
  return code;
}

static bool param_val_to_int32(const char *name, param_val_t *v, int32_t *value) {
  rational_t *q;

  if (v->tag == PARAM_VAL_RATIONAL) {
    q = v->val.rational;
    if (q_is_smallint(q)) {
      *value = q_get_smallint(q);
      return true;
    } else if (q_is_integer(q)) {
      report_invalid_param_value(name, "integer overflow");
      return false;
    }
    // if q is a rational: same error as not a number
  }

  report_invalid_param_value(name, "integer required");

  return false;
}

static bool param_val_to_pos32(const char *name, param_val_t *v, int32_t *value) {
  if (param_val_to_int32(name, v, value)) {
    if (*value > 0) return true;
    report_invalid_param_value(name, "must be positive");
  }
  return false;
}

static bool param_val_to_nonneg32(const char *name, param_val_t *v, int32_t *value) {
  if (param_val_to_int32(name, v, value)) {
    if (*value > 0) return true;
    report_invalid_param_value(name, "cannot be negative");
  }
  return false;
}



static bool param_val_to_float(const char *name, param_val_t *v, double *value) {
  mpq_t aux;

  if (v->tag == PARAM_VAL_RATIONAL) {
    mpq_init(aux);
    q_get_mpq(v->val.rational, aux);
    /*
     * NOTE: the GMP documentation says that conversion to double
     * may raise a hardware trap (overflow, underflow, etc.) on
     * some systems. We ignore this here.
     */
    *value = mpq_get_d(aux);
    mpq_clear(aux);
    return true;
  } else {
    report_invalid_param_value(name, "number required");
    return false;
  }
}


static bool param_val_to_posfloat(const char *name, param_val_t *v, double *value) {
  if (param_val_to_float(name, v, value)) {
    if (*value > 0.0) return true;
    report_invalid_param_value(name, "must be positive");
  }
  return false;
}

// ratio: number between 0 and 1 (inclusive)
static bool param_val_to_ratio(const char *name, param_val_t *v, double *value) {
  if (param_val_to_float(name, v, value)) {
    if (0 <= *value && *value <= 1.0) return true;
    report_invalid_param_value(name, "must be between 0 and 1");
  }
  return false;
}

// factor: must be at least 1
static bool param_val_to_factor(const char *name, param_val_t *v, double *value) {
  if (param_val_to_float(name, v, value)) {
    if (1.0 <= *value) return true;
    report_invalid_param_value(name, "must be at leat 1");
  }
  return false;
}




/*
 * Special case: branching mode
 * - allowed modes are 'default' 'positive' 'negative' 'theory' 'th-neg' 'th-pos'
 */
static bool param_val_to_branching(const char *name, param_val_t *v, branch_t *value) {
  int32_t i;

  if (v->tag == PARAM_VAL_SYMBOL) {
    i = binary_search_string(v->val.symbol, branching_modes, NUM_BRANCHING_MODES);
    if (i >= 0) {
      assert(i < NUM_BRANCHING_MODES);
      *value = branching_code[i];
      return true;
    }
  }

  report_error("invalid branching mode");
  fputs("valid modes are", stderr);
  for (i=0; i<NUM_BRANCHING_MODES; i++) {
    fprintf(stderr, " '%s'", branching_modes[i]);
  }
  fputc('\n', stderr);

  return false;
}





/*
 * Print a parameter name and its value
 * - n = number of character for name + spaces (for alignment)
 */
// print 'name:    ' with as many spaces as required for n characters
// if name is more than n character long, print 'name:'
static void show_param_name(const char *name, uint32_t n) {
  uint32_t l;

  l = strlen(name) + 1;
  fputs(name, stdout);
  fputc(':', stdout);
  while (n > l) {
    fputc(' ', stdout);
    n --;
  }
}

static void show_bool_param(const char *name, bool value, uint32_t n) {
  show_param_name(name, n);
  if (value) {
    fputs(" true\n", stdout);
  } else {
    fputs(" false\n", stdout);
  }
}

static void show_pos32_param(const char *name, uint32_t value, uint32_t n) {
  show_param_name(name, n);
  printf(" %"PRIu32"\n", value);
}

static void show_float_param(const char *name, double value, uint32_t n) {
  show_param_name(name, n);
  if (value < 1.0) {
    printf(" %.4f\n", value);
  } else {
    printf(" %.2f\n", value);
  }
}

static void show_string_param(const char *name, const char *value, uint32_t n) {
  show_param_name(name, n);
  fputc(' ', stdout);
  fputs(value, stdout);
  fputc('\n', stdout);
}

// main function to display a parameter value
// p = parameter id
// n = size for alignment (as used in show_param_name
static void show_param(yices_param_t p, uint32_t n) {
  switch (p) {
  case PARAM_VAR_ELIM:
    show_bool_param(param2string[p], context_var_elim_enabled(context), n);
    break;

  case PARAM_ARITH_ELIM:
    show_bool_param(param2string[p], context_arith_elim_enabled(context), n);
    break;

  case PARAM_FLATTEN:
    // this activates both flatten or and flatten diseq.
    show_bool_param(param2string[p], context_flatten_or_enabled(context), n);
    break;

  case PARAM_LEARN_EQ:
    show_bool_param(param2string[p], context_eq_abstraction_enabled(context), n);
    break;

  case PARAM_KEEP_ITE:
    show_bool_param(param2string[p], context_keep_ite_enabled(context), n);
    break;

  case PARAM_FAST_RESTARTS:
    show_bool_param(param2string[p], parameters.fast_restart, n);
    break;

  case PARAM_C_THRESHOLD:
    show_pos32_param(param2string[p], parameters.c_threshold, n);
    break;

  case PARAM_C_FACTOR:
    show_float_param(param2string[p], parameters.c_factor, n);
    break;

  case PARAM_D_THRESHOLD:
    show_pos32_param(param2string[p], parameters.d_threshold, n);
    break;

  case PARAM_D_FACTOR:
    show_float_param(param2string[p], parameters.c_factor, n);
    break;

  case PARAM_R_THRESHOLD:
    show_pos32_param(param2string[p], parameters.r_threshold, n);
    break;

  case PARAM_R_FRACTION:
    show_float_param(param2string[p], parameters.r_fraction, n);
    break;

  case PARAM_R_FACTOR:
    show_float_param(param2string[p], parameters.r_factor, n);
    break;

  case PARAM_VAR_DECAY:
    show_float_param(param2string[p], parameters.var_decay, n);
    break;

  case PARAM_RANDOMNESS:
    show_float_param(param2string[p], parameters.randomness, n);
    break;

  case PARAM_RANDOM_SEED:
    show_pos32_param(param2string[p], the_seed, n);
    break;

  case PARAM_BRANCHING:
    show_string_param(param2string[p], branching2string[parameters.branching], n);
    break;

  case PARAM_CLAUSE_DECAY:
    show_float_param(param2string[p], parameters.clause_decay, n);
    break;

  case PARAM_CACHE_TCLAUSES:
    show_bool_param(param2string[p], parameters.cache_tclauses, n);
    break;

  case PARAM_TCLAUSE_SIZE:
    show_pos32_param(param2string[p], parameters.tclause_size, n);
    break;

  case PARAM_DYN_ACK:
    show_bool_param(param2string[p], parameters.use_dyn_ack, n);
    break;

  case PARAM_DYN_BOOL_ACK:
    show_bool_param(param2string[p], parameters.use_bool_dyn_ack, n);
    break;

  case PARAM_MAX_ACK:
    show_pos32_param(param2string[p], parameters.max_ackermann, n);
    break;

  case PARAM_MAX_BOOL_ACK:
    show_pos32_param(param2string[p], parameters.max_boolackermann, n);
    break;

  case PARAM_AUX_EQ_QUOTA:
    show_pos32_param(param2string[p], parameters.aux_eq_quota, n);
    break;

  case PARAM_AUX_EQ_RATIO:
    show_float_param(param2string[p], parameters.aux_eq_ratio, n);
    break;

  case PARAM_MAX_INTERFACE_EQS:
    show_pos32_param(param2string[p], parameters.max_interface_eqs, n);
    break;

  case PARAM_EAGER_LEMMAS:
    show_bool_param(param2string[p], splx_eager_lemmas_enabled(context), n);
    break;

  case PARAM_SIMPLEX_PROP:
    show_bool_param(param2string[p], parameters.use_simplex_prop, n);
    break;

  case PARAM_PROP_THRESHOLD:
    show_pos32_param(param2string[p], parameters.max_prop_row_size, n);
    break;

  case PARAM_BLAND_THRESHOLD:
    show_pos32_param(param2string[p], parameters.bland_threshold, n);
    break;

  case PARAM_ICHECK:
    show_bool_param(param2string[p], splx_periodic_icheck_enabled(context), n);
    break;

  case PARAM_ICHECK_PERIOD:
    show_pos32_param(param2string[p], parameters.integer_check_period, n);
    break;

  case PARAM_UNKNOWN:
  default:
    report_bug("invalid parameter id in 'show_param'");
    break;
  }
}





/**************
 *  COMMANDS  *
 *************/

/*
 * Exit: close the current include file or exit the toplevel
 */
static void yices_exit_cmd(void) {
  if (include_depth > 0) {
    parser_pop_lexer(&parser);
    include_depth --;
  } else {
    if (verbose) {
      fputs("exiting\n", stdout);
      fflush(stdout);
    }
    done = true;
  }
}


/*
 * Echo
 */
static void yices_echo_cmd(char *s) {
  fputs(s, stdout);
  fflush(stdout);
}


/*
 * Include a file
 */
static void yices_include_cmd(char *s) {
  if (parser_push_lexer(&parser, s) < 0) {
    report_system_error(s);
  } else {
    include_depth ++;    
  }
}


/*
 * Parameter assignment
 */
static void yices_setparam_cmd(char *param, param_val_t *val) {
  bool tt;
  int32_t n;
  double x;
  branch_t b;

  switch (find_param(param)) {
  case PARAM_VAR_ELIM:
    if (param_val_to_bool(param, val, &tt)) {
      if (tt) {
	enable_variable_elimination(context);
      } else {
	disable_variable_elimination(context);
      }
      print_ok();
    }
    break;

  case PARAM_ARITH_ELIM:
    if (param_val_to_bool(param, val, &tt)) {
      if (tt) {
	enable_arith_elimination(context);
      } else {
	disable_arith_elimination(context);
      }
      print_ok();
    }
    break;

  case PARAM_FLATTEN:
    if (param_val_to_bool(param, val, &tt)) {
      if (tt) {
	enable_diseq_and_or_flattening(context);
      } else {
	disable_diseq_and_or_flattening(context);
      }
      print_ok();
    }
    break;

  case PARAM_LEARN_EQ:
    if (param_val_to_bool(param, val, &tt)) {
      if (tt) {
	enable_eq_abstraction(context);
      } else {
	disable_eq_abstraction(context);
      }
      print_ok();
    }
    break;

  case PARAM_KEEP_ITE:
    if (param_val_to_bool(param, val, &tt)) {
      if (tt) {
	enable_keep_ite(context);
      } else {
	disable_keep_ite(context);
      }
      print_ok();
    }
    break;

  case PARAM_FAST_RESTARTS:
    if (param_val_to_bool(param, val, &tt)) {
      parameters.fast_restart = tt;
      print_ok();
    }
    break;

  case PARAM_C_THRESHOLD:
    if (param_val_to_pos32(param, val, &n)) {
      parameters.c_threshold = n;
      print_ok();
    }
    break;

  case PARAM_C_FACTOR:
    if (param_val_to_factor(param, val, &x)) {
      parameters.c_factor = x;
      print_ok();
    }
    break;

  case PARAM_D_THRESHOLD:
    if (param_val_to_pos32(param, val, &n)) {      
      parameters.d_threshold = n;
      print_ok();
    }
    break;
    
  case PARAM_D_FACTOR:
    if (param_val_to_factor(param, val, &x)) {
      parameters.d_factor = x;
      print_ok();
    }
    break;

  case PARAM_R_THRESHOLD:
    if (param_val_to_pos32(param, val, &n)) {
      parameters.r_threshold = n;
      print_ok();
    }
    break;

  case PARAM_R_FRACTION:
    if (param_val_to_ratio(param, val, &x)) {
      parameters.r_fraction = x;
      print_ok();
    }
    break;

  case PARAM_R_FACTOR:
    if (param_val_to_factor(param, val, &x)) {
      parameters.r_factor = x;
      print_ok();
    }
    break;

  case PARAM_VAR_DECAY:
    if (param_val_to_ratio(param, val, &x)) {
      parameters.var_decay = x;
      print_ok();
    }
    break;

  case PARAM_RANDOMNESS:
    if (param_val_to_ratio(param, val, &x)) {
      parameters.randomness = x;
      print_ok();
    }
    break;

  case PARAM_RANDOM_SEED:
    if (param_val_to_int32(param, val, &n)) {
      smt_set_seed((uint32_t) n);
      the_seed = n;
      print_ok();
    }
    break;

  case PARAM_BRANCHING:
    if (param_val_to_branching(param, val, &b)) {
      parameters.branching = b;
      print_ok();
    }
    break;

  case PARAM_CLAUSE_DECAY:
    if (param_val_to_ratio(param, val, &x)) {
      parameters.clause_decay = x;
      print_ok();
    }
    break;

  case PARAM_CACHE_TCLAUSES:
    if (param_val_to_bool(param, val, &tt)) {
      parameters.cache_tclauses = tt;
      print_ok();
    }
    break;

  case PARAM_TCLAUSE_SIZE:
    if (param_val_to_pos32(param, val, &n)) {
      parameters.tclause_size = n;
      print_ok();
    }
    break;

  case PARAM_DYN_ACK:
    if (param_val_to_bool(param, val, &tt)) {
      parameters.use_dyn_ack = true;
      print_ok();
    }
    break;

  case PARAM_DYN_BOOL_ACK:
    if (param_val_to_bool(param, val, &tt)) {
      parameters.use_bool_dyn_ack = true;
      print_ok();
    }
    break;
    
  case PARAM_MAX_ACK:
    if (param_val_to_pos32(param, val, &n)) {
      parameters.max_ackermann = n;
      print_ok();
    }
    break;

  case PARAM_MAX_BOOL_ACK:
    if (param_val_to_pos32(param, val, &n)) {
      parameters.max_boolackermann = n;
      print_ok();
    }
    break;

  case PARAM_AUX_EQ_QUOTA:
    if (param_val_to_pos32(param, val, &n)) {
      parameters.aux_eq_quota = n;
      print_ok();
    }
    break;

  case PARAM_AUX_EQ_RATIO:
    if (param_val_to_posfloat(param, val, &x)) {
      parameters.aux_eq_ratio = x;
      print_ok();
    }
    break;

  case PARAM_MAX_INTERFACE_EQS:
    if (param_val_to_pos32(param, val, &n)) {
      parameters.max_interface_eqs = n;
      print_ok();
    }
    break;

  case PARAM_EAGER_LEMMAS:
    if (param_val_to_bool(param, val, &tt)) {
      if (tt) {
	enable_splx_eager_lemmas(context);
      } else {
	disable_splx_eager_lemmas(context);
      }
      print_ok();
    } 
    break;

  case PARAM_SIMPLEX_PROP:
    if (param_val_to_bool(param, val, &tt)) {
      parameters.use_simplex_prop = tt;
      print_ok();
    }
    break;

  case PARAM_PROP_THRESHOLD:
    if (param_val_to_nonneg32(param, val, &n)) {
      parameters.max_prop_row_size = n;
      print_ok();
    }
    break;

  case PARAM_BLAND_THRESHOLD:
    if (param_val_to_pos32(param, val, &n)) {
      parameters.bland_threshold = n;
      print_ok();
    }
    break;

  case PARAM_ICHECK:
    if (param_val_to_bool(param, val, &tt)) {
      if (tt) {
	enable_splx_periodic_icheck(context);
      } else {
	disable_splx_periodic_icheck(context);
      }
      print_ok();
    }
    break;

  case PARAM_ICHECK_PERIOD:
    if (param_val_to_pos32(param, val, &n)) {
      parameters.integer_check_period = n;
      print_ok();
    }
    break;

  case PARAM_UNKNOWN:
  default:
    report_invalid_param(param);
    break;
  }
}



/*
 * Print all the parameter settings
 */
static void yices_showparams_cmd(void) {
  uint32_t i;

  for (i=0; i<NUM_PARAMETERS; i++) {
    show_param(i, 20);;
  }
}



/*
 * Dump: print all internal tables
 */
static void yices_dump_cmd(void) {
  assert(context != NULL);

  printf("--- Substitutions ---\n");
  print_context_intern_subst(stdout, context);
  printf("--- Auxiliary vectors ---\n\n");
  print_context_subst_eqs(stdout, context);
  print_context_top_eqs(stdout, context);
  print_context_top_atoms(stdout, context);
  print_context_top_formulas(stdout, context);
  print_context_top_interns(stdout, context);
  printf("\n");
  fflush(stdout);
}



/*
 * Reset
 */
static void yices_reset_cmd(void) {
  reset_context(context);
  print_ok();
}


/*
 * Push
 */
static void yices_push_cmd(void) {
  if (! context_supports_pushpop(context)) {
    report_error("push/pop not supported by this context");    
  } else {
    switch (context_status(context)) {
    case STATUS_UNKNOWN:
    case STATUS_SAT:
      // return to IDLE
      context_clear(context);
      assert(context_status(context) == STATUS_IDLE);
      // fall-through intended.

    case STATUS_IDLE:
      context_push(context);
      print_ok();
      break;

    case STATUS_UNSAT:
      // cannot take (push)
      fputs("The context is unsat; (push) is not allowed\n", stdout);
      fflush(stdout);
      break;

    case STATUS_SEARCHING:
    case STATUS_INTERRUPTED:
    default:
      // should not happen
      report_bug("unexpected context status in push");
      break;  
    }
  }
}



/*
 * Pop
 */
static void yices_pop_cmd(void) {
  if (! context_supports_pushpop(context)) {
    report_error("push/pop not supported by this context");
  } else if (context_base_level(context) == 0) {
    report_error("pop not allowed at bottom level");
  } else {
    switch (context_status(context)) {
    case STATUS_UNKNOWN:
    case STATUS_SAT:
      // delete the model first
      context_clear(context);
      assert(context_status(context) == STATUS_IDLE);
      // fall-through intended
    case STATUS_IDLE:
    case STATUS_UNSAT:
      context_pop(context);
      print_ok();
      break;

    case STATUS_SEARCHING:
    case STATUS_INTERRUPTED:
    default:
      report_bug("unexpected context status in pop");
      break;
    }    
  }
}


/*
 * Assert formula f
 */
static void yices_assert_cmd(term_t f) {
  int32_t code;

  switch (context_status(context)) {
  case STATUS_UNKNOWN:
  case STATUS_SAT:
    // cleanup then return to the idle state
    context_clear(context); 
    assert(context_status(context) == STATUS_IDLE);
    // fall-through intended

  case STATUS_IDLE:
    if (yices_term_is_bool(f)) {
      code = assert_formula(context, f);
      print_internalization_code(code);
    } else {
      report_error("type error in assert: boolean term required");
    }
    break;


  case STATUS_UNSAT:
    // cannot take more assertions
    fputs("The context is unsat. Try (pop) or (reset)\n", stdout);
    fflush(stdout);    
    break;

  case STATUS_SEARCHING:
  case STATUS_INTERRUPTED:
  default:
    // should not happen
    report_bug("unexpected context status in assert");
    break;    
  }
}




/*
 * Check whether the context is satisfiable
 */
static void yices_check_cmd(void) {
  smt_status_t stat;

  stat = context_status(context);
  switch (stat) {
  case STATUS_UNKNOWN:
  case STATUS_UNSAT:
  case STATUS_SAT:
    // already solved: print the status
    fputs(status2string[stat], stdout);
    fputc('\n', stdout);
    break;

  case STATUS_IDLE:
    fputs("Check not supported\n", stdout);
    break;

  case STATUS_SEARCHING:
  case STATUS_INTERRUPTED:
  default:
    // this should not happen
    report_bug("unexpected context status in check");
    break;
  }
}



/*
 * Build model if needed and display it
 */
static void yices_showmodel_cmd(void) {
  fputs("Not supported\n", stdout);
}



/*
 * Eval term t in the current model
 * - build the model if needed
 */
static void yices_eval_cmd(term_t t) {
  fputs("Not supported\n", stdout);
}



/*
 * Feedback for define or define-term
 */
static void yices_type_defined_cmd(char *name, type_t tau) {
  print_ok();
}

static void yices_term_defined_cmd(char *name, term_t t) {
  print_ok();
}



/**********
 *  MAIN  *
 *********/

/*
 * This is a separate function so that we can use it to invoke yices
 * via foreign function calls in LISP.
 */
int yices_main(int argc, char *argv[]) {
  int32_t code;

  // Deal with command-line options
  process_command_line(argc, argv);

  /*
   * Check the input file
   * - initialize the lexer
   * - set the interactive flag
   */
  interactive = false;
  include_depth = 0;
  the_seed = PRNG_DEFAULT_SEED;

  if (input_filename == NULL) {
    init_yices_stdin_lexer(&lexer);
    interactive = true;
  } else if (init_yices_file_lexer(&lexer, input_filename) < 0) {
    perror(input_filename);
    exit(YICES_EXIT_FILE_NOT_FOUND);
  }

  /*
   * The lexer is ready: initialize the other structures
   */
  yices_init();
  init_tstack(&stack);
  tstack_set_exit_cmd(&stack, yices_exit_cmd);
  tstack_set_echo_cmd(&stack, yices_echo_cmd);
  tstack_set_include_cmd(&stack, yices_include_cmd);
  tstack_set_setparam_cmd(&stack, yices_setparam_cmd);
  tstack_set_showparams_cmd(&stack, yices_showparams_cmd);
  tstack_set_dump_cmd(&stack, yices_dump_cmd);
  tstack_set_reset_cmd(&stack, yices_reset_cmd);
  tstack_set_push_cmd(&stack, yices_push_cmd);
  tstack_set_pop_cmd(&stack, yices_pop_cmd);
  tstack_set_assert_cmd(&stack, yices_assert_cmd);
  tstack_set_check_cmd(&stack, yices_check_cmd);
  tstack_set_showmodel_cmd(&stack, yices_showmodel_cmd);
  tstack_set_eval_cmd(&stack, yices_eval_cmd);  
  tstack_set_type_defined_cmd(&stack, yices_type_defined_cmd);
  tstack_set_term_defined_cmd(&stack, yices_term_defined_cmd);
  init_parameter_name_table();

  init_parser(&parser, &lexer, &stack);
  if (verbose) {
    print_version();
  }

  init_ctx();

  /*
   * Read-eval loop
   * - done is set to true when (exit) is called
   *   or on the first error if we're not in interactive mode
   */
  done = false;
  while (current_token(&lexer) != TK_EOS && !done) {
    if (interactive && include_depth == 0) {
      // prompt
      fputs("yices> ", stdout);
      fflush(stdout);
    }
    code = parse_yices_command(&parser, stderr);
    if (code < 0) {
      // error
      if (interactive) {
	/*
	 * If the error occurs within an include file, 
	 * we close all included files and return to main
	 */
	while (include_depth > 0) {
	  parser_pop_lexer(&parser);
	  include_depth --;
	}
	flush_lexer(&lexer);
      } else {
	done = true;
      }      
    }    
  }

  /*
   * Clean up
   */
  delete_ctx();
  delete_parser(&parser);
  if (interactive) {
    // keep stdin open
    close_lexer_only(&lexer);
  } else {
    close_lexer(&lexer);
  }
  delete_tstack(&stack);
  yices_exit();

  return YICES_EXIT_SUCCESS;
}

