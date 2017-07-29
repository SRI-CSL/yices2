/*
 * The Yices SMT Solver. Copyright 2016 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Parse a file in DIMACS/CNF format then call the (new) sat solver.
 */

#if defined(CYGWIN) || defined(MINGW)
#ifndef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__ __declspec(dllexport)
#endif
#endif

#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <signal.h>
#include <inttypes.h>

#include "solvers/cdcl/new_sat_solver.h"
#include "utils/command_line.h"
#include "utils/cputime.h"
#include "utils/memalloc.h"
#include "utils/memsize.h"

#include "yices.h"
#include "yices_exit_codes.h"


/*
 * GLOBAL OBJECTS
 */

static sat_solver_t solver;
static double construction_time, search_time;



/*
 * DIMACS PARSER
 */

/*
 * Array to read one line of the input file
 */

#define MAX_LINE 1000
static char line[MAX_LINE];

/*
 * Problem size + buffer for reading clauses
 */
static int nvars, nclauses;
static literal_t *clause;
static uint32_t buffer_size;


/*
 * Wrapped around getc or getc_unlocked
 */
static inline int read_char(FILE *f) {
#if defined(MINGW)
    return getc(f);
#else
    return getc_unlocked(f);
#endif
}

/*
 * Read until the end of the line
 */
static void finish_line(FILE *f) {
  int c;

  do {
    c = read_char(f);
  } while (c != '\n');
}


/*
 * Buffer allocation
 */
#define MAX_BUFFER (UINT32_MAX/sizeof(literal_t))

static void alloc_buffer(uint32_t size) {
  assert(size <= MAX_BUFFER);
  clause = malloc(size * sizeof(literal_t));
  buffer_size = size;
  if (clause == NULL) {
    fprintf(stderr, "Out of memory\n");
    exit(2);
  }
}

static void expand_buffer(void) {
  /*
   * Added the assertion buffer_size > 0 to stop a false report from
   * the clang static analyzer.
   */
  assert(buffer_size > 0 && buffer_size <= MAX_BUFFER);
  buffer_size = 2 * buffer_size;
  if (buffer_size > MAX_BUFFER) {
    buffer_size = MAX_BUFFER;
  }

  clause = realloc(clause, buffer_size * sizeof(literal_t));
  if (clause == NULL) {
    fprintf(stderr, "Out of memory\n");
    exit(2);
  }
}

static void delete_buffer(void) {
  safe_free(clause);
  buffer_size = 0;
  clause = NULL;
}


/*
 * Read a literal in DIMACS encoding from a file
 * convert it to the yices sat format.
 * - returns a negative number if an error occurs
 *   or if the integer read is 0.
 *   or a literal l between 0 and 2nv - 1 otherwise.
 */
#define BAD_INPUT -1
#define END_OF_CLAUSE -2

static literal_t read_literal(FILE *f, int32_t nv) {
  int d;
  int32_t var, delta;

  do {
    d = read_char(f);
  } while (isspace(d));


  /*
   * Conversion: literal in new_sat_solver format = 2 * var + delta
   * where var = variable index in DIMACS format (between 1 and nv)
   *     delta = 0 if literal is positive in DIMACS format
   *     delta = 1 if literal is negative in DIMACS format
   * This works since yices variable index = DIMACS var
   * and literal in yices format = 2 * (var index) + sign
   */
  delta = 0;
  var = 0;
  if (d == '-') {
    delta = 1;
    d = read_char(f);
  }
  if (!isdigit(d)) {
    return BAD_INPUT;
  }

  do {
    var = 10 * var + (d - '0');
    d = read_char(f);
  } while (isdigit(d) && var <= nv);

  if (var == 0) {
    return END_OF_CLAUSE;
  } else if (var <= nv) {
    return var + var + delta;
  } else {
    return BAD_INPUT;
  }
}


/*
 * Read DIMACS instance from filename and construct a solver
 * - pp true means build the solver for preprocessing
 * - pp false means disable preprocessing (this is the default)
 * returns 0 if no error occurred.
 * -1 means file could not be opened.
 * -2 means bad format in the input file.
 */
#define OPEN_ERROR -1
#define FORMAT_ERROR -2

static int build_instance(char *filename, bool pp) {
  int n, x, c_idx, l_idx, literal;
  reader_t reader;
  char pline[200];

  f = fopen(filename, "r");
  if (f == NULL) {
    perror(filename);
    return OPEN_ERROR;
  }

  s = fgets(line, MAX_LINE, f);
  if (s == NULL) {
    fprintf(stderr, "%s: empty file\n", filename);
    fclose(f);
    return FORMAT_ERROR;
  }
  if (strlen(s) == MAX_LINE-1) {
    finish_line(f);
  }
  l = 1; /* line number */


  /* skip empty lines and comments */
  while (*s == 'c' || *s == '\n') {
    s = fgets(line, MAX_LINE, f);
    if (s == NULL) {
      fprintf(stderr, "Format error: file %s, line %d\n", filename, l);
      fclose(f);
      return FORMAT_ERROR;
    }
    if (strlen(s) == MAX_LINE-1) {
      finish_line(f);
    }
    l ++;    
  }

  /* read problem size */
  n = sscanf(s, "p cnf %d %d", &nvars, &nclauses);
  if (n != 2 || nvars < 0 || nclauses < 0) {
    fprintf(stderr, "Format error: file %s, line %d\n", filename, l);
    fclose(f);
    return FORMAT_ERROR;
  }

  /* initialize solver for nvars */
  init_nsat_solver(&solver, nvars + 1, pp);
  nsat_solver_add_vars(&solver, nvars);

  /* now read clauses and translate them */
  c_idx = 0;

  while (c_idx < nclauses) {
    l_idx = 0;
    for (;;) {
      literal = read_literal(f, nvars);
      if (literal < 0) break;

      if (l_idx >= (int)buffer_size) expand_buffer();
      clause[l_idx] = literal;
      l_idx ++;
    }

    if (literal != END_OF_CLAUSE) {
      fprintf(stderr, "Format error: file %s\n", filename);
      fclose(f);
      return FORMAT_ERROR;
    }

    nsat_solver_simplify_and_add_clause(&solver, l_idx, clause);
    c_idx ++;
  }

  fclose(f);
  return 0;
}




/*
 * COMMAND-LINE OPTIONS
 */

/*
 * Parameter:
 * - input_filename = name of the input file
 * - verbose = true for verbose output
 * - model = true for produce model (if SAT)
 * - preprocess = true to enable preprocessing
 * - seed_given = true if a seed is given on the command line
 *   seed_value = value of the seed
 * - stats = true for printing statistics
 * - data = true for collecting data
 */
static char *input_filename = NULL;
static bool verbose;
static bool model;
static bool preprocess;
static bool seed_given;
static uint32_t seed_value;
static bool stats;
static bool data;

static bool keep_lbd_given;
static bool reduce_fraction_given;
static bool stack_threshold_given;
static bool subsume_skip_given;
static bool var_elim_skip_given;
static bool res_clause_limit_given;
static uint32_t keep_lbd;
static uint32_t reduce_fraction;
static uint32_t stack_threshold;
static uint32_t subsume_skip;
static uint32_t var_elim_skip;
static uint32_t res_clause_limit;

enum {
  version_flag,
  help_flag,
  verbose_flag,
  model_flag,
  preprocess_flag,
  seed_opt,
  stats_flag,
  keep_lbd_opt,
  reduce_fraction_opt,
  stack_threshold_opt,
  subsume_skip_opt,
  var_elim_skip_opt,
  res_clause_limit_opt,
  data_flag,
};

#define NUM_OPTIONS (data_flag+1)

static option_desc_t options[NUM_OPTIONS] = {
  { "version", 'V', FLAG_OPTION, version_flag },
  { "help", 'h', FLAG_OPTION, help_flag },
  { "verbose", 'v', FLAG_OPTION, verbose_flag },
  { "model", 'm', FLAG_OPTION, model_flag },
  { "preprocess", 'p', FLAG_OPTION, preprocess_flag },
  { "seed", 's', MANDATORY_INT, seed_opt },
  { "stats", '\0', FLAG_OPTION, stats_flag },
  { "keep-lbd", '\0', MANDATORY_INT, keep_lbd_opt },
  { "reduce-fraction", '\0', MANDATORY_INT, reduce_fraction_opt },
  { "stack-threshold", '\0', MANDATORY_INT, stack_threshold_opt },
  { "subsume-skip", '\0', MANDATORY_INT, subsume_skip_opt },
  { "var-elim-skip", '\0', MANDATORY_INT, var_elim_skip_opt },
  { "res-clause-limit", '\0', MANDATORY_INT, res_clause_limit_opt },
  { "data", '\0', FLAG_OPTION, data_flag },
};


/*
 * Version and help
 */
static void print_version(FILE *f) {
  fprintf(f,
          "Yices %s. Copyright SRI International.\n"
          "Build date: %s\n"
          "Platform: %s (%s)\n",
          yices_version,
          yices_build_date,
          yices_build_arch,
          yices_build_mode);
  fflush(f);
}

static void print_help(char *progname) {
  printf("Usage: %s [options] filename\n\n", progname);
  printf("Option summary:\n"
         "   --version, -V           Show version and exit\n"
         "   --help, -h              Print this message and exit\n"
         "   --model, -m             Show a model if the problem is satisfiable\n"
         "   --verbose, -v           Verbose mode\n"
	 "   --preprocess, -p        Use preprocessing\n"
	 "   --seed=<int>, -s <int>  Set the prng seed\n"
	 "   --stats                 Print statistics at the end of the search\n"
	 "   --data                  Store conflict data in 'xxxx.data'\n"
         "\n"
         "For bug reporting and other information, please see http://yices.csl.sri.com/\n");
  fflush(stdout);
}


/*
 * Error in options
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
  int32_t k;

  input_filename = NULL;
  model = false;
  verbose = false;
  seed_given = false;
  stats = false;
  preprocess = false;
  data = false;

  keep_lbd_given = false;
  reduce_fraction_given = false;
  stack_threshold_given = false;
  subsume_skip_given = false;
  var_elim_skip_given = false;
  res_clause_limit_given = false;

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
        fprintf(stderr, "%s: too many arguments\n", parser.command_name);
        goto bad_usage;
      }
      break;

    case cmdline_option:
      k = elem.key;
      switch (k) {
      case version_flag:
        print_version(stdout);
        exit(YICES_EXIT_SUCCESS);

      case help_flag:
        print_help(parser.command_name);
        exit(YICES_EXIT_SUCCESS);

      case verbose_flag:
        verbose = true;
        break;

      case model_flag:
        model = true;
        break;

      case preprocess_flag:
	preprocess = true;
	break;

      case seed_opt:
        seed_given = true;
        seed_value = elem.i_value;
        break;

      case stats_flag:
	stats = true;
	break;

      case keep_lbd_opt:
	if (elem.i_value < 0) {
	  fprintf(stderr, "keep-lbd can't be negative\n");
	  goto bad_usage;
	}
	keep_lbd_given = true;
	keep_lbd = elem.i_value;
	break;

      case reduce_fraction_opt:
	if (elem.i_value < 0 || elem.i_value > 32) {
	  fprintf(stderr, "reduce-fraction must be between 0 and 32\n");
	  goto bad_usage;
	}
	reduce_fraction_given = true;
	reduce_fraction = elem.i_value;
	break;

      case stack_threshold_opt:
	if (elem.i_value < 0) {
	  fprintf(stderr, "stack-threshold can't be negative\n");
	  goto bad_usage;
	}
	stack_threshold_given = true;
	stack_threshold = elem.i_value;
	break;

      case subsume_skip_opt:
	if (elem.i_value < 0) {
	  fprintf(stderr, "subsume-skip can't be negative\n");
	  goto bad_usage;
	}
	subsume_skip_given = true;
	subsume_skip = elem.i_value;
	break;

      case var_elim_skip_opt:
	if (elem.i_value < 0) {
	  fprintf(stderr, "var-elim-skip can't be negative\n");
	  goto bad_usage;
	}
	var_elim_skip_given = true;
	var_elim_skip = elem.i_value;
	break;

      case res_clause_limit_opt:
	if (elem.i_value < 0) {
	  fprintf(stderr, "res-clause-limit can't be negative\n");
	  goto bad_usage;
	}
	res_clause_limit_given = true;
	res_clause_limit = elem.i_value;
	break;

      case data_flag:
	data = true;
	break;
      }
      break;

    case cmdline_error:
      cmdline_print_error(&parser, &elem);
      goto bad_usage;
    }
  }

 done:
  if (input_filename == NULL) {
    fprintf(stderr, "%s: no input file given\n", parser.command_name);
    goto bad_usage;
  }

  return;

 bad_usage:
  yices_usage(parser.command_name);
  exit(YICES_EXIT_USAGE);
}



/*
 * STATISTICS AND RESULTS
 */
static void show_stats(sat_solver_t *solver) {
  solver_stats_t *stat = &solver->stats;

  fprintf(stderr, "c\n");
  fprintf(stderr, "c Statistics\n");
  fprintf(stderr, "c  starts                  : %"PRIu32"\n", stat->starts);
  fprintf(stderr, "c  simplify db             : %"PRIu32"\n", stat->simplify_calls);
  fprintf(stderr, "c  reduce db               : %"PRIu32"\n", stat->reduce_calls);
  fprintf(stderr, "c  scc calls               : %"PRIu32"\n", stat->scc_calls);
  fprintf(stderr, "c  apply subst calls       : %"PRIu32"\n", stat->subst_calls);
  fprintf(stderr, "c  substituted vars        : %"PRIu32"\n", stat->subst_vars);
  fprintf(stderr, "c  decisions               : %"PRIu64"\n", stat->decisions);
  fprintf(stderr, "c  random decisions        : %"PRIu64"\n", stat->random_decisions);
  fprintf(stderr, "c  propagations            : %"PRIu64"\n", stat->propagations);
  fprintf(stderr, "c  conflicts               : %"PRIu64"\n", stat->conflicts);
  fprintf(stderr, "c  lits in pb. clauses     : %"PRIu32"\n", solver->pool.num_prob_literals);
  fprintf(stderr, "c  lits in learned clauses : %"PRIu32"\n", solver->pool.num_learned_literals);
  fprintf(stderr, "c  subsumed lits.          : %"PRIu64"\n", stat->subsumed_literals);
  fprintf(stderr, "c  deleted pb. clauses     : %"PRIu64"\n", stat->prob_clauses_deleted);
  fprintf(stderr, "c  deleted learned clauses : %"PRIu64"\n", stat->learned_clauses_deleted);
  fprintf(stderr, "c\n");
}

static void print_results(void) {
  solver_status_t result;
  double mem_used;

  search_time = get_cpu_time() - construction_time;

  result = solver.status;

  if (verbose) {
    show_stats(&solver);
    fprintf(stderr, "c Search time              : %.4f s\n", search_time);
    mem_used = mem_size() / (1024 * 1024);
    if (mem_used > 0) {
      fprintf(stderr, "c Memory used              : %.2f MB\n", mem_used);
    }
    speed = solver.stats.propagations/search_time;
    fprintf(stderr, "c Speed                    : %.2f prop/s\n", speed);
    fprintf(stderr, "c\n");
  }

  switch (result) {
  case STAT_UNSAT:
    printf("s UNSATISFIABLE\n");
    break;

  case STAT_SAT:
    printf("s SATISFIABLE\n");
    break;

  default:
    printf("s UNKOWN\n");
    break;
  }
}


/*
 * Print initial size
 */
void print_solver_size(FILE *f, sat_solver_t *sol) {
  fprintf(f, "c  vars                 : %"PRIu32"\n", sol->nvars);
  fprintf(f, "c  unit clauses         : %"PRIu32"\n", sol->units);
  fprintf(f, "c  binary clauses       : %"PRIu32"\n", sol->binaries);
  fprintf(f, "c  other clauses        : %"PRIu32"\n", sol->pool.num_prob_clauses);
  fprintf(f, "c  assignments          : %"PRIu32"\n", sol->stack.top);
  fprintf(f, "c\n");
}


/*
 * Print the solution if the problem is satisfiable.
 * Print the list of true literals terminated by 0
 *
 * For variable v = 1 to nvars
 *   if val[v] == true then print  +v (positive literal)
 *   if val[v] == false then print -v (negative literal)
 *   if val[v] == undef skip v
 *
 */
static void print_model(void) {
  int v, k, l;

  if (nsat_status(&solver) == STAT_SAT) {
    // for formatting: 10 literals per line
    // use the prefix 'v ' after each line break
    k = 0;
    for (v=1; v<=nvars; v++) {
      if (var_is_assigned(&solver, v)) {
	l = var_is_true(&solver, v) ? v : -v;
	if (k == 0) printf("v");
	printf(" %d", l);
	k ++;
	if (k >= 10) {
	  printf("\n");
	  k = 0;
	}
      }
    }
    printf("\nv 0\n");
  }
}




/*
 * Signal handler: call print_results
 */
static void handler(int signum) {
  fprintf(stderr, "Interrupted by signal %d\n\n", signum);
  print_results();
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


int main(int argc, char* argv[]) {
  uint32_t verb;
  int resu;

  parse_command_line(argc, argv);

  alloc_buffer(200);
  resu = build_instance(input_filename, preprocess);
  delete_buffer();

  if (resu == OPEN_ERROR) {
    return YICES_EXIT_FILE_NOT_FOUND;
  } else if (resu == FORMAT_ERROR) {
    return YICES_EXIT_SYNTAX_ERROR;
  } else {
    if (verbose || stats) {
      construction_time = get_cpu_time();
      fprintf(stderr, "c\nc Construction time     : %.4f s\n", construction_time);
      print_solver_size(stderr, &solver);
    }
    if (seed_given) {
      nsat_set_random_seed(&solver, seed_value);
    }
    if (keep_lbd_given) {
      nsat_set_keep_lbd(&solver, keep_lbd);
    }
    if (reduce_fraction_given) {
      nsat_set_reduce_fraction(&solver, reduce_fraction);
    }
    if (stack_threshold_given) {
      nsat_set_stack_threshold(&solver, stack_threshold);
    }
    if (subsume_skip_given) {
      nsat_set_subsume_skip(&solver, subsume_skip);
    }
    if (var_elim_skip_given) {
      nsat_set_var_elim_skip(&solver, var_elim_skip);
    }
    if (res_clause_limit_given) {
      nsat_set_res_clause_limit(&solver, res_clause_limit);
    }
    verb = verbose ? 2 : stats ? 1 : 0;
    nsat_set_verbosity(&solver, verb);

    init_handler();
    nsat_set_randomness(&solver, 0);          // overwrite the default
    //    nsat_set_var_decay_factor(&solver, 0.94); // the default is 0.95

    if (data) {
      nsat_open_datafile(&solver, "xxxx.data");
    }
    (void) nsat_solve(&solver);
    print_results();
    if (model) {
      print_model();
    }

    delete_nsat_solver(&solver);

    return YICES_EXIT_SUCCESS;
  }
}
