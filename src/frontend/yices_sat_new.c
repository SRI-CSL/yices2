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

#include "io/reader.h"
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
 * Problem size + buffer for reading clauses
 */
static int nvars, nclauses;
static literal_t *clause;
static uint32_t buffer_size;


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
 * Read until the end of a line
 */
static void finish_line(reader_t *reader) {
  int x;

  do {
    x = reader_next_char(reader);
  } while (x != '\n' && x != EOF);
}


/*
 * Read a line and copy it in buffer and add '\0' at the end.
 * - when this function is called reader->current_char is the first
 *   character of the line.
 * - it the line has more than n-1 characters, then
 *   the first n-1 characteres are copied in buffer,
 *   the rest of the line is ignored.
 */
static void read_line(reader_t *reader, uint32_t n, char buffer[]) {
  uint32_t i;
  int x;

  assert(n > 0);

  n --;
  x = reader_current_char(reader);
  for (i=0; i<n; i++) {
    if (x == '\n' || x == EOF) {
      buffer[i] = '\0';  // end marker
      return;
    }
    buffer[i] = (char) x;
    x = reader_next_char(reader);
  }
  buffer[i] = '\0';
  finish_line(reader);
}



/*
 * Read a literal in DIMACS encoding and
 * convert it to the yices sat format.
 * - when this function is called, reader->current_char contains a
 *   character that may be part of the literal.
 * - nv = number of variables
 * - returns a negative number if an error occurs
 *   or if the integer read is 0.
 *   or a literal l between 0 and 2nv - 1 otherwise.
 */
#define BAD_INPUT -1
#define END_OF_CLAUSE -2

static literal_t read_literal(reader_t *reader, int32_t nv) {
  int d;
  int32_t var, delta;

  d = reader_current_char(reader);
  while (isspace(d)) {
    d = reader_next_char(reader);
  }

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
    d = reader_next_char(reader);
  }
  if (!isdigit(d)) {
    return BAD_INPUT;
  }

  do {
    var = 10 * var + (d - '0');
    d = reader_next_char(reader);
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

static int build_instance(const char *filename, bool pp) {
  int n, x, c_idx, l_idx, literal;
  reader_t reader;
  char pline[200];

  if (init_file_reader(&reader, filename) < 0) {
    // can't open the file
    perror(filename);
    return OPEN_ERROR;
  }

  // skip empty lines and comments
  for (;;) {
    x = reader_next_char(&reader);
    if (x == 'c') {
      finish_line(&reader);
      continue;
    } 
    if (x != '\n') break;
  }

  if (x == EOF) {
    fprintf(stderr, "file %s: line %"PRIu32": unexpected end of file\n", filename, reader_line(&reader));
    close_reader(&reader);
    return FORMAT_ERROR;
  }

  /* read problem size */
  read_line(&reader, 200, pline);
  n = sscanf(pline, "p cnf %d %d", &nvars, &nclauses);
  if (n != 2 || nvars < 0 || nclauses < 0) {
    fprintf(stderr, "file %s, line %"PRIu32": expected 'p cnf <nvars> <nclauses>\n", filename, reader_line(&reader));
    close_reader(&reader);
    return FORMAT_ERROR;
  }

  /* initialize solver for nvars */
  init_nsat_solver(&solver, nvars + 1, pp);
  nsat_solver_add_vars(&solver, nvars);

  /* now read clauses and translate them */
  c_idx = 0;
  while (c_idx < nclauses) {
    // some non-conforming benchmarks have 'c lines' interspersed with the 
    // clauses so we check and skip them here
    x = reader_next_char(&reader);
    if (x == 'c') {
      // not a clause
      finish_line(&reader);
    } else {
      l_idx = 0;
      for (;;) {
	literal = read_literal(&reader, nvars);
	if (literal < 0) break;
	if (l_idx >= (int)buffer_size) expand_buffer();
	clause[l_idx] = literal;
	l_idx ++;
      }

      if (literal != END_OF_CLAUSE) {
	fprintf(stderr, "file %s: line %"PRIu32": invalid format\n", filename, reader_line(&reader));
	close_reader(&reader);
	return FORMAT_ERROR;
      }

      nsat_solver_simplify_and_add_clause(&solver, l_idx, clause);
      c_idx ++;
    }
  }

  close_reader(&reader);

  return 0;
}



/*
 * Check whether clause a[0 .... n-1] is true in the solver's model
 */
static bool clause_is_true(uint32_t n, literal_t *a) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (lit_value(&solver, a[i]) == BVAL_TRUE) {
      return true;
    }
    if (lit_value(&solver, a[i]) != BVAL_FALSE) {
      fprintf(stderr, "BUG: the model does not assign a value to literal %"PRId32"\n", a[i]);
      exit(1);
    }
  }
  return false;
}

/*
 * Parse instance again and check whether all clauses are true in the solver's model.
 */
static void check_model(const char *filename) {
  int n, x, c_idx, l_idx, literal;
  reader_t reader;
  char pline[200];

  if (init_file_reader(&reader, filename) < 0) {
    // can't open the file
    fprintf(stderr, "can't check model: ");
    perror(filename);
    return;
  }

  // skip empty lines and comments
  for (;;) {
    x = reader_next_char(&reader);
    if (x == 'c') {
      finish_line(&reader);
      continue;
    } 
    if (x != '\n') break;
  }

  if (x == EOF) {
    fprintf(stderr, "can't check model: file %s: line %"PRIu32": unexpected end of file\n", filename, reader_line(&reader));
    goto done;
  }

  /* read problem size */
  read_line(&reader, 200, pline);
  n = sscanf(pline, "p cnf %d %d", &nvars, &nclauses);
  if (n != 2 || nvars < 0 || nclauses < 0) {
    fprintf(stderr, "can't check model: file %s: line %"PRIu32": expected 'p cnf <nvars> <nclauses>\n", filename, reader_line(&reader));
    goto done;
  }

  /* now read clauses and translate them */
  c_idx = 0;
  while (c_idx < nclauses) {
    // some non-conforming benchmarks have 'c lines' interspersed with the 
    // clauses so we check and skip them here
    x = reader_next_char(&reader);
    if (x == 'c') {
      // not a clause
      finish_line(&reader);
    } else {
      l_idx = 0;
      for (;;) {
	literal = read_literal(&reader, nvars);
	if (literal < 0) break;
	if (l_idx >= (int)buffer_size) expand_buffer();
	clause[l_idx] = literal;
	l_idx ++;
      }

      if (literal != END_OF_CLAUSE) {
	fprintf(stderr, "error in check model: file %s: line %"PRIu32": invalid format\n", filename, reader_line(&reader));
	goto done;
      }

      if (!clause_is_true(l_idx, clause)) {
	fprintf(stderr, "error in check model: clause %"PRIu32" is false (line %"PRIu32")\n", c_idx, reader_line(&reader));	
	goto done;
      }
      c_idx ++;
    }
  }
  printf("model looks correct\n");

 done:
  close_reader(&reader);
}


/*
 * COMMAND-LINE OPTIONS
 */

/*
 * Parameter:
 * - input_filename = name of the input file
 * - verbose = true for verbose output
 * - model = true for produce model (if SAT)
 * - check = true to force checking of the model
 * - preprocess = true to enable preprocessing
 * - seed_given = true if a seed is given on the command line
 *   seed_value = value of the seed
 * - stats = true for printing statistics
 * - data = true for collecting data
 */
static char *input_filename = NULL;
static bool verbose;
static bool model;
static bool check;
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
  check_flag,
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
  { "check", 'c', FLAG_OPTION, check_flag },
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
	 "   --check, -c             Verify the model if the problem is satisfiable\n"
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
  check = false;
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

      case check_flag:
        check = true;
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

  fprintf(stderr, "starts                  : %"PRIu32"\n", stat->starts);
  fprintf(stderr, "simplify db             : %"PRIu32"\n", stat->simplify_calls);
  fprintf(stderr, "reduce db               : %"PRIu32"\n", stat->reduce_calls);
  fprintf(stderr, "scc calls               : %"PRIu32"\n", stat->subst_calls);
  fprintf(stderr, "substituted vars        : %"PRIu32"\n", stat->subst_vars);
  fprintf(stderr, "decisions               : %"PRIu64"\n", stat->decisions);
  fprintf(stderr, "random decisions        : %"PRIu64"\n", stat->random_decisions);
  fprintf(stderr, "propagations            : %"PRIu64"\n", stat->propagations);
  fprintf(stderr, "conflicts               : %"PRIu64"\n", stat->conflicts);
  fprintf(stderr, "lits in pb. clauses     : %"PRIu32"\n", solver->pool.num_prob_literals);
  fprintf(stderr, "lits in learned clauses : %"PRIu32"\n", solver->pool.num_learned_literals);
  fprintf(stderr, "subsumed lits.          : %"PRIu64"\n", stat->subsumed_literals);
  fprintf(stderr, "deleted pb. clauses     : %"PRIu64"\n", stat->prob_clauses_deleted);
  fprintf(stderr, "deleted learned clauses : %"PRIu64"\n\n", stat->learned_clauses_deleted);
  fprintf(stderr, "\n");
}

static void print_results(void) {
  solver_status_t result;
  double mem_used;
  double speed;

  search_time = get_cpu_time() - construction_time;
  result = solver.status;

  if (verbose || stats) {
    show_stats(&solver);
    fprintf(stderr, "Search time             : %.4f s\n", search_time);
    mem_used = mem_size() / (1024 * 1024);
    if (mem_used > 0) {
      fprintf(stderr, "Memory used             : %.2f MB\n", mem_used);
    }
    speed = solver.stats.propagations/search_time;
    fprintf(stderr, "Speed                   : %.2f prop/s\n", speed);
    fprintf(stderr, "\n\n");
  }

  switch (result) {
  case STAT_UNSAT:
    printf("unsat\n\n");
    break;

  case STAT_SAT:
    printf("sat\n\n");
    break;

  default:
    printf("unkown\n\n");
    break;
  }
}


/*
 * Print initial size
 */
void print_solver_size(FILE *f, sat_solver_t *sol) {
  fprintf(f, "nb. of vars          : %"PRIu32"\n", sol->nvars);
  fprintf(f, "nb. of unit clauses  : %"PRIu32"\n", sol->units);
  fprintf(f, "nb. of bin clauses   : %"PRIu32"\n", sol->binaries);
  fprintf(f, "nb. of big clauses   : %"PRIu32"\n", sol->pool.num_prob_clauses);
  fprintf(f, "nb. of assignments   : %"PRIu32"\n\n", sol->stack.top);
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
  int v;
  bval_t val;

  if (nsat_status(&solver) == STAT_SAT) {
    for (v = 1; v<=nvars; v++) {
      val = var_value(&solver, v);
      switch (val) {
      case BVAL_FALSE:
        printf("-%"PRIu32" ", v);
        break;
      case BVAL_TRUE:
        printf("%"PRIu32" ", v);
        break;
      case BVAL_UNDEF_FALSE:
      case BVAL_UNDEF_TRUE:
        break;
      }
    }
    printf("0\n");
  }
}


/*
 * Check the model if any (reread the file)
 */
static void do_check(const char* filename) {
  if (nsat_status(&solver) == STAT_SAT) {
    alloc_buffer(200);
    check_model(filename);
    delete_buffer();
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
      fprintf(stderr, "Construction time    : %.4f s\n", construction_time);
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
    nsat_set_var_decay_factor(&solver, 0.94); // the default is 0.95

    if (data) {
      nsat_open_datafile(&solver, "xxxx.data");
    }
    (void) nsat_solve(&solver);
    print_results();
    if (model) {
      print_model();
    }
    if (check) {
      do_check(input_filename);
    }

    delete_nsat_solver(&solver);

    return YICES_EXIT_SUCCESS;
  }
}
