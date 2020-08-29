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
#include <errno.h>
#include <math.h>

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
 *   the first n-1 characters are copied in buffer,
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
    if (lit_value(&solver, a[i]) == VAL_TRUE) {
      return true;
    }
    if (lit_value(&solver, a[i]) != VAL_FALSE) {
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

static bool var_decay_given;
static bool clause_decay_given;
static bool randomness_given;
static bool stack_threshold_given;
static bool keep_lbd_given;
static bool reduce_fraction_given;
static bool reduce_interval_given;
static bool reduce_delta_given;
static bool restart_interval_given;
static bool subsume_skip_given;
static bool var_elim_skip_given;
static bool res_clause_limit_given;
static bool res_extra_given;
static bool simplify_interval_given;
static bool simplify_bin_delta_given;

static double var_decay;
static double clause_decay;
static double randomness;
static uint32_t stack_threshold;
static uint32_t keep_lbd;
static uint32_t reduce_fraction;
static uint32_t reduce_interval;
static uint32_t reduce_delta;
static uint32_t restart_interval;
static uint32_t subsume_skip;
static uint32_t var_elim_skip;
static uint32_t res_clause_limit;
static uint32_t res_extra;
static uint32_t simplify_interval;
static uint32_t simplify_bin_delta;

enum {
  version_flag,
  help_flag,
  help_params_flag,
  verbose_flag,
  model_flag,
  check_flag,
  preprocess_flag,
  seed_opt,
  stats_flag,

  var_decay_opt,
  clause_decay_opt,
  randomness_opt,
  stack_threshold_opt,
  keep_lbd_opt,
  reduce_fraction_opt,
  reduce_interval_opt,
  reduce_delta_opt,
  restart_interval_opt,
  subsume_skip_opt,
  var_elim_skip_opt,
  res_clause_limit_opt,
  res_extra_opt,
  simplify_interval_opt,
  simplify_bin_delta_opt,
  data_flag,
};

#define NUM_OPTIONS (data_flag+1)

static option_desc_t options[NUM_OPTIONS] = {
  { "version", 'V', FLAG_OPTION, version_flag },
  { "help", 'h', FLAG_OPTION, help_flag },
  { "help-params", '\0', FLAG_OPTION, help_params_flag },
  { "verbose", 'v', FLAG_OPTION, verbose_flag },
  { "model", 'm', FLAG_OPTION, model_flag },
  { "check", 'c', FLAG_OPTION, check_flag },
  { "preprocess", 'p', FLAG_OPTION, preprocess_flag },
  { "seed", 's', MANDATORY_INT, seed_opt },
  { "stats", '\0', FLAG_OPTION, stats_flag },

  { "var-decay", '\0', MANDATORY_FLOAT, var_decay_opt },
  { "clause-decay", '\0', MANDATORY_FLOAT, clause_decay_opt },
  { "randomness", '\0', MANDATORY_FLOAT, randomness_opt },
  { "stack-threshold", '\0', MANDATORY_INT, stack_threshold_opt },
  { "keep-lbd", '\0', MANDATORY_INT, keep_lbd_opt },
  { "reduce-fraction", '\0', MANDATORY_INT, reduce_fraction_opt },
  { "reduce-interval", '\0', MANDATORY_INT, reduce_interval_opt },
  { "reduce-delta", '\0', MANDATORY_INT, reduce_delta_opt },
  { "restart-interval", '\0', MANDATORY_INT, restart_interval_opt },
  { "subsume-skip", '\0', MANDATORY_INT, subsume_skip_opt },
  { "var-elim-skip", '\0', MANDATORY_INT, var_elim_skip_opt },
  { "res-clause-limit", '\0', MANDATORY_INT, res_clause_limit_opt },
  { "res-extra", '\0', MANDATORY_INT, res_extra_opt },
  { "simplify-interval", '\0', MANDATORY_INT,  simplify_interval_opt },
  { "simplify-bin-delta", '\0', MANDATORY_INT, simplify_bin_delta_opt },

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
         "   --help-params           List solver parameters that can be set on the command line\n"
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

static void print_parameters(char *progname) {
  printf("Branching heuristics\n"
	 "   --randomness=<float>           Fraction of random decision (between 0.0 and 1.0)\n"
	 "\n"
	 "Clause deletion\n"
	 "   --clause-decay=<float>         Number between 0.0 and 1.0\n"
	 "   --keep-lbd=<integer>           Never delete learned clauses with this lbd of lower\n"
	 "   --reduce-fraction=<integer>    Fraction of learned clauses to remove (0 to 32)\n"
	 "   --reduce-interval=<integer>    How often to delete learned clauses\n"
	 "   --reduce-delta=<integer>       Increment to the reduce interval\n"
	 "\n"
	 "Restart\n"
	 "   --restart-interval=<inteeger>  Minimal number of conflicts between restarts\n"
	 "\n"
	 "Preprocessing\n"
	 "   --subsume-skip=<integer>       Skip clauses of that length or more in subsumption\n"
	 "   --var-elim-skip=<integer>      Don't try to eliminate variables that occur in many clauses\n"
	 "   --res-clause-limit=<integer>   Don't create clauses bigger than this during variable elimination\n"
	 "   --res-extra=<integer>          Allow variable eliminations that incresae the number of clauses\n"
	 "\n"
	 "Simplification\n"
	 "   --simplify-interval=<integer>   Number of conflicts between simplification\n"
	 "   --simplify-bin-delta=<integer>  Number of new binary clauses between SCC computations\n"
	 "\n"
	 "Not used anymore\n"
         "   --var-decay=<float>\n"
         "   --stack-threshold=<integer>\n"
	 "   --data\n"
	 "\n");
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

  var_decay_given = false;
  clause_decay_given = false;
  randomness_given = false;
  stack_threshold_given = false;
  keep_lbd_given = false;
  reduce_fraction_given = false;
  reduce_interval_given = false;
  reduce_delta_given = false;
  restart_interval_given = false;
  subsume_skip_given = false;
  var_elim_skip_given = false;
  res_clause_limit_given = false;
  res_extra_given = false;
  simplify_interval_given = false;
  simplify_bin_delta_given = false;

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

      case help_params_flag:
	print_parameters(parser.command_name);
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

      case var_decay_opt:
	// must be in [0.0, 1.1]
	if (! validate_double_option(&parser, &elem, 0.0, false, 1.0, false)) goto bad_usage;
	var_decay_given = true;
	var_decay = elem.d_value;
	break;

      case clause_decay_opt:
	// must be in [0.0, 1.1]
	if (! validate_double_option(&parser, &elem, 0.0, false, 1.0, false)) goto bad_usage;
	clause_decay_given = true;
	clause_decay = elem.d_value;
	break;

      case randomness_opt:
	// must be in [0.0, 1.1]
	if (! validate_double_option(&parser, &elem, 0.0, false, 1.0, false)) goto bad_usage;
	randomness_given = true;
	randomness = elem.d_value;
	break;

      case stack_threshold_opt:
	// must be >=0
	if (! validate_integer_option(&parser, &elem, 0, INT32_MAX)) goto bad_usage;
	stack_threshold_given = true;
	stack_threshold = elem.i_value;
	break;

      case keep_lbd_opt:
	// must be >= 0
	if (! validate_integer_option(&parser, &elem, 0, INT32_MAX)) goto bad_usage;
	keep_lbd_given = true;
	keep_lbd = elem.i_value;
	break;

      case reduce_fraction_opt:
	// range: [0, 32]
	if (! validate_integer_option(&parser, &elem, 0, 32)) goto bad_usage;
	reduce_fraction_given = true;
	reduce_fraction = elem.i_value;
	break;

      case reduce_interval_opt:
	// must be positive
	if (! validate_integer_option(&parser, &elem, 1, INT32_MAX)) goto bad_usage;
	reduce_interval_given = true;
	reduce_interval = elem.i_value;
	break;

      case reduce_delta_opt:
	if (! validate_integer_option(&parser, &elem, 1, INT32_MAX)) goto bad_usage;
	reduce_delta_given = true;
	reduce_delta = elem.i_value;
	break;

      case restart_interval_opt:
	if (! validate_integer_option(&parser, &elem, 1, INT32_MAX)) goto bad_usage;
	restart_interval_given = true;
	restart_interval = elem.i_value;
	break;

      case subsume_skip_opt:
	if (! validate_integer_option(&parser, &elem, 0, INT32_MAX)) goto bad_usage;
	subsume_skip_given = true;
	subsume_skip = elem.i_value;
	break;

      case var_elim_skip_opt:
	if (! validate_integer_option(&parser, &elem, 0, INT32_MAX)) goto bad_usage;
	var_elim_skip_given = true;
	var_elim_skip = elem.i_value;
	break;

      case res_clause_limit_opt:
	if (! validate_integer_option(&parser, &elem, 0, INT32_MAX)) goto bad_usage;
	res_clause_limit_given = true;
	res_clause_limit = elem.i_value;
	break;

      case res_extra_opt:
	res_extra_given = true;
	res_extra = elem.i_value;
	break;

      case simplify_interval_opt:
	if (! validate_integer_option(&parser, &elem, 1, INT32_MAX)) goto bad_usage;
	simplify_interval_given = true;
	simplify_interval = elem.i_value;
	break;

      case simplify_bin_delta_opt:
	if (! validate_integer_option(&parser, &elem, 1, INT32_MAX)) goto bad_usage;
	simplify_bin_delta_given = true;
	simplify_bin_delta = elem.i_value;
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

/*
 * printf/fprintf are not safe to use in a signal handler
 * so we use write to 1 (stdout) or 2 (stderr) instead.
 */
static void do_write(int fd, const char *buffer, uint32_t n) {
  uint32_t i;
  ssize_t w;

  i = 0;
  while (n > 0) {
    do {
      w = write(fd, buffer + i, n);
    } while (w < 0 && errno == EAGAIN);
    if (w < 0) break; // write ERROR. We can't do much about it.
    i += (uint32_t) w;
    n -= (uint32_t) w;
  }
}

/*
 * Reverse b[0 ... n-1]
 */
static void reverse(char *b, uint32_t n) {
  uint32_t i, j;
  char c;

  assert(n > 0);
  i = 0;
  j = n-1;
  while (i < j) {
    c =  b[i]; b[i] = b[j]; b[j] = c;
    i ++;
    j --;
  }
}

/*
 * Store digits of x in b  then return the number of digits.
 * - b must be large enough to store all the digits
 *   (2^64 - 1 has 20 digits).
 */
static uint32_t digits_of_uint(char *b, uint64_t x) {
  uint32_t n, d;

  n = 0;
  do {
    d = x % 10;
    x = x/10;
    b[n] = (char) (d + '0');
    n ++;
  } while (x > 0);

  reverse(b, n);

  return n;
}

// print nd digits for x. padd with '0' if needed
// x must be less than 10^d
static void digits_of_frac(char *b, uint64_t x, uint32_t nd) {
  uint32_t i, d;

  for (i=0; i<nd; i++) {
    d = x % 10;
    x = x/10;
    b[i] = (char) (d + '0');
  }
  reverse(b, nd);
}

static double scale[5] = { 1.0, 10.0, 100.0, 1000.0, 10000.0 };

// for a floating point x, d = number of digits after the '.'
// d must be between 0 and 4, x must be non-negative
static uint32_t digits_of_float(char *b, double x, uint32_t d) {
  double f;
  uint64_t p;
  uint32_t n;

  assert(0 <= d && d <= 4);

  p = (uint64_t) x;       // integral part
  f = (x - p) * scale[d]; // fractional part * 10^d

  if (d == 0) {
    if (f > 0.5) p ++;
    n = digits_of_uint(b, p);
  } else {
    n = digits_of_uint(b, p);
    b[n] = '.';
    n ++;
    p = (uint64_t) f;
    if (f - p > 0.5) p ++;
    digits_of_frac(b + n, p, d);
    n += d;
  }

  return n;
}

static char buffer[1000];

static void writeln(int fd) {
  buffer[0] = '\n';
  do_write(fd, buffer, 1);
}

static void write_line(int fd, const char* s) {
  uint32_t n;

  n = strlen(s);
  assert(n < 999);
  memcpy(buffer, s, n);
  buffer[n] = '\n';
  do_write(fd, buffer, n+1);
}

static void write_line_and_uint(int fd, const char *s, uint64_t x) {
  uint32_t n;

  n = strlen(s);
  memcpy(buffer, s, n);
  n += digits_of_uint(buffer + n, x);
  buffer[n] = '\n';
  do_write(fd, buffer, n+1);
}

// print something equivalent to printf("%s %.<d>f %s\n", s, x, unit)
static void write_line_and_float(int fd, const char *s, double x, uint32_t d, const char *unit) {
  uint32_t n, p;

  n = strlen(s);
  memcpy(buffer, s, n);
  n += digits_of_float(buffer + n, x, d);
  p = strlen(unit);
  memcpy(buffer + n, unit, p);
  buffer[n+p] = '\n';
  do_write(fd, buffer, n+p+1);
}


static void show_stats(sat_solver_t *solver) {
  solver_stats_t *stat = &solver->stats;

  write_line(2, "c");
  write_line(2, "c Statistics");
  write_line_and_uint(2, "c  starts                  : ", stat->starts);
  write_line_and_uint(2, "c  stabilizations          : ", stat->stabilizations);
  write_line_and_uint(2, "c  simplify db             : ", stat->simplify_calls);
  write_line_and_uint(2, "c  reduce db               : ", stat->reduce_calls);
  write_line_and_uint(2, "c  scc calls               : ", stat->scc_calls);
  write_line_and_uint(2, "c  apply subst calls       : ", stat->subst_calls);
  write_line_and_uint(2, "c  probings                : ", stat->probe_calls);
  write_line_and_uint(2, "c  substituted vars        : ", stat->subst_vars);
  write_line_and_uint(2, "c  decisions               : ", stat->decisions);
  write_line_and_uint(2, "c  random decisions        : ", stat->random_decisions);
  write_line_and_uint(2, "c  propagations            : ", stat->propagations);
  write_line_and_uint(2, "c  conflicts               : ", stat->conflicts);
  write_line_and_uint(2, "c  local subsumptions      : ", stat->local_subsumptions);
  write_line_and_uint(2, "c  probed literals         : ", stat->probed_literals);
  write_line_and_uint(2, "c  failed literals         : ", stat->failed_literals);
  write_line_and_uint(2, "c  probing progatations    : ", stat->probing_propagations);
  write_line_and_uint(2, "c  max_depth               : ", solver->max_depth);
  write_line_and_uint(2, "c  lits in pb. clauses     : ", solver->pool.num_prob_literals);
  write_line_and_uint(2, "c  lits in learned clauses : ", solver->pool.num_learned_literals);
  write_line_and_uint(2, "c  subsumed lits.          : ", stat->subsumed_literals);
  write_line_and_uint(2, "c  deleted pb. clauses     : ", stat->prob_clauses_deleted);
  write_line_and_uint(2, "c  deleted learned clauses : ", stat->learned_clauses_deleted);
  write_line(2, "c");
}


static void print_results(void) {
  solver_status_t result;
  double mem_used;
  double speed;

  search_time = get_cpu_time() - construction_time;
  result = solver.status;

  if (verbose || stats) {
    show_stats(&solver);
    write_line_and_float(2, "c Search time              : ", search_time, 4, " s");
    mem_used = mem_size() / (1024 * 1024);
    if (mem_used > 0) {
      write_line_and_float(2, "c Memory used              : ", mem_used, 2, " MB");
    }
    if (search_time > 0.0001) {
      // if search_time is close to 0, this speed is meaningless.
      speed = solver.stats.propagations/search_time;
      write_line_and_float(2, "c Speed                    : ", speed, 2, " prop/s");
    }
    write_line(2, "c");
  }

  switch (result) {
  case STAT_UNSAT:
    write_line(1, "s UNSATISFIABLE");
    break;

  case STAT_SAT:
    write_line(1, "s SATISFIABLE");
    break;

  default:
    write_line(1, "s UNKNOWN");
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
  write_line_and_uint(2, "c Interrupted by signal ", signum);
  writeln(2);
  print_results();
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
    nsat_set_randomness(&solver, 0);          // overwrite the default

    if (seed_given) nsat_set_random_seed(&solver, seed_value);
    if (var_decay_given) nsat_set_var_decay_factor(&solver, var_decay);
    if (clause_decay_given) nsat_set_clause_decay_factor(&solver, clause_decay);
    if (randomness_given) nsat_set_randomness(&solver, randomness);
    if (stack_threshold_given) nsat_set_stack_threshold(&solver, stack_threshold);
    if (keep_lbd_given) nsat_set_keep_lbd(&solver, keep_lbd);
    if (reduce_fraction_given) nsat_set_reduce_fraction(&solver, reduce_fraction);
    if (reduce_interval_given) nsat_set_reduce_interval(&solver, reduce_interval);
    if (reduce_delta_given) nsat_set_reduce_delta(&solver, reduce_delta);
    if (restart_interval_given) nsat_set_restart_interval(&solver, restart_interval);
    if (subsume_skip_given) nsat_set_subsume_skip(&solver, subsume_skip);
    if (var_elim_skip_given) nsat_set_var_elim_skip(&solver, var_elim_skip);
    if (res_clause_limit_given) nsat_set_res_clause_limit(&solver, res_clause_limit);
    if (res_extra_given) nsat_set_res_extra(&solver, res_extra);
    if (simplify_interval_given) nsat_set_simplify_interval(&solver, simplify_interval);
    if (simplify_bin_delta_given) nsat_set_simplify_bin_delta(&solver, simplify_bin_delta);

    verb = verbose ? 2 : stats ? 1 : 0;
    nsat_set_verbosity(&solver, verb);

    init_handler();

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
