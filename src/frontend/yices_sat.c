/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Parse a file in DIMACS/CNF format then call the sat solver.
 */

#if defined(CYGWIN) || defined(MINGW)
#ifndef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__ __declspec(dllexport)
#endif
#endif

#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include <signal.h>
#include <inttypes.h>

#include "solvers/cdcl/sat_solver.h"
#include "utils/cputime.h"
#include "utils/memsize.h"
#include "utils/command_line.h"

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
 * Buffer allocation
 */
#define MAX_CLAUSE_SIZE (UINT32_MAX/sizeof(literal_t))

static void alloc_buffer(uint32_t size) {
  assert(size <= MAX_CLAUSE_SIZE);
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
  assert(buffer_size > 0 && buffer_size <= MAX_CLAUSE_SIZE);
  buffer_size = 2 * buffer_size;
  if (buffer_size > MAX_CLAUSE_SIZE) {
    buffer_size = MAX_CLAUSE_SIZE;
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
    d = getc(f);
  } while (isspace(d));


  /*
   * Conversion: literal in sat_solver format = 2 * var + delta
   * where var = variable index in DIMACS format (between 1 and nv)
   *     delta = -2 if literal is positive in DIMACS format
   *     delta = -1 if literal is negative in DIMACS format
   * This works since yices variable index = DIMACS var - 1
   * and literal in yices format = 2 * (var index) + sign
   */
  delta = -2;
  var = 0;
  if (d == '-') {
    delta = -1;
    d = getc(f);
  }

  //else if (d == '+') {
  //    d = getc(f);
  //  }

  if (!isdigit(d)) {
    return BAD_INPUT;
  }

  do {
    var = 10 * var + (d - '0');
    d = getc(f);
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
 * returns 0 if no error occurred.
 * -1 means file could not be opened.
 * -2 means bad format in the input file.
 */
#define OPEN_ERROR -1
#define FORMAT_ERROR -2

static int build_instance(char *filename) {
  int l, n, c_idx, l_idx, literal;
  char *s;
  FILE *f;

  f = fopen(filename, "r");
  if (f == NULL) {
    perror(filename);
    return OPEN_ERROR;
  }

  s = fgets(line, MAX_LINE, f);
  l = 1; /* line number */

  if (s == NULL) {
    fprintf(stderr, "%s: empty file\n", filename);
    fclose(f);
    return FORMAT_ERROR;
  }

  /* skip empty lines and comments */
  while (*s == 'c' || *s == '\n') {
    s = fgets(line, MAX_LINE, f);
    l ++;

    if (s == NULL) {
      fprintf(stderr, "Format error: file %s, line %d\n", filename, l);
      fclose(f);
      return FORMAT_ERROR;
    }
  }

  /* read problem size */
  n = sscanf(s, "p cnf %d %d", &nvars, &nclauses);
  if (n != 2 || nvars < 0 || nclauses < 0) {
    fprintf(stderr, "Format error: file %s, line %d\n", filename, l);
    fclose(f);
    return FORMAT_ERROR;
  }

  /* initialize solver for nvars */
  init_sat_solver(&solver, nvars);
  sat_solver_add_vars(&solver, nvars);

  /* now read clauses and translate them */
  c_idx = 0;

  while (c_idx < nclauses) {
    l_idx = 0;
    for (;;) {
      literal = read_literal(f, nvars);
      if (literal < 0) break;

      if (l_idx >= buffer_size) expand_buffer();
      clause[l_idx] = literal;
      l_idx ++;
    }

    if (literal != END_OF_CLAUSE) {
      fprintf(stderr, "Format error: file %s\n", filename);
      fclose(f);
      return FORMAT_ERROR;
    }

    sat_solver_simplify_and_add_clause(&solver, l_idx, clause);
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
 * - seed_given = true if a seed is given on the command line
 *   seed_value = value of the seed
 */
static char *input_filename = NULL;
static bool verbose;
static bool model;
static bool seed_given;
static uint32_t seed_value;

enum {
  version_flag,
  help_flag,
  verbose_flag,
  model_flag,
  seed_opt,
};

#define NUM_OPTIONS (seed_opt+1)

static option_desc_t options[NUM_OPTIONS] = {
  { "version", 'V', FLAG_OPTION, version_flag },
  { "help", 'h', FLAG_OPTION, help_flag },
  { "verbose", 'v', FLAG_OPTION, verbose_flag },
  { "model", 'm', FLAG_OPTION, model_flag },
  { "seed", 's', MANDATORY_INT, seed_opt },
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
         "   --version, -V        Show version and exit\n"
         "   --help, -h           Print this message and exit\n"
         "   --model, -m          Show a model if the problem is satisfiable\n"
         "   --verbose, -v        Print statistics during the search\n"
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

      case model_flag:
        model = true;
        break;

      case verbose_flag:
        verbose = true;
        break;

      case seed_opt:
	seed_given = true;
	seed_value = elem.i_value;
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
static void show_stats(solver_stats_t *stat) {
  fprintf(stderr, "starts                  : %"PRIu32"\n", stat->starts);
  fprintf(stderr, "simplify db             : %"PRIu32"\n", stat->simplify_calls);
  fprintf(stderr, "reduce db               : %"PRIu32"\n", stat->reduce_calls);
  fprintf(stderr, "decisions               : %"PRIu64"\n", stat->decisions);
  fprintf(stderr, "random decisions        : %"PRIu64"\n", stat->random_decisions);
  fprintf(stderr, "propagations            : %"PRIu64"\n", stat->propagations);
  fprintf(stderr, "conflicts               : %"PRIu64"\n", stat->conflicts);
  fprintf(stderr, "lits in pb. clauses     : %"PRIu64"\n", stat->prob_literals);
  fprintf(stderr, "lits in learned clauses : %"PRIu64"\n", stat->learned_literals);
  fprintf(stderr, "total lits. in learned  : %"PRIu64"\n", stat->literals_before_simpl);
  fprintf(stderr, "subsumed lits.          : %"PRIu64"\n", stat->subsumed_literals);
  fprintf(stderr, "deleted pb. clauses     : %"PRIu64"\n", stat->prob_clauses_deleted);
  fprintf(stderr, "deleted learned clauses : %"PRIu64"\n", stat->learned_clauses_deleted);
  fprintf(stderr, "deleted binary clauses  : %"PRIu64"\n", stat->bin_clauses_deleted);
}


static void print_results(void) {
  solver_stats_t *stat;
  int resu;
  double mem_used;

  search_time = get_cpu_time() - construction_time;

  stat = &solver.stats;
  resu = solver.status;

  if (verbose) {
    show_stats(stat);
    fprintf(stderr, "Search time             : %.4f s\n", search_time);
    mem_used = mem_size() / (1024 * 1024);
    if (mem_used > 0) {
      fprintf(stderr, "Memory used             : %.2f MB\n", mem_used);
    }
    fprintf(stderr, "\n\n");
  }

  if (resu == status_sat) {
    printf("sat\n");
  } else if (resu == status_unsat) {
    printf("unsat\n");
  } else {
    printf("unknown\n");
  }
}


/*
 * Print initial size
 */
void print_solver_size(FILE *f, sat_solver_t *sol) {
  fprintf(f, "nb. of vars          : %"PRIu32"\n", sol->nb_vars);
  fprintf(f, "nb. of unit clauses  : %"PRIu32"\n", sol->nb_unit_clauses);
  fprintf(f, "nb. of bin clauses   : %"PRIu32"\n", sol->nb_bin_clauses);
  fprintf(f, "nb. of big clauses   : %"PRIu32"\n", sol->nb_clauses);
  fprintf(f, "nb. of assignments   : %"PRIu32"\n", sol->stack.top);
  fprintf(f, "clause increment     : %g\n", sol->cla_inc);
  fprintf(f, "inverse clause decay : %g\n", sol->inv_cla_decay);
  fprintf(f, "var increment        : %g\n", sol->heap.act_increment);
  fprintf(f, "inverse var decay    : %g\n\n", sol->heap.inv_act_decay);

}


/*
 * Print the solution if the problem is satisfiable.
 * Print the list of true literals terminated by 0
 *
 * For variable v = 0 to nvars - 1
 *   if val[v] == true then print +(v + 1) (positive literal)
 *   if val[v] == false then print -(v + 1) (negative literal)
 *   if val[v] == undef skip v
 *
 */
static void print_model(void) {
  int v;
  bval_t val;

  if (solver_status(&solver) == status_sat) {
    for (v = 0; v<nvars; v++) {
      val = get_variable_assignment(&solver, v);
      switch (val) {
      case val_false:
        printf("%d ", - (v + 1));
        break;
      case val_true:
        printf("%d ", (v + 1));
        break;
      case val_undef_false:
      case val_undef_true:
        break;
      }
    }
    printf("0\n");
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
#if INSTRUMENT_CLAUSES
  FILE *stats;
#endif
  int resu;

  parse_command_line(argc, argv);

  alloc_buffer(200);
  resu = build_instance(input_filename);
  delete_buffer();

  if (resu == OPEN_ERROR) {
    return YICES_EXIT_FILE_NOT_FOUND;
  } else if (resu == FORMAT_ERROR) {
    return YICES_EXIT_SYNTAX_ERROR;
  } else {
    if (verbose) {
      construction_time = get_cpu_time();
      fprintf(stderr, "Construction time    : %.4f s\n", construction_time);
      print_solver_size(stderr, &solver);
    }

    if (seed_given) {
      sat_solver_set_seed(&solver, seed_value);
    }

#if INSTRUMENT_CLAUSES
    stats = fopen("clauses.data", "w");
    if (stats == NULL) {
      fprintf(stderr, "Couldn't open the statistics file\n");
      perror("clauses.data");
      fflush(stderr);
      return YICES_EXIT_SYSTEM_ERROR;
    }

    init_learned_clauses_stats(stats);
#endif

    init_handler();
    (void) solve(&solver, verbose);
    print_results();
    if (model) {
      print_model();
    }

    delete_sat_solver(&solver);

#if INSTRUMENT_CLAUSES
    flush_learned_clauses_stats();
    fclose(stats);
#endif


    return YICES_EXIT_SUCCESS;
  }
}
