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
 * TEST OF THE SMT_CORE MODULE USED AS A (BOOLEAN) SAT SOLVER
 * - Same as test_core2 but uses a different restart strategy
 */

#include <stdio.h>
#include <stdbool.h>
#include <stdint.h>
#include <inttypes.h>
#include <ctype.h>
#include <signal.h>
#include <assert.h>

#include "solvers/cdcl/smt_core.h"
#include "utils/cputime.h"
#include "utils/int_vectors.h"
#include "utils/memalloc.h"
#include "utils/memsize.h"



/******************
 *   SAT SOLVER   *
 *****************/

/*
 * Descriptor for the null-theory
 */
static void do_nothing(void *t) {
}

static void null_backtrack(void *t, uint32_t back_level) {
}

static fcheck_code_t null_final_check(void *t) {
  return FCHECK_SAT;
}

static bool empty_propagate(void *t) {
  return true;
}

static th_ctrl_interface_t null_theory_ctrl = {
  do_nothing,       // start_internalization
  do_nothing,       // start_search
  empty_propagate,  // propagate
  null_final_check, // final_check
  do_nothing,       // increase_dlevel
  null_backtrack,   // backtrack
  do_nothing,       // push
  do_nothing,       // pop
  do_nothing,       // reset
  do_nothing,       // clear
};

static th_smt_interface_t null_theory_smt = {
  NULL,            // assert_atom
  NULL,            // expand explanation
  NULL,            // select polarity
  NULL,            // delete_atom
  NULL,            // end_deletion
};


/*
 * Heuristic parameters
 */
typedef struct core_param_s {
  /*
   * Restart heuristic: similar to PICOSAT or MINISAT
   *
   * If fast_restart is true:  PICOSAT-style
   * - inner restarts based on c_threshold
   * - outer restarts based on d_threshold
   *
   * If fast_restart: MINISAT style restarts
   * - c_threshold and c_factor are used
   * - d_threshold and d_factor are ignored
   * - to get periodic restart: make c_factor = 1.0
   */
  bool     fast_restart;    // enable PICOSAT-style restart
  uint32_t c_threshold;     // initial value of c_threshold
  uint32_t d_threshold;     // initial value of d_threshold
  double   c_factor;        // increase factor for next c_threshold
  double   d_factor;        // increase factor for next d_thershold

  /*
   * Clause-deletion heuristic
   * - initial reduce_threshold is max(r_threshold, num_prob_clauses * r_fraction)
   * - increase by r_factor on every outer restart provided reduce was called in that loop
   */
  uint32_t r_threshold;
  double   r_fraction;
  double   r_factor;
  float    clause_decay;   // decay factor for learned-clause activity

  /*
   * Branching heuristic
   */
  float    randomness;      // probability of a random pick in select_unassigned_literal
  double   var_decay;       // decay factor for variable activity

} core_param_t;



/*
 * Default parameters
 */
static core_param_t default_settings = {
  false, // MINISAT
  100,   // c_threshold
  100,   // d_threshold (unused)
  1.5,   // c_factor
  1.1,   // d_factor    (unused)

  1000,  // r_threshold
  0.25,  // r_fraction
  1.05,  // r_factor
  0.999F, // clause_decay (same default as in smt_core.h)

  0.02F,  // randomness
  0.95,   // var_decay
};





/*
 * Initialize core for pure SAT solving:
 * - n = number of boolean variables
 * (since index 0 is reserved for the boolean constant, the n variables
 *  are indexed from 1 to n)
 */
static void init_sat_solver(smt_core_t *core, uint32_t n) {
  init_smt_core(core, n+1, NULL, &null_theory_ctrl, &null_theory_smt, SMT_MODE_BASIC);
  add_boolean_variables(core, n);
}


/*
 * Bounded search: search until the conflict bound is reached
 * or until the problem is solved.
 * - reduce_threshold: number of learned clauses above which reduce_clause_database is called
 * - r_factor = increment factor for reduce threshold
 */
static void sat_search(smt_core_t *core, uint32_t conflict_bound, uint32_t *reduce_threshold, double r_factor) {
  uint64_t max_conflicts;
  uint32_t r_threshold;
  literal_t l;

  assert(smt_status(core) == STATUS_SEARCHING || smt_status(core) == YICES_STATUS_INTERRUPTED);

  max_conflicts = num_conflicts(core) + conflict_bound;
  r_threshold = *reduce_threshold;

  smt_process(core);
  while (smt_status(core) == STATUS_SEARCHING && num_conflicts(core) <= max_conflicts) {
    // reduce heuristic
    if (num_learned_clauses(core) >= r_threshold) {
      reduce_clause_database(core);
      r_threshold = (uint32_t) (r_threshold * r_factor);
    }

    // decision
    l = select_unassigned_literal(core);
    if (l == null_literal) {
      // all variables assigned: the problem is satisfiable
      end_search_sat(core);
      break;
    }
    // propagation
    decide_literal(core, l);
    smt_process(core);
  }

  *reduce_threshold = r_threshold;
}


/*
 * Print some statistic data + header if requested (on stdout)
 */
static void show_progress(smt_core_t *core,
			  uint32_t restart_threshold, uint32_t reduce_threshold, bool show_header) {

  if (show_header) {
    printf("---------------------------------------------------------------------------------\n");
    printf("|     Thresholds    |  Binary   |      Original     |          Learned          |\n");
    printf("|   Conf.      Del. |  Clauses  |   Clauses   Lits. |   Clauses  Lits. Lits/Cl. |\n");
    printf("---------------------------------------------------------------------------------\n");
  }

  printf("| %7"PRIu32"  %8"PRIu32" |  %8"PRIu32" | %8"PRIu32" %8"PRIu64" | %8"PRIu32" %8"PRIu64" %7.1f |\n",
	 restart_threshold, reduce_threshold,
	 num_binary_clauses(core),
	 num_prob_clauses(core), num_prob_literals(core),
	 num_learned_clauses(core), num_learned_literals(core),
	 ((double) num_learned_literals(core)/num_learned_clauses(core)));
  fflush(stdout);
}


/*
 * Full solver:
 * - params: heuristic parameters.
 *   If params is NULL, the default settings are used.
 * - verbose: if true, prints some data after each outer restart
 */
static void sat_solve(smt_core_t *core, core_param_t *params, bool verbose) {
  uint32_t c_threshold, d_threshold; // Picosat-style
  uint32_t reduce_threshold;

  assert(smt_status(core) == STATUS_IDLE);

  if (params == NULL) {
    params = &default_settings;
  }

  set_randomness(core, params->randomness);
  set_var_decay_factor(core, params->var_decay);
  set_clause_decay_factor(core, params->clause_decay);

  c_threshold = params->c_threshold;
  d_threshold = params->d_threshold;

  reduce_threshold = (uint32_t) (num_prob_clauses(core) * params->r_fraction);
  if (reduce_threshold < params->r_threshold) {
    reduce_threshold = params->r_threshold;
  }

  // initialize then do a propagation + simplification step.
  start_search(core, 0, NULL);
  smt_process(core);
  if (verbose) {
    show_progress(core, d_threshold, reduce_threshold, true);
  }

  if (smt_status(core) == STATUS_SEARCHING) {
    // loop
    for (;;) {
      sat_search(core, c_threshold, &reduce_threshold, params->r_factor);
      if (smt_status(core) != STATUS_SEARCHING) break;

      smt_restart(core);

      // inner restart: increase c_threshold
      c_threshold = (uint32_t) (c_threshold * params->c_factor);

      if (c_threshold >= d_threshold) {
	d_threshold = c_threshold;
	if (params->fast_restart) {
	  // outer restart: reset c_threshold and increase d_threshold
	  c_threshold = params->c_threshold;
	  d_threshold = (uint32_t) (d_threshold * params->d_factor);
	}

	if (verbose) {
	  show_progress(core, d_threshold, reduce_threshold, false);
	}
      }
    }
  }

  if (verbose) {
    printf("---------------------------------------------------------------------------------\n\n");
    fflush(stdout);
  }
}



/*
 * Check whether the unassignment is good (if result is SAT)
 */
static void validate_assignment(smt_core_t *core) {
  if (smt_status(core) == STATUS_SAT) {
    if (all_clauses_true(core)) {
      printf("\nModel looks correct\n");
    } else {
      printf("\nBUG: invalid model\n");
    }
    fflush(stdout);
  }
}





/*******************************
 *   PARSING OF DIMACS INPUT   *
 ******************************/

/*
 * Read a literal in DIMACS encoding from file f with nv variables
 * convert it to the Yices format.
 * - returns BAD_INPUT if an error occurs
 *   returns END_OF_CLAUSE if the dimacs integer read is 0.
 * - return a literal l between 2 and 2nv + 1 otherwise.
 */
#define BAD_INPUT -1
#define END_OF_CLAUSE -2

static literal_t read_literal(FILE *f, int nv) {
  int d, var, delta;

  do {
    d = getc(f);
  } while (isspace(d));


  /*
   * Conversion: literal in Yices format = 2 * var + delta
   * where var = variable index in DIMACS format (between 1 and nv)
   *     delta = 0 if the literal is positive in DIMACS format
   *     delta = 1 if the literal is negative in DIMACS format
   * example: dimacs -10 is neg_lit(10) = 21,
   *           dimacs 10 is pos_lit(10) = 20
   */
  delta = 0;
  var = 0;
  if (d == '-') {
    delta = 1;
    d = getc(f);
  }

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
 * Read a DIMACS formula from filename and initialize core accordingly
 * returns 0 if no error occurred
 * -1 means file could not be opened
 * -2 means bad format in the input file
 */
#define OPEN_ERROR -1
#define FORMAT_ERROR -2

// auxiliary buffer for the lines
#define MAX_LINE 1000
static char line[MAX_LINE];


static int build_instance(char *filename, smt_core_t *core) {
  int l, n, c_idx, literal, nvars, nclauses;
  char *s;
  FILE *f;
  ivector_t buffer;

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

  /* skip empty and comment lines */
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

  /* initialize core for nvars */
  init_sat_solver(core, nvars);

  /* initialize the clause buffer */
  init_ivector(&buffer, 10);

  /* now read the clauses and translate them */
  c_idx = 0;

  while (c_idx < nclauses) {
    for (;;) {
      literal = read_literal(f, nvars);
      if (literal < 0) break;
      ivector_push(&buffer, literal);
    }

    if (literal != END_OF_CLAUSE) {
      fprintf(stderr, "Format error: file %s\n", filename);
      fclose(f);
      return FORMAT_ERROR;
    }

    add_clause(core, buffer.size, buffer.data);
    c_idx ++;
    ivector_reset(&buffer);
  }

  delete_ivector(&buffer);
  fclose(f);

  return 0;
}








/*****************************
 *  PRINT DATA AND RESULTS   *
 ****************************/

/*
 *  Auxiliary function: get the basename of a file name
 *  (same as GNU version of basename)
 */
static char *basename(char *path) {
  char * ptr;

  // Check for empty path (should not happen)
  ptr = path;
  if (*ptr == '\0') return ptr;

  // Normal case: go to the end of path
  // then go back until separator '/' is found or ptr == path
  do {
    ptr ++;
  } while (*ptr != '\0');

  do {
    ptr --;
  } while (*ptr != '/' && ptr > path);

  if (*ptr == '/') ptr ++;

  return ptr;
}

/*
 * Name and size of the problem + core settings
 * and construction_time
 */
static void print_problem_size(FILE *f, smt_core_t *core, char *filename, double construction_time) {
  fprintf(f, "Problem: %s\n\n", basename(filename));
  fprintf(f, "Construction time       : %.4f s\n", construction_time);
  fprintf(f, "nb. of vars             : %"PRIu32"\n", num_vars(core));
  fprintf(f, "nb. of unit clauses     : %"PRIu32"\n", num_unit_clauses(core));
  fprintf(f, "nb. of bin clauses      : %"PRIu32"\n", num_binary_clauses(core));
  fprintf(f, "nb. of big clauses      : %"PRIu32"\n", num_prob_clauses(core));
  fprintf(f, "clause decay            : %g\n", clause_decay_factor(core));
  fprintf(f, "var decay               : %g\n", var_decay_factor(core));
  fprintf(f, "randomness factor       : %g\n\n", randomness_factor(core));
}


static void show_stats(dpll_stats_t *stat) {
  printf("restarts                : %"PRIu32"\n", stat->restarts);
  printf("simplify db             : %"PRIu32"\n", stat->simplify_calls);
  printf("reduce db               : %"PRIu32"\n", stat->reduce_calls);
  printf("decisions               : %"PRIu64"\n", stat->decisions);
  printf("random decisions        : %"PRIu64"\n", stat->random_decisions);
  printf("propagations            : %"PRIu64"\n", stat->propagations);
  printf("conflicts               : %"PRIu64"\n", stat->conflicts);
  printf("theory propagations     : %"PRIu32"\n", stat->th_props);
  printf("clauses from th. prop   : %"PRIu32"\n", stat->th_prop_lemmas);
  printf("theory conflicts        : %"PRIu32"\n", stat->th_conflicts);
  printf("clauses from conflicts  : %"PRIu32"\n", stat->th_conflict_lemmas);
  printf("lits in pb. clauses     : %"PRIu64"\n", stat->prob_literals);
  printf("lits in learned clauses : %"PRIu64"\n", stat->learned_literals);
  printf("total lits. in learned  : %"PRIu64"\n", stat->literals_before_simpl);
  printf("subsumed lits.          : %"PRIu64"\n", stat->subsumed_literals);
  printf("deleted pb. clauses     : %"PRIu64"\n", stat->prob_clauses_deleted);
  printf("deleted learned clauses : %"PRIu64"\n", stat->learned_clauses_deleted);
  printf("deleted binary clauses  : %"PRIu64"\n", stat->bin_clauses_deleted);
}


static const char * const status2string[] = {
  "idle", "searching", "unknown", "sat", "unsat", "interrupted",
  "<invalid status>",
};

static void print_status(FILE *f, smt_status_t s) {
  if (s > YICES_STATUS_INTERRUPTED) {
    s = YICES_STATUS_INTERRUPTED + 1;
  }
  fputs(status2string[s], f);
}


static void print_results(smt_core_t *core, double construction_time, double search_time) {
  dpll_stats_t *stat;
  double mem_used, simplified_percent;

  stat = &core->stats;
  show_stats(stat);
  printf("Search time             : %.4f s\n", search_time);
  mem_used = mem_size() / (1024 * 1024);
  if (mem_used > 0) {
    printf("Memory used             : %.2f MB\n", mem_used);
  }
  printf("\n\n");

  // Print status again, in format used by Leonardo's scripts
  print_status(stdout, smt_status(core));
  printf("\n");
  validate_assignment(core);
  printf("\n");

  simplified_percent = 0.0;
  if (stat->literals_before_simpl > 0) {
    simplified_percent = (100.0 * stat->subsumed_literals) / stat->literals_before_simpl;
  }
  printf("STAT %"PRIu64" %"PRIu64" %"PRIu64" %"PRIu32" %"PRIu64" %"PRIu64" %.2f %.2f %.2f\n",
	 stat->decisions,
	 stat->conflicts,
	 stat->propagations,
	 stat->restarts,
	 stat->literals_before_simpl,
	 stat->learned_literals,
	 mem_used,
	 (search_time + construction_time),
	 simplified_percent);

  fflush(stdout);
}




/***********************
 *  INTERRUPT HANDLER  *
 **********************/

/*
 * Need global variables here. They are used by the signal handler
 */
static smt_core_t solver;
static double construction_time;
static double search_time;


/*
 * Signal handler: call stop_search
 */
static void handler(int signum) {
  if (solver.status == STATUS_SEARCHING) {
    stop_search(&solver);
  }
}

/*
 * Set the signal handler: to print statistics on
 * SIGINT, SIGABRT, SIGXCPU
 */
static void init_handler(void) {
  signal(SIGINT, handler);
  signal(SIGABRT, handler);
#ifndef MINGW
  signal(SIGALRM, handler);
  signal(SIGXCPU, handler);
#endif
}



/*
 * Call solver on file given as an argument
 */
int main(int argc, char *argv[]) {
  int resu;

  if (argc != 2) {
    fprintf(stderr, "Usage: %s <input file>\n", argv[0]);
    exit(1);
  }

  resu = build_instance(argv[1], &solver);
  if (resu < 0) {
    exit(2);
  }

  construction_time = get_cpu_time();
  print_problem_size(stdout, &solver, argv[1], construction_time);
  init_handler();
  sat_solve(&solver, NULL, true);
  search_time = get_cpu_time() - construction_time;
  print_results(&solver, construction_time, search_time);

  delete_smt_core(&solver);

  return 0;
}
