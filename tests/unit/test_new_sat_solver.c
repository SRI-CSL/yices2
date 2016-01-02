/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Test of clause pool
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <inttypes.h>
#include <ctype.h>
#include <assert.h>

#include "solvers/cdcl/new_sat_solver.h"
#include "utils/cputime.h"
#include "utils/memsize.h"


/*
 * GLOBALS
 */

/*
 * Array to read one line of the input file
 */
#define MAX_LINE 1000
static char line[MAX_LINE];

/*
 * Problem size + buffer for reading clauses
 */
static uint32_t nvars, nclauses;
static literal_t *clause;
static uint32_t buffer_size;

/*
 * Solver
 */
static sat_solver_t solver;
static double construction_time, simplification_time;
static double memory_size;


/*
 * DIMACS PARSER
 */

/*
 * Read until the end of the line
 */
static void finish_line(FILE *f) {
  int c;

  do {
    c = getc_unlocked(f);
  } while (c != '\n');
}


/*
 * Buffer allocation
 */
#define MAX_BUFFER_SIZE (UINT32_MAX/sizeof(literal_t))

static void alloc_buffer(uint32_t size) {
  assert(size <= MAX_BUFFER_SIZE);
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
  assert(buffer_size > 0 && buffer_size <= MAX_BUFFER_SIZE);
  buffer_size = 2 * buffer_size;
  if (buffer_size > MAX_BUFFER_SIZE) {
    buffer_size = MAX_BUFFER_SIZE;
  }

  clause = realloc(clause, buffer_size * sizeof(literal_t));
  if (clause == NULL) {
    fprintf(stderr, "Out of memory\n");
    exit(2);
  }
}

static void delete_buffer(void) {
  free(clause);
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
enum {
  BAD_INPUT = -1,
  END_OF_CLAUSE = -2
};

static int32_t read_literal(FILE *f, uint32_t nv) {
  int d;
  int32_t var, delta;

  do {
    d = getc_unlocked(f);
  } while (isspace(d));

  /*
   * Conversion: literal in Yices format = 2 * var + delta
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
    d = getc_unlocked(f);
  }

  if (!isdigit(d)) {
    return BAD_INPUT;
  }

  do {
    var = 10 * var + (d - '0');
    d = getc_unlocked(f);
  } while (isdigit(d) && var <= nv);

  if (var == 0) {
    return END_OF_CLAUSE;
  } else if (var <= nv) {
    return 2 * var + delta;
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
enum {
  OPEN_ERROR = -1,
  FORMAT_ERROR = -2
};

static int32_t build_instance(char *filename) {
  uint32_t i, j, l;
  int32_t literal;
  int n, nv, nc;
  char *s;
  FILE *f;

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
  n = sscanf(s, "p cnf %d %d", &nv, &nc);
  if (n != 2 || nv < 0 || nc < 0) {
    fprintf(stderr, "Format error: file %s, line %d\n", filename, l);
    fclose(f);
    return FORMAT_ERROR;
  }
  nvars = nv;
  nclauses = nc;

  /* initialize the solver */
  init_nsat_solver(&solver, nvars + 1);
  nsat_solver_add_vars(&solver, nvars);
  
  /* now read clauses and translate them */
  alloc_buffer(200);
  i = 0;
  while (i < nclauses) {
    j = 0;
    for (;;) {
      literal = read_literal(f, nvars);
      if (literal < 0) break;

      if (j >= buffer_size) expand_buffer();
      clause[j] = literal;
      j ++;
    }
    if (literal != END_OF_CLAUSE) {
      fprintf(stderr, "Format error: file %s\n", filename);
      fclose(f);
      return FORMAT_ERROR;
    }
    nsat_solver_simplify_and_add_clause(&solver, j, clause);
    i ++;
  }
  delete_buffer();

  fclose(f);

  return 0;
}


/*
 * Convert array size to mega bytes (for an array of 32bit integers)
 */
static double mb(uint32_t n) {
  return (double) (n * sizeof(uint32_t)) / (1024 * 1024);
}


/*
 * Estimate of the memory used by the variables/literal arrays
 * (including heap + stack). The estimate is for 64bit architectures.
 * - n = number of variables.
 *
 * For each variable x we have:
 * - value[x]: 8 bits
 * - ante_tag[x]: 8 bits
 * - ante_data[x]: 32 bits
 * - level[x]: 32 bits
 * - watch[pos(x)]: 64 bits
 * - watch[neg(x)]: 64 bits
 * - heap.activity[x]: 64 bits
 * - heap.heap_index[x]: 32 bits
 * - a spot in heap.heap: 32 bits
 * - a spot in stack.lit: 32 bits
 *
 * Total: 336 bits = 84 bytes
 */
static double mem_for_vars(uint32_t n) {
  return (double) (n * 84)/ (1024 * 1024);
}


/*
 * Total size and capacity of all watch vectors
 */
static uint32_t watch_sizes(sat_solver_t *solver) {
  watch_t *tmp;
  uint32_t s, i, n;

  s = 0;
  n = solver->nliterals;
  for (i=0; i<n; i++) {
    tmp = solver->watch[i];
    if (tmp != NULL) {
      s += tmp->size;
    }
  }
  return s;
}

static uint32_t watch_capacities(sat_solver_t *solver) {
  watch_t *tmp;
  uint32_t s, i, n;

  s = 0;
  n = solver->nliterals;
  for (i=0; i<n; i++) {
    tmp = solver->watch[i];
    if (tmp != NULL) {
      s += tmp->capacity;
    }
  }
  return s;
}

/*
 * Estimate the memory used by watch vectors
 */
static double mem_for_watches(sat_solver_t *solver) {
  return (double) (watch_capacities(solver) * sizeof(uint32_t))/(1024 * 1024);
}

/*
 * Print problem size
 */
static void print_statistics(FILE *f) {
  fprintf(f, "nb. of variables        : %"PRIu32"\n", nvars);
  fprintf(f, "nb. of clauses          : %"PRIu32"\n", nclauses);
  fprintf(f, "\n");
  fprintf(f, "nb. of vars             : %"PRIu32"\n", solver.nvars);
  fprintf(f, "nb. of unit clauses     : %"PRIu32"\n", solver.units);
  fprintf(f, "nb. of bin  clauses     : %"PRIu32"\n", solver.binaries);
  fprintf(f, "nb. of prob clauses     : %"PRIu32"\n", solver.pool.num_prob_clauses);
  fprintf(f, "nb. of prob literals    : %"PRIu32"\n", solver.pool.num_prob_literals);
  fprintf(f, "nb. of learned clauses  : %"PRIu32"\n", solver.pool.num_learned_clauses);
  fprintf(f, "nb. of learned literals : %"PRIu32"\n", solver.pool.num_learned_literals);
  fprintf(f, "\n");
  fprintf(f, "solver vsize            : %"PRIu32"\n", solver.vsize);
  fprintf(f, "solver lsize            : %"PRIu32"\n", solver.lsize);
  fprintf(f, "watchers                : %"PRIu32"\n", watch_sizes(&solver));
  fprintf(f, "watch capacity          : %"PRIu32"\n", watch_capacities(&solver));
  fprintf(f, "mem for vsize           : %.2f MB\n", mem_for_vars(solver.vsize));
  fprintf(f, "mem for watchers        : %.2f MB\n", mem_for_watches(&solver));
  fprintf(f, "pool size               : %"PRIu32" (%.2f MB)\n", solver.pool.size, mb(solver.pool.size));
  fprintf(f, "pool capacity           : %"PRIu32" (%.2f MB)\n", solver.pool.capacity, mb(solver.pool.capacity));  
}

/*
 * Statistics on the search
 */
static void print_search_statistics(FILE *f) {
  solver_stats_t *stat = &solver.stats;

  fprintf(f, "starts                  : %"PRIu32"\n", stat->starts);
  fprintf(f, "simplify db             : %"PRIu32"\n", stat->simplify_calls);
  fprintf(f, "reduce db               : %"PRIu32"\n", stat->reduce_calls);
  fprintf(f, "decisions               : %"PRIu64"\n", stat->decisions);
  fprintf(f, "random decisions        : %"PRIu64"\n", stat->random_decisions);
  fprintf(f, "propagations            : %"PRIu64"\n", stat->propagations);
  fprintf(f, "conflicts               : %"PRIu64"\n", stat->conflicts);
  fprintf(f, "lits in pb. clauses     : %"PRIu32"\n", solver.pool.num_prob_literals);
  fprintf(f, "lits in learned clauses : %"PRIu32"\n", solver.pool.num_learned_literals);
  fprintf(f, "subsumed lits.          : %"PRIu64"\n", stat->subsumed_literals);
  fprintf(f, "deleted pb. clauses     : %"PRIu64"\n", stat->prob_clauses_deleted);
  fprintf(f, "deleted learned clauses : %"PRIu64"\n", stat->learned_clauses_deleted);
  fprintf(f, "\n");
}

int main(int argc, char *argv[]) {
  int resu;
  solver_status_t status;

  if (argc != 2) {
    fprintf(stderr, "Usage: %s <input file>\n", argv[0]);
    exit(1);
  }
  resu = build_instance(argv[1]);
  if (resu < 0) {
    exit(2);
  }
  construction_time = get_cpu_time();
  memory_size = mem_size() / (1024 * 1024);
  printf("\n"
	 "Construction time       : %.3f s\n", construction_time);
  printf("Memory used             : %.2f MB\n", memory_size);
  print_statistics(stdout);

  if (false) {
    printf("\nPropagation Test\n");
    nsat_boolean_propagation(&solver);
    printf("  num props:            : %"PRIu64"\n", solver.stats.propagations);
    printf("  num conflicts:        : %"PRIu64"\n", solver.stats.conflicts);
    printf("  assigned literals     : %"PRIu32"\n", solver.stack.top);
    if (solver.conflict_tag != CTAG_NONE) {
      printf("\nUNSAT by propagation\n");
    } else {
      printf("\nSimplification Test\n");
      nsat_simplify_clause_database(&solver);
      printf("  deleted clauses       : %"PRIu64"\n", solver.stats.prob_clauses_deleted);
      simplification_time = get_cpu_time() - construction_time;
      if (simplification_time < 0.0) {
	simplification_time = 0.0;
      }
      memory_size = mem_size() / (1024 * 1024);
      printf("\n"
	     "Simplification time     : %.3f s\n", simplification_time);
      printf("Memory used             : %.2f MB\n", memory_size);
      print_statistics(stdout);
    }
  }

  nsat_set_randomness(&solver, 0);
  status = nsat_solve(&solver, true);
  switch (status) {
  case STAT_UNSAT:
    printf("unsat\n\n");
    break;

  case STAT_SAT:
    printf("sat\n\n");
    break;

  default:
    printf("unkown status: error\n\n");
    break;
  }
  print_search_statistics(stdout);

  delete_nsat_solver(&solver);

  return 0;
}
