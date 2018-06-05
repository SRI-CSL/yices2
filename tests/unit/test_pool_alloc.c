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
 * Test of clause pool
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <inttypes.h>
#include <ctype.h>
#include <assert.h>

#include "solvers/cdcl/clause_pool.h"
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
 * Clause pool for testing
 */
static clause_pool_t pool;
static double construction_time;
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
    c = getc(f);
  } while (c != '\n');
}


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

static literal_t read_literal(FILE *f, uint32_t nv) {
  int d;
  int32_t var, delta;

  do {
    d = getc(f);
  } while (isspace(d));

  /*
   * Conversion: literal in Yices format = 2 * var + delta
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
  literal_t literal;
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

  /* initialize the pool */
  init_clause_pool(&pool);

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
    (void) clause_pool_add_problem_clause(&pool, j, clause);
    i ++;
  }
  delete_buffer();

  fclose(f);

  return 0;
}


/*
 * Print problem size
 */
static void print_statistics(FILE *f) {
  fprintf(f, "\nConstruction time    : %.3f s\n", construction_time);
  fprintf(f, "Memory used          : %.2f MB\n", memory_size);
  fprintf(f, "nb. of variables     : %"PRIu32"\n", nvars);
  fprintf(f, "nb. of clauses       : %"PRIu32"\n", nclauses);
  fprintf(f, "clause pool\n");
  fprintf(f, "    prob clauses     : %"PRIu32"\n", pool.num_prob_clauses);
  fprintf(f, "    prob literals    : %"PRIu32"\n", pool.num_prob_literals);
  fprintf(f, "    learned clauses  : %"PRIu32"\n", pool.num_learned_clauses);
  fprintf(f, "    learned literals : %"PRIu32"\n", pool.num_learned_literals);
  fprintf(f, "pool size            : %"PRIu32"\n", pool.size);
  fprintf(f, "pool capacity        : %"PRIu32"\n", pool.capacity);
  fprintf(f, "first learned clause : %"PRIu32"\n", pool.learned);
}


int main(int argc, char *argv[]) {
  int resu;

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
  print_statistics(stdout);
  delete_clause_pool(&pool);

  return 0;
}
