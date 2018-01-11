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

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

/*
 * We try to make this self-contained and independent of
 * the rest of the source.
 */
typedef uint32_t literal_t;

/*
 * Extract data produced by the new sat solver.
 * For each conflict, we get:
 * - stats.conflicts
 * - stats.decisions
 * - stats.propagations
 * - slow_ema
 * - fast_ema
 * - blocking_ema
 * - lbd
 * - conflict level
 * - backtrack level
 * - size of the learned clause
 * - then the learned clause (as an array of literals)
 */
typedef struct conflict_data {
  uint64_t conflicts;
  uint64_t decisions;
  uint64_t propagations;
  uint64_t slow_ema;
  uint64_t fast_ema;
  uint64_t blocking_ema;
  uint32_t lbd;
  uint32_t conflict_level;
  uint32_t backtrack_level;
  uint32_t learned_clause_size;
} conflict_data_t;


/*
 * Read data about a conflict from FILE f
 * - fills in the buffer
 * - returns true if this works, false on a read error
 */
static bool read_conflict_data(FILE *f, conflict_data_t *buffer) {
  size_t r;

  r = fread(buffer, sizeof(conflict_data_t), 1, f);
  return r == 1;
}

// n = number of literals
// a = array to store the clause
static bool read_learned_clause(FILE *f, uint32_t n, literal_t *a) {
  size_t r;

  r = fread(a, sizeof(literal_t), n, f);
  return r == (size_t) n;
}


/*
 * Header
 */
static void print_header(FILE *f) {
  fprintf(f, "conflicts,decisions,propagations,lbd,clevel,blevel,size\n");
}

/*
 * Print literal l:
 * - convert l to the DIMACS convention
 * - 2 x --> x
 * - 2 x + 1 --> -x
 */
static void print_literal(FILE *f, literal_t l) {
  if (l & 1) fprintf(f, "-");
  fprintf(f, "%"PRIu32, l>>1);
}

/*
 * Print a clause
 * - n = number of literals
 * - a = array of literals
 */
static void print_clause(FILE *f, uint32_t n, literal_t *a) {
  uint32_t i;

  fprintf(f, "[");
  if (n > 0) {
    print_literal(f, a[0]);
    for (i=1; i<n; i++) {
      fprintf(f, ",");
      print_literal(f, a[i]);
    }
  }
  fprintf(f, "]\n");
}

/*
 * Print data about a conflict:
 * - f = output file
 * - data = statistics record
 * - a = learned clause
 */
static void print_data(FILE *f, conflict_data_t *data, literal_t *a) {
  fprintf(f, "%"PRIu64",%"PRIu64",%"PRIu64",%"PRIu32",%"PRIu32",%"PRIu32",%"PRIu32"\n",
	  data->conflicts, data->decisions, data->propagations,
	  data->lbd, data->conflict_level, data->backtrack_level, data->learned_clause_size);
  if (false) {
    print_clause(f, data->learned_clause_size, a);
  }
}

/*
 * Print all data from f
 * - return true if no error was detected
 * - return false otherwise
 */
static bool print_all_data(FILE *f) {
  conflict_data_t data;
  literal_t *litarray, *aux;
  uint32_t litmax;

  litmax = 1000;
  litarray = malloc(litmax * sizeof(literal_t));
  if (litarray == NULL) goto malloc_failed;

  print_header(stdout);

  while (true) {
    if (! read_conflict_data(f, &data)) {
      if (ferror(f)) goto read_failed;
      // end of file
      break;
    }
    if (data.learned_clause_size > (UINT32_MAX>>2)) goto bad_data;
    if (data.learned_clause_size > litmax) {
      litmax = data.learned_clause_size;
      aux = realloc(litarray, litmax * sizeof(literal_t));
      if (aux == NULL) {
	free(litarray);
	goto malloc_failed;
      }
    }
    if (! read_learned_clause(f, data.learned_clause_size, litarray)) {
      if (ferror(f)) goto read_failed;
      // end of file
      goto missing_data;
    }
    print_data(stdout, &data, litarray);
  }

  return true;

 malloc_failed:
  fprintf(stderr, "Failed to allocate a large enough buffer\n");
  return false;

 bad_data:
  fprintf(stderr, "Got invalid clause_size_length (too large)\n");
  return false;

 read_failed:
  perror("read data: ");
  return false;

 missing_data:
  fprintf(stderr, "Missing clause: file may be truncated\n");
  return false;
}


/*
 * Expect a single argument; filename
 */
int main(int argc, char *argv[]) {
  FILE *f;
  bool ok;

  if (argc != 2) {
    fprintf(stderr, "Usage: %s <filename>\n", argv[0]);
    return EXIT_FAILURE;
  }

  f = fopen(argv[1], "r");
  if (f == NULL) {
    perror(argv[1]);
    return EXIT_FAILURE;
  }

  ok = print_all_data(f);
  fclose(f);

  return ok ? EXIT_SUCCESS : EXIT_FAILURE;
}
