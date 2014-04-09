/*
 * EXPORT CLAUSES IN DIMACS FORMAT
 */

#include <inttypes.h>
#include <stdio.h>

#include "smt_core_exporter.h"


/*
 * Print literal l in DIMACS format
 * - l is 2 * v + s with 0 <= v < nvars and s=0 or s=1
 * - 0 is not allowed as a variable in DIMACS so we
 *   convert variable v to DIMACS var (v+1)
 */
static void dimacs_print_literal(FILE *f, literal_t l) {
  bvar_t v;

  v = var_of(l);
  if (is_neg(l)) fputc('-', f);
  fprintf(f, "%"PRId32, v+1);
}


/*
 * Print clause c in DIMACS format:
 * - print all literals then add '0' + newline as end marker
 */
static void dimacs_print_clause(FILE *f, clause_t *cl) {
  uint32_t i;
  literal_t l;

  i = 0;
  l = cl->cl[0];
  while (l >= 0) {
    dimacs_print_literal(f, l);
    fputc(' ', f);
    i ++;
    l = cl->cl[i];
  }
  fputs("0\n", f);
}


static void dimacs_print_empty_clause(FILE *f) {
  fputs("0\n", f);
}

static void dimacs_print_unit_clause(FILE *f, literal_t l) {
  dimacs_print_literal(f, l);
  fputs(" 0\n", f);
}

static void dimacs_print_binary_clause(FILE *f, literal_t l1, literal_t l2) {
  dimacs_print_literal(f, l1);
  fputc(' ', f);
  dimacs_print_literal(f, l2);
  fputs(" 0\n", f);
}


/*
 * Print clauses of core
 */
static void dimacs_print_unit_clauses(FILE *f, smt_core_t *core) {
  prop_stack_t *stack;
  uint32_t i, n;

  n = core->nb_unit_clauses;
  stack = &core->stack;
  for (i=0; i<n; i++) {
    dimacs_print_unit_clause(f, stack->lit[i]);
  }
}


static void dimacs_print_binary_clauses(FILE *f, smt_core_t *core) {
  int32_t n;
  literal_t l1, l2;
  literal_t *bin;

  n = core->nlits;
  for (l1=0; l1<n; l1++) {
    bin = core->bin[l1];
    if (bin != NULL) {
      for (;;) {
        l2 = *bin ++;
        if (l2 < 0) break;
        if (l1 <= l2) {
          dimacs_print_binary_clause(f, l1, l2);
        }
      }
    }
  }
}


static void dimacs_print_clause_vector(FILE *f, clause_t **vector) {
  uint32_t i, n;

  if (vector != NULL) {
    n = get_cv_size(vector);
    for (i=0; i<n; i++) {
      dimacs_print_clause(f, vector[i]);
    }
  }
}


static void dimacs_print_problem_clauses(FILE *f, smt_core_t *core) {
  if (core->inconsistent) {
    dimacs_print_empty_clause(f);
  }
  dimacs_print_unit_clause(f, true_literal);
  dimacs_print_unit_clauses(f, core);
  dimacs_print_binary_clauses(f, core);
  dimacs_print_clause_vector(f, core->problem_clauses);
}


/*
 * DIMACS header: number of variables + number of clauses
 */
static void dimacs_print_header(FILE *f, smt_core_t *core) {
  uint32_t num_clauses;

  num_clauses = core->nb_prob_clauses + core->nb_bin_clauses + core->nb_unit_clauses + 1;
  if (core->inconsistent) {
    num_clauses ++;
  }

  fprintf(f, "p cnf %"PRIu32" %"PRIu32"\n", core->nvars, num_clauses);
}


/*
 * Export the clauses of core into the given file:
 * - use the DIMACs CNF format
 * - don't export the learned clauses
 * - return 0 if this works
 * - return -1 if the file can't be opened
 */
int32_t smt_core_export(smt_core_t *core, const char *filename) {
  FILE *f;

  f = fopen(filename, "w");
  if (f == NULL) return -1;

  dimacs_print_header(f, core);
  dimacs_print_problem_clauses(f, core);
  fclose(f);

  return 0;
}

