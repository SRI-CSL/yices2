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
 * PRINT SMT-CORE STRUCTURE
 */

#include <inttypes.h>

#include "solvers/cdcl/smt_core_printer.h"


static const char * const bval2string[] = {
  "undef", "undef", "false", "true", "<invalid bval>",
};

static const char * const status2string[] = {
  "idle", "searching", "unknown", "sat", "unsat", "interrupted",
  "<invalid status>",
};


/*
 * Boolean value
 */
void print_bval(FILE *f, bval_t b) {
  // cast to (int) prevents compilation warnings with clang
  // because it uses (unsigned) for the bval_t enum.
  if ((int) b < 0 || b > VAL_TRUE) {
    b = VAL_TRUE + 1;
  }
  fputs(bval2string[b], f);
}

/*
 * Status
 */
void print_status(FILE *f, smt_status_t s) {
  if (s > SMT_STATUS_INTERRUPTED) {
    s = SMT_STATUS_INTERRUPTED + 1;
  }
  fputs(status2string[s], f);
}

/*
 * Boolean variable
 */
void print_bvar(FILE *f, bvar_t x) {
  if (x < 0) {
    if (x == null_bvar) {
      fputs("null_bvar", f);
    } else {
      fprintf(f, "BVAR%"PRId32, x);
    }
  } else if (x == const_bvar) {
    fputs("true", f);
  } else {
    fprintf(f, "p!%"PRId32, x);
  }
}

/*
 * Literal
 */
void print_literal(FILE *f, literal_t l) {
  if (l < 0) {
    if (l == null_literal) {
      //      fputs("null_literal", f);
      fputs("nil", f);
    } else {
      fprintf(f, "LIT%"PRId32, l);
    }
  } else if (l == true_literal) {
    fputs("tt", f);
  } else if (l == false_literal) {
    fputs("ff", f);
  } else {
    if (is_neg(l)) fputc('~', f);
    fprintf(f, "p!%"PRId32, var_of(l));
  }
}


/*
 * Clause
 */
void print_clause(FILE *f, clause_t *cl) {
  uint32_t i;
  literal_t l;


  /*
   * Some problem clauses may be hidden (because one of their
   * literal is true. For such clauses, the first two literals
   * are negated.
   */
  if (cl->cl[0] < 0 || cl->cl[1] < 0) {

    fputc('[', f);
    print_literal(f, - cl->cl[0]);
    fputc(' ', f);
    print_literal(f, - cl->cl[1]);
    i = 2;
    l = cl->cl[i];
    while (l >= 0) {
      fputc(' ', f);
      print_literal(f, l);
      i ++;
      l = cl->cl[i];
    }
    fputc(']', f);

  } else {
    fputc('{', f);
    print_literal(f, cl->cl[0]);
    i = 1;
    l = cl->cl[i];
    while (l >= 0) {
      fputc(' ', f);
      print_literal(f, l);
      i ++;
      l = cl->cl[i];
    }
    fputc('}', f);
  }
}



/*
 * Print unit clauses = all the literals in core->stack[0 .. core->nb_units-1]
 */
void print_unit_clause(FILE *f, literal_t l) {
  fputc('{', f);
  print_literal(f, l);
  fputc('}', f);
}

void print_unit_clauses(FILE *f, smt_core_t *core) {
  prop_stack_t *stack;
  uint32_t i, n;

  n = core->nb_unit_clauses;
  stack = &core->stack;
  for (i=0; i<n; i++) {
    print_unit_clause(f, stack->lit[i]);
    fputc('\n', f);
  }
}


/*
 * Print array a, formatted as a clause
 */
void print_litarray(FILE *f, uint32_t n, literal_t *a) {
  uint32_t i;

  fputc('{', f);
  if (n > 0) {
    print_literal(f, a[0]);
    for (i=1; i<n; i++) {
      fputc(' ', f);
      print_literal(f, a[i]);
    }
  }
  fputc('}', f);
}


#if 0
/*
 * Variant of print_clause: sort the literals first
 */
void print_clause_sorted(FILE *f, clause_t *cl) {
  ivector_t v;
  uint32_t i;
  literal_t l;

  init_ivector(&v, 10);

  if (cl->cl[0] < 0 || cl->cl[1] < 0) {
    ivector_push(&v, - cl->cl[0]);
    ivector_push(&v, - cl->cl[1]);
  } else {
    ivector_push(&v, cl->cl[0]);
    ivector_push(&v, cl->cl[1]);
  }
  i = 2;
  l = cl->cl[i];
  while (l >= 0) {
    ivector_push(&v, l);
    i ++;
    l = cl->cl[i];
  }
  int_array_sort(v.data, v.size);
  print_litarray(f, v.size, v.data);

  delete_ivector(&v);      
}
#endif


/*
 * Print binary and problem clauses
 */
void print_binary_clause(FILE *f, literal_t l1, literal_t l2) {
  fputc('{', f);
  print_literal(f, l1);
  fputc(' ', f);
  print_literal(f, l2);
  fputc('}', f);
}

void print_binary_clauses(FILE *f, smt_core_t *core) {
  int32_t n;
  literal_t l1, l2;
  literal_t *bin;

  n = core->nlits;
  for (l1=0; l1<n; l1++) {
    bin = core->bin[l1];
    if (bin != NULL) {
      for (;;) {
        l2 = *bin++;
        if (l2 < 0) break;
        if (l1 <= l2) {
          print_binary_clause(f, l1, l2);
          fputc('\n', f);
        }
      }
    }
  }
}

static void print_clause_vector(FILE *f, clause_t **vector) {
  uint32_t i, n;

  if (vector != NULL) {
    n = get_cv_size(vector);
    for (i=0; i<n; i++) {
      print_clause(f, vector[i]);
      fputc('\n', f);
    }
  }
}

void print_problem_clauses(FILE *f, smt_core_t *core) {
  print_clause_vector(f, core->problem_clauses);
}

void print_learned_clauses(FILE *f, smt_core_t *core) {
  print_clause_vector(f, core->learned_clauses);
}

void print_clauses(FILE *f, smt_core_t *core) {
  print_unit_clauses(f, core);
  print_binary_clauses(f, core);
  print_problem_clauses(f, core);
  fputc('\n', f);
}

void print_all_clauses(FILE *f, smt_core_t *core) {
  print_binary_clauses(f, core);
  fputc('\n', f);
  print_problem_clauses(f, core);
  fputc('\n', f);
  print_learned_clauses(f, core);
  fputc('\n', f);
}

/*
 * Find the length of a lemma a:
 * - a must be terminated by null_literal (or any negative end marker)
 */
static uint32_t lemma_length(literal_t *a) {
  uint32_t n;

  n = 0;
  while (*a >= 0) {
    a ++;
    n ++;
  }
  return n;
}


/*
 * Print all lemmas
 */
void print_lemmas(FILE *f, smt_core_t *core) {
  lemma_block_t *tmp;
  literal_t *lemma;
  uint32_t i, j, n;

  for (i=0; i<core->lemmas.free_block; i++) {
    tmp = core->lemmas.block[i];
    lemma = tmp->data;
    j = 0;
    while (j < tmp->ptr) {
      n = lemma_length(lemma);
      print_litarray(f, n, lemma);
      fputc('\n', f);
      n ++;
      j += n;
      lemma += n;
    }
  }
}


/*
 * Print assignment
 */
void print_boolean_assignment(FILE *f, smt_core_t *core) {
  prop_stack_t *stack;
  uint32_t i, n;
  literal_t l;

  stack = &core->stack;
  n = stack->top;
  for (i=0; i<n; i++) {
    l = stack->lit[i];
    fputc(' ', f);
    if (is_pos(l)) fputc(' ', f);
    print_literal(f, l);
    fprintf(f, " level = %"PRIu32"\n", core->level[var_of(l)]);
  }
}

/*
 * Print conflict data
 */
void print_conflict(FILE *f, smt_core_t *core) {
  literal_t l;
  uint32_t i;

  if (core->inconsistent) {
    i = 0;
    l = core->conflict[i];
    if (l < 0) {
      fputs("Conflict: empty clause\n", f);
    } else {
      fputs("Conflict:", f);
      while (l >= 0) {
        fputc(' ', f);
        print_literal(f, l);
        i ++;
        l = core->conflict[i];
      }
      fputc('\n', f);
    }

  } else {
    fputs("No conflict\n", f);
  }
}


/*
 * Size of a clause vector (deal with the case v == NULL)
 */
static inline uint32_t cv_size(clause_t **v) {
  return v == NULL ? 0 : get_cv_size(v);
}

/*
 * Print current state of core
 * (This needs to be exported for now, because it's used in the tests)
 */
void print_smt_core(FILE *f, smt_core_t *core) {
  fprintf(f, "SMT Core %p\n", core);
  fprintf(f, "  %"PRIu32" variables\n", core->nvars);
  fprintf(f, "  %"PRIu32" unit clauses\n", core->nb_unit_clauses);
  fprintf(f, "  %"PRIu32" binary clauses\n", core->nb_bin_clauses);
  fprintf(f, "  %"PRIu32" problem clauses\n", cv_size(core->problem_clauses));
  fprintf(f, "  %"PRIu32" learned clauses\n", cv_size(core->learned_clauses));
  fprintf(f, "status = %s\n", status2string[core->status]);
  fprintf(f, "base_level = %"PRIu32"\n", core->base_level);
  fprintf(f, "decision_level = %"PRIu32"\n", core->decision_level);
  print_conflict(f, core);
  fprintf(f, "Assignment:\n");
  print_boolean_assignment(f, core);
  fprintf(f, "Clauses:\n");
  print_unit_clauses(f, core);
  print_binary_clauses(f, core);
  print_problem_clauses(f, core);
  print_learned_clauses(f, core);
  fputc('\n', f);
  fflush(f);
}




