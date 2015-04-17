/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * EXPORT CLAUSES IN DIMACS FORMAT
 */

#include <inttypes.h>
#include <stdio.h>

#include "context/internalization_codes.h"
#include "io/term_printer.h"
#include "solvers/bv/dimacs_printer.h"


/*
 * Print boolean variable x in Dimacs format
 * - we can't use 0 as a variable id, so we print (x+1)
 */
void dimacs_print_bvar(FILE *f, bvar_t x) {
  fprintf(f, "%"PRId32, x+1);
}


/*
 * Print literal l in DIMACS format
 * - l is 2 * v + s with 0 <= v < nvars and s=0 or s=1
 * - 0 is not allowed as a variable in DIMACS so we
 *   convert variable v to DIMACS var (v+1)
 */
void dimacs_print_literal(FILE *f, literal_t l) {
  bvar_t v;

  v = var_of(l);
  if (is_neg(l)) fputc('-', f);
  fprintf(f, "%"PRId32, v+1);
}


/*
 * Print clause c in DIMACS format:
 * - print all literals then add '0' + newline as end marker
 */
void dimacs_print_clause(FILE *f, clause_t *cl) {
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


void dimacs_print_empty_clause(FILE *f) {
  fputs("0\n", f);
}


void dimacs_print_unit_clause(FILE *f, literal_t l) {
  dimacs_print_literal(f, l);
  fputs(" 0\n", f);
}


void dimacs_print_binary_clause(FILE *f, literal_t l1, literal_t l2) {
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

// all the clauses (including the learned caluses)
static void dimacs_print_all_clauses(FILE *f, smt_core_t *core) {
  dimacs_print_problem_clauses(f, core);
  dimacs_print_clause_vector(f, core->learned_clauses);
}


/*
 * DIMACS header: number of variables + number of clauses
 * - we print one extra clause for the true_literal
 */
static void dimacs_print_header(FILE *f, smt_core_t *core) {
  uint32_t num_clauses;

  num_clauses = num_empty_clauses(core) + num_unit_clauses(core) + num_binary_clauses(core) +
    num_prob_clauses(core) + 1;

  fprintf(f, "p cnf %"PRIu32" %"PRIu32"\n", core->nvars, num_clauses);
}


/*
 * Full header: includes the learned clauses
 */
static void dimacs_print_full_header(FILE *f, smt_core_t *core) {
  uint32_t num_clauses;

  num_clauses = num_empty_clauses(core) + num_unit_clauses(core) + num_binary_clauses(core) +
    num_prob_clauses(core) + num_learned_clauses(core) + 1;

  fprintf(f, "p cnf %"PRIu32" %"PRIu32"\n", core->nvars, num_clauses);
}


/*
 * Print all the problem clauses from core
 * First print the DIMACS header:
 *   p cnf <number of variables> <number of clauses>
 */
void dimacs_print_core(FILE *f, smt_core_t *core) {
  dimacs_print_header(f, core);
  dimacs_print_problem_clauses(f, core);
}


/*
 * Print all clauses: original + learned clauses
 * First print the DIMACS header
 */
void dimacs_print_full_core(FILE *f, smt_core_t *core) {
  dimacs_print_full_header(f, core);
  dimacs_print_all_clauses(f, core);
}



/*
 * BITVECTOR STUFF
 */

/*
 * Print the literal mapped to s in the table
 * - if nothing is mapped to s, print "_"
 */
void dimacs_print_pseudo_literal(FILE *f, remap_table_t *table, literal_t s) {
  if (s != null_literal) {
    s = remap_table_find(table, s);
  }

  if (s == null_literal) {
    fputs("_", f);
  } else {
    dimacs_print_literal(f, s);
  }
}


/*
 * Same thing for an array of n pseudo literals:
 * - use the format [ .... ]
 */
void dimacs_print_pseudo_litarray(FILE *f, remap_table_t *remap, literal_t *a, uint32_t n) {
  uint32_t i;

  fputc('[', f);
  for (i=0; i<n; i++) {
    if (i > 0) fputc(' ', f);
    dimacs_print_pseudo_literal(f, remap, a[i]);
  }
  fputc(']', f);
}



/*
 * Print the pseudo literal array mapped to bitvariable x
 * - x must be a valid variable
 * - it this is called before bit blasting, we print 'not mapped'
 *   otherwise we print the pseudo literal array mapped to x
 */
void dimacs_print_bvvar(FILE *f, bv_solver_t *solver, thvar_t x) {
  bv_vartable_t *vtbl;
  literal_t *map;
  uint32_t n;

  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  if (0 <= x && x < n) {
    map = bvvar_get_map(vtbl, x);
    if (map != NULL) {
      assert(solver->remap != NULL);
      dimacs_print_pseudo_litarray(f, solver->remap, map, bvvar_bitsize(vtbl, x));
    } else {
      fputs("not mapped", f);
    }
  } else {
    fputs("invalid bitvector variable", f);
  }
}


/*
 * Print a Boolean internalization code:
 * - polarity = 0 or 1 (1 means negate)
 * - code can be either the constant true or false (bool2code(true) or bool2code(false))
 *   or a literal code
 */
static void dimacs_print_bool_code(FILE *f, int32_t code, uint32_t polarity) {
  literal_t l;

  if (code_is_eterm(code)) {
    if (code == bool2code(true)) {
      l = true_literal;
    } else if (code == bool2code(false)) {
      l = false_literal;
    } else {
      l = null_literal; // should not happen if we're using QF_BV
    }
  } else {
    l = code2literal(code);
  }

  if (l == null_literal) {
    fputs("not boolean", f);
  } else {
    dimacs_print_literal(f, l ^ polarity);
  }
}


/*
 * Print a bit-vector internalization code
 */
static void dimacs_print_bv_code(FILE *f, context_t *ctx, int32_t code) {
  thvar_t x;

  x = code2thvar(code);
  dimacs_print_bvvar(f, ctx->bv_solver, x);
}


/*
 * Print what's mapped to t in the context's internalization table.
 * - if t is mapped to a Boolean, the corresponding DIMACS literal is printed
 * - if t is mapped to a bitvector then the corresponding literal array is printed
 * - otherwise we print "non boolean"
 */
void dimacs_print_internalized_term(FILE *f, context_t *ctx, term_t t) {
  intern_tbl_t *intern;
  type_table_t *types;
  term_t r;
  type_t tau;
  int32_t code;
  uint32_t polarity;

  intern = &ctx->intern;
  types = ctx->types;

  r = intern_tbl_get_root(intern, t);
  if (t != r) {
    // substitution: t --> r (can't deal with this)
    fputs("eliminated", f);
  } else if (intern_tbl_root_is_mapped(intern, r)) {
    // t = r is mapped to something
    polarity = polarity_of(r);
    r = unsigned_term(r);

    tau = intern_tbl_type_of_root(intern, r);
    if (is_boolean_type(tau)) {
      // Boolean term
      code = intern_tbl_map_of_root(intern, r);
      assert(code_is_valid(code));
      dimacs_print_bool_code(f, code, polarity);
    } else if (is_bv_type(types, tau)) {
      // Bitvector term
      code = intern_tbl_map_of_root(intern, r);
      assert(code_is_valid(code));
      assert(polarity == 0);
      dimacs_print_bv_code(f, ctx, code);
    } else {
      // Can't be converted to DIMACS
      fputs("non boolean", f);
    }
  } else {
    // r not mapped to anything
    fputs("not internalized", f);
  }
}


/*
 * Print the mapping for t as a comment in DIMACS
 */
void dimacs_print_term_map(FILE *f, context_t *ctx, term_t t) {
  term_table_t *terms;

  terms = ctx->terms;
  assert(good_term(terms, t));
  fputs("c   ", f);
  print_term_name(f, terms, t);
  fputs(" --> ", f);
  dimacs_print_internalized_term(f, ctx, t);
  fputc('\n', f);
}


/*
 * Same thing for an array of n terms:
 * - add an empty comment line before and after
 */
void dimacs_print_term_map_array(FILE *f, context_t *ctx, term_t *a, uint32_t n) {
  uint32_t i;

  fputs("c\n", f);
  for (i=0; i<n; i++) {
    dimacs_print_term_map(f, ctx, a[i]);
  }
  fputs("c\n", f);
}



/*
 * CONTEXT AFTER INTERNALIZATION AND BITBLASTING
 */

/*
 * Print the term map for every uninterpreted term present in ctx->intern_tbl
 * then print the core
 */
void dimacs_print_bvcontext(FILE *f, context_t *ctx) {
  term_table_t *terms;
  intern_tbl_t *intern;
  uint32_t i, n;
  term_t t;

  assert(ctx->core != NULL);

  fputs("c Autogenerated by Yices\n", f);
  fputs("c\n", f);

  terms = ctx->terms;
  intern = &ctx->intern;
  n = intern->map.top;
  for (i=0; i<n; i++) {
    t = pos_term(i);
    if (good_term(terms, t) && term_kind(terms, t) == UNINTERPRETED_TERM) {
      dimacs_print_term_map(f, ctx, t);
    }
  }
  fputs("c\n", f);

  dimacs_print_core(f, ctx->core);

  fflush(f);
}

