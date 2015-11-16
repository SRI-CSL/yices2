/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Print a context (for debugging mostly)
 * Moved the code here to clean-up yices_reval.c
 */

#include "context/context.h"
#include "context/context_printer.h"
#include "context/dump_context.h"
#include "io/term_printer.h"
#include "io/type_printer.h"
#include "solvers/bv/bvsolver_printer.h"
#include "solvers/cdcl/gates_printer.h"
#include "solvers/cdcl/smt_core_printer.h"

#ifndef NDEBUG
#include "api/yices_globals.h"
#endif

/*
 * Print internal tables
 */
static void dump_bv_solver(FILE *f, bv_solver_t *solver) {
#ifndef NDEBUG
  fprintf(f, "\n--- Bitvector Partition ---\n");
  print_bv_solver_partition(f, solver);
#endif
  fprintf(f, "\n--- Bitvector Variables ---\n");
  print_bv_solver_vars(f, solver);
  fprintf(f, "\n--- Bitvector Atoms ---\n");
  print_bv_solver_atoms(f, solver);
#ifndef NDEBUG
  fprintf(f, "\n--- Bitvector Bounds ---\n");
  print_bv_solver_bounds(f, solver);
  fprintf(f, "\n--- DAG ---\n");
  print_bv_solver_dag(f, solver);
  if (solver->blaster != NULL) {
    fprintf(f, "\n--- Gates ---\n");
    print_gate_table(f, &solver->blaster->htbl);
  }
#endif
  fprintf(f, "\n");
}


/*
 * TOP LEVEL
 */
void dump_context(FILE *f, context_t *context) {
  assert(context != NULL);

#ifndef NDEBUG
  fprintf(f, "--- All terms ---\n");
  pp_term_table(f, __yices_globals.terms);
  fputc('\n', f);

  fprintf(f, "--- Substitutions ---\n");
  print_context_intern_subst(f, context);

  fprintf(f, "\n--- Internalization ---\n");
  print_context_intern_mapping(f, context);

  fprintf(f, "\n--- Gates ---\n");
  print_gate_table(f, &context->gate_manager.htbl);
#endif

  if (context_has_bv_solver(context)) {
    dump_bv_solver(f, context->bv_solver);
  }

  fprintf(f, "--- Clauses ---\n");
  print_clauses(f, context->core);
  fprintf(f, "\n");

#if 0
  fprintf(f, "--- Auxiliary vectors ---\n");
  print_context_subst_eqs(f, context);
  print_context_top_eqs(f, context);
  print_context_top_atoms(f, context);
  print_context_top_formulas(f, context);
  print_context_top_interns(f, context);
  fprintf(f, "\n");
#endif

  fflush(f);
}
