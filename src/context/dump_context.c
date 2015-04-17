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
#include "solvers/egraph/egraph_printer.h"
#include "solvers/floyd_warshall/idl_fw_printer.h"
#include "solvers/floyd_warshall/rdl_fw_printer.h"
#include "solvers/simplex/simplex_printer.h"

#ifndef NDEBUG
#include "api/yices_globals.h"
#endif

/*
 * Dump: print all internal tables
 * + the egraph/core and theory solvers
 */
static void dump_egraph(FILE *f, egraph_t *egraph) {
  fprintf(f, "\n--- Egraph Variables ---\n");
  print_egraph_terms(f, egraph);
  fprintf(f, "\n--- Egraph Atoms ---\n");
  print_egraph_atoms(f, egraph);
#ifndef DEBUG
  fprintf(f, "\n--- Egraph Classes ---\n");
  print_egraph_root_classes(f, egraph);
#endif
}

static void dump_idl_solver(FILE *f, idl_solver_t *idl) {
  fprintf(f, "\n--- IDL Variables ---\n");
  print_idl_var_table(f, idl);
  fprintf(f, "\n--- IDL Atoms ---\n");
  print_idl_atoms(f, idl);
  fprintf(f, "\n--- IDL Constraints ---\n");
  print_idl_axioms(f, idl);
}

static void dump_rdl_solver(FILE *f, rdl_solver_t *rdl) {
  fprintf(f, "\n--- RDL Variables ---\n");
  print_rdl_var_table(f, rdl);
  fprintf(f, "\n--- RDL Atoms ---\n");
  print_rdl_atoms(f, rdl);
  fprintf(f, "\n--- RDL Constraints ---\n");
  print_rdl_axioms(f, rdl);
}

static void dump_simplex_solver(FILE *f, simplex_solver_t *simplex) {
  fprintf(f, "\n--- Simplex ---\n");
#ifndef NDEBUG
  print_simplex_flags(f, simplex);
  fprintf(f, "\n");
#endif
  print_simplex_vars(f, simplex);
#ifndef NDEBUG
  print_simplex_saved_rows(f, simplex);
#endif
  print_simplex_atoms(f, simplex);
  fprintf(f, "\n--- Tableau ---\n");
  print_simplex_matrix(f, simplex);
  fprintf(f, "---  Bounds ---\n");
  print_simplex_bounds(f, simplex);
  fprintf(f, "\n");
}

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

  if (context_has_egraph(context)) {
    dump_egraph(f, context->egraph);
  }

  if (context_has_arith_solver(context)) {
    if (context_has_idl_solver(context)) {
      dump_idl_solver(f, context->arith_solver);
    } else if (context_has_rdl_solver(context)) {
      dump_rdl_solver(f, context->arith_solver);
    } else {
      assert(context_has_simplex_solver(context));
      dump_simplex_solver(f, context->arith_solver);
    }
  }

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
