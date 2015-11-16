/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * PRINT STATISTICS ABOUT A CONTEXT
 */

#include <stdint.h>
#include <inttypes.h>

#include "context/context.h"
#include "context/context_statistics.h"
#include "solvers/bv/bvsolver.h"


/*
 * TRACE/STATISTICS AND SUPPORT FOR DEBUGGING
 */

/*
 * Statistics in the smt_core
 */
static void show_stats(FILE *f, dpll_stats_t *stat) {
  fprintf(f, "Core\n");
  fprintf(f, " restarts                : %"PRIu32"\n", stat->restarts);
  fprintf(f, " simplify db             : %"PRIu32"\n", stat->simplify_calls);
  fprintf(f, " reduce db               : %"PRIu32"\n", stat->reduce_calls);
  fprintf(f, " remove irrelevant       : %"PRIu32"\n", stat->remove_calls);
  fprintf(f, " decisions               : %"PRIu64"\n", stat->decisions);
  fprintf(f, " random decisions        : %"PRIu64"\n", stat->random_decisions);
  fprintf(f, " propagations            : %"PRIu64"\n", stat->propagations);
  fprintf(f, " conflicts               : %"PRIu64"\n", stat->conflicts);
  fprintf(f, " theory propagations     : %"PRIu32"\n", stat->th_props);
  fprintf(f, " propagation-lemmas      : %"PRIu32"\n", stat->th_prop_lemmas);
  fprintf(f, " theory conflicts        : %"PRIu32"\n", stat->th_conflicts);
  fprintf(f, " conflict-lemmas         : %"PRIu32"\n", stat->th_conflict_lemmas);

  fprintf(f, " lits in pb. clauses     : %"PRIu64"\n", stat->prob_literals);
  fprintf(f, " lits in learned clauses : %"PRIu64"\n", stat->learned_literals);
  fprintf(f, " total lits. in learned  : %"PRIu64"\n", stat->literals_before_simpl);
  fprintf(f, " subsumed lits.          : %"PRIu64"\n", stat->subsumed_literals);
  fprintf(f, " deleted pb. clauses     : %"PRIu64"\n", stat->prob_clauses_deleted);
  fprintf(f, " deleted learned clauses : %"PRIu64"\n", stat->learned_clauses_deleted);
  fprintf(f, " deleted binary clauses  : %"PRIu64"\n", stat->bin_clauses_deleted);
}

/*
 * Bitvector solver statistics
 */
static void show_bvsolver_stats(FILE *f, bv_solver_t *solver) {
  fprintf(f, "Bit-vectors\n");
  fprintf(f, " variables               : %"PRIu32"\n", bv_solver_num_vars(solver));
  fprintf(f, " atoms                   : %"PRIu32"\n", bv_solver_num_atoms(solver));
  fprintf(f, " eq. atoms               : %"PRIu32"\n", bv_solver_num_eq_atoms(solver));
  fprintf(f, " dyn eq. atoms           : %"PRIu32"\n", solver->stats.on_the_fly_atoms);
  fprintf(f, " ge atoms                : %"PRIu32"\n", bv_solver_num_ge_atoms(solver));
  fprintf(f, " sge atoms               : %"PRIu32"\n", bv_solver_num_sge_atoms(solver));
  fprintf(f, " equiv lemmas            : %"PRIu32"\n", solver->stats.equiv_lemmas);
  fprintf(f, " equiv conflicts         : %"PRIu32"\n", solver->stats.equiv_conflicts);
  fprintf(f, " semi-equiv lemmas       : %"PRIu32"\n", solver->stats.half_equiv_lemmas);
  fprintf(f, " interface lemmas        : %"PRIu32"\n", solver->stats.interface_lemmas);
}



void yices_print_presearch_stats(FILE *f, context_t *ctx) {
  smt_core_t *core;

  core = ctx->core;

  fprintf(f, "boolean variables       : %"PRIu32"\n", core->nvars);
  fprintf(f, "atoms                   : %"PRIu32"\n", core->atoms.natoms);
  fprintf(f, "\n");
  fflush(f);
}

void yices_show_statistics(FILE *f, context_t *ctx) {
  smt_core_t *core;

  core = ctx->core;

  show_stats(f, &core->stats);
  fprintf(f, " boolean variables       : %"PRIu32"\n", core->nvars);
  fprintf(f, " atoms                   : %"PRIu32"\n", core->atoms.natoms);
  if (context_has_bv_solver(ctx)) {
    show_bvsolver_stats(f, ctx->bv_solver);
  }
}


void yices_dump_context(FILE *f, context_t *ctx) {
  // NOT IMPLEMENTED
}
