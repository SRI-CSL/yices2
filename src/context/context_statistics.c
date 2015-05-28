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
#include "solvers/floyd_warshall/idl_floyd_warshall.h"
#include "solvers/floyd_warshall/rdl_floyd_warshall.h"
#include "solvers/funs/fun_solver.h"
#include "solvers/simplex/simplex.h"


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
 * Egraph statistics
 */
static void show_egraph_stats(FILE *f, egraph_stats_t *stat) {
  fprintf(f, "Egraph\n");
  fprintf(f, " eq from simplex         : %"PRIu32"\n", stat->eq_props);
  fprintf(f, " app/update reductions   : %"PRIu32"\n", stat->app_reductions);
  fprintf(f, " prop. to core           : %"PRIu32"\n", stat->th_props);
  fprintf(f, " conflicts               : %"PRIu32"\n", stat->th_conflicts);
  fprintf(f, " non-distinct lemmas     : %"PRIu32"\n", stat->nd_lemmas);
  fprintf(f, " auxiliary eqs. created  : %"PRIu32"\n", stat->aux_eqs);
  fprintf(f, " dyn boolack. lemmas     : %"PRIu32"\n", stat->boolack_lemmas);
  fprintf(f, " other dyn ack.lemmas    : %"PRIu32"\n", stat->ack_lemmas);
  fprintf(f, " final checks            : %"PRIu32"\n", stat->final_checks);
  fprintf(f, " interface equalities    : %"PRIu32"\n", stat->interface_eqs);
}

/*
 * Array/function solver statistics
 */
static void show_funsolver_stats(FILE *f, fun_solver_stats_t *stat) {
  fprintf(f, "Arrays\n");
  fprintf(f, " init. variables         : %"PRIu32"\n", stat->num_init_vars);
  fprintf(f, " init. edges             : %"PRIu32"\n", stat->num_init_edges);
  fprintf(f, " update axiom1           : %"PRIu32"\n", stat->num_update_axiom1);
  fprintf(f, " update axiom2           : %"PRIu32"\n", stat->num_update_axiom2);
  fprintf(f, " extensionality axioms   : %"PRIu32"\n", stat->num_extensionality_axiom);
}

/*
 * Simplex statistics
 */
static void show_simplex_stats(FILE *f, simplex_stats_t *stat) {
  fprintf(f, "Simplex\n");
  fprintf(f, " init. variables         : %"PRIu32"\n", stat->num_init_vars);
  fprintf(f, " init. rows              : %"PRIu32"\n", stat->num_init_rows);
  fprintf(f, " init. atoms             : %"PRIu32"\n", stat->num_atoms);
  fprintf(f, " end atoms               : %"PRIu32"\n", stat->num_end_atoms);
  fprintf(f, " elim. candidates        : %"PRIu32"\n", stat->num_elim_candidates);
  fprintf(f, " elim. rows              : %"PRIu32"\n", stat->num_elim_rows);
  fprintf(f, " fixed vars after simpl. : %"PRIu32"\n", stat->num_simpl_fvars);
  fprintf(f, " rows after simpl.       : %"PRIu32"\n", stat->num_simpl_rows);
  fprintf(f, " fixed vars              : %"PRIu32"\n", stat->num_fixed_vars);
  fprintf(f, " rows in init. tableau   : %"PRIu32"\n", stat->num_rows);
  fprintf(f, " rows in final tableau   : %"PRIu32"\n", stat->num_end_rows);
  fprintf(f, " calls to make_feasible  : %"PRIu32"\n", stat->num_make_feasible);
  fprintf(f, " pivots                  : %"PRIu32"\n", stat->num_pivots);
  fprintf(f, " bland-rule activations  : %"PRIu32"\n", stat->num_blands);
  fprintf(f, " simple lemmas           : %"PRIu32"\n", stat->num_binary_lemmas);
  //  fprintf(f, " propagation lemmas      : %"PRIu32"\n", stat->num_prop_lemmas);  (it's always zero)
  fprintf(f, " prop. to core           : %"PRIu32"\n", stat->num_props);
  fprintf(f, " derived bounds          : %"PRIu32"\n", stat->num_bound_props);
  fprintf(f, " productive propagations : %"PRIu32"\n", stat->num_prop_expl);
  fprintf(f, " conflicts               : %"PRIu32"\n", stat->num_conflicts);
  fprintf(f, " interface lemmas        : %"PRIu32"\n", stat->num_interface_lemmas);
  fprintf(f, " reduced inter. lemmas   : %"PRIu32"\n", stat->num_reduced_inter_lemmas);
  fprintf(f, " trichotomy lemmas       : %"PRIu32"\n", stat->num_tricho_lemmas);
  fprintf(f, " reduced tricho. lemmas  : %"PRIu32"\n", stat->num_reduced_tricho);
  if (stat->num_make_intfeasible > 0 || stat->num_dioph_checks > 0) {
    fprintf(f, "Integer arithmetic\n");
    fprintf(f, " make integer feasible   : %"PRIu32"\n", stat->num_make_intfeasible);
    fprintf(f, " branch atoms            : %"PRIu32"\n", stat->num_branch_atoms);
    fprintf(f, "bound strengthening\n");
    fprintf(f, " conflicts               : %"PRIu32"\n", stat->num_bound_conflicts);
    fprintf(f, " recheck conflicts       : %"PRIu32"\n", stat->num_bound_recheck_conflicts);
    fprintf(f, "integrality tests\n");
    fprintf(f, " conflicts               : %"PRIu32"\n", stat->num_itest_conflicts);
    fprintf(f, " bound conflicts         : %"PRIu32"\n", stat->num_itest_bound_conflicts);
    fprintf(f, " recheck conflicts       : %"PRIu32"\n", stat->num_itest_recheck_conflicts);
    fprintf(f, "diohpantine solver\n");
    fprintf(f, " gcd conflicts           : %"PRIu32"\n", stat->num_dioph_gcd_conflicts);
    fprintf(f, " dioph checks            : %"PRIu32"\n", stat->num_dioph_checks);
    fprintf(f, " dioph conflicts         : %"PRIu32"\n", stat->num_dioph_conflicts);
    fprintf(f, " bound conflicts         : %"PRIu32"\n", stat->num_dioph_bound_conflicts);
    fprintf(f, " recheck conflicts       : %"PRIu32"\n", stat->num_dioph_recheck_conflicts);
  }
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
  egraph_t *egraph;

  core = ctx->core;
  egraph = ctx->egraph;

  fprintf(f, "boolean variables       : %"PRIu32"\n", core->nvars);
  fprintf(f, "atoms                   : %"PRIu32"\n", core->atoms.natoms);
  if (egraph != NULL) {
    fprintf(f, "egraph terms            : %"PRIu32"\n", egraph->terms.nterms);
    fprintf(f, "app/update reductions   : %"PRIu32"\n", egraph->stats.app_reductions);
  }

  if (context_has_simplex_solver(ctx)) {
    fprintf(f, "arithmetic solver       : Simplex\n");
  } else if (context_has_idl_solver(ctx)) {
    fprintf(f, "arithmetic solver       : IDL Floyd-Warshall\n");
  } else if (context_has_rdl_solver(ctx)) {
    fprintf(f, "arithmetic solver       : RDL Floyd-Warshall\n");
  }
  fprintf(f, "\n");
  fflush(f);
}

void yices_show_statistics(FILE *f, context_t *ctx) {
  smt_core_t *core;
  egraph_t *egraph;
  simplex_solver_t *simplex;
  fun_solver_t *fsolver;

  core = ctx->core;
  egraph = ctx->egraph;

  show_stats(f, &core->stats);
  fprintf(f, " boolean variables       : %"PRIu32"\n", core->nvars);
  fprintf(f, " atoms                   : %"PRIu32"\n", core->atoms.natoms);

  if (egraph != NULL) {
    show_egraph_stats(f, &egraph->stats);
    fprintf(f, " egraph terms            : %"PRIu32"\n", egraph->terms.nterms);
    if (context_has_fun_solver(ctx)) {
      fsolver = ctx->fun_solver;
      show_funsolver_stats(f, &fsolver->stats);
    }
  }

  if (context_has_simplex_solver(ctx)) {
    simplex = ctx->arith_solver;
    if (simplex != NULL) {
      simplex_collect_statistics(simplex);
      show_simplex_stats(f, &simplex->stats);
    }
  }

  if (context_has_bv_solver(ctx)) {
    show_bvsolver_stats(f, ctx->bv_solver);
  }
}


void yices_dump_context(FILE *f, context_t *ctx) {
  // NOT IMPLEMENTED
}
