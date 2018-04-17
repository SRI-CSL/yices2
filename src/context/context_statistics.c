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
 * Context statistics
 */
static void show_context_stats(FILE *f, ctx_stats_t *stat) {
  fprintf(f, "Assertions (time)\n");
  fprintf(f, " base_bool_propagate     : %7.1f\n", stat->base_bool_propagate);
  fprintf(f, " base_th_propagate       : %7.1f\n", stat->base_th_propagate);
  fprintf(f, " flatten_assertion       : %7.1f\n", stat->flatten_assertion);
  fprintf(f, " preprocess_assertion    : %7.1f\n", stat->preprocess_assertion);
  fprintf(f, " assert_toplevel_formula : %7.1f\n", stat->assert_toplevel_formula);
  fprintf(f, " assert_toplevel_intern  : %7.1f\n", stat->assert_toplevel_intern);
  fprintf(f, "No. of assert rounds     : %"PRIu32"\n", stat->nassert_rounds);
  fprintf(f, "No. of asserts           : %"PRIu32"\n", stat->nassert);
}

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
 * Detailed statistics in the smt_core
 */
static void show_detail_stats(FILE *f, dpll_detail_stats_t *stat) {
  fprintf(f, "Core (time)\n");
  fprintf(f, " boolean_propagation         : %7.1f\n", stat->boolean_propagation);
  fprintf(f, " theory_propagation          : %7.1f\n", stat->theory_propagation);
  fprintf(f, " resolve_conflict            : %7.1f\n", stat->resolve_conflict);
  fprintf(f, " smt_restart                 : %7.1f\n", stat->smt_restart);
  fprintf(f, " select_unassigned_literal   : %7.1f\n", stat->select_unassigned_literal);
  fprintf(f, " decide_literal              : %7.1f\n", stat->decide_literal);
  fprintf(f, " add_all_lemmas              : %7.1f\n", stat->add_all_lemmas);
  fprintf(f, " delete_irrelevant_variables : %7.1f\n", stat->delete_irrelevant_variables);
  fprintf(f, " simplify_clause_database    : %7.1f\n", stat->simplify_clause_database);
  fprintf(f, " reduce_clause_database      : %7.1f\n", stat->reduce_clause_database);

  fprintf(f, "No. of atoms asserted        : %"PRIu32"\n", stat->nassert_atom);
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
 * Egraph detailed statistics
 */
static void show_egraph_detail_stats(FILE *f, egraph_detail_stats_t *stat) {
  fprintf(f, "Egraph (time)\n");
  fprintf(f, " propagate                     : %7.1f\n", stat->propagate);
  fprintf(f, "  internal_propagation         : %7.1f\n", stat->internal_propagation);
  fprintf(f, "   reactivate_dynamic_terms    : %7.1f\n", stat->reactivate_dynamic_terms);
  fprintf(f, "   process_equality            : %7.1f\n", stat->process_equality);
  fprintf(f, "    inconsistent_edge          : %7.1f\n", stat->inconsistent_edge);
  fprintf(f, "    invert_branch              : %7.1f\n", stat->invert_branch);
  fprintf(f, "    remove_parents             : %7.1f\n", stat->remove_parents);
  fprintf(f, "    assign_new_label           : %7.1f\n", stat->assign_new_label);
  fprintf(f, "    collect_eqterms            : %7.1f\n", stat->collect_eqterms);
  fprintf(f, "    reprocess_parents          : %7.1f\n", stat->reprocess_parents);
  fprintf(f, "    check_false_eq             : %7.1f\n", stat->check_false_eq);
  fprintf(f, "    atom_propagation           : %7.1f\n", stat->atom_propagation);
  fprintf(f, "    propagate_boolean_equality : %7.1f\n", stat->propagate_boolean_equality);

  fprintf(f, "No. of processed eq.           : %"PRIu32"\n", stat->nprocess_eq);
  fprintf(f, "No. of processed eq. redundant : %"PRIu32"\n", stat->nprocess_eq_redundant);
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

  show_detail_stats(f, &core->tstats);
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

/*
 * Context statistics
 */
static void collect_context_stats(ctx_stats_t *stat, stats_t* st) {
  st->base_bool_propagate = stat->base_bool_propagate;
  st->base_th_propagate = stat->base_th_propagate;
  st->flatten_assertion = stat->flatten_assertion;
  st->preprocess_assertion = stat->preprocess_assertion;
  st->assert_toplevel_formula = stat->assert_toplevel_formula;
  st->assert_toplevel_intern = stat->assert_toplevel_intern;

  st->nassert_rounds = stat->nassert_rounds;
  st->nassert = stat->nassert;
}

/*
 * Statistics in the smt_core
 */
static void collect_stats(dpll_stats_t *stat, stats_t* st) {
  st->restarts = stat->restarts;
  st->simplify_calls = stat->simplify_calls;
  st->reduce_calls = stat->reduce_calls;
  st->decisions = stat->decisions;
  st->random_decisions = stat->random_decisions;
  st->conflicts = stat->conflicts;

  st->remove_calls = stat->remove_calls;
  st->propagations = stat->propagations;
  st->th_props = stat->th_props;
  st->th_prop_lemmas = stat->th_prop_lemmas;
  st->th_conflicts = stat->th_conflicts;
  st->th_conflict_lemmas = stat->th_conflict_lemmas;
  st->prob_literals = stat->prob_literals;
  st->learned_literals = stat->learned_literals;
  st->literals_before_simpl = stat->literals_before_simpl;
  st->subsumed_literals = stat->subsumed_literals;
  st->prob_clauses_deleted = stat->prob_clauses_deleted;
  st->learned_clauses_deleted = stat->learned_clauses_deleted;
  st->bin_clauses_deleted = stat->bin_clauses_deleted;
}

/*
 * Detailed statistics in the smt_core
 */
static void collect_detail_stats(dpll_detail_stats_t *stat, stats_t* st) {
  st->boolean_propagation = stat->boolean_propagation;
  st->theory_propagation = stat->theory_propagation;
  st->resolve_conflict = stat->resolve_conflict;
  st->smt_restart = stat->smt_restart;
  st->select_unassigned_literal = stat->select_unassigned_literal;
  st->decide_literal = stat->decide_literal;
  st->add_all_lemmas = stat->add_all_lemmas;
  st->delete_irrelevant_variables = stat->delete_irrelevant_variables;
  st->simplify_clause_database = stat->simplify_clause_database;
  st->reduce_clause_database = stat->reduce_clause_database;

  st->nassert_atom = stat->nassert_atom;
}

/*
 * Egraph statistics
 */
static void collect_egraph_stats(egraph_stats_t *stat, stats_t* st) {
	st->egraph_eq_props = stat->eq_props;
  st->egraph_th_props = stat->th_props;
  st->egraph_th_conflicts = stat->th_conflicts;
  st->egraph_final_checks = stat->final_checks;
  st->egraph_interface_eqs = stat->interface_eqs;

	st->egraph_app_reductions = stat->app_reductions;
	st->egraph_nd_lemmas = stat->nd_lemmas;
	st->egraph_aux_eqs = stat->aux_eqs;
	st->egraph_boolack_lemmas = stat->boolack_lemmas;
	st->egraph_ack_lemmas = stat->ack_lemmas;
}

/*
 * Egraph detailed statistics
 */
static void collect_egraph_detail_stats(egraph_detail_stats_t *stat, stats_t* st) {
  st->propagate = stat->propagate;
  st->internal_propagation = stat->internal_propagation;
  st->reactivate_dynamic_terms = stat->reactivate_dynamic_terms;
  st->process_equality = stat->process_equality;
  st->inconsistent_edge = stat->inconsistent_edge;
  st->invert_branch = stat->invert_branch;
  st->remove_parents = stat->remove_parents;
  st->assign_new_label = stat->assign_new_label;
  st->collect_eqterms = stat->collect_eqterms;
  st->reprocess_parents = stat->reprocess_parents;
  st->check_false_eq = stat->check_false_eq;
  st->atom_propagation = stat->atom_propagation;
  st->propagate_boolean_equality = stat->propagate_boolean_equality;

  st->nprocess_eq = stat->nprocess_eq;
  st->nprocess_eq_redundant = stat->nprocess_eq_redundant;
}

/*
 * Array/function solver statistics
 */
static void collect_funsolver_stats(fun_solver_stats_t *stat, stats_t* st) {
    st->num_init_vars = stat->num_init_vars;
    st->num_init_edges = stat->num_init_edges;
    st->num_update_axiom1 = stat->num_update_axiom1;
    st->num_update_axiom2 = stat->num_update_axiom2;
    st->num_extensionality_axiom = stat->num_extensionality_axiom;
}

/*
 * Bitvector solver statistics
 */
static void collect_bvsolver_stats(bv_solver_t *solver, stats_t* st) {
    st->bv_variables = bv_solver_num_vars(solver);
	st->bv_atoms = bv_solver_num_atoms(solver);
	st->bv_eq_atoms = bv_solver_num_eq_atoms(solver);
	st->bv_dyn_eq_atoms = solver->stats.on_the_fly_atoms;
	st->bv_ge_atoms = bv_solver_num_ge_atoms(solver);
	st->bv_sge_atoms = bv_solver_num_sge_atoms(solver);
	st->bv_equiv_lemmas = solver->stats.equiv_lemmas;
	st->bv_equiv_conflicts = solver->stats.equiv_conflicts;
	st->bv_semi_equiv_lemmas = solver->stats.half_equiv_lemmas;
	st->bv_interface_lemmas = solver->stats.interface_lemmas;
}

bool yices_collect_presearch_stats(context_t *ctx, stats_t* st) {
  smt_core_t *core;
  egraph_t *egraph;

  core = ctx->core;
  egraph = ctx->egraph;

  st->pre_boolean_variables = core->nvars;
  st->pre_atoms = core->atoms.natoms;


  if (egraph != NULL) {
	st->pre_egraph_terms = egraph->terms.nterms;
	st->pre_egraph_app_reductions = egraph->stats.app_reductions;
  }

  if (context_has_simplex_solver(ctx)) {
	  return false;
  } else if (context_has_idl_solver(ctx)) {
	  return false;
  } else if (context_has_rdl_solver(ctx)) {
	  return false;
  }
  return true;
}

bool yices_collect_statistics(context_t *ctx, stats_t* st) {
  smt_core_t *core;
  egraph_t *egraph;
  fun_solver_t *fsolver;

  core = ctx->core;
  egraph = ctx->egraph;

  st->boolean_variables = core->nvars;
  st->atoms = core->atoms.natoms;

  collect_context_stats(&ctx->stats, st);
  collect_stats(&core->stats, st);
  collect_detail_stats(&core->tstats, st);


  if (egraph != NULL) {
    st->egraph_terms = egraph->terms.nterms;
    collect_egraph_stats(&egraph->stats, st);
    collect_egraph_detail_stats(&egraph->tstats, st);
    if (context_has_fun_solver(ctx)) {
      fsolver = ctx->fun_solver;
      collect_funsolver_stats(&fsolver->stats, st);
    }
  }

  if (context_has_bv_solver(ctx)) {
    collect_bvsolver_stats(ctx->bv_solver, st);
  }

  if (context_has_simplex_solver(ctx)) {
	  return false;
  }
  return true;
}

void yices_dump_context(FILE *f, context_t *ctx) {
  // NOT IMPLEMENTED
}
