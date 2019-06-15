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

#include "uf_plugin.h"

#include "mcsat/trail.h"
#include "mcsat/tracing.h"
#include "mcsat/watch_list_manager.h"
#include "mcsat/utils/scope_holder.h"
#include "mcsat/value.h"

#include "mcsat/eq/equality_graph.h"

#include "utils/int_array_sort2.h"
#include "utils/ptr_array_sort2.h"
#include "model/models.h"

#include "terms/terms.h"
#include "inttypes.h"
/* #include "terms/term_manager.h" */

typedef struct {

  /** The plugin interface */
  plugin_t plugin_interface;

  /** The plugin context */
  plugin_context_t* ctx;

  /** Scope holder for the int variables */
  scope_holder_t scope;

  /** Conflict  */
  ivector_t conflict;

  /** The term manager (no ITE simplification) */
  term_manager_t* tm;

  /** Equality graph */
  eq_graph_t eq_graph;

  /** Stuff added to eq_graph */
  ivector_t eq_graph_addition_trail;

  /** Tmp vector */
  int_mset_t tmp;

  struct {
    statistic_int_t* egraph_terms;
    statistic_int_t* propagations;
    statistic_int_t* conflicts;
    statistic_avg_t* avg_conflict_size;
    statistic_avg_t* avg_explanation_size;
  } stats;

  /** Exception handler */
  jmp_buf* exception;

} uf_plugin_t;

static
void uf_plugin_stats_init(uf_plugin_t* uf) {
  // Add statistics
  uf->stats.propagations = statistics_new_int(uf->ctx->stats, "mcsat::uf::propagations");
  uf->stats.conflicts = statistics_new_int(uf->ctx->stats, "mcsat::uf::conflicts");
  uf->stats.egraph_terms = statistics_new_int(uf->ctx->stats, "mcsat::uf::egraph_terms");
  uf->stats.avg_conflict_size = statistics_new_avg(uf->ctx->stats, "mcsat::uf::avg_conflict_size");
  uf->stats.avg_explanation_size = statistics_new_avg(uf->ctx->stats, "mcsat::uf::avg_explanation_size");
}

static
void uf_plugin_bump_terms_and_reset(uf_plugin_t* uf, int_mset_t* to_bump) {
  uint32_t i;
  for (i = 0; i < to_bump->element_list.size; ++ i) {
    term_t t = to_bump->element_list.data[i];
    variable_t t_var = variable_db_get_variable_if_exists(uf->ctx->var_db, t);
    if (t != variable_null) {
      int_hmap_pair_t* find = int_hmap_find(&to_bump->count_map, t);
      uf->ctx->bump_variable_n(uf->ctx, t_var, find->val);
    }
  }
  int_mset_clear(to_bump);
}

static
void uf_plugin_construct(plugin_t* plugin, plugin_context_t* ctx) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  uf->ctx = ctx;

  scope_holder_construct(&uf->scope);
  init_ivector(&uf->conflict, 0);
  int_mset_construct(&uf->tmp, NULL_TERM);

  // Terms
  ctx->request_term_notification_by_kind(ctx, APP_TERM);
  ctx->request_term_notification_by_kind(ctx, ARITH_RDIV);
  ctx->request_term_notification_by_kind(ctx, ARITH_IDIV);
  ctx->request_term_notification_by_kind(ctx, ARITH_MOD);
  ctx->request_term_notification_by_kind(ctx, EQ_TERM);

  // Types
  ctx->request_term_notification_by_type(ctx, UNINTERPRETED_TYPE);

  // Decisions
  ctx->request_decision_calls(ctx, UNINTERPRETED_TYPE);

  // Equality graph
  eq_graph_construct(&uf->eq_graph, ctx, "uf");
  init_ivector(&uf->eq_graph_addition_trail, 0);

  // stats
  uf_plugin_stats_init(uf);
}

static
void uf_plugin_destruct(plugin_t* plugin) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;
  scope_holder_destruct(&uf->scope);
  delete_ivector(&uf->conflict);
  int_mset_destruct(&uf->tmp);
  eq_graph_destruct(&uf->eq_graph);
  delete_ivector(&uf->eq_graph_addition_trail);
}

static
void uf_plugin_process_eq_graph_propagations(uf_plugin_t* uf, trail_token_t* prop) {
  // Process any propagated terms
  if (eq_graph_has_propagated_terms(&uf->eq_graph)) {
    uint32_t i = 0;
    ivector_t eq_propagations;
    init_ivector(&eq_propagations, 0);
    eq_graph_get_propagated_terms(&uf->eq_graph, &eq_propagations);
    for (; i < eq_propagations.size; ++ i) {
      // Term to propagate
      term_t t = eq_propagations.data[i];
      // Variable to propagate
      variable_t t_var = variable_db_get_variable_if_exists(uf->ctx->var_db, t);
      if (t_var != variable_null) {
        // Only set values of uninterpreted and boolean type
        type_kind_t t_type_kind = term_type_kind(uf->ctx->terms, t);
        if (t_type_kind == UNINTERPRETED_TYPE || t_type_kind == BOOL_TYPE) {
          const mcsat_value_t* v = eq_graph_get_propagated_term_value(&uf->eq_graph, t);
          if (!trail_has_value(uf->ctx->trail, t_var)) {
            if (ctx_trace_enabled(uf->ctx, "mcsat::eq::propagate")) {
              FILE* out = ctx_trace_out(uf->ctx);
              ctx_trace_term(uf->ctx, t);
              fprintf(out, " -> ");
              mcsat_value_print(v, out);
              fprintf(out, "\n");
            }
            prop->add(prop, t_var, v);
            (*uf->stats.propagations) ++;
          } else {
            // Ignore, we will report conflict
          }
        }
      }
    }
    delete_ivector(&eq_propagations);
  }
}

static
void uf_plugin_add_to_eq_graph(uf_plugin_t* uf, term_t t, bool record) {

  term_table_t* terms = uf->ctx->terms;

  // The kind
  term_kind_t t_kind = term_kind(terms, t);

  // Add to equality graph
  composite_term_t* t_desc = NULL;
  uint32_t children_start = 0;
  switch (t_kind) {
  case APP_TERM:
    t_desc = app_term_desc(terms, t);
    eq_graph_add_ufun_term(&uf->eq_graph, t, t_desc->arg[0], t_desc->arity - 1, t_desc->arg + 1);
    children_start = 1;
    break;
  case ARITH_RDIV:
    t_desc = arith_rdiv_term_desc(terms, t);
    eq_graph_add_ifun_term(&uf->eq_graph, t, ARITH_RDIV, 2, t_desc->arg);
    break;
  case ARITH_IDIV:
    t_desc = arith_idiv_term_desc(terms, t);
    eq_graph_add_ifun_term(&uf->eq_graph, t, ARITH_IDIV, 2, t_desc->arg);
    break;
  case ARITH_MOD:
    t_desc = arith_mod_term_desc(terms, t);
    eq_graph_add_ifun_term(&uf->eq_graph, t, ARITH_MOD, 2, t_desc->arg);
    break;
  case EQ_TERM:
    t_desc = eq_term_desc(terms, t);
    eq_graph_add_ifun_term(&uf->eq_graph, t, EQ_TERM, 2, t_desc->arg);
    break;
  default:
    assert(false);
  }

  // Make sure the subterms are registered
  uint32_t i;
  for (i = children_start; i < t_desc->arity; ++ i) {
    term_t c = t_desc->arg[i];
    variable_db_get_variable(uf->ctx->var_db, c);
  }

  // Record addition so we can re-add on backtracks
  if (record) {
    (*uf->stats.egraph_terms) ++;
    ivector_push(&uf->eq_graph_addition_trail, t);
  }
}


static
void uf_plugin_new_term_notify(plugin_t* plugin, term_t t, trail_token_t* prop) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  if (ctx_trace_enabled(uf->ctx, "mcsat::new_term")) {
    ctx_trace_printf(uf->ctx, "uf_plugin_new_term_notify: ");
    ctx_trace_term(uf->ctx, t);
  }

  term_kind_t t_kind = term_kind(uf->ctx->terms, t);

  switch (t_kind) {
  case ARITH_MOD:
  case ARITH_IDIV:
  case ARITH_RDIV:
  case APP_TERM:
  case EQ_TERM:
    // Application terms (or other terms we treat as uninterpreted)
    uf_plugin_add_to_eq_graph(uf, t, true);
    break;
  default:
    // All other is of uninterpreted sort, and we treat as variables
    break;
  }

}

/* <<<<<<< HEAD */
/* ======= */
/* /\** Get the value representative of the application representative. *\/ */
/* static inline */
/* variable_t uf_plugin_get_val_rep(uf_plugin_t* uf, variable_t app_rep) { */
/*   int_hmap_pair_t* find = int_hmap_find(&uf->app_rep_to_val_rep, app_rep); */
/*   if (find == NULL) { */
/*     return variable_null; */
/*   } else { */
/*     return find->val; */
/*   } */
/* } */

/* /\** Set the value representative of the application representative. *\/ */
/* static inline */
/* void uf_plugin_set_val_rep(uf_plugin_t* uf, variable_t app_rep, variable_t val_rep) { */
/*   assert(uf_plugin_get_val_rep(uf, app_rep) == variable_null); */
/*   int_hmap_add(&uf->app_rep_to_val_rep, app_rep, val_rep); */
/*   ivector_push(&uf->app_reps_with_val_rep, app_rep); */
/* } */

/* static */
/* void uf_plugin_propagate_eqs(uf_plugin_t* uf, variable_t var, trail_token_t* prop) { */
/*   const mcsat_trail_t* trail = uf->ctx->trail; */
/*   variable_db_t* var_db = uf->ctx->var_db; */

/*   // Go through all the variable lists (constraints) where we're watching var */
/*   remove_iterator_t it; */
/*   variable_list_ref_t var_list_ref; */
/*   variable_t* var_list; */
/*   variable_t* var_list_it; */

/*   // Get the watch-list and process */
/*   remove_iterator_construct(&it, &uf->wlm_eqs, var); */
/*   while (trail_is_consistent(trail) && !remove_iterator_done(&it)) { */

/*     // Get the current list where var appears */
/*     var_list_ref = remove_iterator_get_list_ref(&it); */
/*     var_list = watch_list_manager_get_list(&uf->wlm_eqs, var_list_ref); */

/*     // x = y variable */
/*     variable_t eq_var = watch_list_manager_get_constraint(&uf->wlm_eqs, var_list_ref); */
/*     if (ctx_trace_enabled(uf->ctx, "uf_plugin")) { */
/*       ctx_trace_printf(uf->ctx, "uf_plugin_propagate: eq_var = "); */
/*       ctx_trace_term(uf->ctx, variable_db_get_term(var_db, eq_var)); */
/*     } */

/*     // Put the variable to [1] so that [0] is the unit one */
/*     if (var_list[0] == var && var_list[1] != variable_null) { */
/*       var_list[0] = var_list[1]; */
/*       var_list[1] = var; */
/*     } */

/*     // Find a new watch (start from [2]) */
/*     var_list_it = var_list + 1; */
/*     if (*var_list_it != variable_null) { */
/*       for (++var_list_it; *var_list_it != variable_null; ++var_list_it) { */
/*         if (!trail_has_value(trail, *var_list_it)) { */
/*           // Swap with var_list[1] */
/*           var_list[1] = *var_list_it; */
/*           *var_list_it = var; */
/*           // Add to new watch */
/*           watch_list_manager_add_to_watch(&uf->wlm_eqs, var_list_ref, var_list[1]); */
/*           // Don't watch this one */
/*           remove_iterator_next_and_remove(&it); */
/*           break; */
/*         } */
/*       } */
/*     } */

/*     if (*var_list_it == variable_null) { */
/*       if (ctx_trace_enabled(uf->ctx, "uf_plugin")) { */
/*         ctx_trace_printf(uf->ctx, "no watch found\n"); */
/*       } */
/*       // We did not find a new watch so vars[1], ..., vars[n] are assigned. */
/*       // If vars[0] is an equality, we propagate it, otherwise, we update */
/*       // the feasibility set */
/*       if (var_list[0] == eq_var) { */

/*         // lhs = rhs */
/*         variable_t lhs = var_list[1]; */
/*         variable_t rhs = var_list[2]; */

/*         // Check the model value */
/*         const mcsat_value_t* lhs_value = trail_get_value(trail, lhs); */
/*         const mcsat_value_t* rhs_value = trail_get_value(trail, rhs); */
/*         int lhs_eq_rhs = mcsat_value_eq(lhs_value, rhs_value); */

/*         // Evaluate the equality if it doesn't have a value */
/*         if (!trail_has_value(trail, eq_var)) { */
/*           if (lhs_eq_rhs) { */
/*             prop->add(prop, eq_var, &mcsat_value_true); */
/*           } else { */
/*             prop->add(prop, eq_var, &mcsat_value_false); */
/*           } */
/*         } else { */
/*           // Equality already has a value, check that it's the right one */
/*           bool eq_var_value = trail_get_boolean_value(trail, eq_var); */
/*           if (eq_var_value != lhs_eq_rhs) { */
/*             if (ctx_trace_enabled(uf->ctx, "uf_plugin::conflict")) { */
/*               ctx_trace_printf(uf->ctx, "eq conflict 1\n"); */
/*             } */
/*             term_t eq_term = variable_db_get_term(var_db, eq_var); */
/*             // Equality can not be both true and false at the same time */
/*             ivector_reset(&uf->conflict); */
/*             ivector_push(&uf->conflict, eq_term); */
/*             ivector_push(&uf->conflict, opposite_term(eq_term)); */
/*             prop->conflict(prop); */
/*           } */
/*         } */
/*       } else { */

/*         // Check if equality is true or false and add to feasibility db */
/*         variable_t lhs = var_list[0]; */
/*         variable_t rhs = var_list[1] == eq_var ? var_list[2] : var_list[1]; */

/*         // Is the equailty true */
/*         bool eq_true = trail_get_boolean_value(trail, eq_var); */

/*         // Get the value of the right-hand side (have to cast, since yices rationals */
/*         // don't have const parameters. */
/*         mcsat_value_t* rhs_val = (mcsat_value_t*) trail_get_value(trail, rhs); */
/*         assert(rhs_val->type == VALUE_RATIONAL); */
/*         assert(q_fits_int32(&rhs_val->q)); */
/*         int32_t rhs_val_int; */
/*         q_get32(&rhs_val->q, &rhs_val_int); */

/*         // Update the feasible set */
/*         bool feasible; */
/*         if (eq_true) { */
/*           feasible = uf_feasible_set_db_set_equal(uf->feasible, lhs, rhs_val_int, eq_var); */

/*           // Also propagate the value */
/*           if (!trail_has_value(trail, lhs)) { */
/*             rational_t q; */
/*             q_init(&q); */
/*             q_set32(&q, rhs_val_int); */
/*             mcsat_value_t value; */
/*             mcsat_value_construct_rational(&value, &q); */
/*             prop->add(prop, lhs, &value); */
/*             mcsat_value_destruct(&value); */
/*             q_clear(&q); */
/*           } */

/*         } else { */
/*           feasible = uf_feasible_set_db_set_disequal(uf->feasible, lhs, rhs_val_int, eq_var); */
/*         } */

/*         // Ooops, a conflict */
/*         if (!feasible) { */
/*           if (ctx_trace_enabled(uf->ctx, "uf_plugin::conflict")) { */
/*             ctx_trace_printf(uf->ctx, "eq conflict 2\n"); */
/*           } */
/*           ivector_reset(&uf->conflict); */
/*           uf_feasible_set_db_get_conflict(uf->feasible, lhs, &uf->conflict); */
/*           prop->conflict(prop); */
/*         } */
/*       } */

/*       // Keep the watch, and continue */
/*       remove_iterator_next_and_keep(&it); */
/*     } */
/*   } */

/*   // Done, destruct the iterator */
/*   remove_iterator_destruct(&it); */
/* } */

/* static */
/* void uf_plugin_get_app_conflict(uf_plugin_t* uf, variable_t lhs, variable_t rhs) { */

/*   // CRAP ABOUT TERM NORMALIZATION: We CANT normalize the terms, since otherwise */
/*   // terms like 1 + x = 1 + y would normalize to x = y. To be on the safe side, */
/*   // We always make equalities as binary arith equalities */

/*   ivector_reset(&uf->conflict); */

/*   variable_db_t* var_db = uf->ctx->var_db; */
/*   term_table_t* terms = uf->ctx->terms; */
/*   const mcsat_trail_t* trail = uf->ctx->trail; */

/*   // We have a conflict x1 != y1 or .... or xn != y2 or f(x) != f(y) */

/*   // Add function equality first */
/*   term_t fx = variable_db_get_term(var_db, lhs); */
/*   term_t fy = variable_db_get_term(var_db, rhs); */
/*   assert(fx != fy); */
/*   // Check the type, we treat Booleans specially */
/*   type_kind_t f_type = term_type_kind(terms, fx); */
/*   if (f_type == BOOL_TYPE) { */
/*     if (trail_get_boolean_value(trail, lhs)) { */
/*       ivector_push(&uf->conflict, fx); */
/*     } else { */
/*       ivector_push(&uf->conflict, opposite_term(fx)); */
/*     } */
/*     if (trail_get_boolean_value(trail, rhs)) { */
/*       ivector_push(&uf->conflict, fy); */
/*     } else { */
/*       ivector_push(&uf->conflict, opposite_term(fy)); */
/*     } */
/*   } else { */
/*     term_t fx_eq_fy = mk_eq(&uf->tm, fx, fy); */
/*     ivector_push(&uf->conflict, opposite_term(fx_eq_fy)); */
/*   } */

/*   // Now add all the intermediate equalities */
/*   composite_term_t* fx_app = app_reps_get_uf_descriptor(terms, fx); */
/*   composite_term_t* fy_app = app_reps_get_uf_descriptor(terms, fy); */
/*   assert(app_reps_get_uf(terms, fx) == app_reps_get_uf(terms, fy)); */
/*   assert(fx_app->arity == fy_app->arity); */
/*   uint32_t i = app_reps_get_uf_start(terms, fx); */
/*   uint32_t n = fx_app->arity; */
/*   for (; i < n; ++ i) { */
/*     term_t x = fx_app->arg[i]; */
/*     term_t y = fy_app->arg[i]; */
/*     type_kind_t type = term_type_kind(terms, x); */
/*     if (type == BOOL_TYPE) { */
/*       variable_t x_var = variable_db_get_variable(var_db, x); */
/*       variable_t y_var = variable_db_get_variable(var_db, y); */
/*       if (trail_get_boolean_value(trail, x_var)) { */
/*         ivector_push(&uf->conflict, x); */
/*       } else { */
/*         ivector_push(&uf->conflict, opposite_term(x)); */
/*       } */
/*       if (trail_get_boolean_value(trail, y_var)) { */
/*         ivector_push(&uf->conflict, y); */
/*       } else { */
/*         ivector_push(&uf->conflict, opposite_term(y)); */
/*       } */
/*     } else { */
/*       term_t x_eq_y = mk_eq(&uf->tm, x, y); */
/*       // Don't add trivially true facts */
/*       if (x_eq_y != bool2term(true)) { */
/*         ivector_push(&uf->conflict, x_eq_y); */
/*       } */
/*     } */
/*   } */
/* } */

/* static */
/* void uf_plugin_propagate_apps(uf_plugin_t* uf, variable_t var, trail_token_t* prop) { */

/*   const mcsat_trail_t* trail = uf->ctx->trail; */
/*   variable_db_t* var_db = uf->ctx->var_db; */

/*   // Go through all the variable lists (constraints) where we're watching var */
/*   remove_iterator_t it; */
/*   variable_list_ref_t var_list_ref; */
/*   variable_t* var_list; */
/*   variable_t* var_list_it; */

/*   // Get the watch-list and process */
/*   remove_iterator_construct(&it, &uf->wlm_apps, var); */
/*   while (trail_is_consistent(trail) && !remove_iterator_done(&it)) { */

/*     // Get the current list where var appears */
/*     var_list_ref = remove_iterator_get_list_ref(&it); */
/*     var_list = watch_list_manager_get_list(&uf->wlm_apps, var_list_ref); */

/*     // f(x) variable */
/*     variable_t app_var = watch_list_manager_get_constraint(&uf->wlm_apps, var_list_ref); */
/*     if (ctx_trace_enabled(uf->ctx, "uf_plugin")) { */
/*       ctx_trace_printf(uf->ctx, "uf_plugin_propagate: app_var = "); */
/*       ctx_trace_term(uf->ctx, variable_db_get_term(var_db, app_var)); */
/*     } */

/*     // Find a new watch (start from [1]) */
/*     var_list_it = var_list + 1; */
/*     assert(var == var_list[0]); */
/*     for (; *var_list_it != variable_null; ++var_list_it) { */
/*       if (!trail_has_value(trail, *var_list_it)) { */
/*         // Swap with var_list[1] */
/*         var_list[0] = *var_list_it; */
/*         *var_list_it = var; */
/*         // Add to new watch */
/*         watch_list_manager_add_to_watch(&uf->wlm_apps, var_list_ref, var_list[0]); */
/*         // Don't watch this one */
/*         remove_iterator_next_and_remove(&it); */
/*         break; */
/*       } */
/*     } */

/*     if (*var_list_it == variable_null) { */
/*       // We did not find a new watch so vars[1], ..., vars[n] are assigned. */
/*       // Add and get the representative of this assignment. */
/*       variable_t rep_var = app_reps_get_rep(&uf->app_reps, app_var); */
/*       assert(rep_var != variable_null); */
/*       if (trail_has_value(trail, app_var)) { */
/*         variable_t val_rep_var = uf_plugin_get_val_rep(uf, rep_var); */
/*         // If already has one, and both assigned to a value, check if it's the same value */
/*         if (val_rep_var == variable_null) { */
/*           uf_plugin_set_val_rep(uf, rep_var, app_var); */
/*         } else if (val_rep_var != app_var) { */
/*           const mcsat_value_t* app_value = trail_get_value(trail, app_var); */
/*           const mcsat_value_t* val_rep_value = trail_get_value(trail, val_rep_var); */
/*           if (!mcsat_value_eq(app_value, val_rep_value)) { */
/*             if (ctx_trace_enabled(uf->ctx, "uf_plugin::conflict")) { */
/*               ctx_trace_printf(uf->ctx, "app conflict 1\n"); */
/*             } */
/*             uf_plugin_get_app_conflict(uf, app_var, val_rep_var); */
/*             prop->conflict(prop); */
/*           } */
/*         } */
/*       } */
/*       // Keep the watch, and continue */
/*       remove_iterator_next_and_keep(&it); */
/*     } */
/*   } */

/*   // If a function application, check if it's fully assigned */
/*   term_t var_term = variable_db_get_term(uf->ctx->var_db, var); */
/*   if (app_reps_is_uf(uf->ctx->terms, var_term)) { */
/*     // Get the application representative, if any */
/*     variable_t rep_var = app_reps_get_rep(&uf->app_reps, var); */
/*     if (rep_var != variable_null) { */
/*       // Get the value representative */
/*       variable_t val_rep_var = uf_plugin_get_val_rep(uf, rep_var); */
/*       if (val_rep_var == variable_null) { */
/*         // No value reps yet, take it over */
/*         uf_plugin_set_val_rep(uf, rep_var, var); */
/*       } else if (val_rep_var != var) { */
/*         const mcsat_value_t* var_value = trail_get_value(trail, var); */
/*         const mcsat_value_t* val_rep_value = trail_get_value(trail, val_rep_var); */
/*         if (!mcsat_value_eq(var_value, val_rep_value)) { */
/*           if (ctx_trace_enabled(uf->ctx, "uf_plugin::conflict")) { */
/*             ctx_trace_printf(uf->ctx, "app conflict 2\n"); */
/*           } */
/*           uf_plugin_get_app_conflict(uf, var, val_rep_var); */
/*           prop->conflict(prop); */
/*         } */
/*       } */
/*     } */
/*   } */

/*   // Done, destruct the iterator */
/*   remove_iterator_destruct(&it); */
/* } */

/* >>>>>>> master */
static
void uf_plugin_propagate(plugin_t* plugin, trail_token_t* prop) {

  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  if (ctx_trace_enabled(uf->ctx, "uf_plugin")) {
    ctx_trace_printf(uf->ctx, "uf_plugin_propagate()\n");
  }

  // If we're not watching anything, we just ignore
  if (eq_graph_term_size(&uf->eq_graph) == 0) {
    return;
  }

  // Propagate known terms
  eq_graph_propagate_trail(&uf->eq_graph);
  uf_plugin_process_eq_graph_propagations(uf, prop);

  // Check for conflicts
  if (uf->eq_graph.in_conflict) {
    // Report conflict
    prop->conflict(prop);
    (*uf->stats.conflicts) ++;
    // Construct the conflict
    eq_graph_get_conflict(&uf->eq_graph, &uf->conflict, NULL, &uf->tmp);
    uf_plugin_bump_terms_and_reset(uf, &uf->tmp);
    statistic_avg_add(uf->stats.avg_conflict_size, uf->conflict.size);
  }
}

static
void uf_plugin_push(plugin_t* plugin) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  // Pop the int variable values
  scope_holder_push(&uf->scope,
      &uf->eq_graph_addition_trail.size,
      NULL);

  eq_graph_push(&uf->eq_graph);
}

static
void uf_plugin_pop(plugin_t* plugin) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  uint32_t old_eq_graph_addition_trail_size;

  // Pop the int variable values
  scope_holder_pop(&uf->scope,
      &old_eq_graph_addition_trail_size,
      NULL);

  eq_graph_pop(&uf->eq_graph);

  // Re-add all the terms to eq graph
  uint32_t i;
  for (i = old_eq_graph_addition_trail_size; i < uf->eq_graph_addition_trail.size; ++ i) {
    term_t t = uf->eq_graph_addition_trail.data[i];
    uf_plugin_add_to_eq_graph(uf, t, false);
  }

  // Clear the conflict
  ivector_reset(&uf->conflict);
}

bool value_cmp(void* data, void* v1_void, void* v2_void) {

  const mcsat_value_t* v1 = (mcsat_value_t*) v1_void;
  const mcsat_value_t* v2 = (mcsat_value_t*) v2_void;

  assert(v1->type == VALUE_RATIONAL);
  assert(v2->type == VALUE_RATIONAL);

  return q_cmp(&v1->q, &v2->q) < 0;
}

static
void uf_plugin_decide(plugin_t* plugin, variable_t x, trail_token_t* decide, bool must) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  if (ctx_trace_enabled(uf->ctx, "uf_plugin")) {
    ctx_trace_printf(uf->ctx, "uf_plugin_decide: ");
    ctx_trace_term(uf->ctx, variable_db_get_term(uf->ctx->var_db, x));
  }

  assert(eq_graph_is_trail_propagated(&uf->eq_graph));

  // Get the cached value
  const mcsat_value_t* x_cached_value = NULL;
  if (trail_has_cached_value(uf->ctx->trail, x)) {
    x_cached_value = trail_get_cached_value(uf->ctx->trail, x);
  }

  // Pick a value not in the forbidden set
  term_t x_term = variable_db_get_term(uf->ctx->var_db, x);
  pvector_t forbidden;
  init_pvector(&forbidden, 0);
  bool cache_ok = eq_graph_get_forbidden(&uf->eq_graph, x_term, &forbidden, x_cached_value);
  if (ctx_trace_enabled(uf->ctx, "uf_plugin::decide")) {
    ctx_trace_printf(uf->ctx, "picking !=");
    uint32_t i;
    for (i = 0; i < forbidden.size; ++ i) {
      const mcsat_value_t* v = forbidden.data[i];
      ctx_trace_printf(uf->ctx, " ");
      mcsat_value_print(v, ctx_trace_out(uf->ctx));
    }
    ctx_trace_printf(uf->ctx, "\n");
  }

  int32_t picked_value = 0;
  if (!cache_ok) {
    // Pick smallest value not in forbidden list
    ptr_array_sort2(forbidden.data, forbidden.size, NULL, value_cmp);
    if (ctx_trace_enabled(uf->ctx, "uf_plugin::decide")) {
      ctx_trace_printf(uf->ctx, "picking !=");
      uint32_t i;
      for (i = 0; i < forbidden.size; ++ i) {
        const mcsat_value_t* v = forbidden.data[i];
        ctx_trace_printf(uf->ctx, " ");
        mcsat_value_print(v, ctx_trace_out(uf->ctx));
      }
      ctx_trace_printf(uf->ctx, "\n");
    }
    uint32_t i;
    picked_value = 0;
    for (i = 0; i < forbidden.size; ++ i) {
      const mcsat_value_t* v = forbidden.data[i];
      assert(v->type == VALUE_RATIONAL);
      int32_t v_int = 0;
      bool ok = q_get32((rational_t*)&v->q, &v_int);
      (void) ok;
      assert(ok);
      if (picked_value < v_int) {
        // Found a gap, pick
        break;
      } else {
        picked_value = v_int + 1;
      }
    }
  } else {
    assert(x_cached_value->type == VALUE_RATIONAL);
    bool ok = q_get32((rational_t*)&x_cached_value->q, &picked_value);
    (void) ok;
    assert(ok);
  }

  if (ctx_trace_enabled(uf->ctx, "uf_plugin::decide")) {
    ctx_trace_printf(uf->ctx, "picked %"PRIi32"\n", picked_value);
  }

  // Remove temp
  delete_pvector(&forbidden);

  // Make the yices rational
  rational_t q;
  q_init(&q);
  q_set32(&q, picked_value);

  // Make the mcsat value
  mcsat_value_t value;
  mcsat_value_construct_rational(&value, &q);

  // Set the value
  decide->add(decide, x, &value);

  // Remove temps
  mcsat_value_destruct(&value);
  q_clear(&q);
}

static
void uf_plugin_gc_mark(plugin_t* plugin, gc_info_t* gc_vars) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  // Mark all asserted stuff, and all the children of marked stuff
  eq_graph_gc_mark(&uf->eq_graph, gc_vars, EQ_GRAPH_MARK_ALL);
}

static
void uf_plugin_gc_sweep(plugin_t* plugin, const gc_info_t* gc_vars) {
  // Should be nothing!
}

static
void uf_plugin_get_conflict(plugin_t* plugin, ivector_t* conflict) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;
  ivector_swap(conflict, &uf->conflict);
  ivector_reset(&uf->conflict);
}

static
term_t uf_plugin_explain_propagation(plugin_t* plugin, variable_t var, ivector_t* reasons) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  term_t var_term = variable_db_get_term(uf->ctx->var_db, var);

  if (ctx_trace_enabled(uf->ctx, "uf_plugin")) {
    ctx_trace_printf(uf->ctx, "uf_plugin_explain_propagation():\n");
    ctx_trace_term(uf->ctx, var_term);
    ctx_trace_printf(uf->ctx, "var = %"PRIu32"\n", var);
  }

  term_t subst = eq_graph_explain_term_propagation(&uf->eq_graph, var_term, reasons, NULL, &uf->tmp);
  uf_plugin_bump_terms_and_reset(uf, &uf->tmp);
  statistic_avg_add(uf->stats.avg_explanation_size, reasons->size);
  return subst;
}

static
bool uf_plugin_explain_evaluation(plugin_t* plugin, term_t t, int_mset_t* vars, mcsat_value_t* value) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  if (ctx_trace_enabled(uf->ctx, "uf_plugin")) {
    ctx_trace_printf(uf->ctx, "uf_plugin_explain_evaluation():\n");
    ctx_trace_term(uf->ctx, t);
  }

  term_table_t* terms = uf->ctx->terms;
  variable_db_t* var_db = uf->ctx->var_db;
  const mcsat_trail_t* trail = uf->ctx->trail;

  // Get all the variables and make sure they are all assigned.
  term_kind_t t_kind = term_kind(terms, t);
  if (t_kind == EQ_TERM) {
    composite_term_t* eq_desc = eq_term_desc(terms, t);
    term_t lhs_term = eq_desc->arg[0];
    term_t rhs_term = eq_desc->arg[1];
    variable_t lhs_var = variable_db_get_variable_if_exists(var_db, lhs_term);
    variable_t rhs_var = variable_db_get_variable_if_exists(var_db, rhs_term);

    // Check if both are assigned
    if (lhs_var == variable_null) {
      return false;
    }
    if (rhs_var == variable_null) {
      return false;
    }
    if (!trail_has_value(trail, lhs_var)) {
      return false;
    }
    if (!trail_has_value(trail, rhs_var)) {
      return false;
    }

    const mcsat_value_t* lhs_value = trail_get_value(trail, lhs_var);
    const mcsat_value_t* rhs_value = trail_get_value(trail, rhs_var);
    bool lhs_eq_rhs = mcsat_value_eq(lhs_value, rhs_value);
    bool negated = is_neg_term(t);
    if ((negated && (value->b != lhs_eq_rhs)) ||
        (!negated && (value->b == lhs_eq_rhs))) {
      int_mset_add(vars, lhs_var);
      int_mset_add(vars, rhs_var);
      return true;
    }
  }

  // Default: return false for cases like f(x) -> false, this is done in the
  // core
  return false;
}

static
void uf_plugin_set_exception_handler(plugin_t* plugin, jmp_buf* handler) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;
  uf->exception = handler;
}

typedef struct {
  term_table_t* terms;
  variable_db_t* var_db;
} model_sort_data_t;


//static
//bool uf_plugin_build_model_compare(void *data, variable_t t1_var, variable_t t2_var) {
//  model_sort_data_t* ctx = (model_sort_data_t*) data;
//  term_t t1 = variable_db_get_term(ctx->var_db, t1_var);
//  term_t t2 = variable_db_get_term(ctx->var_db, t2_var);
//  int32_t t1_app = app_reps_get_uf(ctx->terms, t1);
//  int32_t t2_app = app_reps_get_uf(ctx->terms, t2);
//  if (t1_app == t2_app) {
//    return t1 < t2;
//  }
//  return t1_app < t2_app;
//}

static
void uf_plugin_build_model(plugin_t* plugin, model_t* model) {
//  uf_plugin_t* uf = (uf_plugin_t*) plugin;
//
//  term_table_t* terms = uf->ctx->terms;
//  type_table_t* types = uf->ctx->types;
//  value_table_t* values = &model->vtbl;
//  variable_db_t* var_db = uf->ctx->var_db;
//  const mcsat_trail_t* trail = uf->ctx->trail;
//
//  // Data for sorting
//  model_sort_data_t sort_ctx;
//  sort_ctx.terms = terms;
//  sort_ctx.var_db = var_db;
//
//  // Sort the representatives by function used: we get a list of function
//  // applications where we can easily collect them by linear scan
//  ivector_t app_reps;
//  init_ivector(&app_reps, uf->app_reps_with_val_rep.size);
//  ivector_copy(&app_reps, uf->app_reps_with_val_rep.data, uf->app_reps_with_val_rep.size);
//  int_array_sort2(app_reps.data, app_reps.size, &sort_ctx, uf_plugin_build_model_compare);
//
//  // Mappings that we collect for a single function
//  ivector_t mappings;
//  init_ivector(&mappings, 0);
//
//  // Temp for arguments of a one concrete mapping
//  ivector_t arguments;
//  init_ivector(&arguments, 0);
//
//  // Got through all the representatives that have a set value and
//  // - while same function, collect the concrete mappings
//  // - if different function, construct the function and add to model
//  uint32_t i;
//  int32_t app_f, prev_app_f = 0;  // Current and previous function symbol
//  term_t app_term, prev_app_term; // Current and previous function application term
//  variable_t app_var;        // Current function application term variable
//  type_t app_type;           // Current function application term type
//  for (i = 0, prev_app_term = NULL_TERM; i < app_reps.size; ++ i) {
//
//    // Current representative application
//    app_var = app_reps.data[i];
//    app_term = variable_db_get_term(var_db, app_var);
//    app_type = term_type(terms, app_term);
//
//    if (ctx_trace_enabled(uf->ctx, "uf_plugin::model")) {
//      ctx_trace_printf(uf->ctx, "processing app rep:");
//      ctx_trace_term(uf->ctx, app_term);
//    }
//
//    // Current function symbol
//    app_f = app_reps_get_uf(terms, app_term);
//    composite_term_t* app_comp = app_reps_get_uf_descriptor(uf->ctx->terms, app_term);
//
//    // For division operators, we only use the ones that divide by 0
//    if (app_f < 0) {
//      assert(app_comp->arity == 2);
//      term_t divisor_term = app_comp->arg[1];
//      variable_t divisor_var = variable_db_get_variable(var_db, divisor_term);
//      const mcsat_value_t* divisor_value = trail_get_value(trail, divisor_var);
//      if (!mcsat_value_is_zero(divisor_value)) {
//        continue;
//      }
//    }
//
//    // If we changed the function, construct the previous one
//    if (prev_app_term != NULL_TERM && app_f != prev_app_f) {
//      type_t tau = app_reps_get_uf_type(&uf->app_reps, prev_app_term);
//      value_t f_value = vtbl_mk_function(values, tau, mappings.size, mappings.data, vtbl_mk_unknown(values));
//      if (prev_app_f < 0) {
//        // Arithmetic stuffs
//        switch (prev_app_f) {
//        case APP_REP_IDIV_ID:
//          vtbl_set_zero_idiv(values, f_value);
//          break;
//        case APP_REP_RDIV_ID:
//          vtbl_set_zero_rdiv(values, f_value);
//          break;
//        case APP_REP_MOD_ID:
//          vtbl_set_zero_mod(values, f_value);
//          break;
//        }
//      } else {
//        // Regular UF function
//        model_map_term(model, prev_app_f, f_value);
//      }
//      ivector_reset(&mappings);
//    }
//
//    // Next concrete mapping f : (x1, x2, ..., xn) -> v
//    // a) Get the v value
//    mcsat_value_t* v_mcsat = (mcsat_value_t*) trail_get_value(trail, app_var);
//    assert(v_mcsat->type != VALUE_NONE);
//    value_t v = mcsat_value_to_value(v_mcsat, types, app_type, values);
//    // b) Get the argument values
//    uint32_t arg_i;
//    uint32_t arg_start = app_reps_get_uf_start(uf->ctx->terms, app_term);
//    uint32_t arg_end = app_f < 0 ? app_comp->arity - 1 : app_comp->arity;
//    ivector_reset(&arguments);
//    for (arg_i = arg_start; arg_i < arg_end; ++ arg_i) {
//      term_t arg_term = app_comp->arg[arg_i];
//      type_t arg_type = term_type(terms, arg_term);
//      variable_t arg_var = variable_db_get_variable(var_db, arg_term);
//      v_mcsat = (mcsat_value_t*) trail_get_value(trail, arg_var);
//      assert(v_mcsat->type != VALUE_NONE);
//      value_t arg_v = mcsat_value_to_value(v_mcsat, types, arg_type, values);
//      ivector_push(&arguments, arg_v);
//    }
//    // c) Construct the concrete mapping, and save in the list for f
//    value_t map_value = vtbl_mk_map(values, arguments.size, arguments.data, v);
//    ivector_push(&mappings, map_value);
//
//    // Remember the previous one
//    prev_app_f = app_f;
//    prev_app_term = app_term;
//  }
//
//  if (app_reps.size > 0 && mappings.size > 0) {
//    // Construct the last function
//    type_t tau = app_reps_get_uf_type(&uf->app_reps, app_term);
//    value_t f_value = vtbl_mk_function(values, tau, mappings.size, mappings.data, vtbl_mk_unknown(values));
//    if (app_f < 0) {
//      // Arithmetic stuffs
//      switch (app_f) {
//      case APP_REP_IDIV_ID:
//        vtbl_set_zero_idiv(values, f_value);
//        break;
//      case APP_REP_RDIV_ID:
//        vtbl_set_zero_rdiv(values, f_value);
//        break;
//      case APP_REP_MOD_ID:
//        vtbl_set_zero_mod(values, f_value);
//        break;
//      }
//    } else {
//      // Regular UF function
//      model_map_term(model, app_f, f_value);
//    }
//  }
//
//  // Remove temps
//  delete_ivector(&arguments);
//  delete_ivector(&mappings);
//  delete_ivector(&app_reps);
}

plugin_t* uf_plugin_allocator(void) {
  uf_plugin_t* plugin = safe_malloc(sizeof(uf_plugin_t));
  plugin_construct((plugin_t*) plugin);
  plugin->plugin_interface.construct             = uf_plugin_construct;
  plugin->plugin_interface.destruct              = uf_plugin_destruct;
  plugin->plugin_interface.new_term_notify       = uf_plugin_new_term_notify;
  plugin->plugin_interface.new_lemma_notify      = 0;
  plugin->plugin_interface.event_notify          = 0;
  plugin->plugin_interface.propagate             = uf_plugin_propagate;
  plugin->plugin_interface.decide                = uf_plugin_decide;
  plugin->plugin_interface.get_conflict          = uf_plugin_get_conflict;
  plugin->plugin_interface.explain_propagation   = uf_plugin_explain_propagation;
  plugin->plugin_interface.explain_evaluation    = uf_plugin_explain_evaluation;
  plugin->plugin_interface.push                  = uf_plugin_push;
  plugin->plugin_interface.pop                   = uf_plugin_pop;
  plugin->plugin_interface.build_model           = uf_plugin_build_model;
  plugin->plugin_interface.gc_mark               = uf_plugin_gc_mark;
  plugin->plugin_interface.gc_sweep              = uf_plugin_gc_sweep;
  plugin->plugin_interface.set_exception_handler = uf_plugin_set_exception_handler;

  return (plugin_t*) plugin;
}
