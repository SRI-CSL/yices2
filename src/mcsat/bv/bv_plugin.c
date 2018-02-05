/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#if defined(CYGWIN) || defined(MINGW)
#ifndef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__ __declspec(dllexport)
#endif
#endif

#include "bv_plugin.h"

#include "mcsat/trail.h"
#include "mcsat/tracing.h"
#include "mcsat/watch_list_manager.h"
#include "mcsat/utils/scope_holder.h"
#include "mcsat/value.h"

#include "model/models.h"

#include "utils/int_array_sort2.h"
#include "terms/terms.h"
#include "yices.h"

#include <cudd.h>

typedef struct {

  /** The plugin interface */
  plugin_t plugin_interface;

  /** Watch list manager */
  watch_list_manager_t wlm;
  
  /** The plugin context */
  plugin_context_t* ctx;

  /** Next index of the trail to process */
  uint32_t trail_i;

  /** Scope holder for the int variables */
  scope_holder_t scope;

  /** Conflict  */
  ivector_t conflict;

  /** Exception handler */
  jmp_buf* exception;

} bv_plugin_t;

static
void bv_plugin_construct(plugin_t* plugin, plugin_context_t* ctx) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;

  bv->ctx = ctx;
  scope_holder_construct(&bv->scope);
  bv->trail_i = 0;

  watch_list_manager_construct(&bv->wlm, bv->ctx->var_db);

  // Terms
  ctx->request_term_notification_by_kind(ctx, BV_ARRAY);
  ctx->request_term_notification_by_kind(ctx, BV_DIV);
  ctx->request_term_notification_by_kind(ctx, BV_REM);
  ctx->request_term_notification_by_kind(ctx, BV_SDIV);
  ctx->request_term_notification_by_kind(ctx, BV_SREM);
  ctx->request_term_notification_by_kind(ctx, BV_SMOD);
  ctx->request_term_notification_by_kind(ctx, BV_SHL);
  ctx->request_term_notification_by_kind(ctx, BV_LSHR);
  ctx->request_term_notification_by_kind(ctx, BV_ASHR);
  ctx->request_term_notification_by_kind(ctx, BV_EQ_ATOM);
  ctx->request_term_notification_by_kind(ctx, BV_GE_ATOM);
  ctx->request_term_notification_by_kind(ctx, BV_SGE_ATOM);
  ctx->request_term_notification_by_kind(ctx, BV_POLY);
  ctx->request_term_notification_by_kind(ctx, BV64_POLY);
  ctx->request_term_notification_by_kind(ctx, BIT_TERM);
  ctx->request_term_notification_by_kind(ctx, BV_CONSTANT);
  ctx->request_term_notification_by_kind(ctx, BV64_CONSTANT);

  // Types
  ctx->request_term_notification_by_type(ctx, BITVECTOR_TYPE);

  // Decisions
  ctx->request_decision_calls(ctx, BITVECTOR_TYPE);
}

static
void bv_plugin_destruct(plugin_t* plugin) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;
  watch_list_manager_destruct(&bv->wlm);
  scope_holder_destruct(&bv->scope);
}

static
bool bv_plugin_trail_variable_compare(void *data, variable_t t1, variable_t t2) {
  const mcsat_trail_t* trail;
  bool t1_has_value, t2_has_value;
  uint32_t t1_level, t2_level;

  trail = data;

  // We compare variables based on the trail level, unassigned to the front,
  // then assigned ones by decreasing level

  // Literals with no value
  t1_has_value = trail_has_value(trail, t1);
  t2_has_value = trail_has_value(trail, t2);
  if (!t1_has_value && !t2_has_value) {
    // Both have no value, just order by variable
    return t1 < t2;
  }

  // At least one has a value
  if (!t1_has_value) {
    // t1 < t2, goes to front
    return true;
  }
  if (!t2_has_value) {
    // t2 < t1, goes to front
    return false;
  }

  // Both literals have a value, sort by decreasing level
  t1_level = trail_get_level(trail, t1);
  t2_level = trail_get_level(trail, t2);
  if (t1_level != t2_level) {
    // t1 > t2 goes to front
    return t1_level > t2_level;
  } else {
    return t1 < t2;
  }
}


static
void bv_watch_composite(bv_plugin_t* bv, term_t t, trail_token_t* prop) {

  variable_db_t* var_db      = bv->ctx->var_db;
  term_table_t* terms        = bv->ctx->terms;
  const mcsat_trail_t* trail = bv->ctx->trail;

  // Variable for the whole term
  variable_t term_var = variable_db_get_variable(var_db, t);
    
  // Variables for the subterms
  composite_term_t* composite_term = composite_term_desc(terms, t);

  uint32_t arity = composite_term->arity;
  
  // Setup the variable list
  variable_t vars[arity+1];
  vars[0] = term_var;
  for(uint32_t i = 0; i < arity; i++){
    vars[i+1] = variable_db_get_variable(var_db, composite_term->arg[i]);
  }

  // Sort variables by trail index
  int_array_sort2(vars, arity+1, (void*) trail, bv_plugin_trail_variable_compare);

  // Make the variable list
  variable_list_ref_t var_list = watch_list_manager_new_list(&bv->wlm, vars, arity+1, term_var);

  // Add first two variables to watch list
  watch_list_manager_add_to_watch(&bv->wlm, var_list, vars[0]);
  watch_list_manager_add_to_watch(&bv->wlm, var_list, vars[1]);
  
}

static
void bv_plugin_new_term_notify(plugin_t* plugin, term_t t, trail_token_t* prop) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;

  if (ctx_trace_enabled(bv->ctx, "mcsat::new_term")) {
    ctx_trace_printf(bv->ctx, "bv_plugin_new_term_notify: ");
    ctx_trace_term(bv->ctx, t);
  }

  term_kind_t t_kind = term_kind(bv->ctx->terms, t);

  switch (t_kind) {
  case BV_ARRAY: {
    if (ctx_trace_enabled(bv->ctx, "mcsat::new_term")) {
      ctx_trace_printf(bv->ctx, "BV_ARRAY");
    }
    break;
  }
  case BV_DIV:
  case BV_REM:
  case BV_SDIV:
  case BV_SREM:
  case BV_SMOD:
  case BV_SHL:
  case BV_LSHR:
  case BV_ASHR:
  case BV_EQ_ATOM:
  case BV_GE_ATOM:
  case BV_SGE_ATOM:
  case SELECT_TERM:
  case BIT_TERM: {
    bv_watch_composite(bv,t,prop);
    break;
  }
  default:
    // Noting for now
    break;
  }

}

static
void bv_plugin_propagate_var(bv_plugin_t* bv, variable_t var, trail_token_t* prop) {

  // Abbreviations
  const mcsat_trail_t* trail = bv->ctx->trail;
  variable_db_t* var_db = bv->ctx->var_db;

  // Go through all the variable lists (constraints) where we're watching var
  remove_iterator_t it;
  variable_list_ref_t var_list_ref;
  variable_t* var_list;
  variable_t* var_list_it;

  // Get the watch-list and process
  remove_iterator_construct(&it, &bv->wlm, var);
  while (trail_is_consistent(trail) && !remove_iterator_done(&it)) {

    // Get the current list where var appears
    var_list_ref = remove_iterator_get_list_ref(&it);
    var_list = watch_list_manager_get_list(&bv->wlm, var_list_ref);

    // constraint variable
    variable_t bv_constraint = watch_list_manager_get_constraint(&bv->wlm, var_list_ref);
    if (ctx_trace_enabled(bv->ctx, "bv_plugin")) {
      ctx_trace_printf(bv->ctx, "bv_plugin_propagate: bv_constraint = ");
      ctx_trace_term(bv->ctx, variable_db_get_term(var_db, bv_constraint));
    }

    // Put the variable to [1] so that [0] is the unit one
    if (var_list[0] == var && var_list[1] != variable_null) {
      var_list[0] = var_list[1];
      var_list[1] = var;
    }

    // Find a new watch (start from [2])
    var_list_it = var_list + 1;
    if (*var_list_it != variable_null) {
      for (++var_list_it; *var_list_it != variable_null; ++var_list_it) {
        if (!trail_has_value(trail, *var_list_it)) {
          // Swap with var_list[1]
          var_list[1] = *var_list_it;
          *var_list_it = var;
          // Add to new watch
          watch_list_manager_add_to_watch(&bv->wlm, var_list_ref, var_list[1]);
          // Don't watch this one
          remove_iterator_next_and_remove(&it);
          break;
        }
      }
    }

    if (*var_list_it == variable_null) {
      if (ctx_trace_enabled(bv->ctx, "bv_plugin")) {
        ctx_trace_printf(bv->ctx, "no watch found\n");
      }
      // We did not find a new watch so vars[1], ..., vars[n] are assigned.
      // If vars[0] is the constraint, we propagate it, otherwise, we update
      // the feasibility set
      if (var_list[0] == bv_constraint) {

        // copy-paste from UF
        /* // lhs = rhs */
        /* variable_t lhs = var_list[1]; */
        /* variable_t rhs = var_list[2]; */

        /* // Check the model value */
        /* const mcsat_value_t* lhs_value = trail_get_value(trail, lhs); */
        /* const mcsat_value_t* rhs_value = trail_get_value(trail, rhs); */
        /* int lhs_eq_rhs = mcsat_value_eq(lhs_value, rhs_value); */

        /* // Evaluate the equality if it doesn't have a value */
        /* if (!trail_has_value(trail, eq_var)) { */
        /*   if (lhs_eq_rhs) { */
        /*     prop->add(prop, eq_var, &mcsat_value_true); */
        /*   } else { */
        /*     prop->add(prop, eq_var, &mcsat_value_false); */
        /*   } */
        /* } else { */
        /*   // Equality already has a value, check that it's the right one */
        /*   bool eq_var_value = trail_get_boolean_value(trail, eq_var); */
        /*   if (eq_var_value != lhs_eq_rhs) { */
        /*     if (ctx_trace_enabled(bv->ctx, "bv_plugin::conflict")) { */
        /*       ctx_trace_printf(bv->ctx, "eq conflict 1\n"); */
        /*     } */
        /*     term_t eq_term = variable_db_get_term(var_db, eq_var); */
        /*     // Equality can not be both true and false at the same time */
        /*     ivector_reset(&bv->conflict); */
        /*     ivector_push(&bv->conflict, eq_term); */
        /*     ivector_push(&bv->conflict, opposite_term(eq_term)); */
        /*     prop->conflict(prop); */
        /*   } */
        /* } */
      } else {

        /* // Check if equality is true or false and add to feasibility db */
        /* variable_t lhs = var_list[0]; */
        /* variable_t rhs = var_list[1] == eq_var ? var_list[2] : var_list[1]; */

        /* // Is the equailty true */
        /* bool eq_true = trail_get_boolean_value(trail, eq_var); */

        /* // Get the value of the right-hand side (have to cast, since yices rationals */
        /* // don't have const parameters. */
        /* mcsat_value_t* rhs_val = (mcsat_value_t*) trail_get_value(trail, rhs); */
        /* assert(rhs_val->type == VALUE_RATIONAL); */
        /* assert(q_fits_int32(&rhs_val->q)); */
        /* int32_t rhs_val_int; */
        /* q_get32(&rhs_val->q, &rhs_val_int); */

        /* // Update the feasible set */
        /* bool feasible = true; */
        /* if (eq_true) { */
        /*   feasible = bv_feasible_set_db_set_equal(bv->feasible, lhs, rhs_val_int, eq_var); */

        /*   // Also propagate the value */
        /*   if (!trail_has_value(trail, lhs)) { */
        /*     rational_t q; */
        /*     q_init(&q); */
        /*     q_set32(&q, rhs_val_int); */
        /*     mcsat_value_t value; */
        /*     mcsat_value_construct_rational(&value, &q); */
        /*     prop->add(prop, lhs, &value); */
        /*     mcsat_value_destruct(&value); */
        /*     q_clear(&q); */
        /*   } */

        /* } else { */
        /*   feasible = bv_feasible_set_db_set_disequal(bv->feasible, lhs, rhs_val_int, eq_var); */
        /* } */

        /* // Ooops, a conflict */
        /* if (!feasible) { */
        /*   if (ctx_trace_enabled(bv->ctx, "bv_plugin::conflict")) { */
        /*     ctx_trace_printf(bv->ctx, "eq conflict 2\n"); */
        /*   } */
        /*   ivector_reset(&bv->conflict); */
        /*   bv_feasible_set_db_get_conflict(bv->feasible, lhs, &bv->conflict); */
        /*   prop->conflict(prop); */
        /* } */
      }

      // Keep the watch, and continue
      remove_iterator_next_and_keep(&it);
    }
  }

  // Done, destruct the iterator
  remove_iterator_destruct(&it);
}

static
void bv_plugin_propagate(plugin_t* plugin, trail_token_t* prop) {

  bv_plugin_t* bv = (bv_plugin_t*) plugin;
  
  if (ctx_trace_enabled(bv->ctx, "bv_plugin")) {
    ctx_trace_printf(bv->ctx, "bv_plugin_propagate()\n");
  }

  // If we're not watching anything, we just ignore
  if (watch_list_manager_size(&bv->wlm) == 0) {
    return;
  }

  // Abbreviations
  const mcsat_trail_t* trail = bv->ctx->trail;
  variable_db_t* var_db = bv->ctx->var_db;

  // Propagate
  variable_t var;
  for(; trail_is_consistent(trail) && bv->trail_i < trail_size(trail); ++ bv->trail_i) {
    // Current trail element
    var = trail_at(trail, bv->trail_i);

    if (ctx_trace_enabled(bv->ctx, "bv_plugin")) {
      ctx_trace_printf(bv->ctx, "bv_plugin_propagate: ");
      ctx_trace_term(bv->ctx, variable_db_get_term(var_db, var));
      ctx_trace_printf(bv->ctx, "trail: ");
      trail_print(trail, stderr);
    }

    if (trail_is_consistent(trail)) {
      bv_plugin_propagate_var(bv, var, prop);
    }

  }

}

static
void bv_plugin_push(plugin_t* plugin) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;

  // Pop the int variable values
  scope_holder_push(&bv->scope,
      &bv->trail_i,
      NULL);
}

static
void bv_plugin_pop(plugin_t* plugin) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;

  // Pop the int variable values
  scope_holder_pop(&bv->scope,
      &bv->trail_i,
      NULL);
}


static
void bv_plugin_decide(plugin_t* plugin, variable_t x, trail_token_t* decide, bool must) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;

  if (ctx_trace_enabled(bv->ctx, "bv_plugin")) {
    ctx_trace_printf(bv->ctx, "bv_plugin_decide: ");
    ctx_trace_term(bv->ctx, variable_db_get_term(bv->ctx->var_db, x));
    ctx_trace_printf(bv->ctx, "trail: ");
    trail_print(bv->ctx->trail, stderr);
  }

  assert(!trail_has_value(bv->ctx->trail, x));

  mcsat_value_t v;
  bvconstant_t b;
  uint32_t bitsize;

    
  /* if (trail_has_cached_value(bv->ctx->trail, x)) { */
  /*   // Use the cached value if exists */
  /*   v = *trail_get_cached_value(bv->ctx->trail, x); */
  /* } else { */
  bitsize = term_bitsize(bv->ctx->terms, variable_db_get_term(bv->ctx->var_db,x));
  init_bvconstant(&b);
  bvconstant_set_all_zero(&b, bitsize);
  mcsat_value_construct_bv_value(&v, &b);
  /* } */

  decide->add(decide, x, &v);

  // Remove temps
  mcsat_value_destruct(&v);  // Really? does decide->add make a copy?
  delete_bvconstant(&b);
}

static
void bv_plugin_gc_mark(plugin_t* plugin, gc_info_t* gc_vars) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;
  (void) bv;

  // TODO
  assert(false);
}

static
void bv_plugin_gc_sweep(plugin_t* plugin, const gc_info_t* gc_vars) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;
  (void) bv;

  // TODO
  assert(false);
}

static
void bv_plugin_get_conflict(plugin_t* plugin, ivector_t* conflict) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;
  ivector_swap(conflict, &bv->conflict);
  ivector_reset(&bv->conflict);
}

static
term_t bv_plugin_explain_propagation(plugin_t* plugin, variable_t var, ivector_t* reasons) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;
  (void) bv;

  // TODO
  assert(false);

  return NULL_TERM;
}

static
bool bv_plugin_explain_evaluation(plugin_t* plugin, term_t t, int_mset_t* vars, mcsat_value_t* value) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;
  (void) bv;

  // TODO
  assert(false);

  return true;
}

static
void bv_plugin_set_exception_handler(plugin_t* plugin, jmp_buf* handler) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;
  bv->exception = handler;
}

static
void bv_plugin_build_model(plugin_t* plugin, model_t* model) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;
  (void) bv;

  // TODO
  assert(false);
}

plugin_t* bv_plugin_allocator(void) {
  bv_plugin_t* plugin = safe_malloc(sizeof(bv_plugin_t));
  plugin_construct((plugin_t*) plugin);
  plugin->plugin_interface.construct             = bv_plugin_construct;
  plugin->plugin_interface.destruct              = bv_plugin_destruct;
  plugin->plugin_interface.new_term_notify       = bv_plugin_new_term_notify;
  plugin->plugin_interface.new_lemma_notify      = NULL;
  plugin->plugin_interface.event_notify          = NULL;
  plugin->plugin_interface.propagate             = bv_plugin_propagate;
  plugin->plugin_interface.decide                = bv_plugin_decide;
  plugin->plugin_interface.get_conflict          = bv_plugin_get_conflict;
  plugin->plugin_interface.explain_propagation   = bv_plugin_explain_propagation;
  plugin->plugin_interface.explain_evaluation    = bv_plugin_explain_evaluation;
  plugin->plugin_interface.push                  = bv_plugin_push;
  plugin->plugin_interface.pop                   = bv_plugin_pop;
  plugin->plugin_interface.build_model           = bv_plugin_build_model;
  plugin->plugin_interface.gc_mark               = bv_plugin_gc_mark;
  plugin->plugin_interface.gc_sweep              = bv_plugin_gc_sweep;
  plugin->plugin_interface.set_exception_handler = bv_plugin_set_exception_handler;

  return (plugin_t*) plugin;
}
