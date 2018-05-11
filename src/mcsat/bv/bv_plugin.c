/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include "bdd_computation.h"
#include "bv_feasible_set_db.h"
#include "bv_plugin.h"
#include "bv_bdd_manager.h"
#include "bv_evaluator.h"
#include "bv_utils.h"

#include "mcsat/trail.h"
#include "mcsat/tracing.h"
#include "mcsat/watch_list_manager.h"
#include "mcsat/utils/scope_holder.h"
#include "mcsat/value.h"
#include "mcsat/unit_info.h"

#include "model/models.h"

#include "utils/int_array_sort2.h"
#include "utils/int_hash_sets.h"
#include "terms/terms.h"
#include "yices.h"

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

  /** Conflict variable */
  variable_t conflict_variable;

  /** Exception handler */
  jmp_buf* exception;

  /** Map from constraint variables to the constraint_unit_info_t enum */
  int_hmap_t constraint_unit_info;

  /** Map from constraint variables to the variables they are unit in */
  int_hmap_t constraint_unit_var;

  /** Last variable that was decided, but yet unprocessed */
  variable_t last_decided_and_unprocessed;

  /** Feasible set database */
  bv_feasible_set_db_t* feasible;

  /** BDD manager */
  bv_bdd_manager_t* bddm;

  /** Evaluator */
  bv_evaluator_t evaluator;

  /** Variables processed in propagation */
  ivector_t processed_variables;

  /** Size of processed (for backtracking) */
  uint32_t processed_variables_size;

  /** Cache for term traversals */
  int_hset_t visited_cache;

  struct {
    uint32_t* conflicts;
    uint32_t* propagations;
    uint32_t* constraints_attached;
  } stats;

} bv_plugin_t;

static
void bv_plugin_construct(plugin_t* plugin, plugin_context_t* ctx) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;

  bv->ctx = ctx;
  scope_holder_construct(&bv->scope);
  bv->trail_i = 0;

  bv->last_decided_and_unprocessed = variable_null;
  bv->conflict_variable = variable_null;

  if (ctx_trace_enabled(bv->ctx, "mcsat::bv")) {
    ctx_trace_printf(bv->ctx, "bv_plugin_construct(...)\n");
  }

  // Construct the watch-list datastructures
  watch_list_manager_construct(&bv->wlm, bv->ctx->var_db);
  init_int_hmap(&bv->constraint_unit_info, 0);
  init_int_hmap(&bv->constraint_unit_var, 0);
  
  bv->bddm = bv_bdd_manager_new(ctx);
  bv->feasible = bv_feasible_set_db_new(ctx, bv->bddm);

  bv_evaluator_construct(&bv->evaluator, ctx);

  init_ivector(&bv->processed_variables, 0);
  bv->processed_variables_size = 0;

  init_int_hset(&bv->visited_cache, 0);

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
  ctx->request_term_notification_by_kind(ctx, POWER_PRODUCT);
  ctx->request_term_notification_by_kind(ctx, BV_POLY);
  ctx->request_term_notification_by_kind(ctx, BV64_POLY);
  ctx->request_term_notification_by_kind(ctx, BIT_TERM);
  ctx->request_term_notification_by_kind(ctx, BV_CONSTANT);
  ctx->request_term_notification_by_kind(ctx, BV64_CONSTANT);

  // Types
  ctx->request_term_notification_by_type(ctx, BITVECTOR_TYPE);

  // Decisions
  ctx->request_decision_calls(ctx, BITVECTOR_TYPE);

  // Add statistics
  bv->stats.conflicts = statistics_new_uint32(bv->ctx->stats, "mcsat::bv::conflicts");
  bv->stats.propagations = statistics_new_uint32(bv->ctx->stats, "mcsat::bv::propagations");
  bv->stats.constraints_attached = statistics_new_uint32(bv->ctx->stats, "mcsat::bv::constraints_attached");
}

static
void bv_plugin_destruct(plugin_t* plugin) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;

  if (ctx_trace_enabled(bv->ctx, "mcsat::bv")) {
    ctx_trace_printf(bv->ctx, "bv_plugin_destruct(...)\n");
  }

  watch_list_manager_destruct(&bv->wlm);
  delete_int_hmap(&bv->constraint_unit_info);
  delete_int_hmap(&bv->constraint_unit_var);
  scope_holder_destruct(&bv->scope);
  bv_feasible_set_db_delete(bv->feasible);
  bv_bdd_manager_delete(bv->bddm);
  bv_evaluator_destruct(&bv->evaluator);
  delete_ivector(&bv->processed_variables);
  delete_int_hset(&bv->visited_cache);
}

static inline
bool bv_plugin_has_assignment(const bv_plugin_t* bv, variable_t x) {
  return trail_has_value(bv->ctx->trail, x) && trail_get_index(bv->ctx->trail, x) < bv->trail_i;
}

static
void bv_plugin_set_unit_info(bv_plugin_t* bv, variable_t constraint, variable_t unit_var, constraint_unit_info_t value) {
  int_hmap_pair_t* find = NULL;
  int_hmap_pair_t* unit_find = NULL;

  // Add unit tag
  find = int_hmap_find(&bv->constraint_unit_info, constraint);
  if (find == NULL) {
    // First time, just set
    int_hmap_add(&bv->constraint_unit_info, constraint, value);
  } else {
    assert(find->val != value);
    find->val = value;
  }

  // Add unit variable
  unit_find = int_hmap_find(&bv->constraint_unit_var, constraint);
  if (value == CONSTRAINT_UNIT) {
    if (unit_find == NULL) {
      int_hmap_add(&bv->constraint_unit_var, constraint, unit_var);
    } else {
      unit_find->val = unit_var;
    }
  } else {
    if (unit_find != NULL) {
      unit_find->val = variable_null;
    }
  }
}

static
constraint_unit_info_t bv_plugin_get_unit_info(bv_plugin_t* bv, variable_t constraint) {
  int_hmap_pair_t* find = int_hmap_find(&bv->constraint_unit_info, constraint);
  if (find == NULL)  {
    return CONSTRAINT_UNKNOWN;
  } else {
    return find->val;
  }
}

static
variable_t bv_plugin_get_unit_var(bv_plugin_t* nra, variable_t constraint) {
  int_hmap_pair_t* find = int_hmap_find(&nra->constraint_unit_var, constraint);
  if (find == NULL) {
    return variable_null;
  } else {
    return find->val;
  }
}


static
bool bv_plugin_trail_variable_compare(void *data, variable_t t1, variable_t t2) {
  const mcsat_trail_t* trail;
  bool t1_has_value, t2_has_value;
  uint32_t t1_level, t2_level;

  trail = data;

  // We compare variables based on the trail level, unassigned to the front,
  // then assigned ones by decreasing level

  // Variables with no value
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

  // Both variables have a value, sort by decreasing level
  t1_level = trail_get_level(trail, t1);
  t2_level = trail_get_level(trail, t2);
  if (t1_level != t2_level) {
    // t1 > t2 goes to front
    return t1_level > t2_level;
  } else {
    return t1 < t2;
  }
}

void bv_plugin_get_term_variables(bv_plugin_t* bv, term_t t, int_mset_t* vars_out) {

  assert(is_pos_term(t));

  // SKip if already visited
  if (int_hset_member(&bv->visited_cache, t)) {
    return;
  }

  // The term table
  term_table_t* terms = bv->ctx->terms;

  // Variable database
  variable_db_t* var_db = bv->ctx->var_db;

  if (ctx_trace_enabled(bv->ctx, "mcsat::new_term")) {
    ctx_trace_printf(bv->ctx, "bv_plugin_get_variables: ");
    ctx_trace_term(bv->ctx, t);
  }

  term_kind_t kind = term_kind(terms, t);
  switch (kind) {
  case CONSTANT_TERM: // Boolean variables
  case BV_CONSTANT:
  case BV64_CONSTANT:
    // Ignore, no variables here
    break;
  case EQ_TERM: {
      composite_term_t* atom_comp = composite_term_desc(terms, t);
      assert(atom_comp->arity == 2);
      term_t t0 = atom_comp->arg[0], t0_pos = unsigned_term(t0);
      term_t t1 = atom_comp->arg[1], t1_pos = unsigned_term(t1);
      bv_plugin_get_term_variables(bv, t0_pos, vars_out);
      bv_plugin_get_term_variables(bv, t1_pos, vars_out);
      break;
  }
  case BV_EQ_ATOM:
  case BV_GE_ATOM:
  case BV_SGE_ATOM: {
    // These can appear as BV_ARRAY elements
    composite_term_t* atom_comp = composite_term_desc(terms, t);
    assert(atom_comp->arity == 2);
    bv_plugin_get_term_variables(bv, atom_comp->arg[0],vars_out);
    bv_plugin_get_term_variables(bv, atom_comp->arg[1],vars_out);
    break;
  }
  case BV_ARRAY: {
    // Special: make sub-terms positive
    composite_term_t* concat_desc = bvarray_term_desc(terms, t);
    for (uint32_t i = 0; i < concat_desc->arity; ++ i) {
      term_t t_i = concat_desc->arg[i];
      term_t t_i_pos = unsigned_term(t_i);
      bv_plugin_get_term_variables(bv, t_i_pos, vars_out);
    }
    break;
  }
  case OR_TERM: {
    composite_term_t* t_comp = or_term_desc(terms, t);
    for (uint32_t i = 0; i < t_comp->arity; ++ i) {
      term_t t_i = t_comp->arg[i];
      term_t t_i_pos = unsigned_term(t_i);
      bv_plugin_get_term_variables(bv, t_i_pos, vars_out);
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
  case BV_ASHR: {
    composite_term_t* t_comp = composite_term_desc(terms, t);
    for (uint32_t i = 0; i < t_comp->arity; ++ i) {
      bv_plugin_get_term_variables(bv, t_comp->arg[i], vars_out);
    }
    break;
  }
  case BIT_TERM:
    bv_plugin_get_term_variables(bv, bit_term_arg(terms, t), vars_out);
    break;
  case BV_POLY: {
    bvpoly_t* t_poly = bvpoly_term_desc(terms, t);
    for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
      if (t_poly->mono[i].var == const_idx) continue;
      bv_plugin_get_term_variables(bv, t_poly->mono[i].var, vars_out);
    }
    break;
  }
  case BV64_POLY: {
    bvpoly64_t* t_poly = bvpoly64_term_desc(terms, t);
    for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
      if (t_poly->mono[i].var == const_idx) continue;
      bv_plugin_get_term_variables(bv, t_poly->mono[i].var, vars_out);
    }
    break;
  }
  case POWER_PRODUCT: {
    pprod_t* t_pprod = pprod_term_desc(terms, t);
    for (uint32_t i = 0; i < t_pprod->len; ++ i) {
      bv_plugin_get_term_variables(bv, t_pprod->prod[i].var, vars_out);
    }
    break;
  }
  default:
    // A variable or a foreign term
    assert(is_pos_term(t));
    int_mset_add(vars_out, variable_db_get_variable(var_db, t));
  }

  // Mark as visited
  int_hset_add(&bv->visited_cache, t);
}

void bv_plugin_get_notified_term_subvariables(bv_plugin_t* bv, term_t t, int_mset_t* vars_out) {

  term_table_t* terms = bv->ctx->terms;

  term_t t_pos = unsigned_term(t);
  term_kind_t t_pos_kind = term_kind(terms, t_pos);

  int_hset_reset(&bv->visited_cache);

  switch (t_pos_kind) {
  case BV_EQ_ATOM:
  case BV_GE_ATOM:
  case BV_SGE_ATOM: {
    // Terms only
    composite_term_t* atom_comp = composite_term_desc(terms, t_pos);
    assert(atom_comp->arity == 2);
    bv_plugin_get_term_variables(bv, atom_comp->arg[0], vars_out);
    bv_plugin_get_term_variables(bv, atom_comp->arg[1], vars_out);
    break;
  }
  case BIT_TERM: {
    term_t arg = bit_term_arg(terms, t_pos);
    bv_plugin_get_term_variables(bv, arg, vars_out);
    break;
  }
  case BV_ARRAY:
  case BV_DIV:
  case BV_REM:
  case BV_SDIV:
  case BV_SREM:
  case BV_SMOD:
  case BV_SHL:
  case BV_LSHR:
  case BV_ASHR:
  case BV_POLY:
  case BV64_POLY:
  case POWER_PRODUCT:
  case BV_CONSTANT:
  case BV64_CONSTANT:
    // We should get notifications only on theory combination
    assert(false);
    break;
  default:
    // We get here only with variables, or foreign terms.
    break;
  }

  // Reset the cache
  int_hset_reset(&bv->visited_cache);
}

void bv_plugin_report_conflict(bv_plugin_t* bv, trail_token_t* prop, variable_t variable) {
  prop->conflict(prop);
  bv->conflict_variable = variable;
  (*bv->stats.conflicts) ++;
}

/**
 * Process a constraint that is detected to be fully assigned: check consistency.
 */
static
void bv_plugin_process_fully_assigned_constraint(bv_plugin_t* bv, trail_token_t* prop, variable_t constraint_var) {
  // TODO
  assert(false);
}

/**
 * Process a constraint cstr(x, y1, ..., yn) that is detected to be unit in x,
 * i.e., x is considered unassigned, and all y_i are assigned:
 * - compute feasible set of cstr;
 * - update with existing feasibile set for x;
 * - report any conflicts (or propagate if possible).
 *
 * Node that (TODO) the constraint might be of the form [(x + y) x y], i.e. the
 * Constraint is an evaluation constraint. This comes to play in theory
 * theory combination if we do not purify the terms.
 */
static
void bv_plugin_process_unit_constraint(bv_plugin_t* bv, trail_token_t* prop, variable_t cstr, variable_t x) {

  plugin_context_t* ctx = bv->ctx;
  variable_db_t* var_db = ctx->var_db;
  const mcsat_trail_t* trail = ctx->trail;
  bv_bdd_manager_t* bddm = bv->bddm;

  if (ctx_trace_enabled(ctx, "mcsat::bv::propagate")) {
    ctx_trace_printf(ctx, "processing unit constraint :\n");
    ctx_trace_term(ctx, variable_db_get_term(var_db, cstr));
  }

  assert(variable_db_is_boolean(var_db, cstr));

  // Is this an evaluation
  if (x == cstr) {
    // Compute value of the constraint and the level
    uint32_t cstr_eval_level = 0;
    const mcsat_value_t* cstr_value = bv_evaluator_run(&bv->evaluator, cstr, &cstr_eval_level);
    if (!trail_has_value(trail, cstr)) {
      // Unassigned, propagate the value
      prop->add_at_level(prop, cstr, cstr_value, cstr_eval_level);
    } else {
      // The constraint already has a value, check that it's the right one
      assert(mcsat_value_eq(cstr_value, trail_get_value(trail, cstr)));
    }
    return;
  }

  // Get the constraint value
  bool constraint_value = trail_get_value(trail, cstr)->b;

  // Get the terms
  term_t cstr_term = variable_db_get_term(var_db, cstr);
  term_t x_term = variable_db_get_term(var_db, x);

  // Get the BDD of the constraint (negate constraint if assigned to false)
  if (!constraint_value) { cstr_term = opposite_term(cstr_term); }
  bdd_t cstr_bdd = bv_bdd_manager_get_bdd(bddm, cstr_term, x_term);
  assert(cstr_bdd.bdd != NULL);

  // Update the infeasible intervals
  bool feasible = bv_feasible_set_db_update(bv->feasible, x, cstr_bdd, &cstr, 1);

  // If the intervals are empty, we have a conflict
  if (!feasible) {
    bv_plugin_report_conflict(bv, prop, x);
  } else {
    // If the value is implied at zero level, propagate it
    if (!trail_has_value(trail, x) && trail_is_at_base_level(trail)) {
      bdd_t feasible = bv_feasible_set_db_get(bv->feasible, x);
      uint32_t x_bitsize = bv_term_bitsize(ctx->terms, x_term);
      if (bv_bdd_manager_bdd_is_point(bddm, feasible, x_bitsize)) {
        bvconstant_t x_bv_value;
        init_bvconstant(&x_bv_value);
        bvconstant_set_bitsize(&x_bv_value, x_bitsize);
        bv_bdd_manager_pick_value(bddm, x_term, feasible, &x_bv_value);
        mcsat_value_t x_value;
        mcsat_value_construct_bv_value(&x_value, &x_bv_value);
        prop->add_at_level(prop, x, &x_value, 0);
        mcsat_value_destruct(&x_value);
        delete_bvconstant(&x_bv_value);
      }
    }
  }
}

static
void bv_plugin_new_term_notify(plugin_t* plugin, term_t t, trail_token_t* prop) {

  uint32_t i, j;
  bv_plugin_t* bv = (bv_plugin_t*) plugin;
  variable_db_t* var_db = bv->ctx->var_db;
  term_table_t* terms = bv->ctx->terms;

  assert(is_pos_term(t));

  if (ctx_trace_enabled(bv->ctx, "mcsat::new_term")) {
    ctx_trace_printf(bv->ctx, "bv_plugin_new_term_notify: ");
    ctx_trace_term(bv->ctx, t);
  }

  term_kind_t t_kind = term_kind(bv->ctx->terms, t);

  if (t_kind == POWER_PRODUCT && !is_bitvector_term(terms, t)) {
    return;
  }

  // Setup the variable
  variable_t t_var = variable_db_get_variable(var_db, t);
  
  int_mset_t t_vars;
  int_mset_construct(&t_vars, variable_null);
  // Add the term itself
  int_mset_add(&t_vars, t_var);
  // Collect the sub-variables
  bv_plugin_get_notified_term_subvariables(bv, t, &t_vars);

  // It's a constraint if there is more than one variable
  bool is_constraint = t_vars.element_list.size > 1;

  // Setup the constraint
  if (is_constraint) {

    // Get the list of variables
    ivector_t* t_var_list = int_mset_get_list(&t_vars);

    // Addd the variables to the BDD manager (so that we can assign them)
    for (i = 0; i < t_var_list->size; ++ i) {
      variable_t x = t_var_list->data[i];
      term_t x_term = variable_db_get_term(var_db, x);
      bv_bdd_manager_add_term(bv->bddm, x_term);
    }

    // Bump the variables
    for (i = 0; i < t_var_list->size; ++ i) {
      variable_t x = t_var_list->data[i];
      uint32_t deg = int_mset_contains(&t_vars, x);
      for (j = 0; j < deg; ++ j) { bv->ctx->bump_variable(bv->ctx, x); }
    }

    // Sort variables by trail index
    int_array_sort2(t_var_list->data, t_var_list->size, (void*) bv->ctx->trail, bv_plugin_trail_variable_compare);

    if (ctx_trace_enabled(bv->ctx, "mcsat::new_term")) {
      ctx_trace_printf(bv->ctx, "bv_plugin_new_term_notify: vars: \n");
      for (i = 0; i < t_var_list->size; ++ i) {
        ctx_trace_term(bv->ctx, variable_db_get_term(bv->ctx->var_db, t_var_list->data[i]));
      }
    }

    // Make the variable list
    variable_list_ref_t var_list = watch_list_manager_new_list(&bv->wlm, t_var_list->data, t_var_list->size, t_var);

    // Add first two variables to watch list
    watch_list_manager_add_to_watch(&bv->wlm, var_list, t_var_list->data[0]);
    watch_list_manager_add_to_watch(&bv->wlm, var_list, t_var_list->data[1]);

    // Check the current status of the constraint
    variable_t top_var = t_var_list->data[0];
    constraint_unit_info_t unit_status = CONSTRAINT_UNKNOWN;
    if (bv_plugin_has_assignment(bv, top_var)) {
      // All variables assigned,
      unit_status = CONSTRAINT_FULLY_ASSIGNED;
    } else if (bv_plugin_has_assignment(bv, t_var_list->data[1])) {
      // Second one is assigned and processed, so we're unit
      unit_status = CONSTRAINT_UNIT;
    }

    // Set the status of the constraint
    bv_plugin_set_unit_info(bv, t_var, unit_status == CONSTRAINT_UNIT ? top_var : variable_null, unit_status);

    // Process the constraint if it needs to be
    switch (unit_status) {
    case CONSTRAINT_FULLY_ASSIGNED:
      bv_plugin_process_fully_assigned_constraint(bv, prop, t_var);
      break;
    case CONSTRAINT_UNIT:
      bv_plugin_process_unit_constraint(bv, prop, t_var, top_var);
      break;
    case CONSTRAINT_UNKNOWN:
      break;
    }

    // Stats
    (*bv->stats.constraints_attached) ++;
  } else {
    assert(t_vars.size == 1);
    // Propagate constant values
    if (bv_term_kind_get_type(t_kind) == BV_TERM_CONSTANT) {
      mcsat_value_t t_value;
      mcsat_value_construct_from_bv(&t_value, terms, t);
      prop->add_at_level(prop, t_var, &t_value, 0);
      mcsat_value_destruct(&t_value);
    }
  }

  // Remove the temp variables
  int_mset_destruct(&t_vars);
}



static
void bv_plugin_propagate_var(bv_plugin_t* bv, variable_t x, trail_token_t* prop) {

  const mcsat_trail_t* trail = bv->ctx->trail;
  variable_db_t* var_db = bv->ctx->var_db;
  bv_bdd_manager_t* bdd = bv->bddm;

  // Go through all the variable lists (constraints) where we're watching var
  remove_iterator_t it;
  variable_list_ref_t x_watch_list_ref;
  variable_t* cstr_vars;
  variable_t* var_list_it;

  // Mark the variable as processed
  ivector_push(&bv->processed_variables, x);
  bv->processed_variables_size ++;

  if (ctx_trace_enabled(bv->ctx, "mcsat::bv")) {
    ctx_trace_printf(bv->ctx, "trail: ");
    trail_print(bv->ctx->trail, stderr);
  }

  // Notify the BDD manager that it has been assigned
  term_t x_term = variable_db_get_term(var_db, x);
  if (bv_term_is_variable(bv->ctx->terms, x_term) && bv_bdd_manager_has_term(bdd, x_term)) {
    const mcsat_value_t* x_value = trail_get_value(trail, x);
    switch (x_value->type) {
    case VALUE_BOOLEAN:
      bv_bdd_manager_set_bool_value(bdd, x_term, x_value->b);
      break;
    case VALUE_BV:
      bv_bdd_manager_set_bv_value(bdd, x_term, &x_value->bv_value);
      break;
    default:
      assert(false);
    }
  }

  // Get the watch-list and process
  remove_iterator_construct(&it, &bv->wlm, x);
  while (trail_is_consistent(trail) && !remove_iterator_done(&it)) {

    // Get the current list where var appears
    x_watch_list_ref = remove_iterator_get_list_ref(&it);
    cstr_vars = watch_list_manager_get_list(&bv->wlm, x_watch_list_ref);

    // constraint variable
    variable_t cstr = watch_list_manager_get_constraint(&bv->wlm, x_watch_list_ref);
    if (ctx_trace_enabled(bv->ctx, "mcsat::bv::propagate")) {
      ctx_trace_printf(bv->ctx, "propagating ");
      variable_db_print_variable(var_db, x, ctx_trace_out(bv->ctx));
      ctx_trace_printf(bv->ctx, " -> ");
      mcsat_value_print(trail_get_value(trail, x), ctx_trace_out(bv->ctx));
      ctx_trace_printf(bv->ctx, " in [");
      variable_db_print_variables(var_db, cstr_vars, ctx_trace_out(bv->ctx));
      ctx_trace_printf(bv->ctx, "]\n");
    }

    // Put the variable to [1] so that [0] is the unit one
    if (cstr_vars[0] == x && cstr_vars[1] != variable_null) {
      cstr_vars[0] = cstr_vars[1];
      cstr_vars[1] = x;
    }

    // Find a new watch (start from [2])
    var_list_it = cstr_vars + 1;
    if (*var_list_it != variable_null) {
      for (++var_list_it; *var_list_it != variable_null; ++var_list_it) {
        if (!bv_plugin_has_assignment(bv, *var_list_it)) {
          // Swap with var_list[1]
          cstr_vars[1] = *var_list_it;
          *var_list_it = x;
          // Add to new watch
          watch_list_manager_add_to_watch(&bv->wlm, x_watch_list_ref, cstr_vars[1]);
          // Don't watch this one
          remove_iterator_next_and_remove(&it);
          break;
        }
      }
    }

    if (*var_list_it == variable_null) {
      // We did not find a new watch: vars[1], ..., vars[n] are assigned:
      // - if vars[0] is the constraint, we propagate it based on value
      // - otherwise cstr is unit in vars[0] and we need to update the feasibility
      if (!bv_plugin_has_assignment(bv, cstr_vars[0])) {
        bv_plugin_set_unit_info(bv, cstr, cstr_vars[0], CONSTRAINT_UNIT);
        bv_plugin_process_unit_constraint(bv, prop, cstr, cstr_vars[0]);
      } else {
        bv_plugin_set_unit_info(bv, cstr, variable_null, CONSTRAINT_FULLY_ASSIGNED);
        if (cstr_vars[0] == cstr) {
          uint32_t cstr_eval_level = 0;
          const mcsat_value_t* cstr_value = bv_evaluator_run(&bv->evaluator, cstr, &cstr_eval_level);
          if (!trail_has_value(trail, cstr)) {
            // Unassigned, propagate the value
            prop->add_at_level(prop, cstr, cstr_value, cstr_eval_level);
          } else {
            // The constraint already has a value, check that it's the right one
            assert(mcsat_value_eq(cstr_value, trail_get_value(trail, cstr)));
          }
        }
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
  const mcsat_trail_t* trail = bv->ctx->trail;

  variable_t x = variable_null;
  for(; trail_is_consistent(trail) && bv->trail_i < trail_size(trail); ++ bv->trail_i) {
    x = trail_at(trail, bv->trail_i);
    bv_plugin_propagate_var(bv, x, prop);
  }
}

static
void bv_plugin_push(plugin_t* plugin) {

  bv_plugin_t* bv = (bv_plugin_t*) plugin;

  if (ctx_trace_enabled(bv->ctx, "mcsat::bv")) {
    ctx_trace_printf(bv->ctx, "bv_plugin_push(...)\n");
  }

  // Pop the int variable values
  scope_holder_push(&bv->scope,
      &bv->trail_i,
      &bv->processed_variables_size,
      NULL);
}

static
void bv_plugin_pop(plugin_t* plugin) {

  bv_plugin_t* bv = (bv_plugin_t*) plugin;

  if (ctx_trace_enabled(bv->ctx, "mcsat::bv")) {
    ctx_trace_printf(bv->ctx, "bv_plugin_pop(...)\n");
  }

  // Pop the int variable values
  scope_holder_pop(&bv->scope,
      &bv->trail_i,
      &bv->processed_variables_size,
      NULL);

  // Undo the processed variables
  while (bv->processed_variables.size > bv->processed_variables_size) {
    // The variable to undo
    variable_t x = ivector_pop2(&bv->processed_variables);

    // Go through the watch and mark the constraints
    remove_iterator_t it;
    remove_iterator_construct(&it, &bv->wlm, x);
    while (!remove_iterator_done(&it)) {
      variable_t cstr = remove_iterator_get_constraint(&it);
      constraint_unit_info_t unit_info = bv_plugin_get_unit_info(bv, cstr);
      switch (unit_info) {
      case CONSTRAINT_UNKNOWN:
        // Nothing to do
        break;
      case CONSTRAINT_UNIT:
        // If it was unit it becomes not unit
        bv_plugin_set_unit_info(bv, cstr, variable_null, CONSTRAINT_UNKNOWN);
        break;
      case CONSTRAINT_FULLY_ASSIGNED:
        // It is unit now
        bv_plugin_set_unit_info(bv, cstr, x, CONSTRAINT_UNIT);
        break;
      }
      remove_iterator_next_and_keep(&it);
    }
    remove_iterator_destruct(&it);
  }

  // We undid last decision, so we're back to normal
  bv->last_decided_and_unprocessed = variable_null;
}


static
void bv_plugin_decide(plugin_t* plugin, variable_t x, trail_token_t* decide, bool must) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;
  mcsat_value_t v;
  bvconstant_t b;
  uint32_t bitsize;

  assert(!trail_has_value(bv->ctx->trail, x));
    
  // Get the feasible set
  bdd_t x_bdd = bv_feasible_set_db_get(bv->feasible, x);

  // Construct a new value
  bitsize = term_bitsize(bv->ctx->terms, variable_db_get_term(bv->ctx->var_db,x));
  init_bvconstant(&b);
  bvconstant_set_all_zero(&b, bitsize);
  if (x_bdd.bdd != NULL) {
    term_t x_term = variable_db_get_term(bv->ctx->var_db, x);
    bv_bdd_manager_pick_value(bv->bddm, x_term, x_bdd, &b);
  }
  mcsat_value_construct_bv_value(&v, &b);

  if (ctx_trace_enabled(bv->ctx, "mcsat::bv")) {
    ctx_trace_printf(bv->ctx, "bv_plugin_decide: ");
    variable_db_print_variable(bv->ctx->var_db, x,ctx_trace_out(bv->ctx));
    ctx_trace_printf(bv->ctx, " gets assigned ");
    mcsat_value_print(&v, ctx_trace_out(bv->ctx));
    ctx_trace_printf(bv->ctx, " in trail: ");
    trail_print(bv->ctx->trail, stderr);
  }

  // Add decision to solver
  decide->add(decide, x, &v);
  bv->last_decided_and_unprocessed = x;

  // Remove temps
  mcsat_value_destruct(&v);
  delete_bvconstant(&b);
}

static
void bv_plugin_get_conflict(plugin_t* plugin, ivector_t* conflict) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;

  if (ctx_trace_enabled(bv->ctx, "mcsat::bv")) {
    ctx_trace_printf(bv->ctx, "bv_plugin_get_conflict: ");
    ctx_trace_term(bv->ctx, variable_db_get_term(bv->ctx->var_db, bv->conflict_variable));
  }

  assert(false);

  // Compute the conflict
  ivector_t core, lemma_reasons;
  init_ivector(&core, 0);
  init_ivector(&lemma_reasons, 0);
  bv_feasible_set_db_get_conflict_reasons(bv->feasible, bv->conflict_variable, &core, &lemma_reasons);

  ivector_swap(conflict, &bv->conflict);
  ivector_reset(&bv->conflict);

  delete_ivector(&core);
  delete_ivector(&lemma_reasons);
}

static
term_t bv_plugin_explain_propagation(plugin_t* plugin, variable_t var, ivector_t* reasons) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;
  (void) bv;

  if (ctx_trace_enabled(bv->ctx, "mcsat::bv")) {
    ctx_trace_printf(bv->ctx, "bv_plugin_explain_propagation(...) -> assert(false);\n");
  }
  // TODO
  assert(false);

  return NULL_TERM;
}

static
bool bv_plugin_explain_evaluation(plugin_t* plugin, term_t t, int_mset_t* vars, mcsat_value_t* value) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;
  (void) bv;

  if (ctx_trace_enabled(bv->ctx, "mcsat::bv")) {
    ctx_trace_printf(bv->ctx, "bv_plugin_explain_evaluation(...) -> assert(false);\n");
  }
  // TODO
  assert(false);

  return true;
}

static
void bv_plugin_set_exception_handler(plugin_t* plugin, jmp_buf* handler) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;

  if (ctx_trace_enabled(bv->ctx, "mcsat::bv")) {
    ctx_trace_printf(bv->ctx, "bv_plugin_set_exception_handler(...)\n");
  }

  bv->exception = handler;
}

static
void bv_plugin_new_lemma_notify(plugin_t* plugin, ivector_t* lemma, trail_token_t* prop) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;

  uint32_t i;

  // Check if all atoms unit in single variable x, then we can propagate
  bool is_unit = true;
  variable_t unit_var = variable_null;
  for (i = 0; is_unit && i < lemma->size; ++ i) {
    term_t literal = lemma->data[i];
    term_t atom = unsigned_term(literal);
    variable_t atom_var = variable_db_get_variable_if_exists(bv->ctx->var_db, atom);
    assert(atom_var != variable_null);
    if (bv_plugin_get_unit_info(bv, atom_var) != CONSTRAINT_UNIT) {
      // Not unit
      is_unit = false;
    } else {
      // Unit, check if same variable
      variable_t atom_unit_var = bv_plugin_get_unit_var(bv, atom_var);
      if (unit_var == variable_null) {
        unit_var = atom_unit_var;
      } else if (unit_var != atom_unit_var) {
        is_unit = false;
      }
    }
  }

  // If its a clause (A1(x) or ... or An(x)) we can remember at zero level
  if (is_unit && bv->ctx->trail->decision_level == 0) {
    assert(false);
  }
}


plugin_t* bv_plugin_allocator(void) {
  bv_plugin_t* plugin = safe_malloc(sizeof(bv_plugin_t));
  plugin_construct((plugin_t*) plugin);
  plugin->plugin_interface.construct             = bv_plugin_construct;
  plugin->plugin_interface.destruct              = bv_plugin_destruct;
  plugin->plugin_interface.new_term_notify       = bv_plugin_new_term_notify;
  plugin->plugin_interface.new_lemma_notify      = bv_plugin_new_lemma_notify;
  plugin->plugin_interface.event_notify          = NULL;
  plugin->plugin_interface.propagate             = bv_plugin_propagate;
  plugin->plugin_interface.decide                = bv_plugin_decide;
  plugin->plugin_interface.get_conflict          = bv_plugin_get_conflict;
  plugin->plugin_interface.explain_propagation   = bv_plugin_explain_propagation;
  plugin->plugin_interface.explain_evaluation    = bv_plugin_explain_evaluation;
  plugin->plugin_interface.push                  = bv_plugin_push;
  plugin->plugin_interface.pop                   = bv_plugin_pop;
  plugin->plugin_interface.gc_mark               = NULL;
  plugin->plugin_interface.gc_sweep              = NULL;
  plugin->plugin_interface.set_exception_handler = bv_plugin_set_exception_handler;

  return (plugin_t*) plugin;
}
