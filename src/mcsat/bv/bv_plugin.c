/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2019 SRI International.
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

#include "bdd_computation.h"
#include "bv_feasible_set_db.h"
#include "bv_plugin.h"
#include "bv_bdd_manager.h"
#include "bv_evaluator.h"
#include "bv_explainer.h"
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
#include "utils/generic_heap.h"

#include "terms/terms.h"
#include "terms/bv64_constants.h"

typedef enum {
  BV_PROP_EVALUATION = 1,
  BV_PROP_SINGLETON
} bv_propagation_type_t;

typedef enum {
  BV_CONFLICT_UNIT,
  BV_CONFLICT_EVAL,
  BV_CONFLICT_ASSUMPTION
} bv_conflict_type_t;

typedef struct {

  /** The plugin interface */
  plugin_t plugin_interface;

  /** Watch list manager */
  watch_list_manager_t wlm;
  
  /** The plugin context */
  plugin_context_t* ctx;

  /** Term manager */
  term_manager_t* tm;

  /** Next index of the trail to process */
  uint32_t trail_i;

  /** Scope holder for the int variables */
  scope_holder_t scope;

  /** Conflict variable */
  variable_t conflict_variable;

  /** Bool is the conflict evaluation conflict */
  bv_conflict_type_t conflict_type;

  /** Exception handler */
  jmp_buf* exception;

  /** Map from constraint variables to the constraint_unit_info_t enum */
  int_hmap_t constraint_unit_info;

  /** Map from constraint variables to the variables they are unit in */
  int_hmap_t constraint_unit_var;

  /** Last variable that was decided, but yet unprocessed */
  variable_t last_decided_and_unprocessed;

  /** Map from variables to the propagation type */
  int_hmap_t variable_propagation_type;

  /** Feasible set database */
  bv_feasible_set_db_t* feasible;

  /** BDD manager */
  bv_bdd_manager_t* bddm;

  /** Evaluator */
  bv_evaluator_t evaluator;

  /** Explainer */
  bv_explainer_t explainer;

  /** Variables processed in propagation */
  ivector_t processed_variables;

  /** Size of processed (for backtracking) */
  uint32_t processed_variables_size;

  /** Cache for term traversals. Maps from term to bump value. */
  int_hmap_t visited_cache;

  /** Heap for term traversal order */
  generic_heap_t visit_heap;

  struct {
    statistic_int_t* conflicts;
    statistic_int_t* propagations;
    statistic_int_t* evaluations;
    statistic_int_t* constraints_attached;
  } stats;

} bv_plugin_t;

static
bool term_visit_cmp(void *data, int32_t x, int32_t y) {
  return x > y;
}

static
void bv_plugin_construct(plugin_t* plugin, plugin_context_t* ctx) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;

  bv->ctx = ctx;
  bv->tm = ctx->tm;
  scope_holder_construct(&bv->scope);
  bv->trail_i = 0;

  bv->last_decided_and_unprocessed = variable_null;
  bv->conflict_variable = variable_null;
  bv->conflict_type = BV_CONFLICT_UNIT;

  if (ctx_trace_enabled(bv->ctx, "mcsat::bv")) {
    ctx_trace_printf(bv->ctx, "bv_plugin_construct(...)\n");
  }

  // Construct the watch-list data structures
  watch_list_manager_construct(&bv->wlm, bv->ctx->var_db);
  init_int_hmap(&bv->constraint_unit_info, 0);
  init_int_hmap(&bv->constraint_unit_var, 0);
  
  init_int_hmap(&bv->variable_propagation_type, 0);

  bv->bddm = bv_bdd_manager_new(ctx);
  bv->feasible = bv_feasible_set_db_new(ctx, bv->bddm);

  bv_evaluator_construct(&bv->evaluator, ctx);

  bv_explainer_construct(&bv->explainer, ctx, &bv->wlm, &bv->evaluator);

  init_ivector(&bv->processed_variables, 0);
  bv->processed_variables_size = 0;

  init_int_hmap(&bv->visited_cache, 0);
  init_generic_heap(&bv->visit_heap, 0, 0, term_visit_cmp, NULL);

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
  bv->stats.conflicts = statistics_new_int(bv->ctx->stats, "mcsat::bv::conflicts");
  bv->stats.propagations = statistics_new_int(bv->ctx->stats, "mcsat::bv::propagations");
  bv->stats.evaluations = statistics_new_int(bv->ctx->stats, "mcsat::bv::evaluations");
  bv->stats.constraints_attached = statistics_new_int(bv->ctx->stats, "mcsat::bv::constraints_attached");
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
  delete_int_hmap(&bv->variable_propagation_type);
  scope_holder_destruct(&bv->scope);
  bv_feasible_set_db_delete(bv->feasible);
  bv_bdd_manager_delete(bv->bddm);
  bv_evaluator_destruct(&bv->evaluator);
  bv_explainer_destruct(&bv->explainer);
  delete_ivector(&bv->processed_variables);
  delete_int_hmap(&bv->visited_cache);
  delete_generic_heap(&bv->visit_heap);
}


/**
 * Test if variable x has been assigned a value in the trail, but only if this
 * assignment has already been processed by the bv plugin.
 */

static inline
bool bv_plugin_has_assignment(const bv_plugin_t* bv, variable_t x) {
  return trail_has_value(bv->ctx->trail, x) && trail_get_index(bv->ctx->trail, x) < bv->trail_i;
}

/**
 * Setting status of constraint: if value is CONSTRAINT_UNIT, then unit_var is the variable in which constraint is unit;
 * otherwise unit_var is variable_null
 */

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
    assert(unit_var == variable_null);
    if (unit_find != NULL) {
      unit_find->val = variable_null;
    }
  }
}

/**
 * Getting status of constraint: if return value is CONSTRAINT_UNIT,
 * then bv_plugin_get_unit_var returns the variable in which constraint is unit
 * (otherwise it returns variable_null)
 */

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
variable_t bv_plugin_get_unit_var(bv_plugin_t* bv, variable_t constraint) {
  int_hmap_pair_t* find = int_hmap_find(&bv->constraint_unit_var, constraint);
  if (find == NULL) {
    return variable_null;
  } else {
    return find->val;
  }
}

/**
 * Comparing variables; used for the creation of a watch list, which is initially sorted with this function.
 * the two initial watched variables are the two smallest variables according to this function.
 */

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

#define MAX_BUMP_VALUE 1073741824 // 2^30

/**
 * Scores are additive.
 */
static inline
void bv_plugin_get_term_variable_visit_term(bv_plugin_t* bv, term_t t, uint32_t parent_bump, uint32_t t_bump) {
  assert(is_pos_term(t));
  generic_heap_add(&bv->visit_heap, t);
  if (parent_bump > t_bump || t_bump > MAX_BUMP_VALUE) {
    // overflow or too big
    t_bump = MAX_BUMP_VALUE;
  }
  int_hmap_pair_t* find = int_hmap_get(&bv->visited_cache, t);
  if (find->val < 0) {
    find->val = t_bump;
  } else {
    find->val += t_bump;
    if (find->val > MAX_BUMP_VALUE) {
      find->val = MAX_BUMP_VALUE;
    }
  }
}

/**
 * This is a notification for base BV terms. It's expected that these would
 * be atoms, except in the case of theory combination. For example,
 * f(t1::t2) would notify t1::t2 which is not an atom.
 *
 * The simplest way to collect the variables would be to just do a recursive
 * traversal with caching. This simple solution doesn't give us access to
 * position-relevant variable occurrences.
 *
 * For example, consider the term
 *
 *   ((x<<1) + (x<<1)*(x<<1))
 *     1        2      3
 *
 * In the simple traversal we would only visit the variable x in the context
 * of the LHS of + and ignore it in the power-product as it is cached within
 * the already visited terms.
 *
 * Instead our cache will store and accumulate the bump factor and we will
 * visit in the term-id order. For above example we will visit:
 *
 * 1. ((x<<1) + (x<<1)*(x<<1))
 * 2. (x<<1)*(x<<1) -> bump factor ++ for (x<<1)
 * 3. (x<<1) -> bump factor ++ for x
 * 4. x
 *
 * Above allows us to consider all contexts where variables occur.
 */
void bv_plugin_get_notified_term_subvariables(bv_plugin_t* bv, term_t constraint, int_mset_t* vars_out, uint64_t bump_amount) {

  term_table_t* terms = bv->ctx->terms;
  variable_db_t* var_db = bv->ctx->var_db;

  // Make sure we're starting fresh
  int_hmap_reset(&bv->visited_cache);
  reset_generic_heap(&bv->visit_heap);

  // Visit
  term_t constraint_pos = unsigned_term(constraint);
  bv_plugin_get_term_variable_visit_term(bv, constraint_pos, 0, bump_amount);

  // Visit until done
  while (!generic_heap_is_empty(&bv->visit_heap)) {

    // Get the current term
    term_t current = generic_heap_get_min(&bv->visit_heap);
    assert(is_pos_term(current));
    uint32_t current_bump = int_hmap_find(&bv->visited_cache, current)->val;

    if (ctx_trace_enabled(bv->ctx, "mcsat::new_term")) {
      ctx_trace_printf(bv->ctx, "bv_plugin_get_variables: ");
      ctx_trace_term(bv->ctx, current);
    }

    bool handle_variable = false;
    term_kind_t kind = term_kind(terms, current);
    switch (kind) {
    case CONSTANT_TERM: // Boolean variables
    case BV_CONSTANT:
    case BV64_CONSTANT:
       // Ignore, no variables here
       break;
    case EQ_TERM: {
      composite_term_t* atom_comp = composite_term_desc(terms, current);
      assert(atom_comp->arity == 2);
      term_t t0 = atom_comp->arg[0], t0_pos = unsigned_term(t0);
      term_t t1 = atom_comp->arg[1], t1_pos = unsigned_term(t1);
      if (!is_boolean_term(terms, t0) && !is_bitvector_term(terms, t0)) {
        // Ignore non-bitvector equalities
        handle_variable = true;
      } else {
        bv_plugin_get_term_variable_visit_term(bv, t0_pos, current_bump, current_bump);
        bv_plugin_get_term_variable_visit_term(bv, t1_pos, current_bump, current_bump);
      }
      break;
    }
    case BV_EQ_ATOM:
    case BV_GE_ATOM:
    case BV_SGE_ATOM: {
      // These can appear as BV_ARRAY elements
      composite_term_t* atom_comp = composite_term_desc(terms, current);
      assert(atom_comp->arity == 2);
      bv_plugin_get_term_variable_visit_term(bv, atom_comp->arg[0], current_bump, current_bump);
      bv_plugin_get_term_variable_visit_term(bv, atom_comp->arg[1], current_bump, current_bump);
      break;
    }
    case BV_ARRAY: {
      // Special: make sub-terms positive
      composite_term_t* concat_desc = bvarray_term_desc(terms, current);
      uint32_t child_bump = current_bump;
      if (child_bump > 0) {
        child_bump = (child_bump / concat_desc->arity) + 1;
      }
      for (uint32_t i = 0; i < concat_desc->arity; ++i) {
        term_t t_i = concat_desc->arg[i];
        term_t t_i_pos = unsigned_term(t_i);
        bv_plugin_get_term_variable_visit_term(bv, t_i_pos, 0, child_bump);
      }
      break;
    }
    case OR_TERM: {
      composite_term_t* current_comp = or_term_desc(terms, current);
      uint32_t child_bump = current_bump;
      if (child_bump > 0) {
        child_bump ++; // Increasing complexity
      }
      for (uint32_t i = 0; i < current_comp->arity; ++i) {
        term_t t_i = current_comp->arg[i];
        term_t t_i_pos = unsigned_term(t_i);
        bv_plugin_get_term_variable_visit_term(bv, t_i_pos, current_bump, child_bump);
      }
      break;
    }
    case XOR_TERM: {
      composite_term_t* current_comp = xor_term_desc(terms, current);
      uint32_t child_bump = current_bump;
      if (child_bump > 0) {
        child_bump ++; // Increasing complexity
      }
      for (uint32_t i = 0; i < current_comp->arity; ++i) {
        term_t t_i = current_comp->arg[i];
        term_t t_i_pos = unsigned_term(t_i);
        bv_plugin_get_term_variable_visit_term(bv, t_i_pos, current_bump, child_bump);
      }
      break;
    }
    case BV_DIV:
    case BV_REM:
    case BV_SDIV:
    case BV_SREM:
    case BV_SMOD: {
      composite_term_t* current_comp = composite_term_desc(terms, current);
      uint32_t child_bump = current_bump * 2;
      term_t lhs = current_comp->arg[0];
      term_t rhs = current_comp->arg[1];
      bv_plugin_get_term_variable_visit_term(bv, lhs, current_bump, child_bump);
      bv_plugin_get_term_variable_visit_term(bv, rhs, current_bump, child_bump);
      break;
    }
    case BV_SHL:
    case BV_LSHR:
    case BV_ASHR: {
      composite_term_t* current_comp = composite_term_desc(terms, current);
      term_t child_bump = current_bump;
      if (current_bump > 0) {
        child_bump++;
      }
      term_t lhs = current_comp->arg[0];
      term_t rhs = current_comp->arg[1];
      bv_plugin_get_term_variable_visit_term(bv, lhs, current_bump, child_bump);
      bv_plugin_get_term_variable_visit_term(bv, rhs, current_bump, child_bump);
      break;
    }
    case BIT_TERM: {
      term_t subterm = bit_term_arg(terms, current);
      term_t child_bump = current_bump;
      if (current_bump > 0) {
        child_bump ++;
      }
      bv_plugin_get_term_variable_visit_term(bv, subterm, current_bump, child_bump);
      break;
    }
    case BV_POLY: {
      bvpoly_t* current_poly = bvpoly_term_desc(terms, current);
      term_t child_bump = current_bump;
      if (current_bump > 0) {
        child_bump ++;
      }
      for (uint32_t i = 0; i < current_poly->nterms; ++i) {
        if (current_poly->mono[i].var == const_idx) continue;
        term_t var = current_poly->mono[i].var;
        bv_plugin_get_term_variable_visit_term(bv, var, current_bump, child_bump);
      }
      break;
    }
    case BV64_POLY: {
      bvpoly64_t* current_poly = bvpoly64_term_desc(terms, current);
      uint32_t child_bump = current_bump;
      if (child_bump > 0) {
        child_bump ++;
      }
      for (uint32_t i = 0; i < current_poly->nterms; ++i) {
        if (current_poly->mono[i].var == const_idx) continue;
        term_t var = current_poly->mono[i].var;
        bv_plugin_get_term_variable_visit_term(bv, var, current_bump, child_bump);
      }
      break;
    }
    case POWER_PRODUCT: {
      pprod_t* current_pprod = pprod_term_desc(terms, current);
      uint32_t child_bump = current_bump;
      if (child_bump > 0) {
        child_bump += current_pprod->len;
      }
      for (uint32_t i = 0; i < current_pprod->len; ++i) {
        term_t var = current_pprod->prod[i].var;
        bv_plugin_get_term_variable_visit_term(bv, var, current_bump, child_bump);
      }
      break;
    }
    default:
      handle_variable = true;
      break;
    }

    if (handle_variable) {
      // A variable or a foreign term
      assert(is_pos_term(current));
      if (current == constraint_pos) {
        // The constraint itself is a variable
        continue;
      } else {
        variable_t t_var = variable_db_get_variable(var_db, current);
        int_mset_add(vars_out, t_var);
        if (current_bump > 0) {
          uint32_t wordsize = bv_term_bitsize(terms, current)/32+1;
          uint32_t to_bump = current_bump * wordsize;
          if (current_bump > to_bump || to_bump > MAX_BUMP_VALUE) {
            to_bump = MAX_BUMP_VALUE; // Overflow or too big
          }
          if (ctx_trace_enabled(bv->ctx, "mcsat::bv::bump")) {
            if (kind == UNINTERPRETED_TERM) {
              ctx_trace_printf(bv->ctx, "new term: ");
              ctx_trace_term(bv->ctx, current);
              ctx_trace_printf(bv->ctx, "bump    : %"PRIu32"\n", to_bump);
            }
          }
          bv->ctx->bump_variable_n(bv->ctx, t_var, to_bump);
        }
      }
    }

  }

  // Reset the cache
  int_hmap_reset(&bv->visited_cache);
  reset_generic_heap(&bv->visit_heap);
}

void bv_plugin_report_conflict(bv_plugin_t* bv, trail_token_t* prop, variable_t variable, bv_conflict_type_t type) {
  // Although we do full propagation for shared sorts (Bool) a conflict can
  // still happen. For example if we have
  //  x = bool2bv(y)
  // [x->bv1, y->false, (x = bool2bv)->true] can because we don't control
  // how Boolean plugin propagates values
  prop->conflict(prop);
  bv->conflict_variable = variable;
  bv->conflict_type = type;
  (*bv->stats.conflicts) ++;
}

/**
 * Process a constraint that is detected to be fully assigned: check
 * consistency unless we propagated it.
 */
static
void bv_plugin_process_fully_assigned_constraint(bv_plugin_t* bv, trail_token_t* prop, variable_t cstr) {
  const mcsat_trail_t* trail = bv->ctx->trail;
  assert(trail_has_value(trail, cstr));
  if (trail_get_source_id(trail, cstr) != bv->ctx->plugin_id) {
    uint32_t cstr_eval_level = 0;
    const mcsat_value_t* cstr_value = bv_evaluator_evaluate_var(&bv->evaluator, cstr, &cstr_eval_level);
    if (!mcsat_value_eq(cstr_value, trail_get_value(trail, cstr))) {
      if (ctx_trace_enabled(bv->ctx, "mcsat::bv::conflict")) {
        FILE* out = ctx_trace_out(bv->ctx);
        fprintf(out, "Evaluation conflict:\n");
        fprintf(out, "cstr = "); ctx_trace_term(bv->ctx, variable_db_get_term(bv->ctx->var_db, cstr));
        trail_print(bv->ctx->trail, out);
      }
      bv_plugin_report_conflict(bv, prop, cstr, BV_CONFLICT_EVAL);
    }
  }
}

/**
 * Process a constraint cstr(x, y1, ..., yn) that is detected to be unit in x,
 * i.e., x is considered unassigned, and all y_i are assigned:
 * - compute feasible set of cstr;
 * - update with existing feasibile set for x;
 * - report any conflicts (or propagate if possible).
 *
 * Note that (TODO) the constraint might be of the form [(y1 + y2), y1, y2], i.e. be x itself.
 * In that case the constraint is an evaluation constraint. This comes to play in theory
 * theory combination if we do not purify the terms.
 *
 * Precondition? bv_plugin_has_assignment(...,x) is false.
 * But trail_has_value(trail, x) could be true (assignment of x has not yet been processed by the bv plugin)
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
    if (!trail_has_value(trail, cstr)) {
      // Unassigned, propagate the value
      const mcsat_value_t* cstr_value = bv_evaluator_evaluate_var(&bv->evaluator, cstr, &cstr_eval_level);
      prop->add_at_level(prop, cstr, cstr_value, cstr_eval_level);
      int_hmap_pair_t* find = int_hmap_get(&bv->variable_propagation_type, cstr);
      find->val = BV_PROP_EVALUATION;
      (*bv->stats.evaluations) ++;
    } else {
      // No need to evaluate here, we will check when it is processed as
      // fully assigned
    }
    return;
  }

  // Get the constraint value
  bool constraint_value = trail_get_value(trail, cstr)->b;

  // Get the terms
  term_t cstr_term = variable_db_get_term(var_db, cstr);
  if (!constraint_value) { cstr_term = opposite_term(cstr_term); }
  term_t x_term = variable_db_get_term(var_db, x);

  // Get the BDD of the constraint
  bdd_t cstr_bdd = bv_bdd_manager_get_bdd(bddm, cstr_term, x_term);
  assert(cstr_bdd.bdd[0] != NULL);

  // Update the feasible intervals
  bool feasible = bv_feasible_set_db_update(bv->feasible, x, cstr_bdd, &cstr, 1);

  // If the intervals are empty, we have a conflict
  if (!feasible) {
    bv_plugin_report_conflict(bv, prop, x, BV_CONFLICT_UNIT);
  } else {
    if (!trail_has_value(trail, x)) {
      bdd_t feasible = bv_feasible_set_db_get(bv->feasible, x);
      uint32_t x_bitsize = bv_term_bitsize(ctx->terms, x_term);
      bool is_fixed = bv_bdd_manager_bdd_is_point(bddm, feasible, x_bitsize);
      if (is_fixed) {
        bool is_boolean = variable_db_get_type_kind(var_db, x) == BOOL_TYPE;
        bvconstant_t x_bv_value;
        init_bvconstant(&x_bv_value);
        bvconstant_set_bitsize(&x_bv_value, x_bitsize);
        bv_bdd_manager_pick_value(bddm, x_term, feasible, &x_bv_value);
        if (ctx_trace_enabled(ctx, "mcsat::bv::propagate")) {
          ctx_trace_printf(ctx, "propagating value for :\n");
          ctx_trace_term(ctx, x_term);
        }

        int_hmap_pair_t* find = int_hmap_get(&bv->variable_propagation_type, x);
        find->val = BV_PROP_SINGLETON;
        (*bv->stats.propagations) ++;

        if (is_boolean) {
          bool x_value = bvconst_tst_bit(x_bv_value.data, 0);
          prop->add(prop, x, x_value ? &mcsat_value_true : &mcsat_value_false);
        } else {
          mcsat_value_t x_value;
          mcsat_value_construct_bv_value(&x_value, &x_bv_value);
          prop->add(prop, x, &x_value);
          mcsat_value_destruct(&x_value);
        }
        delete_bvconstant(&x_bv_value);
      }
    }
  }
}

// Required as plugin_t field

static
void bv_plugin_new_term_notify(plugin_t* plugin, term_t t, trail_token_t* prop) {

  uint32_t i;
  bv_plugin_t* bv = (bv_plugin_t*) plugin;
  variable_db_t* var_db = bv->ctx->var_db;
  term_table_t* terms = bv->ctx->terms;

  assert(is_pos_term(t));

  if (ctx_trace_enabled(bv->ctx, "mcsat::new_term")) {
    ctx_trace_printf(bv->ctx, "bv_plugin_new_term_notify: ");
    ctx_trace_term(bv->ctx, t);
  }

  term_kind_t t_kind = term_kind(bv->ctx->terms, t);

  if (!is_bitvector_term(terms, t) && !is_boolean_term(terms, t)) {
    return;
  }

  // Set up the variable
  variable_t t_var = variable_db_get_variable(var_db, t);
  
  int_mset_t t_vars;
  int_mset_construct(&t_vars, variable_null);
  // Add the term itself
  int_mset_add(&t_vars, t_var);
  // Collect the sub-variables
  bv_plugin_get_notified_term_subvariables(bv, t, &t_vars, 1);

  // It's a constraint if there is more than one variable
  bool is_constraint = t_vars.element_list.size > 1;

  // Set up the constraint
  if (is_constraint) {

    // Get the list of variables
    ivector_t* t_var_list = int_mset_get_list(&t_vars);

    // Add the variables to the BDD manager (so that we can assign them)
    for (i = 0; i < t_var_list->size; ++ i) {
      variable_t x = t_var_list->data[i];
      term_t x_term = variable_db_get_term(var_db, x);
      bv_bdd_manager_add_term(bv->bddm, x_term);
      // It can happen that term is assigned, but it only now became a BV
      // variable (e.g., Boolean variables).
      if (trail_has_value(bv->ctx->trail, x)) {
        const mcsat_value_t* v = trail_get_value(bv->ctx->trail, x);
        switch (v->type) {
        case VALUE_BOOLEAN:
          bv_bdd_manager_set_bool_value(bv->bddm, x_term, v->b);
          break;
        case VALUE_BV:
          bv_bdd_manager_set_bv_value(bv->bddm, x_term, &v->bv_value);
          break;
        default:
          assert(false);
        }
      }
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
    // Only one variable: constraint with no other variables
    // Either a Boolean variable or a constant term
    // Propagate constant values
    if (bv_term_kind_get_type(t_kind) != BV_TERM_VARIABLE) {
      uint32_t t_eval_level = 0;
      const mcsat_value_t* t_value = bv_evaluator_evaluate_term(&bv->evaluator, t, &t_eval_level);
      prop->add_at_level(prop, t_var, t_value, t_eval_level);
    }
  }

  // Remove the temp variables
  int_mset_destruct(&t_vars);
}


/**
 * Reaction to the discovery that x has been assigned a value
 */

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
    ctx_trace_term(bv->ctx, variable_db_get_term(bv->ctx->var_db, x));
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
      // - if fully assigned, we propagate it based on value (or check that it is correct)
      // - otherwise cstr is unit in vars[0] and we need to update the feasibility
      if (!bv_plugin_has_assignment(bv, cstr_vars[0])) {
        bv_plugin_set_unit_info(bv, cstr, cstr_vars[0], CONSTRAINT_UNIT);
        bv_plugin_process_unit_constraint(bv, prop, cstr, cstr_vars[0]);
      } else {
        bv_plugin_set_unit_info(bv, cstr, variable_null, CONSTRAINT_FULLY_ASSIGNED);
        bv_plugin_process_fully_assigned_constraint(bv, prop, cstr);
      }

      // Keep the watch, and continue
      remove_iterator_next_and_keep(&it);
    }
  }

  // Done, destruct the iterator
  remove_iterator_destruct(&it);
}

// Required as plugin_t field

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

// Required as plugin_t field

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

  // Push the feasibility information
  bv_feasible_set_db_push(bv->feasible);
}

// Required as plugin_t field

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

  // Pop the feasibility
  bv_feasible_set_db_pop(bv->feasible);

  // Undo conflict
  bv->conflict_variable = variable_null;
  bv->conflict_type = BV_CONFLICT_UNIT;

  // We undid last decision, so we're back to normal
  bv->last_decided_and_unprocessed = variable_null;
}


static
void bv_plugin_decide(plugin_t* plugin, variable_t x, trail_token_t* decide, bool must) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;

  assert(!trail_has_value(bv->ctx->trail, x));
  const mcsat_value_t* v = bv_feasible_set_db_pick_value(bv->feasible, x);;

  if (ctx_trace_enabled(bv->ctx, "mcsat::bv::decide")) {
    ctx_trace_printf(bv->ctx, "bv_plugin_decide: ");
    variable_db_print_variable(bv->ctx->var_db, x,ctx_trace_out(bv->ctx));
    ctx_trace_printf(bv->ctx, " gets assigned ");
    mcsat_value_print(v, ctx_trace_out(bv->ctx));
    ctx_trace_printf(bv->ctx, "\n");
  }

  // Add decision to solver
  decide->add(decide, x, v);
  bv->last_decided_and_unprocessed = x;
}

// Required as plugin_t field

static
void bv_plugin_get_conflict(plugin_t* plugin, ivector_t* conflict) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;

  uint32_t i;
  variable_t atom_i_var;
  term_t atom_i_term;
  bool atom_i_value;

  const variable_db_t* var_db = bv->ctx->var_db;
  const mcsat_trail_t* trail = bv->ctx->trail;

  if (ctx_trace_enabled(bv->ctx, "mcsat::bv::conflict")) {
    ctx_trace_printf(bv->ctx, "bv_plugin_get_conflict: ");
    ctx_trace_term(bv->ctx, variable_db_get_term(bv->ctx->var_db, bv->conflict_variable));
  }

  // If the conflict is an evaluation, just return A or !A
  if (bv->conflict_type == BV_CONFLICT_EVAL) {
    term_t cstr = variable_db_get_term(var_db, bv->conflict_variable);
    ivector_push(conflict, cstr);
    ivector_push(conflict, opposite_term(cstr));
    return;
  }

  // Compute the conflict
  ivector_t conflict_core, lemma_reasons;
  init_ivector(&conflict_core, 0);
  init_ivector(&lemma_reasons, 0);

  switch (bv->conflict_type) {
  case BV_CONFLICT_UNIT:
    bv_feasible_set_db_get_reasons(bv->feasible, bv->conflict_variable, &conflict_core, &lemma_reasons, EXPLAIN_EMPTY);
    break;
  case BV_CONFLICT_ASSUMPTION:
    bv_feasible_set_db_get_reasons(bv->feasible, bv->conflict_variable, &conflict_core, &lemma_reasons, EXPLAIN_ASSUMPTION);
    break;
  default:
    assert(false);
  }

  if (ctx_trace_enabled(bv->ctx, "mcsat::bv::conflict")) {
    trail_print(trail, ctx_trace_out(bv->ctx));
    ctx_trace_printf(bv->ctx, "core:\n");
    for (i = 0; i < conflict_core.size; ++ i) {
      atom_i_var = conflict_core.data[i];
      atom_i_value = trail_get_boolean_value(trail, atom_i_var);
      ctx_trace_printf(bv->ctx, "[%"PRIu32"] (%s): ", i, (atom_i_value ? "T" : "F"));
      atom_i_term = variable_db_get_term(var_db, atom_i_var);
      ctx_trace_term(bv->ctx, atom_i_term);
    }
  }

  // Explain with the appropriate theory
  switch (bv->conflict_type) {
  case BV_CONFLICT_UNIT:
    bv_explainer_get_conflict(&bv->explainer, &conflict_core, bv->conflict_variable, conflict);
    break;
  case BV_CONFLICT_ASSUMPTION: {
    assert(conflict_core.size == 1);
    assert(lemma_reasons.size == 0);
    variable_t constraint_var = conflict_core.data[0];
    term_t constraint_term = variable_db_get_term(bv->ctx->var_db, constraint_var);
    ivector_push(conflict, constraint_term);
    ivector_push(conflict, opposite_term(constraint_term));
    break;
  }
  default:
    assert(false);
  }

  // Remove temps
  delete_ivector(&conflict_core);
  delete_ivector(&lemma_reasons);
}

// Required as plugin_t field

static
term_t bv_plugin_explain_propagation(plugin_t* plugin, variable_t var, ivector_t* reasons) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;
#ifndef NDEBUG
  term_table_t* terms = bv->ctx->terms;
#endif
  const mcsat_trail_t* trail = bv->ctx->trail;
  const variable_db_t* var_db = bv->ctx->var_db;

  term_t var_term = variable_db_get_term(var_db, var);
  if (ctx_trace_enabled(bv->ctx, "mcsat::bv::explain")) {
    ctx_trace_printf(bv->ctx, "bv_plugin_explain_propagation(): var = ");
    ctx_trace_term(bv->ctx, var_term);
  }

  // Why did we propagate (evaluation/unit)
  int_hmap_pair_t* find = int_hmap_find(&bv->variable_propagation_type, var);
  assert(find != NULL);
  bv_propagation_type_t propagation_type = find->val;

  if (propagation_type == BV_PROP_SINGLETON) {

    ivector_t explain_core, lemma_reasons;
    init_ivector(&explain_core, 0);
    init_ivector(&lemma_reasons, 0);
    bv_feasible_set_db_get_reasons(bv->feasible, var, &explain_core, &lemma_reasons, EXPLAIN_SINGLETON);

    if (ctx_trace_enabled(bv->ctx, "mcsat::bv::explain")) {
      trail_print(trail, ctx_trace_out(bv->ctx));
      ctx_trace_printf(bv->ctx, "core:\n");
      uint32_t i;
      for (i = 0; i < explain_core.size; ++ i) {
        variable_t atom_i_var = explain_core.data[i];
        bool atom_i_value = trail_get_boolean_value(trail, atom_i_var);
        ctx_trace_printf(bv->ctx, "[%"PRIu32"] (%s): ", i, (atom_i_value ? "T" : "F"));
        term_t atom_i_term = variable_db_get_term(var_db, atom_i_var);
        ctx_trace_term(bv->ctx, atom_i_term);
      }
    }

    assert(lemma_reasons.size == 0);
    term_t subst = bv_explainer_explain_propagation(&bv->explainer, var, &explain_core, reasons);
    if (ctx_trace_enabled(bv->ctx, "mcsat::bv::explain")) {
      ctx_trace_printf(bv->ctx, "bv_plugin_explain_propagation(): subst = ");
      ctx_trace_term(bv->ctx, subst);
    }
    assert(term_type(terms, var_term) == term_type(terms, subst));
    // Remove temps
    delete_ivector(&explain_core);
    delete_ivector(&lemma_reasons);

    return subst;
  } else {
    // We explain them using the literal itself
    bool value = trail_get_boolean_value(trail, var);
    if (ctx_trace_enabled(bv->ctx, "mcsat::bv::conflict")) {
      ctx_trace_printf(bv->ctx, "assigned to %s\n", value ? "true" : "false");
    }
    if (value) {
      // atom => atom = true
      ivector_push(reasons, var_term);
      return bool2term(true);
    } else {
      // neg atom => atom = false
      ivector_push(reasons, opposite_term(var_term));
      return bool2term(false);
    }
  }
}

static
bool bv_plugin_explain_evaluation(plugin_t* plugin, term_t t, int_mset_t* vars, mcsat_value_t* value) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;
  bool result = true;

  if (ctx_trace_enabled(bv->ctx, "mcsat::bv::conflict")) {
    FILE* out = ctx_trace_out(bv->ctx);
    fprintf(out, "asked to explain evaluation for: ");
    ctx_trace_term(bv->ctx, t);
  }

  // Get all the variables and make sure they are all assigned.
  bv_plugin_get_notified_term_subvariables(bv, t, vars, 0);

  // Check if the variables are assigned
  ivector_t* var_list = int_mset_get_list(vars);
  uint32_t i = 0;
  for (i = 0; i < var_list->size; ++ i) {
    bool var_evaluates = trail_has_value(bv->ctx->trail, var_list->data[i]);
    if (ctx_trace_enabled(bv->ctx, "mcsat::bv::conflict")) {
      FILE* out = ctx_trace_out(bv->ctx);
      fprintf(out, "%"PRIu32": ", i);
      ctx_trace_term(bv->ctx, variable_db_get_term(bv->ctx->var_db, var_list->data[i]));
      if (!var_evaluates) {
        fprintf(out, "term doesn't evaluate: ");
        ctx_trace_term(bv->ctx, t);
      }
    }
    if (!var_evaluates) {
      result = false;
    }
  }

  // All variables assigned
  return result;
}

// Required as plugin_t field

static
void bv_plugin_set_exception_handler(plugin_t* plugin, jmp_buf* handler) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;

  if (ctx_trace_enabled(bv->ctx, "mcsat::bv")) {
    ctx_trace_printf(bv->ctx, "bv_plugin_set_exception_handler(...)\n");
  }

  bv->exception = handler;
}

// Required as plugin_t field

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

// Required as plugin_t field

static
void bv_plugin_gc_mark(plugin_t* plugin, gc_info_t* gc_vars) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;
  // The BV plugin doesn't really need to keep much. The only things we'd
  // like to keep are
  // - the lemmas that restrict top level feasibility sets (bv->feasible)
  // - all the bitvector variables that are in use (bv->wlm)
  bv_feasible_set_db_gc_mark(bv->feasible, gc_vars);
  watch_list_manager_gc_mark(&bv->wlm, gc_vars);
}

// Required as plugin_t field

static
void bv_plugin_gc_sweep(plugin_t* plugin, const gc_info_t* gc_vars) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;

  // The feasibility sets keep everything, we just gc the BDDs,
  // the watchlists and the unit information.

  // The BDDs database works over terms, so we can keep it for now
  // TODO: copy over the info cache for terms in gc_vars.
  // bv_bdd_manager_db_gc_sweep(bv->bddm, gc_vars);

  // Feasible sets: everything asserted is in the trail, variables are
  // also marked by the watch manager... nothing to do

  // Unit information (constraint_unit_info, constraint_unit_var)
  gc_info_sweep_int_hmap_keys(gc_vars, &bv->constraint_unit_info);
  gc_info_sweep_int_hmap_keys(gc_vars, &bv->constraint_unit_var);

  // Propagation type
  gc_info_sweep_int_hmap_keys(gc_vars, &bv->variable_propagation_type);

  // Watch list manager
  watch_list_manager_gc_sweep_lists(&bv->wlm, gc_vars);
}

static
void bv_plugin_decide_assignment(plugin_t* plugin, variable_t x, const mcsat_value_t* value, trail_token_t* decide) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;

  // Decide the variable anyhow
  bv->last_decided_and_unprocessed = x;
  decide->add(decide, x, value);

  // Get the feasibility set and check
  bdd_t feasible = bv_feasible_set_db_get(bv->feasible, x);
  term_t x_term = variable_db_get_term(bv->ctx->var_db, x);
  assert(value->type == VALUE_BV);
  if (feasible.bdd[0] != NULL) {
    bool ok = bv_bdd_manager_is_model(bv->bddm, x_term, feasible, &value->bv_value);
    if (!ok) {
      // Ouch, conflict
      bv_plugin_report_conflict(bv, decide, x, BV_CONFLICT_ASSUMPTION);
    }
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
  plugin->plugin_interface.decide_assignment     = bv_plugin_decide_assignment;
  plugin->plugin_interface.get_conflict          = bv_plugin_get_conflict;
  plugin->plugin_interface.explain_propagation   = bv_plugin_explain_propagation;
  plugin->plugin_interface.explain_evaluation    = bv_plugin_explain_evaluation;
  plugin->plugin_interface.push                  = bv_plugin_push;
  plugin->plugin_interface.pop                   = bv_plugin_pop;
  plugin->plugin_interface.gc_mark               = bv_plugin_gc_mark;
  plugin->plugin_interface.gc_sweep              = bv_plugin_gc_sweep;
  plugin->plugin_interface.set_exception_handler = bv_plugin_set_exception_handler;

  return (plugin_t*) plugin;
}
