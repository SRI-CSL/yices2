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
 * Lazy ITE plugin. For a non-Boolean term t = ite(c, a, b), the plugin
 * registers the atoms (t = a) and (t = b) and watches c. It adds no lemma.
 * When c gets a value, the plugin propagates the atom of the selected branch
 * with the reason c or (not c). When an atom becomes false while c has no
 * value, the plugin propagates c with the negated atom as the reason. The
 * owner of the type of t keeps control of its value.
 */

#include "mcsat/ite/ite_plugin.h"
#include "mcsat/tracing.h"
#include "mcsat/utils/int_lset.h"
#include "mcsat/utils/scope_holder.h"

#include "terms/term_manager.h"
#include "utils/int_hash_map.h"
#include "utils/int_vectors.h"
#include "utils/memalloc.h"

typedef struct {
  /** Variable of the ITE term t */
  variable_t t_var;
  /** Condition, as in the ITE term (can be a negative term) */
  term_t c;
  /** Atoms (t = then-branch) and (t = else-branch), or true_term/false_term */
  term_t eq_then;
  term_t eq_else;
} ite_info_t;

typedef struct {

  /** The plugin interface */
  plugin_t plugin_interface;

  /** The plugin context */
  plugin_context_t* ctx;

  /** Information on each registered non-Boolean ITE term */
  ite_info_t* infos;
  uint32_t infos_size;
  uint32_t infos_capacity;

  /** Map from the variable of t to its index in infos */
  int_hmap_t info_of_var;

  /** Map from an atom variable to 2 * t_var + (1 if then-branch, 0 if else-branch) */
  int_hmap_t atom_owner;

  /** Map from a variable that this plugin propagated to the reason literal */
  int_hmap_t reason_of;

  /** Map from the variable of unsigned_term(c) to the variables of the ITE terms */
  int_lset_t watch;

  /** ITE variables registered while their condition already had a value */
  ivector_t pending;

  /** Next trail element to process */
  uint32_t trail_i;

  /** Scope for trail_i */
  scope_holder_t scope;

  /** The conflict to report */
  ivector_t conflict;

  struct {
    statistic_int_t* propagations;
    statistic_int_t* reverse_propagations;
    statistic_int_t* conflicts;
    statistic_int_t* conflicts_t_first;
  } stats;

  /** Exception handler */
  jmp_buf* exception;

} ite_plugin_t;

static
void ite_plugin_construct(plugin_t* plugin, plugin_context_t* ctx) {
  ite_plugin_t* ite = (ite_plugin_t*) plugin;

  ite->ctx = ctx;
  ite->infos = NULL;
  ite->infos_size = 0;
  ite->infos_capacity = 0;
  init_int_hmap(&ite->info_of_var, 0);
  init_int_hmap(&ite->atom_owner, 0);
  init_int_hmap(&ite->reason_of, 0);
  int_lset_construct(&ite->watch);
  init_ivector(&ite->pending, 0);
  ite->trail_i = 0;
  scope_holder_construct(&ite->scope);
  init_ivector(&ite->conflict, 0);

  ite->stats.propagations = statistics_new_int(ctx->stats, "mcsat::ite::propagations");
  ite->stats.reverse_propagations = statistics_new_int(ctx->stats, "mcsat::ite::reverse_propagations");
  ite->stats.conflicts = statistics_new_int(ctx->stats, "mcsat::ite::conflicts");
  ite->stats.conflicts_t_first = statistics_new_int(ctx->stats, "mcsat::ite::conflicts_t_first");

  ctx->request_term_notification_by_kind(ctx, ITE_TERM, false);
  ctx->request_term_notification_by_kind(ctx, ITE_SPECIAL, false);
}

static
void ite_plugin_destruct(plugin_t* plugin) {
  ite_plugin_t* ite = (ite_plugin_t*) plugin;

  safe_free(ite->infos);
  delete_int_hmap(&ite->info_of_var);
  delete_int_hmap(&ite->atom_owner);
  delete_int_hmap(&ite->reason_of);
  int_lset_destruct(&ite->watch);
  delete_ivector(&ite->pending);
  scope_holder_destruct(&ite->scope);
  delete_ivector(&ite->conflict);
}

static
ite_info_t* ite_plugin_get_info(ite_plugin_t* ite, variable_t t_var) {
  int_hmap_pair_t* find = int_hmap_find(&ite->info_of_var, t_var);
  assert(find != NULL);
  return ite->infos + find->val;
}

static
void ite_plugin_new_term_notify(plugin_t* plugin, term_t term, trail_token_t* prop) {
  ite_plugin_t* ite = (ite_plugin_t*) plugin;
  term_table_t* terms = ite->ctx->terms;
  variable_db_t* var_db = ite->ctx->var_db;

  if (ctx_trace_enabled(ite->ctx, "mcsat::new_term")) {
    ctx_trace_printf(ite->ctx, "ite_plugin_new_term_notify: ");
    ctx_trace_term(ite->ctx, term);
  }

  assert(term_kind(terms, term) == ITE_TERM || term_kind(terms, term) == ITE_SPECIAL);

  // When the solver notifies the ITE plugin of a Boolean ITE term, the ITE
  // plugin shall add no lemma and no trail entry for that term.
  if (term_type_kind(terms, term) == BOOL_TYPE) {
    return;
  }

  variable_t t_var = variable_db_get_variable(var_db, term);
  if (int_hmap_find(&ite->info_of_var, t_var) != NULL) {
    return;
  }

  // When the solver notifies the ITE plugin of a non-Boolean ITE term, the
  // ITE plugin shall add no lemma for that term.
  // The two branch atoms are registered here, not during search: registration
  // during search lets other plugins add trail entries that the propagation
  // loop does not see. The owners of the atoms register the branches.
  composite_term_t* desc = ite_term_desc(terms, term);
  term_t eq_then = mk_eq(ite->ctx->tm, term, desc->arg[1]);
  term_t eq_else = mk_eq(ite->ctx->tm, term, desc->arg[2]);
  if (eq_then != true_term && eq_then != false_term) {
    variable_t atom_var = variable_db_get_variable(var_db, unsigned_term(eq_then));
    int_hmap_get(&ite->atom_owner, atom_var)->val = 2 * t_var + 1;
  }
  if (eq_else != true_term && eq_else != false_term) {
    variable_t atom_var = variable_db_get_variable(var_db, unsigned_term(eq_else));
    int_hmap_get(&ite->atom_owner, atom_var)->val = 2 * t_var;
  }

  if (ite->infos_size == ite->infos_capacity) {
    ite->infos_capacity = ite->infos_capacity == 0 ? 16 : 2 * ite->infos_capacity;
    ite->infos = (ite_info_t*) safe_realloc(ite->infos, ite->infos_capacity * sizeof(ite_info_t));
  }
  ite_info_t* info = ite->infos + ite->infos_size;
  info->t_var = t_var;
  info->c = desc->arg[0];
  info->eq_then = eq_then;
  info->eq_else = eq_else;
  int_hmap_add(&ite->info_of_var, t_var, ite->infos_size);
  ite->infos_size ++;

  variable_t c_var = variable_db_get_variable(var_db, unsigned_term(desc->arg[0]));
  int_lset_add(&ite->watch, c_var, t_var);

  // When the solver notifies the ITE plugin of a non-Boolean ITE term whose
  // condition already has a value, the ITE plugin shall add the trail entry
  // of the selected branch at the next call to propagate.
  if (trail_has_value(ite->ctx->trail, c_var)) {
    ivector_push(&ite->pending, t_var);
  }

  (void) prop;
}

static
void ite_plugin_report_conflict(ite_plugin_t* ite, trail_token_t* prop, variable_t t_var, variable_t c_var) {
  const mcsat_trail_t* trail = ite->ctx->trail;

  (*ite->stats.conflicts) ++;
  if (trail_has_value(trail, t_var) && trail_get_index(trail, t_var) < trail_get_index(trail, c_var)) {
    (*ite->stats.conflicts_t_first) ++;
  }
  prop->conflict(prop);
}

/** Propagate the atom of the selected branch of the ITE variable t_var */
static
void ite_plugin_fire(ite_plugin_t* ite, variable_t t_var, trail_token_t* prop) {
  const mcsat_trail_t* trail = ite->ctx->trail;
  variable_db_t* var_db = ite->ctx->var_db;

  ite_info_t* info = ite_plugin_get_info(ite, t_var);
  variable_t c_var = variable_db_get_variable_if_exists(var_db, unsigned_term(info->c));
  assert(c_var != variable_null);

  // While the condition of a registered non-Boolean ITE term t has no value
  // on the trail, the ITE plugin shall add no trail entry for t.
  if (!trail_has_value(trail, c_var)) {
    return;
  }

  bool c_value = trail_get_boolean_value(trail, c_var);
  if (is_neg_term(info->c)) {
    c_value = !c_value;
  }
  term_t lit = c_value ? info->c : opposite_term(info->c);

  term_t atom = c_value ? info->eq_then : info->eq_else;

  if (ctx_trace_enabled(ite->ctx, "mcsat::ite")) {
    ctx_trace_printf(ite->ctx, "ite_plugin_fire: ");
    ctx_trace_term(ite->ctx, atom);
  }

  if (atom == true_term) {
    return;
  }

  // If the condition of a registered non-Boolean ITE term t selects a branch
  // and the trail forces t to differ from that branch, then the ITE plugin
  // shall report a conflict whose learned clause is (the negated condition
  // literal) or (t equals that branch).
  if (atom == false_term) {
    ivector_reset(&ite->conflict);
    ivector_push(&ite->conflict, lit);
    ite_plugin_report_conflict(ite, prop, t_var, c_var);
    return;
  }

  variable_t atom_var = variable_db_get_variable_if_exists(var_db, unsigned_term(atom));
  assert(atom_var != variable_null);
  bool atom_var_value = is_pos_term(atom);

  if (trail_has_value(trail, atom_var)) {
    if (trail_get_boolean_value(trail, atom_var) != atom_var_value) {
      ivector_reset(&ite->conflict);
      ivector_push(&ite->conflict, lit);
      ivector_push(&ite->conflict, opposite_term(atom));
      ite_plugin_report_conflict(ite, prop, t_var, c_var);
    }
    return;
  }

  // While the condition c of a registered non-Boolean term t = ite(c, a, b)
  // is true on the trail and the trail does not force t to differ from a,
  // when the solver calls the ITE plugin to propagate, the ITE plugin shall
  // add a trail entry that forces t to equal a.
  // While the condition c of a registered non-Boolean term t = ite(c, a, b)
  // is false on the trail and the trail does not force t to differ from b,
  // when the solver calls the ITE plugin to propagate, the ITE plugin shall
  // add a trail entry that forces t to equal b.
  uint32_t level = trail_get_level(trail, c_var);
  int_hmap_get(&ite->reason_of, atom_var)->val = lit;
  prop->add_at_level(prop, atom_var, atom_var_value ? &mcsat_value_true : &mcsat_value_false, level);
  (*ite->stats.propagations) ++;
}

/** Propagate the condition of an ITE term from a false branch atom */
static
void ite_plugin_reverse(ite_plugin_t* ite, variable_t atom_var, int32_t owner, trail_token_t* prop) {
  const mcsat_trail_t* trail = ite->ctx->trail;
  variable_t t_var = owner / 2;
  bool is_then = (owner % 2) == 1;
  const ite_info_t* info = ite_plugin_get_info(ite, t_var);

  term_t atom = is_then ? info->eq_then : info->eq_else;
  bool atom_is_true = trail_get_boolean_value(trail, atom_var) == is_pos_term(atom);
  if (atom_is_true) {
    return;
  }

  // When c has a value, ite_plugin_fire reports the conflict of a selected
  // branch whose atom is false.
  variable_t c_var = variable_db_get_variable_if_exists(ite->ctx->var_db, unsigned_term(info->c));
  assert(c_var != variable_null);
  if (trail_has_value(trail, c_var)) {
    return;
  }

  // While the condition c of a registered non-Boolean term t = ite(c, a, b)
  // has no value on the trail, when the atom (t = a) becomes false on the
  // trail, the ITE plugin shall add a trail entry that sets c to false with
  // the literal (not (t = a)) as the only reason.
  // While the condition c of a registered non-Boolean term t = ite(c, a, b)
  // has no value on the trail, when the atom (t = b) becomes false on the
  // trail, the ITE plugin shall add a trail entry that sets c to true with the
  // literal (not (t = b)) as the only reason.
  term_t c_lit = is_then ? opposite_term(info->c) : info->c;
  int_hmap_get(&ite->reason_of, c_var)->val = opposite_term(atom);
  uint32_t level = trail_get_level(trail, atom_var);
  prop->add_at_level(prop, c_var, is_pos_term(c_lit) ? &mcsat_value_true : &mcsat_value_false, level);
  (*ite->stats.reverse_propagations) ++;
}

static
void ite_plugin_propagate(plugin_t* plugin, trail_token_t* prop) {
  ite_plugin_t* ite = (ite_plugin_t*) plugin;
  const mcsat_trail_t* trail = ite->ctx->trail;
  int_lset_iterator_t it;
  uint32_t i;

  while (trail_is_consistent(trail) && ite->trail_i < trail_size(trail)) {
    variable_t var = trail_at(trail, ite->trail_i);
    ite->trail_i ++;
    int_hmap_pair_t* owner = int_hmap_find(&ite->atom_owner, var);
    if (owner != NULL) {
      ite_plugin_reverse(ite, var, owner->val, prop);
    }
    if (!int_lset_has_list(&ite->watch, var)) {
      continue;
    }
    int_lset_iterator_construct(&it, &ite->watch, var);
    while (!int_lset_iterator_done(&it) && trail_is_consistent(trail)) {
      ite_plugin_fire(ite, *int_lset_iterator_get(&it), prop);
      int_lset_iterator_next_and_keep(&it);
    }
    int_lset_iterator_destruct(&it);
  }

  // ITE terms registered while their condition already had a value
  i = 0;
  while (i < ite->pending.size && trail_is_consistent(trail)) {
    ite_plugin_fire(ite, ite->pending.data[i], prop);
    i ++;
  }
  // Keep the ones that did not fire
  uint32_t j;
  for (j = 0; i < ite->pending.size; ++ i, ++ j) {
    ite->pending.data[j] = ite->pending.data[i];
  }
  ivector_shrink(&ite->pending, j);
}

static
term_t ite_plugin_explain_propagation(plugin_t* plugin, variable_t var, ivector_t* reasons) {
  ite_plugin_t* ite = (ite_plugin_t*) plugin;
  const mcsat_trail_t* trail = ite->ctx->trail;

  // When the solver asks the ITE plugin to explain a trail entry that forces
  // t to equal a, the ITE plugin shall return the literal c as the only reason.
  // When the solver asks the ITE plugin to explain a trail entry that forces
  // t to equal b, the ITE plugin shall return the literal (not c) as the only
  // reason.
  // The reason of a condition from a false atom is the negated atom.
  int_hmap_pair_t* find = int_hmap_find(&ite->reason_of, var);
  assert(find != NULL);
  ivector_push(reasons, find->val);

  return bool2term(trail_get_boolean_value(trail, var));
}

static
void ite_plugin_get_conflict(plugin_t* plugin, ivector_t* conflict) {
  ite_plugin_t* ite = (ite_plugin_t*) plugin;
  ivector_add(conflict, ite->conflict.data, ite->conflict.size);
  ivector_reset(&ite->conflict);
}

static
void ite_plugin_push(plugin_t* plugin) {
  ite_plugin_t* ite = (ite_plugin_t*) plugin;
  scope_holder_push(&ite->scope, &ite->trail_i, NULL);
}

static
void ite_plugin_pop(plugin_t* plugin) {
  ite_plugin_t* ite = (ite_plugin_t*) plugin;
  scope_holder_pop(&ite->scope, &ite->trail_i, NULL);
  ivector_reset(&ite->conflict);
}

static
void ite_plugin_gc_mark_term(const variable_db_t* var_db, gc_info_t* gc_vars, term_t t) {
  if (t == true_term || t == false_term) {
    return;
  }
  variable_t x = variable_db_get_variable_if_exists(var_db, unsigned_term(t));
  if (x != variable_null && !gc_info_is_marked(gc_vars, x)) {
    gc_info_mark(gc_vars, x);
  }
}

static
void ite_plugin_gc_mark(plugin_t* plugin, gc_info_t* gc_vars) {
  ite_plugin_t* ite = (ite_plugin_t*) plugin;
  variable_db_t* var_db = ite->ctx->var_db;
  uint32_t i;

  // An atom that stays keeps its ITE term, so that explain_propagation works
  int_hmap_pair_t* it = int_hmap_first_record(&ite->atom_owner);
  for (; it != NULL; it = int_hmap_next_record(&ite->atom_owner, it)) {
    variable_t t_var = it->val / 2;
    if (gc_info_is_marked(gc_vars, it->key) && !gc_info_is_marked(gc_vars, t_var)) {
      gc_info_mark(gc_vars, t_var);
    }
  }

  // An ITE term that stays keeps its condition and its two atoms
  for (i = 0; i < ite->infos_size; ++ i) {
    const ite_info_t* info = ite->infos + i;
    if (gc_info_is_marked(gc_vars, info->t_var)) {
      ite_plugin_gc_mark_term(var_db, gc_vars, info->c);
      ite_plugin_gc_mark_term(var_db, gc_vars, info->eq_then);
      ite_plugin_gc_mark_term(var_db, gc_vars, info->eq_else);
    }
  }
}

static
void ite_plugin_gc_sweep(plugin_t* plugin, const gc_info_t* gc_vars) {
  ite_plugin_t* ite = (ite_plugin_t*) plugin;
  variable_db_t* var_db = ite->ctx->var_db;
  uint32_t i, j;

  // Keep the ITE terms that stay, and rebuild the index and the watch lists
  int_hmap_reset(&ite->info_of_var);
  int_lset_destruct(&ite->watch);
  int_lset_construct(&ite->watch);
  for (i = 0, j = 0; i < ite->infos_size; ++ i) {
    ite_info_t info = ite->infos[i];
    if (!gc_info_is_marked(gc_vars, info.t_var)) {
      continue;
    }
    ite->infos[j] = info;
    int_hmap_add(&ite->info_of_var, info.t_var, j);
    variable_t c_var = variable_db_get_variable_if_exists(var_db, unsigned_term(info.c));
    assert(c_var != variable_null);
    int_lset_add(&ite->watch, c_var, info.t_var);
    j ++;
  }
  ite->infos_size = j;

  gc_info_sweep_int_hmap_keys(gc_vars, &ite->atom_owner);
  gc_info_sweep_int_hmap_keys(gc_vars, &ite->reason_of);

  for (i = 0, j = 0; i < ite->pending.size; ++ i) {
    if (gc_info_is_marked(gc_vars, ite->pending.data[i])) {
      ite->pending.data[j ++] = ite->pending.data[i];
    }
  }
  ivector_shrink(&ite->pending, j);
}

static
void ite_plugin_event_notify(plugin_t* plugin, plugin_notify_kind_t kind) {
  ite_plugin_t* ite = (ite_plugin_t*) plugin;

  // A user pop removes atoms that were propagated inside the popped level,
  // while their conditions can stay on the trail below trail_i. The ITE terms
  // stay registered, so the solver does not notify them again. Scan the whole
  // trail again: firing an ITE term a second time adds nothing.
  if (kind == MCSAT_SOLVER_POP) {
    ite->trail_i = 0;
  }
}

static
void ite_plugin_set_exception_handler(plugin_t* plugin, jmp_buf* handler) {
  ite_plugin_t* ite = (ite_plugin_t*) plugin;
  ite->exception = handler;
}

plugin_t* ite_plugin_allocator(void) {
  ite_plugin_t* plugin = safe_malloc(sizeof(ite_plugin_t));
  plugin_construct((plugin_t*) plugin);
  plugin->plugin_interface.construct             = ite_plugin_construct;
  plugin->plugin_interface.destruct              = ite_plugin_destruct;
  plugin->plugin_interface.new_term_notify       = ite_plugin_new_term_notify;
  plugin->plugin_interface.event_notify          = ite_plugin_event_notify;
  plugin->plugin_interface.propagate             = ite_plugin_propagate;
  plugin->plugin_interface.explain_propagation   = ite_plugin_explain_propagation;
  plugin->plugin_interface.get_conflict          = ite_plugin_get_conflict;
  plugin->plugin_interface.push                  = ite_plugin_push;
  plugin->plugin_interface.pop                   = ite_plugin_pop;
  plugin->plugin_interface.gc_mark               = ite_plugin_gc_mark;
  plugin->plugin_interface.gc_sweep              = ite_plugin_gc_sweep;
  plugin->plugin_interface.set_exception_handler = ite_plugin_set_exception_handler;

  return (plugin_t*) plugin;
}
