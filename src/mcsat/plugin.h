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
 
#ifndef PLUGIN_H_
#define PLUGIN_H_

#include "mcsat/variable_db.h"
#include "mcsat/trail.h"
#include "mcsat/gc.h"

#include "utils/int_mset.h"
#include "mcsat/utils/statistics.h"
#include "mcsat/options.h"

#include "io/tracer.h"

#include <setjmp.h>

/**
 * Notification of basic solver events.
 */
typedef enum {
  /** Each time a the search starts */
  MCSAT_SOLVER_START,
  /** Each time a restart is initiated */
  MCSAT_SOLVER_RESTART,
  /** Each time a conflict is encountered */
  MCSAT_SOLVER_CONFLICT,
  /** Each time we do a user pop, before garbage collection */
  MCSAT_SOLVER_POP
} plugin_notify_kind_t;

/**
 * Context for the plugins, and the interface for plugins to request various features.
 */
struct plugin_context_s {

  /** Variable database */
  variable_db_t* var_db;

  /** Term table */
  term_table_t* terms;

  /** Type table */
  type_table_t* types;

  /** Exception handler */
  jmp_buf* exception;

  /** Options */
  const mcsat_options_t* options;

  /** The read-only solver trail */
  const mcsat_trail_t* trail;

  /** Statistics */
  statistics_t* stats;

  /** The tracer */
  tracer_t* tracer;

  /** Request term registration for this kind */
  void (*request_term_notification_by_kind) (plugin_context_t* self, term_kind_t kind);

  /** Request term registration for this type */
  void (*request_term_notification_by_type) (plugin_context_t* self, type_kind_t type);

  /** Request a restart */
  void (*request_restart) (plugin_context_t* self);

  /** Request garbage collection */
  void (*request_gc) (plugin_context_t* self);

  /** Request propagation calls */
  void (*request_propagation_calls) (plugin_context_t* self);

  /** Request decision calls for a specific type */
  void (*request_decision_calls) (plugin_context_t* self, type_kind_t type);

  /** Bump the heuristic value of the given variable */
  void (*bump_variable) (plugin_context_t* self, variable_t x);

  /** Compare the heuristic values of the given variables */
  int (*cmp_variables) (plugin_context_t* self, variable_t x, variable_t y);

  /**
   * Request a split in the current context, i.e. add a lemma
   *   (l1 or ... or ln)
   * for li in split_literals. The literals are terms and they should constitute
   * a valid lemma.
   */
  void (*request_split) (plugin_context_t* self, ivector_t* split_literals);

};

/** Token to add entries to the trail */
struct trail_token_s {

  /**
   * Add a propagation at the current decision level. Returns true if OK,
   * i.e. the variable is not already assigned a value.
   */
  bool (*add) (trail_token_t* token, variable_t x, const mcsat_value_t* value);

  /**
   * Add a propagation at a level lower than the current decision level. Returns
   * true if OK, i.e. the variable is not already assigned a value.
   */
  bool (*add_at_level) (trail_token_t* token, variable_t x, const mcsat_value_t* value, uint32_t level);

  /**
   * Report a conflict.
   */
  void (*conflict) (trail_token_t* token);

  /**
   * Add a top-level lemma that will stay for the current user level.
   */
  void (*lemma) (trail_token_t* token, term_t lemma);

};

/**
 * Allocator for plugins. An allocator shoudld
 * - Allocate the plugin, basically malloc(sizeof(actual_plugin_size))
 * - Setup all the interface methods
 * - All other construction goes into the construct method
 */
typedef plugin_t* (*plugin_allocator_t) (void);

struct plugin_s {

  /** Construct the plugin data. */
  void (*construct) (plugin_t* plugin, plugin_context_t* ctx);

  /** Destruct and free the plugin */
  void (*destruct) (plugin_t* plugin);

  /**
   * Registration of terms. The solver calls this on any term that has not been
   * registered yet. The kind of the term is associated with this function though
   * the solver. The visitor should traverse the term and add any variable to
   * subterms that it will interpret, or it needs the interpretation of.
   *
   * @param plugin
   *        The plugin itself
   * @param term
   *        The new term
   * @param prop
   *        The token to use for propagating any values
   * Examples:
   *
   *  (x + ite(b, y, z) > 0):
   *    the arith visitor adds a variable for the whole term (it will interpret
   *    it), and variables for x and ite(b, y, z) (it needs those interpretations)
   *
   *  not (x + y > 0):
   *    the CNF visitor should visit not, and add a variable for (x + y > 0) since
   *    can interpret it (as a Boolean)
   *
   *  not (x and (y or z)):
   *    the CNF visitor should visit the whole thing, register variables for any
   *
   *  f(x) > g(y):
   *    the arith visitor adds variables for f(x) and g(y)
   *
   *  f(x + 1):
   *    UF visitor add variables for f(x + 1) and (x + 1)
   */
  void (*new_term_notify) (plugin_t* plugin, term_t term, trail_token_t* prop);

  /**
   * Notification of new lemmas. Each lemma is a disjunction given as a vector
   * of terms.
   */
  void (*new_lemma_notify) (plugin_t* plugin, ivector_t* lemma, trail_token_t* prop);

  /**
   * Notification of solver events.
   */
  void (*event_notify) (plugin_t* plugin, plugin_notify_kind_t kind);

  /**
   * Propagate using the given trail token. You can read from the trail that
   * was given at construction time, but only propagate deductions through the
   * propagation token.
   */
  void (*propagate) (plugin_t* plugin, trail_token_t* prop);

  /**
   * Decide a variable using the given trail token. The token can be used
   * only once. If must is true, the plugin must decide on the variable.
   */
  void (*decide) (plugin_t* plugin, variable_t x, trail_token_t* decide, bool must);

  /**
   * Explain the conflict that you reported. The plugin should return a conflict
   * such that
   *
   *  (and conflict) => false
   *
   * is a valid lemma, and v(c) evaluates to true for each c in conflict. The
   * conflict vector contains term_t objects.
   */
  void (*get_conflict) (plugin_t* plugin, ivector_t* conflict);

  /**
   * Explain a propagation x -> v made by the plugin. The plugin should return
   * a substitution t such that
   *
   *  (and reasons) => x = t
   *
   * is a valid lemma, v(r) evaluates to true for each r in reason, and t
   * evaluates to v. The reasons are term_t objects.
   *
   * If the x = t is a literal assigned is due to evaluation, it is ok to return
   * the literal itself.
   *
   */
  term_t (*explain_propagation) (plugin_t* plugin, variable_t var, ivector_t* reasons);

  /**
   * Explain an evaluation. Return true if the constraint indeed evaluates, and
   * collect the variables that are responsible for the evaluation. If given
   * value is not NULL, and the term evaluates, then put the evaluation into it.
   * If the value is NULL, just collect the variables that contribute to the
   * value. The output variables should be mcsat variables (variable_t).
   */
  bool (*explain_evaluation) (plugin_t* plugin, term_t t, int_mset_t* vars, mcsat_value_t* value);

  /**
   * Push the internal context.
   */
  void (*push) (plugin_t* plugin);

  /**
   * Pop the internal context.
   */
  void (*pop) (plugin_t* plugin);

  /**
   * Build the model.
   */
  void (*build_model) (plugin_t* plugin, model_t* model);

  /**
   * Collect all the variables that are still relevant in the current context.
   */
  void (*gc_mark) (plugin_t* plugin, gc_info_t* gc);

  /**
   * Use the gc info to collect all the useless stuff.
   * @param gc the set of variables marked to keep
   */
  void (*gc_sweep) (plugin_t* plugin, const gc_info_t* gc_vars);

  /**
   * Notifies the plugin about a new exception handler.
   */
  void (*set_exception_handler)(plugin_t* plugin, jmp_buf* handler);

};

/** Construct the plugin */
static inline
void plugin_construct(plugin_t* plugin) {
  plugin->construct             = NULL;
  plugin->destruct              = NULL;
  plugin->new_term_notify       = NULL;
  plugin->new_lemma_notify      = NULL;
  plugin->propagate             = NULL;
  plugin->decide                = NULL;
  plugin->get_conflict          = NULL;
  plugin->explain_propagation   = NULL;
  plugin->explain_evaluation    = NULL;
  plugin->push                  = NULL;
  plugin->pop                   = NULL;
  plugin->build_model           = NULL;
  plugin->gc_mark               = NULL;
  plugin->gc_sweep              = NULL;
  plugin->set_exception_handler = NULL;
}


#endif /* PLUGIN_H_ */
