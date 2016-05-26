/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * RECORD TO STORE SEARCH OPTIONS/SETTINGS
 */

#ifndef __SEARCH_PARAMETERS_H
#define __SEARCH_PARAMETERS_H


#include <stdbool.h>
#include <stdint.h>

#include "yices_types.h"


/*
 * Possible branching heuristics:
 * - determine whether to assign the decision literal to true or false
 */
typedef enum {
  BRANCHING_DEFAULT,  // use internal smt_core cache
  BRANCHING_NEGATIVE, // branch l := false
  BRANCHING_POSITIVE, // branch l := true
  BRANCHING_THEORY,   // defer to the theory solver
  BRANCHING_TH_NEG,   // defer to theory solver for atoms, branch l := false otherwise
  BRANCHING_TH_POS,   // defer to theory solver for atoms, branch l := true otherwise
} branch_t;

#define NUM_BRANCHING_MODES 6


struct param_s {
  /*
   * Restart heuristic: similar to PICOSAT or MINISAT
   *
   * If fast_restart is true: PICOSAT-style heuristic
   * - inner restarts based on c_threshold
   * - outer restarts based on d_threshold
   *
   * If fast_restart is false: MINISAT-style restarts
   * - c_threshold and c_factor are used
   * - d_threshold and d_threshold are ignored
   * - to get periodic restart set c_factor = 1.0
   *
   * HACK to select a Luby-style restart:
   * - set fast_restart to true and c_factor to 0.0
   * - then c_threshold defines the base period
   * - d_threshold and d_factor are ignored
   */
  bool     fast_restart;
  uint32_t c_threshold;     // initial value of c_threshold
  uint32_t d_threshold;     // initial value of d_threshold
  double   c_factor;        // increase factor for next c_threshold
  double   d_factor;        // increase factor for next d_threshold

  /*
   * Clause-deletion heuristic
   * - initial reduce_threshold is max(r_threshold, num_prob_clauses * r_fraction)
   * - increase by r_factor on every outer restart provided reduce was called in that loop
   */
  uint32_t r_threshold;
  double   r_fraction;
  double   r_factor;

  /*
   * SMT Core parameters:
   * - randomness and var_decay are used by the branching heuristic
   *   the default branching mode uses the cached polarity in smt_core.
   * - clause_decay influence clause deletion
   * - random seed
   *
   * SMT Core caching of theory lemmas:
   * - if cache_tclauses is true, then the core internally turns
   *   some theory lemmas into learned clauses
   * - for the core, a theory lemma is either a conflict reported by
   *   the theory solver or a theory implication
   * - a theory implication is considered for caching if it's involved
   *   in a conflict resolution
   * - parameter tclause_size controls the lemma size: only theory lemmas
   *   of size <= tclause_size are turned into learned clauses
   */
  double   var_decay;       // decay factor for variable activity
  float    randomness;      // probability of a random pick in select_unassigned_literal
  uint32_t random_seed;
  branch_t branching;       // branching heuristic
  float    clause_decay;    // decay factor for learned-clause activity
  bool     cache_tclauses;
  uint32_t tclause_size;

  /*
   * EGRAPH PARAMETERS
   *
   * Control of the Ackermann lemmas
   * - use_dyn_ack: if true, the dynamic ackermann heuristic is enabled for
   *   non-boolean terms
   * - use_bool_dyn_ack: if true, the dynamic ackermann heuristic is enabled
   *   for boolean terms
   * - use_optimistic_fcheck: if true, model reconciliation is used
   *   in final_check
   *
   * Limits to stop the Ackermann trick if too many lemmas are generated
   * - max_ackermann: limit for the non-boolean version
   * - max_boolackermann: limit for the boolean version
   *
   * The Ackermann clauses may require the construction of new equality
   * terms that were not present in the context. This is controlled by
   * the egraph's quota on auxiliary equalities. The quota is initialized
   * to max(aux_eq_ratio * n, aux_eq_quota) where n is the total
   * number of terms in the initial egraph.
   *
   * Thresholds for generation of Ackermann lemma: no effect unless
   * use_dyn_ack or use_bool_dyn_ack is true.
   *
   * Control of interface equality generation: set a limit on
   * the number of interface equalities created per round.
   */
  bool     use_dyn_ack;
  bool     use_bool_dyn_ack;
  bool     use_optimistic_fcheck;
  uint32_t max_ackermann;
  uint32_t max_boolackermann;
  uint32_t aux_eq_quota;
  double   aux_eq_ratio;
  uint16_t dyn_ack_threshold;
  uint16_t dyn_bool_ack_threshold;
  uint32_t max_interface_eqs;


  /*
   * SIMPLEX PARAMETERS
   * - simplex_prop: if true enable propagation via propagation table
   * - adjust_simplex_model: if true, enable adjustment in
   *   reconciliation of the egraph and simplex models
   * - integer_check: if true, periodically call the integer solver
   * - max_prop_row_size: limit on the size of the propagation rows
   * - bland_threshold: threshold that triggers switching to Bland's rule
   * - integer_check_period: how often the integer solver is called
   */
  bool     use_simplex_prop;
  bool     adjust_simplex_model;
  bool     integer_check;
  uint32_t max_prop_row_size;
  uint32_t bland_threshold;
  int32_t  integer_check_period;

  /*
   * ARRAY SOLVER PARAMETERS
   * - max_update_conflicts: limit on the number of update axioms generated
   *   per call to final_check
   * - max_extensionality: limit on the number of extensionality axioms
   *   generated per call to reconcile_model
   */
  uint32_t max_update_conflicts;
  uint32_t max_extensionality;

};



/************************
 *  PARAMETER RECORDS   *
 ***********************/

/*
 * Initialize params with default values
 */
extern void init_params_to_defaults(param_t *parameters);


/*
 * Get a pointer to an internal record (set to defaults)
 */
extern const param_t *get_default_params(void);


/*
 * Set a field in the parameter record
 * - key = field name
 * - value = value for that field
 *
 * Return code:
 *  -1 if the key is not recognized
 *  -2 if the value is not recognized
 *  -3 if the value is not valid for the key
 *   0 otherwise
 */
extern int32_t params_set_field(param_t *parameters, const char *key, const char *value);


/*
 * To synchronize with set-random-seed/get-random-seed
 */
extern uint32_t params_default_random_seed(void);


#endif /* __SEARCH_PARAMETERS_H */
