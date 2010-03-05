/*
 * STREAMLINED SAT SOLVER FOR BITBLASTING
 *
 * This uses data types defined in smt_core.h
 */

#ifndef __BIT_SOLVER_H
#define __BIT_SOLVER_H


#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "bitvectors.h"
#include "int_vectors.h"
#include "smt_core.h"


/*
 * Types defined in smt_core.h
 * - boolean variables and literals
 * - clauses and learned clauses
 * - variable heap
 * - assignment/propagation stack
 */

/*
 * Statistics record
 */
typedef struct bit_solver_stats_s { 
  uint32_t restarts;         // number of restarts
  uint32_t simplify_calls;   // number of calls to simplify_clause_database
  uint32_t reduce_calls;     // number of calls to reduce_learned_clause_set

  uint64_t decisions;        // number of decisions
  uint64_t random_decisions; // number of random decisions
  uint64_t propagations;     // number of boolean propagations
  uint64_t conflicts;        // number of conflicts/backtrackings

  uint64_t prob_literals;     // number of literals in problem clauses
  uint64_t learned_literals;  // number of literals in learned clauses

  uint64_t prob_clauses_deleted;     // number of problem clauses deleted
  uint64_t learned_clauses_deleted;  // number of learned clauses deleted
  uint64_t bin_clauses_deleted;      // number of binary clauses deleted

  uint64_t literals_before_simpl;
  uint64_t subsumed_literals;

} bit_solver_stats_t;


/*
 * Solver state
 * - global flags and counters
 * - clause data base divided into:
 *    - vector of problem clauses
 *    - vector of learned clauses
 *   unit and binary clauses are stored implicitly.
 * - propagation structures: for every literal l
 *   bin[l] = literal vector for binary clauses
 *   watch[l] = list of clauses where l is a watched literal 
 *     (i.e., clauses where l occurs in position 0 or 1)
 *
 * - for every variable x between 0 and nb_vars - 1 
 *   - antecedent[x]: antecedent type and value 
 *   - level[x]: decision level (only meaningful if x is assigned)
 *   - mark[x]: 1 bit used in UIP computation
 *   - polarity[x]: 1 bit (preferred polarity if x is picked as a decision variable)
 *   - value[x] = current assignment for x
 *   - NOTE: value ranges from -1 to nb_vars - 1 so that
 *     value[x] exists for x = null_bvar (value[x] = VAL_UNDEF)
 *
 * - a stack of assumptions represented as a vector
 *   - each assumption is a literal
 *   - the top of the stack is the last element of the vector
 *   to retract assumptions, we also keep a vector of redundant assumptions
 * 
 * - a heap for the decision heuristic
 *
 * - an assignment + propagation stack
 *
 * - other arrays for contructing and simplifying learned clauses
 */
typedef struct bit_solver_s {
  uint32_t status;            // UNSOLVED, SAT, OR UNSAT

  uint32_t nvars;             // Number of variables
  uint32_t nlits;             // Number of literals = twice the number of variables
  uint32_t vsize;             // Size of the variable arrays (>= nb_vars)
  uint32_t lsize;             // size of the literal arrays (>= nb_lits)

  uint32_t nb_clauses;        // Number of problem + learned clauses with at least 3 literals
  uint32_t nb_prob_clauses;   // Number of (non-hidden) problem clauses
  uint32_t nb_unit_clauses;   // Number of unit clauses
  uint32_t nb_bin_clauses;    // Number of binary clauses

  /* Simplify DB heuristic  */
  uint32_t simplify_bottom;     // stack top pointer after last simplify_clause_database
  uint64_t simplify_props;      // value of propagation counter at that point
  uint64_t simplify_threshold;  // number of propagations before simplify is enabled again

  uint64_t aux_literals;        // temporary counter used by simplify_clause
  uint32_t aux_clauses;         // temporary counter used by simplify_clause

  /* Reduce DB heuristic */
  uint32_t reduce_threshold;    // number of learned clauses before reduce is called

  /* Current decision level */
  uint32_t decision_level;
  uint32_t backtrack_level;
  uint32_t base_level;

  /* Activity increments and decays for learned clauses */
  float cla_inc;          // Clause activity increment
  float inv_cla_decay;    // Inverse of clause decay (e.g., 1/0.999)

  /* Randomness parameter */
  uint32_t scaled_random;    // 0x1000000 * random_factor

  /* Conflict data */
  literal_t conflict_buffer[4];
  literal_t *conflict;
  clause_t *false_clause;

  /* Auxiliary vectors for conflict resolution */
  ivector_t buffer;
  ivector_t buffer2;

  /* Clause database */
  clause_t **problem_clauses;
  clause_t **learned_clauses;

  /* Out-of-order unit clauses */
  ivector_t saved_units;

  /* Assumption stack */
  ivector_t assumptions;
  ivector_t redundant_assumptions;

  /* Variable-indexed arrays */
  antecedent_t *antecedent;
  uint32_t *level;
  byte_t *mark;        // bitvector
  byte_t *polarity;    // bitvector

  /* Literal-indexed arrays */
  uint8_t *value;
  literal_t **bin;   // array of literal vectors
  link_t *watch;     // array of watch lists

  /* Propagation stack */
  prop_stack_t stack;

  /* Heap */
  var_heap_t heap;

  /* Statistics */
  bit_solver_stats_t stats;

} bit_solver_t;



/*
 * PARAMETERS USED IN SEARCH
 */
#define INITIAL_RESTART_THRESHOLD   100
#define MIN_REDUCE_THRESHOLD        1000
#define RESTART_FACTOR_C            1.1
#define RESTART_FACTOR_D            1.1
#define REDUCE_FACTOR               1.05
#define MAX_DTHRESHOLD              1000000




/*
 * INITIALIZATION, CREATION OF VARIABLES AND CLAUSES
 */

/*
 * Solver initialization
 * - size = initial size of the variable arrays
 */
extern void init_bit_solver(bit_solver_t *solver, uint32_t size);

/*
 * Delete solver
 */
extern void delete_bit_solver(bit_solver_t *solver);

/*
 * Allocate a fresh boolean variable and return its index
 */
extern bvar_t bit_solver_new_var(bit_solver_t *solver);

/*
 * Add n new variables
 */
extern void bit_solver_add_vars(bit_solver_t *solver, uint32_t n);


/*
 * Addition of simplified clause
 * - each clause is an array of literals (integers between 0 and 2nvars - 1)
 *   that does not contain twice the same literals or complementary literals
 */
extern void bit_solver_add_empty_clause(bit_solver_t *solver);
extern void bit_solver_add_unit_clause(bit_solver_t *solver, literal_t l);
extern void bit_solver_add_binary_clause(bit_solver_t *solver, literal_t l0, literal_t l1);
extern void bit_solver_add_ternary_clause(bit_solver_t *solver, literal_t l0, literal_t l1, literal_t l2);

// clause l[0] ... l[n-1]
extern void bit_solver_add_clause(bit_solver_t *solver, uint32_t n, literal_t *l);

/*
 * Simplify then add a clause: remove duplicate literals, and already
 * assigned literals, and simplify
 */
extern void bit_solver_simplify_and_add_clause(bit_solver_t *solver, uint32_t n, literal_t *l);




/************************
 *  SEARCH/ASSUMPTIONS  *
 ***********************/

/*
 * Start the search:
 * - base_level must be zero
 * - reset all counters
 * - perform one round of boolean propagation
 * - if there's no conflict, set status to SEARCHING,
 *   and return true.
 * - if there's a conflict, set status to UNSAT
 *   and return false
 */
extern bool bit_solver_start_search(bit_solver_t *solver);

/*
 * Assert l as an assumption and perform a round
 * of boolean propagation.
 * - if there's no conflict, return true
 * - if there's a conflict, return false and set 
 *   solver status to UNSAT
 * - the conflict clause is stored internally in
 *   solver->conflict
 */
extern bool bit_solver_assume(bit_solver_t *solver, literal_t l);

/*
 * Get the number of assumptions so far
 */
static inline uint32_t bit_solver_num_assumptions(bit_solver_t *solver) {
  return solver->assumptions.size;
}

/*
 * Check satisfiability of the set of clauses + assumptions
 * - solver->status must be STATUS_SEARCHING (i.e., start_search
 *   must be called first).
 * - return code = either STATUS_SAT or STATUS_UNSAT
 * - the same code is stored in solver->status
 * - if the status is UNSAT, a conflict clause is stored
 *   internally in solver->conflict
 */
extern smt_status_t bit_solver_check(bit_solver_t *solver);

/*
 * Restore the solver to a clean state after check
 * - check uses simplifications that reduce the set of clauses
 * - this function restore the set of clauses to its original state
 * - it also removes all learned clauses
 */
extern void bit_solver_restore(bit_solver_t *solver);

/*
 * Get the unsat core:
 * - solver->status must be UNSAT and there must be
 *   a conflict clause in solver->conflict.
 * - compute an inconsistnet subset of the assumptions
 * - the result is added to vector v
 */
extern void bit_solver_get_unsat_core(bit_solver_t *solver, ivector_t *v);

/*
 * Get the explanation for literal l
 * - l must be true in the current (partial) assignment
 * - add the set of assumed literals that imply l into vector v
 */
extern void bit_solver_explain_literal(bit_solver_t *solver, literal_t l, ivector_t *v);

/*
 * Retract the last assumption and reset the 
 * status to SEARCHING
 * - there must be an assumption
 */
extern void bit_solver_retract(bit_solver_t *solver);

/*
 * Retract all the assumptions
 */
extern void bit_solver_retract_all(bit_solver_t *solver);

/*
 * Clear the current assignment and reset the solver status to IDLE
 */
extern void bit_solver_clear(bit_solver_t *solver);





/************
 *  MODELS  *
 ***********/

/*
 * Access to the current boolean assignment
 * - val must be an array of at least n elements 
 *   (where n = the number of variables)
 * - for each variable x, val[x] is the value of x in 
 *   the current assignment. If the function is called 
 *   after bit_solver_check returns SAT, then this is a model.
 */
extern void get_allvars_assignment(bit_solver_t *solver, bval_t *val);


/*
 * Copy all the true literals in array a:
 * - a must have size >= solver->nvars.
 * return the number of literals added to a.
 *
 * If solver->status == SAT this should be equal to solver->nvars.
 */
extern uint32_t get_true_literals(bit_solver_t *solver, literal_t *a);



/*
 * Read the value assigned to l at the current decision level
 * (VAL_UNDEF) if l is not assigned
 */
static inline bval_t bit_solver_lit_value(bit_solver_t *s, literal_t l) {
  assert(0 <= l && l < s->nlits);
  return s->value[l];
}


/*
 * Read the value assigned to l at the base level
 * - returns VAL_UNDEF if l is not assigned at that level
 */
static inline bval_t bit_solver_lit_base_value(bit_solver_t *s, literal_t l) {
  assert(0 <= l && l < s->nlits);
  if (s->level[var_of(l)] > s->base_level) {
    return VAL_UNDEF;
  } else {
    return s->value[l];
  }
}

/*
 * Read the value assigned to variable x at the current decision level.
 * This can be used to build a model if s->status is SAT
 */
static inline bval_t bit_solver_bvar_value(bit_solver_t *s, bvar_t x) {
  return bit_solver_lit_value(s, pos_lit(x));
}

/*
 * Read the value assigned to a variable x at the base level
 */
static inline bval_t bit_solver_bvar_base_value(bit_solver_t *s, bvar_t x) {
  return bit_solver_lit_base_value(s, pos_lit(x));
}






/*
 * MISCELLANEOUS
 */
static inline smt_status_t bit_solver_status(bit_solver_t *solver) {
  return solver->status;
}

static inline uint32_t bit_solver_nvars(bit_solver_t *solver) {
  return solver->nvars;
}

static inline uint32_t bit_solver_nliterals(bit_solver_t *solver) {
  return solver->nlits;
}

static inline uint32_t bit_solver_nclauses(bit_solver_t *solver) {
  return solver->nb_clauses;
}

static inline uint32_t bit_solver_nbin_clauses(bit_solver_t *solver) {
  return solver->nb_bin_clauses;
}

static inline uint32_t bit_solver_nunit_clauses(bit_solver_t *solver) {
  return solver->nb_unit_clauses;
}

static inline bit_solver_stats_t *bit_solver_statistics(bit_solver_t *solver) {
  return &solver->stats;
}




#endif /* __BIT_SOLVER_H */
