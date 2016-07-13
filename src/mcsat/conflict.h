/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#ifndef MCSAT_CONFLICT_H_
#define MCSAT_CONFLICT_H_

#include "mcsat/trail.h"
#include "mcsat/variable_db.h"

#include "utils/int_hash_map.h"
#include "utils/int_hash_sets.h"
#include "io/tracer.h"


/** Reference of the conflict element in the memory */
typedef int32_t conflict_element_ref_t;

/** Null reference for conflict elements */
#define conflict_element_ref_null (-1)

/**
 * The conflict element is just a disjunct in the conflict clause. It
 * associated with its top variable that implies it to be false, and linked
 * with other disjuncts that are false due to the same variable. The variable
 * itself is kept outside, so he element only holds the reference to the next
 * element.
 */
typedef struct conflict_element_s {
  /** The disjunct itself */
  term_t D;
  /** Reference to the next element */
  conflict_element_ref_t next;
} conflict_element_t;

typedef struct mcsat_evaluator_interface_s mcsat_evaluator_interface_t;

/**
 * Object to help evaluate terms and constraints.
 */
struct mcsat_evaluator_interface_s {
  /**
   * Check if the term evaluates and return the variables responsible
   * for the evaluation. If value != NULL, and the term evaluates, the output value
   * should be assigned to it.
   */
  bool (*evaluates) (const mcsat_evaluator_interface_t* self, term_t t, int_mset_t* top_level_vars, mcsat_value_t* value);
};

/**
 * The conflict is a disjunction (D1 or D2 or ... or Dn) that evaluates to
 * false in the current trail. Each disjunct is associated with its top variable
 * (in the trail) that is part of the reason it is false.
 */
typedef struct conflict_s {

  /** Memory for the elements of the conflict */
  conflict_element_t* elements;

  /** Number of used elements */
  uint32_t elements_size;

  /** The capacity of the elements array */
  uint32_t elements_capacity;

  /** Free list of elements */
  conflict_element_ref_t elements_free_list;

  /** Map from variables (not terms) to elements where this variable is the top */
  int_hmap_t var_to_element_map;

  /** Collection of variables (one variable per each top level literals it appears in) */
  int_mset_t top_level_vars;

  /** All variables that ever appeared during the conflict resolution */
  int_mset_t vars_all;

  /** Set of current disjuncts */
  int_mset_t disjuncts;

  /** Level of the conflict */
  uint32_t level;

  /** The number of top level variables in the conflict */
  uint32_t top_level_vars_count;

  /** The variable database */
  variable_db_t* var_db;

  /** The trail */
  mcsat_trail_t* trail;

  /** The terms for debugging */
  term_table_t* terms;

  /** The tracer for debugging */
  tracer_t* tracer;

  /** Evaluator so that we can evaluate terms */
  const mcsat_evaluator_interface_t* evaluator;

} conflict_t;

/**
 * Construct the conflict. The conflict_lits are literals (terms) that evaluate
 * to true and the lemma (and conflict_lits) => false is valid.
 */
void conflict_construct(conflict_t* conflict, const ivector_t* conflict_lits,
    const mcsat_evaluator_interface_t* evaluator, variable_db_t* var_db, mcsat_trail_t* trail,
    term_table_t* terms, tracer_t* tracer);

/** Destruct the conflict */
void conflict_destruct(conflict_t* conflict);

/** Print the conflict */
void conflict_print(const conflict_t* conflict, FILE* out);

/** Returns the level at which the conflict is false. */
uint32_t conflict_get_level(const conflict_t* conflict);

/** Returns true if the variable is part of the conflit (not necesserily as top) */
bool conflict_contains(const conflict_t* conflict, variable_t var);

/** Returns true if the variable is part of the conflict (as top) */
bool conflict_contains_as_top(const conflict_t* conflict, variable_t var);

/** Get the number of variables responsible for the conflict at the conflict top level */
uint32_t conflict_get_top_level_vars_count(const conflict_t* conflict);

/** Recompute level information */
void conflict_recompute_level_info(conflict_t* conflict);

/** Resolve the given variable by using ((and reasons) => var = substitution). */
void conflict_resolve_propagation(conflict_t* conflict, variable_t var, term_t substitution, ivector_t* reasons);

/** Get all the variables responsible for the conflict (internal reference) */
ivector_t* conflict_get_variables(conflict_t* conflict);

/** Get all the variables that were ever in the conflict */
const int_mset_t* conflict_get_variables_all(conflict_t* conflict);

/** Get all the literals */
ivector_t* conflict_get_literals(conflict_t* conflict);

/** Get all the literals of the given variable */
void conflict_get_literals_of(conflict_t* conflict, variable_t var, ivector_t* literals);

#endif
