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
 * INPUT TO THE EXISTS/FORALL SOLVER
 */

/*
 * Data structure to store an exist/forall problem.
 * The basic form is
 *
 *    A(x) AND (FORALL y: B(y) => C(x, y))
 *
 * and the goal is to find x that satisfies this constraint.
 *
 * Generalization:
 * - A(x) is a conjunction: A_1(x) .... A_n(x)
 * - several universal constraints:
 *     (forall y_1: B_1(y_1) => C_1(x, y_1))
 *       ...
 *     (forall y_t: B_t(y_t) => C_t(x, y_t))
 *
 * To represent such problems, we store:
 * - the set of all existential variables
 * - the set of all universal variables (the union of y_1 ... y_t)
 * - the set of all constraints on x: the list A_1(x) ... A_n(x)
 * - a descriptor for each universal constraint
 *
 * For a constraint (forall y: B(y) => C(x, y)), the descriptor includes
 * - the set of existential variables occurring in C (i.e., a subset of x)
 * - the set of universal variables occurring in B or C
 * - the assumption B(y)
 * - the guarantee C(x, y)
 *
 * To store sets of terms: we use the index_vector data structure
 * (cf. index_vectors.h).
 */

#ifndef __EF_PROBLEM_H
#define __EF_PROBLEM_H

#include <stdint.h>
#include <stdbool.h>

#include "terms/term_manager.h"
#include "utils/int_vectors.h"
#include "solvers/quant/ef_parameters.h"

/*
 * Descriptor for a universal constraint
 */
typedef struct ef_cnstr_s {
  term_t *evars;     // existential variables
  term_t *uvars;     // universal variables
  term_t *pvars;     // pattern variables
  term_t assumption; // B(y)
  term_t guarantee;  // C(x, y)
  bool has_uint;     // true if constraint has an uninterpreted function/sort
} ef_cnstr_t;


/*
 * Descriptor for the full problem
 * - terms/managers = pointers to term table and term manager
 * - all_evars and all_uvars are sorted in increasing order
 */
typedef struct ef_prob_s {
  term_table_t *terms;
  term_manager_t *manager;
  term_t *all_evars;      // existential variables
  term_t *all_uvars;      // universal variables
  term_t *all_pvars;      // pattern variables
  term_t *conditions;     // constraints on x = A_1(x), ..., A_n(x)
  uint32_t num_cnstr;     // number of forall constraints
  uint32_t cnstr_size;    // size of array cnstr
  ef_cnstr_t *cnstr;      // array of constraint descriptors

  bool has_uint;          // true if prob has an uninterpreted function/sort
  ptr_hmap_t *patterns;   // map from term to smt2 patterns
  ef_param_t *parameters; // link to EF parameters
} ef_prob_t;


// default and max size for array cnstr
#define DEF_EF_CNSTR_SIZE 10
#define MAX_EF_CNSTR_SIZE (UINT32_MAX/sizeof(ef_cnstr_t))


/*
 * Delete pattern map
 */
extern void delete_pattern_map(ptr_hmap_t *m);


/*
 * Initialization: all empty
 * - mngr = relevant term manager
 */
extern void init_ef_prob(ef_prob_t *prob, term_manager_t *mngr, ptr_hmap_t *patterns, ef_param_t *parameters);


/*
 * Reset to empty
 */
extern void reset_ef_prob(ef_prob_t *prob);


/*
 * Delete the whole thing
 */
extern void delete_ef_prob(ef_prob_t *prob);


/*
 * Check emptiness
 */
extern bool ef_prob_is_empty(ef_prob_t *prob);


/*
 * Add v[0...n-1] to all_evars or all_uvars or all_pvars (remove duplicates)
 */
extern void ef_prob_add_evars(ef_prob_t *prob, term_t *v, uint32_t n);
extern void ef_prob_add_uvars(ef_prob_t *prob, term_t *v, uint32_t n);
extern void ef_prob_add_pvars(ef_prob_t *prob, term_t *v, uint32_t n);

/*
 * Add t as a constraint on x
 */
extern void ef_prob_add_condition(ef_prob_t *prob, term_t t);


/*
 * Add a universal constraint:
 * - ev = existential variables, nev = size of the ev array
 * - uv = universal variables, nuv = size of the uv array
 * - pv = pattern variables, must be of the same size as uv (i.e., nuv).
 * - assumption = formula on uv
 * - guarantee = formula on uv and ev
 *
 * The global arrays all_evars and all_uvars are updated:
 * - all_evars := all_evars union ev
 * - all_uvars := all_uvars union uv
 */
extern void ef_prob_add_constraint(ef_prob_t *prob, term_t *ev, uint32_t nev, term_t *uv, uint32_t nuv,
				   term_t assumption, term_t guarantee, term_t *pv);


/*
 * Print a forall constraint
 */
extern void ef_print_constraint(FILE *f, ef_cnstr_t *cnstr);


/*
 * Number of existential/universal variables
 */
extern uint32_t ef_prob_num_evars(ef_prob_t *prob); // size of all_evars
extern uint32_t ef_prob_num_uvars(ef_prob_t *prob); // size of all_uvars


/*
 * Check the type of universal variables
 * - this returns true if some universal variables are integer or real
 */
extern bool ef_prob_has_arithmetic_uvars(ef_prob_t *prob);


/*
 * Number of conditions
 */
extern uint32_t ef_prob_num_conditions(ef_prob_t *prob);


/*
 * Number of constraints
 */
static inline uint32_t ef_prob_num_constraints(ef_prob_t *prob) {
  return prob->num_cnstr;
}


/*
 * Number of variables in a forall constraint
 */
extern uint32_t ef_constraint_num_evars(ef_cnstr_t *cnstr);
extern uint32_t ef_constraint_num_uvars(ef_cnstr_t *cnstr);


/*
 * Convert prob to an array of formulas (a big conjunction)
 * - all the conditions are added to v
 * - for every constraint, the formula (B_i => C_i) is added to v
 *   (without quantifiers)
 */
extern void ef_prob_collect_conjuncts(ef_prob_t *prob, ivector_t *v);


#endif /* __EF_PROBLEM_H */
