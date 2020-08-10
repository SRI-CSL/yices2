/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2020 SRI International.
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
 * STRATIFICATION: ORGANIZE TYPES/VARIABLES/DISEQUALITIES BY LEVELS
 */

/*
 * We use an ordering on function types to handle functions and arrays in
 * a well-founded order. This is important when we handle functions
 * of type (-> (-> bool bool) T) or variants.
 *
 * If f is a function of this type, we construct a value for f by
 * looking at the E-graph. This value will include a default value
 * of type T and a partial mapping that defines f[i_0] ... f[i_k]
 * where i_0, ..., i_k are E-graph classes of type (-> bool bool).
 *
 * This works as long as k < 4 as there are only four objects of
 * type (-> bool bool). To ensure this, we must first make sure
 * that functions of type (-> bool bool) are processed befroe
 * we look at functions of type (-> (-> bool bool) T).
 *
 * If there are more than 4 distinct classes of type (-> bool bool)
 * in the E-graph, the fun solver will generate extensionality axioms
 * for some of them, which will force backtracking.
 */

#ifndef __STRATIFICATION_H
#define __STRATIFICATION_H

#include <assert.h>
#include <stdint.h>

#include "solvers/egraph/egraph_base_types.h"
#include "solvers/funs/fun_level.h"

/*
 * For each level i, we keep track of
 * - the number of root variables at this level
 * - the number of disequalities at this level
 * + two integer indices that keep track of this level
 *   in arrays vars and diseqs
 *
 * Each variable and disequality is identified by an integer index.
 *
 * We also use two arrays that store variables and disequality ids
 * in level order.
 *
 * Variables of level i are stored in a slice of array vars.
 * - start of that slice = sum of strata[j].nvars for j<i
 * - end of that slice = start + strata[i].nvars
 * - when we store variable in vars: strata[i].var_idx is an index
 *   such that start of slice i <= var_idx < end_of_slice i
 *   var_idx is incremented with every addition at that level.
 *
 * The diseq_idx is used in the same way to store disequalities in
 * array diseqs.
 */
// record for each level
typedef struct stratum_s {
  uint32_t nvars;
  uint32_t ndiseqs;
  uint32_t var_idx;
  uint32_t diseq_idx;
} stratum_t;

typedef struct stratification_s {
  flevel_table_t levels; // see fun_level.h
  uint32_t size;         // size of array strata
  uint32_t nlevels;      // strata[0 ... nlevels-1]: initialized/active
  uint32_t nvars;        // total number of variables = sum strata[i].nvars
  uint32_t ndiseqs;      // total number of disequalities = sum strata[i].diseqs
  stratum_t *strata;
  // phase 2:
  thvar_t *vars;         // array of all variables stored in level order
  uint32_t *diseqs;      // array of disequality ids stored in level order
} stratification_t;


// default and max number of levels
#define DEF_STRATIFICATION_SIZE 8
#define MAX_STRATIFICATION_SIZE (UINT32_MAX/sizeof(stratum_t))

// max number of vars and disequalities
#define MAX_STRATIFICATION_NUM_VARS (UINT32_MAX/sizeof(thvar_t))
#define MAX_STRATIFICATION_NUM_DISEQS (UINT32_MAX/sizeof(uint32_t))


/*
 * Initialize: use the give type table
 * - allocate a strata array of default size
 */
extern void init_stratification(stratification_t *s, type_table_t *types);

/*
 * Delete: free memory
 */
extern void delete_stratification(stratification_t *s);


/*
 * FIRST-PASS: determine the size of each stratum.
 */

/*
 * Increment the count of variables of level k = flevel(sigma).
 * - resize array strata if needed.
 */
extern void stratify_incr_var_count(stratification_t *s, type_t sigma);

/*
 * Increment the count of disequalities of level k = flevel(sigma)
 */
extern void stratify_incr_diseq_count(stratification_t *s, type_t sigma);


/*
 * SECOND PASS: create the variables/disequality arrays.
 */

/*
 * Allocate the arrays for variables and disequalities
 */
extern void stratify_make_arrays(stratification_t *s);

/*
 * Add variable x of type sigma
 */
extern void stratify_add_var(stratification_t *s, thvar_t x, type_t sigma);

/*
 * Add disequality i of type sigma
 */
extern void stratify_add_diseq(stratification_t *s, uint32_t i, type_t sigma);


/*
 * RESULTS: after phase 2
 */

// number of strata
static inline uint32_t strat_num_levels(const stratification_t *s) {
  return s->nlevels;
}

// total number of vars
static inline uint32_t strat_num_vars(const stratification_t *s) {
  return s->nvars;
}

// total number of disequalities
static inline uint32_t strat_num_diseqs(const stratification_t *s) {
  return s->ndiseqs;
}

// number of vars in stratum i
static inline uint32_t num_vars_in_stratum(const stratification_t *s, uint32_t i) {
  assert(i < s->nlevels);
  return s->strata[i].nvars;
}

// start of variable slice for stratum i
extern uint32_t first_var_in_stratum(const stratification_t *s, uint32_t i);

// number of disequalities in stratum i
static inline uint32_t num_diseqs_in_stratum(const stratification_t *s, uint32_t i) {
  assert(i < s->nlevels);
  return s->strata[i].ndiseqs;
}

// start of disequality slice for stratum i
extern uint32_t first_diseq_in_stratum(const stratification_t *s, uint32_t i);

#endif /* __STRATIFICATION_H */
