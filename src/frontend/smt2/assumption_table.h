/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2018 SRI International.
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
 * Table to keep track of the names of assumptions
 * -----------------------------------------------
 *
 * This is used to print unsat cores in the format required by SMT2.
 * SMT2 has two ways of marking formulas as assumptions:
 * 
 * 1) named assertions as in 
 *
 *       (assert (! t :named AAA))
 *
 *    On a call to (get-unsat-core), we must construct a list of
 *    names.
 *
 * 2) positive/negative assumptions as in
 *
 *     (check-sat-assuming ( A (not B) (not C) ... ))
 *
 *    where A, B, C, are symbols. On a call to (get-unsat-assumptions),
 *    we must construct a list like (A (not C)).
 *
 * To do this, we store two pieces of information for every term t
 * used as an assumption: its name and its polarity. The polarity is
 * always positive for named assertions. For assumptions in
 * check-sat-assuming, the polarity allows us to distinguish between B
 * and (not B).
 */

#ifndef __ASSUMPTION_TABLE_H
#define __ASSUMPTION_TABLE_H

#include "terms/terms.h"
#include "utils/int_vectors.h"

#include <stdint.h>
#include <stdbool.h>

/*
 * Element in the table:
 */
typedef struct assumption_s {
  const char* name;
  term_t term;
  bool polarity;
} assumption_t;


/*
 * Table:
 * - data = array of assumptions
 * - index = array of indices sorted to help find the descriptor
 *   for an assumption t.
 * - the index is built lazily and we ignore duplicate assumptions
 *   if any.
 */
typedef struct assumption_table_s {
  assumption_t *data;
  int32_t *index;
  uint32_t size;
  uint32_t nelems;
  uint32_t index_size;
} assumption_table_t;

#define ASSUMPTION_TABLE_MAX_SIZE (UINT32_MAX/sizeof(assumption_t))
#define ASSUMPTION_TABLE_DEF_SIZE 128

/*
 * Initialize table:
 * - the size is 0 and nothing is allocated.
 */
extern void init_assumption_table(assumption_table_t *table);

/*
 * Delete: free memory
 */
extern void delete_assumption_table(assumption_table_t *table);

/*
 * Reset: empty the table and delete the index.
 */
extern void reset_assumption_table(assumption_table_t *table);

/*
 * Add an assumption to the table
 * - t = assumed term
 * - name = name to use for t
 * - polarity: true if the assumption is 'name'
 *             false if the assumption is '(not name)'
 */
extern void assumption_table_add(assumption_table_t *table, term_t t, const char* name, bool polarity);

/*
 * Build the internal index and filter duplicates
 */
extern void assumption_table_build_index(assumption_table_t *table);


/*
 * Collect all the assumed terms (duplicates removed if any)
 * - this requires the index to be constructed.
 * - the assumptions are returned in vector v
 */
extern void collect_assumptions(assumption_table_t *table, ivector_t *v);

/*
 * Get the descriptor for assumpion t:
 * - this requires the index to be constructed
 * - returns NULL if there's no such assumption
 */
extern assumption_t *assumption_table_get(const assumption_table_t *table, term_t t);


#endif /* __ASSUMPTION_TABLE_H */
