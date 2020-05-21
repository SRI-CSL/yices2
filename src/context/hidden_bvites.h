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
 * TRY TO CONVERT PAIRS OF IMPLICATIONS INTO EQUALITIES
 *
 * This code searches for pairs of assertions of the form:
 *   (c => t = a)
 *   (not(c) => t = b)
 * where a and b are bit-vector constants and c is a Boolean variable. 
 * When it finds them, it rewrites the pair to
 *    t = (ite c a b).
 *
 * Variant:
 *   (c => t = u)
 *   (not (c) => (bvsub t u) = a)
 * can be rewritten to
 *   (bvsub t u) = (ite c zero a)
 */


#ifndef __HIDDEN_BVITES_H
#define __HIDDEN_BVITES_H

#include <stdint.h>

#include "context/context_types.h"
#include "terms/term_utils.h"
#include "utils/int_hash_sets.h"
#include "utils/vector_hash_map.h"

/*
 * Conditional definition:
 * - store four terms: t, c, a, b such that
 *   t is an assertion
 *   t is equivalent to c => a = b
 */
typedef struct half_ite_s {
  term_t c;
  term_t a;
  term_t b;
  term_t t;
} half_ite_t;

/*
 * Table to store these descriptors:
 * - context = the context
 * - terms = the relevant term table
 * - index: maps a Boolean variable x to a vector
 *   of indices [i0, i1, ...]
 *   where data[i0].cond = either x or not x
 *         data[i1].cond = either x or not x
 *
 * - subsumed: assertions that become redundant after
 *   we add equalities
 */
typedef struct half_ite_table_s {
  context_t *context;
  term_table_t *terms;
  half_ite_t *data;
  uint32_t nelems;
  uint32_t size;
  vector_hmap_t index;
  int_hset_t subsumed;
} half_ite_table_t;


#define DEF_HALF_ITE_TABLE_SIZE 1024
#define MAX_HALF_ITE_TABLE_SIZE (UINT32_MAX/sizeof(half_ite_t))

/*
 * OPERATIONS
 */

/*
 * Initialize the table
 */
extern void init_half_ite_table(half_ite_table_t *table, context_t *context);

/*
 * Delete it
 */
extern void delete_half_ite_table(half_ite_table_t *table);

/*
 * Process a conditional equality:
 * - t is equivalent to (cond => left = right)
 * - the triple (cond, left, right) is stored in condeq
 */
extern void add_half_ite(half_ite_table_t *table, conditional_eq_t *condeq, term_t t);

/*
 * Search for complementary entries in the table.
 * - for each pair of complementary entries, assert an auxiliary equality in the context
 * - return the total number of auxiliary equalities
 */
extern uint32_t assert_hidden_ites(half_ite_table_t *table);

/*
 * Check whether term t is in the subsumed set
 */
extern bool subsumed_by_hidden_ite(half_ite_table_t *table, term_t t);


#endif /* __CONDITIONAL_DEFINITIONS_H */
