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
 * SHARED/UNSHARED TERMS
 */

/*
 * Given a set of assertions { t1, ..., t_n }, this module computes
 * the subterms of t1 ... t_n that occur only once.  For each such
 * subterm, we keep the id of the term's unique parent. All the other
 * subterms are marked as shared.
 *
 * We use an internalization table to deal with term substitutions
 * and to skip terms that are already internalized (in a solver).
 */

#ifndef __SHARED_TERMS_H
#define __SHARED_TERMS_H

#include <stdbool.h>

#include "context/internalization_table.h"
#include "terms/terms.h"
#include "utils/int_hash_map.h"
#include "utils/int_queues.h"


/*
 * Data structure:
 * - hmap = hash table: this stores parent data based on term index
 *   hmap[i] = unique parent of i, if exactly one occurrence of i
 *             has been so far
 *   hmap[i] = bool_const if i has more than one occurrence
 * - intern = pointer to the relevant internalization table
 * - terms = pointer to the relevant term table
 * - queue for exploring terms
 *
 * We use bool_const as a marker for terms seen more than once.
 * The hmap is based on term indices so it can't distinguish between
 * visiting t and visiting (not t).
 */
typedef struct sharing_map_s {
  int_hmap_t hmap;
  term_table_t *terms;
  intern_tbl_t *intern;
  int_queue_t queue;
} sharing_map_t;


/*
 * Initialization:
 * - intern must be the context's internalization table
 * - the term table is extracted from intern
 */
extern void init_sharing_map(sharing_map_t *map, intern_tbl_t *intern);


/*
 * Delete the whole thing
 */
extern void delete_sharing_map(sharing_map_t *map);


/*
 * Reset: empty the hmap
 */
extern void reset_sharing_map(sharing_map_t *map);


/*
 * Process term t:
 * - all subterms of t are visited recursively and added the map
 */
extern void sharing_map_add_term(sharing_map_t *map, term_t t);


/*
 * Process all terms in array a
 * - n = size of the array
 */
extern void sharing_map_add_terms(sharing_map_t *map, term_t *a, uint32_t n);


/*
 * Check whether t occurs more that once among all the terms visited so far 
 * - this returns false if t is not in the map or if t has been seen only once
 */
extern bool term_is_shared(sharing_map_t *map, term_t t);


/*
 * Check whether t occurs once
 * - this returns false if t is not in the map or if t has been visited more than once
 */
extern bool term_is_not_shared(sharing_map_t *map, term_t t);


/*
 * Get the unique parent of t
 * - if t has been seen only once, this returns t's parent as stored in map->hmap
 * - if t has not been seen at all, this returns NULL_TERM
 * - if t has more than once occurrences, this returns true_term (as a marker).
 */
extern term_t unique_parent(sharing_map_t *map, term_t t);


#endif /* __UNIQUE_PARENTS_H */
