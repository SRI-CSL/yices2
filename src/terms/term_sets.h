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
 * SUPPORT TO BUILD SETS OF TERMS
 */

/*
 * A term set is implemented using the int_hset data structure.
 * This module provides a wrapper to construct and fill a int_hset
 * with terms.
 */
#ifndef __TERM_SETS_H
#define __TERM_SETS_H

#include <stdint.h>

#include "terms/terms.h"
#include "utils/int_hash_sets.h"


/*
 * Build the set that contains terms a[0 ... n-1]
 * - a may contain several times the same term.
 * - duplicates are ignored
 */
extern int_hset_t *new_term_set(uint32_t n, const term_t *a);


/*
 * Delete a set constructed by the previous function
 */
extern void free_term_set(int_hset_t *s);


/*
 * Initialize set:
 * - initial content = all terms in a[0 ... n-1]
 */
extern void init_term_set(int_hset_t *set, uint32_t n, const term_t *a);


/*
 * Delete a set of terms:
 */
static inline void delete_term_set(int_hset_t *set) {
  delete_int_hset(set);
}


#endif /* __TERM_SETS_H */
