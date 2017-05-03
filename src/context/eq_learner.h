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
 * Analyze a UF formula F to learn global equalities implied by F
 * The result is stored as an epartition.
 */

#ifndef __EQ_LEARNER_H
#define __EQ_LEARNER_H

#include "context/eq_abstraction.h"
#include "terms/terms.h"
#include "utils/ptr_hash_map.h"


/*
 * Learner object:
 * - terms = term table
 * - manager = partition manager
 * - cache = hash_map
 */
typedef struct eq_learner_s {
  term_table_t *terms;
  epartition_manager_t manager;
  ptr_hmap_t cache;
} eq_learner_t;


/*
 * Initialization: tbl = the term table
 */
extern void init_eq_learner(eq_learner_t *learner, term_table_t *tbl);


/*
 * Delete the learner
 */
extern void delete_eq_learner(eq_learner_t *learner);


/*
 * Process formula f and return its abstraction
 * - return NULL if f is not an OR formula
 * - otherwise return an epartition object p
 *   for every pair of terms (t, u), if t and u are in the same class in p
 *   then f implies (t == u)
 */
extern epartition_t *eq_learner_process(eq_learner_t *learner, term_t f);



#endif /* __EQ_LEARNER_H */
