/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Analyze a UF formula F to learn global equalities implied by F
 * The result is stored as an epartition.
 */

#ifndef __EQ_LEARNER_H
#define __EQ_LEARNER_H

#include "terms/terms.h"
#include "context/eq_abstraction.h"
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
