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
 * Processing of terms t as part EF-solving
 */

/*
 * All processing is based on the convention that uninterpreted terms
 * represent existential variables and any variable is universal.
 *
 * Example assertion:
 *
 *   (and (<= 0 x) (<= x 10)  (forall y: (=> (<= y 10) (< (* y x) 5)))
 *
 * In the internal representation:
 * - x is an uninterpreted term
 * - y is a variable
 * These are syntactically different objects
 *
 * After flattening and stripping away the universal quantifiers, we
 * get three formulas:
 *   (<= 0 x)
 *   (<= x 10)
 *   (=> (<= y 10) (< (* y x) 5))
 *
 * We can still extract universal and existential variables from these:
 * - any uninterpreted term is considered an existential variable (e.g., x)
 * - any (free) variable is considered a universal variable (e.g., y).
 */

#ifndef __EF_ANALYZE_H
#define __EF_ANALYZE_H

#include <stdint.h>
#include <stdbool.h>

#include "solvers/quant/ef_problem.h"
#include "terms/term_manager.h"
#include "terms/term_substitution.h"
#include "utils/int_hash_sets.h"
#include "utils/int_queues.h"
#include "utils/int_vectors.h"
#include "utils/string_buffers.h"

/*
 * EF clause = a disjunction of formulas: assumptions and guarantees
 * - formulas that contain only universal variables (no existential variables)
 *   are stored in the assumptions vector
 * - other formulas are stored in the guarantees vector
 * - the existential variables are stored in evars
 * - the universal variables are stored in uvars
 *
 * Special case:
 * - a formula that contains no universal variables is stored
 *   in the guarantees vector.
 */
typedef struct ef_clause_s {
  ivector_t evars; // existential variables
  ivector_t uvars; // universal variables
  ivector_t pvars; // pattern variables
  ivector_t assumptions;
  ivector_t guarantees;
} ef_clause_t;


/*
 * EF analyzer: to process/decompose an EF-problem
 * - terms = term table where all terms are defined
 * - manager = relevant term manager
 * - subst = to convert universal variables to uninterpreted terms
 *
 * - queue = queue to explore terms/subterms
 * - cache = set of already visited terms
 * - flat = vector of assertions (result of flattening)
 * - disjuncts = vector of formula (or-flattening of assertions)
 * - foralls = universally quantified deferred to the second flattening phase
 * - existentials = the set of existential variables (variables)
 * - evars = reusable vector to collect existential variables (no longer just uninterpreted terms)
 * - uvars = reusable vector to collect universal variables (variables)
 * - aux = auxiliary general-purpose vectors
 * - sbuffer = string buffer to store the names of skolem constants
 */
typedef struct ef_analyzer_s {
  term_table_t *terms;
  term_manager_t *manager;
  term_subst_t subst;
  int_queue_t queue;
  int_hset_t cache;
  ivector_t flat;
  ivector_t disjuncts;
  ivector_t foralls;
  int_hmap_t existentials;
  ivector_t evars;
  ivector_t uvars;
  ivector_t aux;
  string_buffer_t sbuffer;
  uint32_t num_skolem;
} ef_analyzer_t;


/*
 * Error codes when formulas can't be converted to the expected
 * EXISTS/FORALL format
 */
typedef enum ef_code {
  EF_NO_ERROR = 0,       // everything fine
  EF_UNINTERPRETED_FUN,  // formula contains uninterpreted function or predicates
  EF_NESTED_QUANTIFIER,  // nested quantifiers that can't be flattened (e.g., exists inside forall)
  EF_HIGH_ORDER_UVAR,    // universal variables have non-atomic types
  EF_HIGH_ORDER_EVAR,    // existential variables not atomic
  EF_ERROR,              // other errors
} ef_code_t;

#define NUM_EF_CODES (EF_ERROR+1)


/*
 * ANALYZER
 */

/*
 * Initialize the data structure
 */
extern void init_ef_analyzer(ef_analyzer_t *ef, term_manager_t *mngr);


/*
 * Reset: empty cache and queue and internal vectors
 */
extern void reset_ef_analyzer(ef_analyzer_t *ef);


/*
 * Free all memory used
 */
extern void delete_ef_analyzer(ef_analyzer_t *ef);


/*
 * Full processing:
 * - build problem descriptor from a set of assertions
 *   n = number of assertions
 *   a[0 ... n-1] = the assertions
 *   f_ite: flag to enable flattening of if-then-else
 *   f_iff: flag to enable flattening of iff
 * - prob = empty problem descriptor (must be initialized and have
 *   the same term table as ef).
 * - result code: same as ef_decompose
 * - if code is either EF_NO_ERROR or EF_UNINTERPRETED_FUN then prob is
 *   filled in with the problem
 * - otherwise, prob is partially filled in.
 */
extern ef_code_t ef_analyze(ef_analyzer_t *ef, ef_prob_t *prob, uint32_t n, term_t *a,
    bool f_ite, bool f_iff, bool ematching);


#endif /* __EF_ANALYZE_H */
