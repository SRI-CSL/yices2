/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

/*
 * Skolemization for the EF solver.
 */

#ifndef __EF_SKOLEMIZE_H
#define __EF_SKOLEMIZE_H

#include "exists_forall/ef_analyze.h"
#include "terms/term_utils.h"

#include "yices_types.h"

/*
 * skolemize object:
 */
typedef struct ef_skolemize_s {
  ef_analyzer_t *analyzer;
  ef_prob_t *prob;
  bool flatten_ite;
  bool flatten_iff;
  bool ematching;

  term_manager_t *mgr;
  term_table_t *terms;
  ivector_t uvars;
  ivector_t aux;
  bool has_uvars;

  // for error reporting: some terms are not supported
  // if we see them, we set failed to true and store the term kind in unsupported
  bool failed;
  term_kind_t unsupported;

  ptr_hmap_t cache;
} ef_skolemize_t;


/*
 * Initialize the skolemize object
 */
extern void init_ef_skolemize(ef_skolemize_t *sk, ef_analyzer_t *analyzer, ef_prob_t *prob,
			      bool f_ite, bool f_iff, bool ematching);


/*
 * Delete the skolemize object
 */
extern void delete_ef_skolemize(ef_skolemize_t *sk);


/*
 * Skolemize an assertion t and flatten conjuncts:
 * - add the result to vector v
 * - this first computes the skolemization sk of term t
 * - if the term sk is a conjunction (i.e. of the form (NOT (OR ...)) then
 *   sk is flattened and the conjuncts are added to vector v
 * - if sk is not a conjunction, it's added as is to v.
 */
extern void ef_skolemize(ef_skolemize_t *sk, term_t t, ivector_t *v);


/*
 * Skolemize patterns
 */
extern void ef_skolemize_patterns(ef_skolemize_t *sk);



#endif /* __EF_SKOLEMIZE_H */
