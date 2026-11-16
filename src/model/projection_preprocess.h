/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

#ifndef __PROJECTION_PREPROCESS_H
#define __PROJECTION_PREPROCESS_H

#include <stdint.h>

#include "model/model_eval.h"
#include "model/models.h"
#include "model/projection.h"
#include "terms/term_manager.h"
#include "utils/int_vectors.h"


/*
 * RDIV preprocessing context.
 *
 * This is scoped to one model/generalization call. It caches the rewrite of
 * signed literals because WIDE projection may see the same atom in several
 * enumerated cubes.
 */
typedef struct rdiv_preprocess_cache_s rdiv_preprocess_cache_t;
typedef struct arith_construct_preprocess_cache_s arith_construct_preprocess_cache_t;

/*
 * Exact ABS normalization.
 *
 * This rewrites ARITH_ABS terms into equivalent arithmetic ITE terms:
 *   abs(t)  -->  ite(t >= 0, t, -t)
 *
 * The pass is intended to run before Boolean abstraction/cube enumeration so
 * that the existing ITE handling can choose model-relevant branches. Terms
 * that cannot be rebuilt are kept unchanged; this pass must not make
 * model generalization fail before cube enumeration has a chance to skip a
 * later unsupported cube.
 */
extern proj_flag_t preprocess_abs_terms(term_manager_t *mngr,
                                        uint32_t n, const term_t *a,
                                        ivector_t *v, int32_t *extra_error);

/*
 * Per-cube arithmetic-construct preprocessing context.
 *
 * This is scoped to one model/generalization call. It caches signed literal
 * rewrites because WIDE projection may see the same atom in several cubes.
 * Fresh auxiliary integer variables introduced by the rewrite are also scoped
 * to this cache and are removed from the model when the cache is deleted.
 */
extern arith_construct_preprocess_cache_t *new_arith_construct_preprocess_cache(model_t *mdl, term_manager_t *mngr);

extern void delete_arith_construct_preprocess_cache(arith_construct_preprocess_cache_t *cache);

/*
 * Best-effort elimination of ARITH_FLOOR, ARITH_CEIL, ARITH_IDIV, and
 * ARITH_MOD from model-true cube literals.
 *
 * - a[0 ... n-1] is expected to be a flat cube of literals after get_implicant
 * - all emitted literals are appended to v; v is not reset
 * - fresh integer auxiliaries that must be eliminated by projection are
 *   appended to fresh_elims; fresh_elims is not reset
 * - literals without these constructs are appended unchanged
 * - if a construct cannot be eliminated safely (for example div/mod by a term
 *   whose model value is zero), the original literal is appended unchanged
 *
 * eval is borrowed for this call only. The cache keeps no evaluator ownership:
 * model_eval does not support multiple concurrent evaluators for one model.
 *
 * The pass is intentionally non-failing. Any remaining unsupported constructs
 * are left to project_literals, so a WIDE cube can be skipped without
 * collapsing the whole preprocessing phase.
 */
extern proj_flag_t preprocess_arith_construct_literals(arith_construct_preprocess_cache_t *cache,
                                                       evaluator_t *eval,
                                                       uint32_t n, const term_t *a,
                                                       ivector_t *v, ivector_t *fresh_elims,
                                                       int32_t *extra_error);

extern rdiv_preprocess_cache_t *new_rdiv_preprocess_cache(model_t *mdl, term_manager_t *mngr);

extern void delete_rdiv_preprocess_cache(rdiv_preprocess_cache_t *cache);

/*
 * Rewrite RDIV-containing arithmetic literals in a model-true cube into
 * RDIV-free literals plus model-sign guards.
 *
 * - a[0 ... n-1] is expected to be a flat cube of literals
 * - all emitted literals are appended to v; v is not reset
 * - literals without RDIV are appended unchanged
 * - if an RDIV-containing literal cannot be rewritten, return an error
 * - eval is borrowed for this call only; the cache keeps no evaluator ownership
 *
 * If the return code is PROJ_ERROR_UNSUPPORTED_ARITH_TERM, *extra_error is set
 * to ARITH_RDIV.
 */
extern proj_flag_t preprocess_rdiv_literals(rdiv_preprocess_cache_t *cache,
                                            evaluator_t *eval,
                                            uint32_t n, const term_t *a,
                                            ivector_t *v, int32_t *extra_error);

#endif /* __PROJECTION_PREPROCESS_H */
