/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2026 SRI International.
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

#ifndef __PROJECTION_PREPROCESS_H
#define __PROJECTION_PREPROCESS_H

#include <stdint.h>

#include "model/models.h"
#include "model/projection.h"
#include "terms/term_manager.h"
#include "utils/int_vectors.h"


/*
 * Rewrite RDIV-containing arithmetic literals in a model-true cube into
 * RDIV-free literals plus model-sign guards.
 *
 * - a[0 ... n-1] is expected to be a flat cube of literals
 * - all emitted literals are appended to v; v is not reset
 * - literals without RDIV are appended unchanged
 * - if an RDIV-containing literal cannot be rewritten, return an error
 *
 * If the return code is PROJ_ERROR_UNSUPPORTED_ARITH_TERM, *extra_error is set
 * to ARITH_RDIV.
 */
extern proj_flag_t preprocess_rdiv_literals(model_t *mdl, term_manager_t *mngr,
                                            uint32_t n, const term_t *a,
                                            ivector_t *v, int32_t *extra_error);

#endif /* __PROJECTION_PREPROCESS_H */
