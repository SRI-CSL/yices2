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
 * HARDCODED LIMITS
 */

/*
 * There are limits on the number of terms, term arity, etc., because
 * of the internal data representation.  The bounds listed below
 * should be safe and far beyond what we can actually deal with.
 */

#ifndef __YICES_LIMITS_H
#define __YICES_LIMITS_H

#include <stdint.h>

/*
 * Maximal number of types or terms.
 */
#define YICES_MAX_TYPES (UINT32_MAX/8)
#define YICES_MAX_TERMS (UINT32_MAX/8)

/*
 * Maximal arity for terms and types
 */
#define YICES_MAX_ARITY (UINT32_MAX/16)


/*
 * Maximal degree of polynomials
 */
#define YICES_MAX_DEGREE (UINT32_MAX/2)


/*
 * Maximal n in (FORALL/EXISTS (x_1 .... x_n) P)
 */
#define YICES_MAX_VARS (UINT32_MAX/16)


/*
 * Maximal bitvector size
 */
#define YICES_MAX_BVSIZE (UINT32_MAX/16)

#endif
