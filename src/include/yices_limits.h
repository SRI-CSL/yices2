/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
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
 * Maximal number of types or terms
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
