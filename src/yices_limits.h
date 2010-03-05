/*
 * HARDCODED LIMITS
 */

/*
 * There are limits on the number of terms, term arity, etc. because
 * of the internal data representation: 
 * - some bits used for tagging 
 * - maximal size of internal tables 
 * - bounds to prevent numerical overflow
 *
 * The bounds listed below should be safe and far beyond what we can
 * actually deal with.
 */

#ifndef __YICES_LIMITS_H
#define __YICES_LIMITS_H

#include <stdint.h>

/*
 * Maximal number of types or terms
 */
#define YICES_MAX_TYPES (INT32_MAX/8)
#define YICES_MAX_TERMS (INT32_MAX/8)

/*
 * Maximal arity for terms and types
 */
#define YICES_MAX_ARITY ((INT32_MAX/16)-1)

/*
 * Maximal n in (FORALL/EXISTS (x_1 .... x_n) P)
 */
#define YICES_MAX_VARS ((INT32_MAX/16)-1)

/*
 * Maximal bitvector size
 */
#define YICES_MAX_BVSIZE ((INT32_MAX/16)-1)


#endif
