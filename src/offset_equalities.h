/*
 * Support for handling arithmetic equalities of the form x = y + k
 * where x and y are variables and k is a constant.
 */

/*
 * When we connect the Simplex solver and the Egraph, the equality
 * constraints propagated from the Egraph get turned into rows of the
 * form z = x - y in the tableau, with the constraint 0 <= z <= 0
 * asserted on z.  We also get equalities of the same form but with
 * constraints a <= z <= a where a is a non-zero rational.
 *
 * We want to propagate equalities in the other direction (from
 * Simplex to the egraph). A relatively simple technique is to
 * focus on offset equalities and propagate their consequences.
 *
 * Example: if egraph term t1 is mapped to p1 = x1 + 2 x2 + 1 in
 * Simplex and term t2 is mapped to p2 = x3 + 2 x2 + 2 in Simplex,
 * then we can propgate t1 == t2 to the Egraph when the offset
 * equality (x1 == x3 + 1) is asserted.
 *
 * To support this, we keep the polynomials p1 and p2 normalized
 * modulo a set of offset equalities. We use data structures 
 * similar to the Egraph. 
 * 
 * We keep variables stored into offset classes:
 * the class contains a root variable r, all other variables
 * in the class are equal to r + some offset. 
 *
 * When a new offset equality is asserted, we merge two offset
 * classes. 
 *
 * To propagate equalities to the Egraph, we store polynomials
 * in a hash table, that uses equality modulo the offset classes.
 * This is cheap to implement, since we just apply a variable
 * substitutions of the form x := r + k (replace x by its root + offset pair).
 */

#ifndef __OFFSET_EQUALITIES_H
#define __OFFSET_EQUALITIES_H

#include <stdint.h>

#include "rationals.h"
#include "polynomials.h"



#endif /* __OFFSET_EQUALITIES_H */
