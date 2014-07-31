/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Extended numbers = pairs of rationals (c, d)
 * representing a number of the form c + d.delta
 * where delta is infinitesimal.
 */

#ifndef __EXTENDED_RATIONALS_H
#define __EXTENDED_RATIONALS_H

#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>

#include "terms/rationals.h"


/*
 * extended rational: pairs of rationals (c, d)
 */
typedef struct {
  rational_t main;   // stores c
  rational_t delta;  // stores d
} xrational_t;






/*********************************************
 *  COMPARISONS/TESTS ON EXTENDED RATIONALS  *
 ********************************************/

/*
 * Comparison: returns a negative number if r1 < r2
 *             returns 0 if r1 = r2
 *             returns a positive number if r1 > r2
 */
extern int xq_cmp(xrational_t *r1, xrational_t *r2);



/*
 * Variants of xq_cmp:
 * - xq_le(r1, r2) is nonzero iff r1 <= r2
 * - xq_lt(r1, r2) is nonzero iff r1 < r2
 * - xq_gt(r1, r2) is nonzero iff r1 > r2
 * - xq_ge(r1, r2) is nonzero iff r1 >= r2
 * - xq_eq(r1, r2) is nonzero iff r1 = r2
 * - xq_neq(r1, r2) is nonzero iff r1 != r2
 */
static inline bool xq_le(xrational_t *r1, xrational_t *r2) {
  return xq_cmp(r1, r2) <= 0;
}

static inline bool xq_lt(xrational_t *r1, xrational_t *r2) {
  return xq_cmp(r1, r2) < 0;
}

static inline bool xq_ge(xrational_t *r1, xrational_t *r2) {
  return xq_cmp(r1, r2) >= 0;
}

static inline bool xq_gt(xrational_t *r1, xrational_t *r2) {
  return xq_cmp(r1, r2) > 0;
}

static inline bool xq_eq(xrational_t *r1, xrational_t *r2) {
  return xq_cmp(r1, r2) == 0;
}

static inline bool xq_neq(xrational_t *r1, xrational_t *r2) {
  return xq_cmp(r1, r2) != 0;
}


/*
 * Compare r with a rational q (i.e., with q + 0.delta)
 * returns a negative number if r < q
 * returns 0 if r = q
 * returns a positive number if r > q
 */
extern int xq_cmp_q(xrational_t *r, rational_t *q);


/*
 * Variants of xq_cmp_q:
 *  xq_le_q(r, q) tests whether r <= q
 *  xq_lt_q(r, q) tests whether r < q
 *  xq_gt_q(r, q) tests whether r > q
 *  xq_ge_q(r, q) tests whether r >= q
 *  xq_eq_q(r, q) tests whether r == q
 *  xq_neg_q(r, q) tests whether r != q
 */
static inline bool xq_le_q(xrational_t *r, rational_t *q) {
  return xq_cmp_q(r, q) <= 0;
}

static inline bool xq_lt_q(xrational_t *r, rational_t *q) {
  return xq_cmp_q(r, q) < 0;
}

static inline bool xq_ge_q(xrational_t *r, rational_t *q) {
  return xq_cmp_q(r, q) >= 0;
}

static inline bool xq_gt_q(xrational_t *r, rational_t *q) {
  return xq_cmp_q(r, q) > 0;
}

static inline bool xq_eq_q(xrational_t *r, rational_t *q) {
  return xq_cmp_q(r, q) == 0;
}

static inline bool xq_neq_q(xrational_t *r, rational_t *q) {
  return xq_cmp_q(r, q) != 0;
}

/*
 * Check whether r is 0, +1, or -1
 */
static inline bool xq_is_zero(xrational_t *r) {
  return q_is_zero(&r->main) && q_is_zero(&r->delta);
}

static inline bool xq_is_one(xrational_t *r) {
  return q_is_one(&r->main) && q_is_zero(&r->delta);
}

static inline bool xq_is_minus_one(xrational_t *r) {
  return q_is_minus_one(&r->main) && q_is_zero(&r->delta);
}


/*
 * Check whether r is a rational or an integer
 */
static inline bool xq_is_rational(xrational_t *r) {
  return q_is_zero(&r->delta);
}

static inline bool xq_is_integer(xrational_t *r) {
  return q_is_zero(&r->delta) && q_is_integer(&r->main);
}



/*
 * Get the sign of r
 * - xq_sgn(r) = 0 if r = 0
 * - xq_sgn(r) = -1 if r < 0
 * - xq_sgn(r) = +1 if r > 0
 */
static inline int xq_sgn(xrational_t *r) {
  if (q_is_zero(&r->main)) {
    return q_sgn(&r->delta);
  } else {
    return q_sgn(&r->main);
  }
}




/******************************************
 *  ASSIGNMENT AND ARITHMETIC OPERATIONS  *
 *****************************************/

/*
 * Set r to 0 + 0.delta
 */
static inline void xq_init(xrational_t *r) {
  q_init(&r->main);
  q_init(&r->delta);
}


/*
 * Clear r: free the gmp numbers attached to rx if any
 * then set r to 0 + 0.delta
 */
static inline void xq_clear(xrational_t *r) {
  q_clear(&r->main);
  q_clear(&r->delta);
}




/*
 * Assignment operations:
 * - r must be initialized first to avoid memory leaks
 */

/*
 * Assign r1 to r
 */
static inline void xq_set(xrational_t *r, xrational_t *r1) {
  q_set(&r->main, &r1->main);
  q_set(&r->delta, &r1->delta);
}

/*
 * Assgin -r1 to r
 */
static inline void xq_set_neg(xrational_t *r, xrational_t *r1) {
  q_set_neg(&r->main, &r1->main);
  q_set_neg(&r->delta, &r1->delta);
}

/*
 * Assign a + 0.delta to r
 */
static inline void xq_set_q(xrational_t *r, rational_t *a) {
  q_set(&r->main, a);
  q_clear(&r->delta);
}

/*
 * Assign a + delta to r
 */
static inline void xq_set_q_plus_delta(xrational_t *r, rational_t *a) {
  q_set(&r->main, a);
  q_set_one(&r->delta);
}

/*
 * Assign a - delta to r
 */
static inline void xq_set_q_minus_delta(xrational_t *r, rational_t *a) {
  q_set(&r->main, a);
  q_set_minus_one(&r->delta);
}


/*
 * Assign +/-1 + 0.delta to r
 */
static inline void xq_set_one(xrational_t *r) {
  q_set_one(&r->main);
  q_clear(&r->delta);
}

static inline void xq_set_minus_one(xrational_t *r) {
  q_set_minus_one(&r->main);
  q_clear(&r->delta);
}




/*
 * OPERATIONS
 */

/*
 * Add r2 to r1
 */
static inline void xq_add(xrational_t *r1, xrational_t *r2) {
  q_add(&r1->main, &r2->main);
  q_add(&r1->delta, &r2->delta);
}

/*
 * Add a rational q2 to r1
 */
static inline void xq_add_q(xrational_t *r1, rational_t *q2) {
  q_add(&r1->main, q2);
}

/*
 * Subtract r2 from r1
 */
static inline void xq_sub(xrational_t *r1, xrational_t *r2) {
  q_sub(&r1->main, &r2->main);
  q_sub(&r1->delta, &r2->delta);
}

/*
 * Subtract a rational q2 from r1
 */
static inline void xq_sub_q(xrational_t *r1, rational_t *q2) {
  q_sub(&r1->main, q2);
}


/*
 * Negate r
 */
static inline void xq_neg(xrational_t *r) {
  q_neg(&r->main);
  q_neg(&r->delta);
}

/*
 * Multiply r by q
 */
static inline void xq_mul(xrational_t *r, rational_t *q) {
  q_mul(&r->main, q);
  q_mul(&r->delta, q);
}


/*
 * Divide r by q
 */
static inline void xq_div(xrational_t *r, rational_t *q) {
  q_div(&r->main, q);
  q_div(&r->delta, q);
}



/*
 * Add q * r2 to r1
 */
static inline void xq_addmul(xrational_t *r1, xrational_t *r2, rational_t *q) {
  q_addmul(&r1->main, &r2->main, q);
  q_addmul(&r1->delta, &r2->delta, q);
}

/*
 * Subtract q * r2 from r1
 */
static inline void xq_submul(xrational_t *r1, xrational_t *r2, rational_t *q) {
  q_submul(&r1->main, &r2->main, q);
  q_submul(&r1->delta, &r2->delta, q);
}


/*
 * Add q1 * q2 to r
 */
static inline void xq_addmul_q(xrational_t *r, rational_t *q1, rational_t *q2) {
  q_addmul(&r->main, q1, q2);
}


/*
 * Subtract q1 * q2 from r
 */
static inline void xq_submul_q(xrational_t *r, rational_t *q1, rational_t *q2) {
  q_submul(&r->main, q1, q2);
}


/*
 * Add +/-1 or +/-delta to r
 */
static inline void xq_add_one(xrational_t *r) {
  q_add_one(&r->main);
}

static inline void xq_sub_one(xrational_t *r) {
  q_sub_one(&r->main);
}

static inline void xq_add_delta(xrational_t *r) {
  q_add_one(&r->delta);
}

static inline void xq_sub_delta(xrational_t *r) {
  q_sub_one(&r->delta);
}




/*
 * Round r to floor or ceiling
 */
extern void xq_ceil(xrational_t *r);
extern void xq_floor(xrational_t *r);



/*
 * Print r on stream f
 */
extern void xq_print(FILE *f, xrational_t *r);


#endif /* __EXTENDED_RATIONALS_H */
