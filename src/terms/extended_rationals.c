/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Operations on extended rationals
 * Each extended rational is a pair (c, d)
 * where c and d are rationals.
 * This represents the number c + d.delta
 * where delta is infinitesimal.
 */

#include <assert.h>

#include "terms/extended_rationals.h"

/*
 * Comparison: returns a negative number if r1 < r2
 *             returns 0 if r1 = r2
 *             returns a positive number if r1 > r2
 */
int xq_cmp(xrational_t *r1, xrational_t *r2) {
  int c;

  c = q_cmp(&r1->main, &r2->main);
  if (c == 0) {
    return q_cmp(&r1->delta, &r2->delta);
  } else {
    return c;
  }
}


/*
 * Comparison with a rational q
 * returns a negative number if r < q
 * returns 0 if r = q
 * returns a positive number if r > q
 */
int xq_cmp_q(xrational_t *r, rational_t *q) {
  int c;

  c = q_cmp(&r->main, q);
  if (c == 0) {
    return q_sgn(&r->delta);
  } else {
    return c;
  }
}



/*
 * Floor of r:
 * r = a + b \delta
 * floor(r) = floor(a) if a is not integer
 *          = a - 1 if a is an integer and b < 0
 *          = a otherwise
 */
void xq_floor(xrational_t *r) {
  if (q_is_integer(&r->main)) {
    if (q_is_neg(&r->delta)) {
      q_sub_one(&r->main);
    }
  } else {
    q_floor(&r->main);
  }
  q_clear(&r->delta);
  assert(xq_is_integer(r));
}



/*
 * Ceiling of r
 * r = a + b \delta
 * ceil(r) = ceil(a) if a is not an integer
 *         = a + 1   if a is an integer and b > 0
 *         = a       if a is an integer and b <= 0
 */
void xq_ceil(xrational_t *r) {
  if (q_is_integer(&r->main)) {
    if (q_is_pos(&r->delta)) {
      q_add_one(&r->main);
    }
  } else {
    q_ceil(&r->main);
  }
  q_clear(&r->delta);
  assert(xq_is_integer(r));
}



/*
 * Print xr
 */
void xq_print(FILE *f, xrational_t *r) {
  int s;

  s = q_sgn(&r->delta);
  if (s == 0) {
    q_print(f, &r->main);
  } else {
    if (q_is_nonzero(&r->main)) {
      q_print(f, &r->main);
      if (s > 0) {
        fputs(" + ", f);
      } else {
        fputs(" - ", f);
      }
    } else if (s < 0) {
      fputs("- ", f);
    }
    if (q_is_one(&r->delta) || q_is_minus_one(&r->delta)) {
      fputs("delta", f);
    } else {
      q_print_abs(f, &r->delta);
      fputs(" * delta", f);
    }
  }
}
