/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * INTERNALIZATION CODES
 *
 * The context maps terms to egraph terms or theory variables.
 * All are encoded in 32integers (as used in internalization_table).
 * The encoding is defined here.
 */

#ifndef __INTERNALIZATION_CODES_H
#define __INTERNALIZATION_CODES_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "solvers/cdcl/smt_core.h"
#include "solvers/egraph/egraph_base_types.h"


/*
 * A term t can be mapped to a theory variable, a literal, or an
 * egraph term-occurrence.  We encode the mapping as a 32bit code
 * stored in internalization_table.
 *
 * If the code of is negative, t is not mapped to anything yet,
 * otherwise the code is of the form [0 b30 .... b2 b1 b0].
 *
 * If b0 == 0, the code denotes the term occurrence [0 0 b30 ... b1].
 * The term occurrence is the concatenation of an eterm id [0 0 0 b30 ... b2]
 * and the polarity bit b1. For a non-boolean term, b1 is always 0.
 *
 * If b0 == 1,  the code is a theory variable or a literal, depending on
 * the type of t.
 * - type = BOOL:
 *   the code denotes literal [0 0 b30 ... b2 b1]
 *   (i.e., boolean variable [0 0 0 b30 ...b2] + polarity bit b1).
 * - type = INT or REAL:
 *   t is mapped to the variable [0 0 b30 ... b1] in the arithmetic solver
 * - type = (BITVECTOR k)
 *   t is mapped to the variable [0 0 b30 ... b1] in the bitvector solver
 *
 */

/*
 * Code for term occurrence x or egraph term t
 */
static inline int32_t occ2code(occ_t x) {
  assert(x >= 0);
  return x << 1;
}

static inline int32_t eterm2code(eterm_t t) {
  assert(t >= 0);
  return t << 2; // same as occ2code(pos_occ(t))
}


/*
 * Code for true or false egraph occurrences
 */
static inline int32_t bool2code(bool val) {
  return occ2code(bool2occ(val));
}


/*
 * Code for literal or theory variables
 */
static inline int32_t literal2code(literal_t l) {
  assert(l >= 0);
  return (l<<1) | 1;
}

// boolean variable
static inline int32_t bvar2code(bvar_t v) {
  return literal2code(pos_lit(v));
}

// arithmetic or bitvector variable
static inline int32_t thvar2code(thvar_t x) {
  assert(x >= 0);
  return (x<<1) | 1;
}



/*
 * Checks on code c and conversion to literal, theory variable, or
 * term occurrence.
 */
static inline bool code_is_valid(int32_t c) {
  return c >= 0;
}

static inline bool code_is_eterm(int32_t c) {
  assert(c >= 0);
  return (c & 1) == 0;
}

static inline bool code_is_var(int32_t c) {
  assert(c >= 0);
  return (c & 1) == 1;
}

static inline occ_t code2occ(int32_t c) {
  assert(code_is_eterm(c));
  return c>>1;
}

static inline eterm_t code2eterm(int32_t c) {
  assert(code_is_eterm(c));
  return c>>2;
}

static inline literal_t code2literal(int32_t c) {
  assert(code_is_var(c));
  return c>>1;
}

static inline bvar_t code2bvar(int32_t c) {
  assert(code_is_var(c));
  return c>>2;
}

static inline thvar_t code2thvar(int32_t c) {
  assert(code_is_var(c));
  return c>>1;
}

#endif /* __INTERNALIZATION_CODES_H */
