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
 * SETS OF BIT-VECTOR VALUES
 *
 * This is used in model construction to find fresh-values of
 * type (bitvector n)
 * - a set is initialized for a fixed bit size n.
 * - a set is stored as a bitvector of 2^n elements, so n must be small.
 * - elements are 32bit unsigned integers truncated to n bits.
 */

#ifndef __SMALL_BVSETS_H
#define __SMALL_BVSETS_H

#include <stdint.h>
#include <stdbool.h>

#include "utils/bitvectors.h"



/*
 * For small bit width n: we store the set of used values
 * as a bitvector of 2^n bits.
 * - set = bitvector
 * - size = 2^n
 * - nelems = number of used values = number of bit sets in the vector
 * - ptr = index between 0 and 2^n: all elements x in 0 <= x < ptr are
 *   present in set.
 */
typedef struct small_bvset_s {
  byte_t *set;
  uint32_t size;
  uint32_t nelems;
  uint32_t ptr;
} small_bvset_t;


/*
 * Initialize a small set for bitsize n
 * - n must be positive and no more than 31
 */
extern void init_small_bvset(small_bvset_t *s, uint32_t n);

/*
 * Delete s: free memory
 */
extern void delete_small_bvset(small_bvset_t *s);

/*
 * Reset s: empty it
 */
extern void reset_small_bvset(small_bvset_t *s);

/*
 * Add element x to s
 * - x must be between 0 and 2^n-1 where n = bitsize of s
 */
extern void small_bvset_add(small_bvset_t *s, uint32_t x);

/*
 * Search for a fresh value x not in s and return it
 * - s must not be full
 * - x is added to s
 */
extern uint32_t small_bvset_get_fresh(small_bvset_t *s);

/*
 * Check whether the set if full
 * - if it is, fresh values cannot be created
 */
static inline bool small_bvset_full(small_bvset_t *s) {
  return s->size == s->nelems;
}

/*
 * Check whether x is present in s
 */
static inline bool small_bvset_member(small_bvset_t *s, uint32_t x) {
  assert(x < s->size);
  return tst_bit(s->set, x);
}


#endif /* __SMVALL_BVSETS_H */
