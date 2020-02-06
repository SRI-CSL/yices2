/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2020 SRI International.
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
 * Given a model M and a term t, we want to compute a set of
 * uninterpreted terms whose value in M is sufficient to derive the
 * value of t. For example, assume
 *    t = (if x>0 then x+1 else y)
 * then M will assign a value to x and to y, from which we can compute
 * the value of t. But in some cases, the value of t is independent of y.
 * For example, if M[x] = 1, then M[t] = 2 and the value of y doesn't matter.
 *
 * In general, we call support of t in M = a set of uninterpreted terms x_1, ... x_n,
 * such that M[t] is defined by M[x_1], ..., M[x_n] but does not depend on other
 * uninterpreted terms. More formally, { x_1, ..., x_n } is a support of t in M if
 * for any model M' we have (M'[x_1] = M[x_1] ... M'[x_n] = M[x_n] => M[t] = M[t]).
 * In the previous example support t in M = { x }.
 *
 * We generalize this to more than one term: support of t_1, ... , t_m in M =
 * a set of uninterpreted terms x_1, ...., x_n such that M[x_1], ..., M[x_n]
 * determine M[t_1], ..., M[t_m].
 *
 * This module computes a (small) support for t_1, ..., t_m given a model M.
 */

#ifndef __MODEL_SUPPORT_H
#define __MODEL_SUPPORT_H

#include <stdint.h>

#include "model/model_eval.h"
#include "utils/int_harray_store.h"
#include "utils/ptr_hash_map.h"
#include "utils/ptr_stack.h"


/*
 * Data structure for computing supports:
 * - eval = the model + support for computing the value of any term
 * - terms = term table
 * - map = maps terms to their support. The support is
 *         represented using arrays of integers (with hash-consing).
 * - store = store to build the arrays of integers
 * - stack = for recursive construction of support
 */
typedef struct support_constructor_s {
  evaluator_t eval;
  term_table_t *terms;
  ptr_hmap_t map;
  int_harray_store_t store;
  ptr_stack_t stack;
} support_constructor_t;



/*
 * Initialization: model = the relevant model
 */
extern void init_support_constructor(support_constructor_t *constructor, model_t *model);

/*
 * Deletion: free memory
 */
extern void delete_support_constructor(support_constructor_t *constructor);

/*
 * Get the support set of term t:
 * - t must be a valid term
 * - the support set is returned as a harray_t h
 *   h->nelems = number of terms in the set
 *   h->data[0 .. h->nelems-1] = the terms in increasing order
 *   (cf. utils/int_array_hsets)
 */
extern harray_t *get_term_support(support_constructor_t *constructor, term_t t);

/*
 * Support for an array of n terms: a[0 ... n-1]
 * - every a[i] must be a valid term
 * - the support set is returned as a harray as above
 */
extern harray_t *get_term_array_support(support_constructor_t *constructor, const term_t *a, uint32_t n);


#endif /* __MODEL_SUPPORT_H */

