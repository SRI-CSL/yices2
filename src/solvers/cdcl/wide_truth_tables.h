/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2019 SRI International.
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
 * EXPERIMENTAL: TRUTH TABLE WITH MORE THAN THREE VARIABLES
 */

#ifndef __WIDE_TRUTH_TABLES_H
#define __WIDE_TRUTH_TABLES_H

#include <stdbool.h>
#include <stdint.h>

#include "solvers/cdcl/truth_tables.h"

/*
 * Data structure to store and manipulate truth tables
 * - size = maximal number of variables
 * - nvars = actual number of variables
 * - var = array of variables
 * - val = array of bits.
 *
 * If size = n then var is an array of n integers,
 * b is an array of 2^n bits (each represented as uint8_t).
 * So the data structure can store a truth table of no more
 * than n variables.
 *
 * The encoding is similar to the one used in (small) truth_tables.h.
 * Given a function f of k variables:
 * - var[0 .. k-1] = variable ids in increasing order (all distinct)
 * - the value of f at some point (b_0, ..., b_{k-1}) is stored in
 *       val[i]
 *   where i is b_0 + 2 b_1 + ... + 2^(k-1) b_{k-1}
 *   and val[i] is either 0 or 1.
 */
typedef struct wide_ttbl_s {
  uint32_t size;
  uint32_t nvars;
  bvar_t *var;
  uint8_t *val;
} wide_ttbl_t;


#define MAX_WIDE_TTBL_SIZE 16


/*
 * Initialize w for size = n.
 * - this allocates arrays var and val
 * - n must be no more than MAX_WIDE_TTBL_SIZE
 * - w is initialized to the constant false function:
 *   nvars = 0, val[0] = 0.
 */
extern void init_wide_ttbl(wide_ttbl_t *w, uint32_t n);

/*
 * Delete w: free memory
 */
extern void delete_wide_ttbl(wide_ttbl_t *w);

/*
 * Reset w to the constant false function
 */
extern void reset_wide_ttbl(wide_ttbl_t *w);

/*
 * Import a regular ttbl into w.
 * - w->size must be at least ttbl->nvars.
 * - ttbl must be normalized
 */
extern void wide_ttbl_import(wide_ttbl_t *w, const ttbl_t *ttbl);

/*
 * Composition:
 * - w1 stores a the truth table for function f(x0,..., x_k)
 * - ttbl stores the truth table for function g(y0, ...).
 * - i is an index between 0 and k
 *
 * This function computes the truth table for 
 *   f(x_0,..., x_i-1, g(y0, y1, y2), x_{i+1}, ... x_k).
 * and stores it into w. This replaces x_i by g(y0, ..) in f.
 *
 * The structure w must not be the same as w1.
 *
 * The function returns false if the composition can't be stored
 * in w (because it requires more variables than w->size).
 * It returns true otherwise.
 */
extern bool wide_ttbl_compose(wide_ttbl_t *w, const wide_ttbl_t *w1, const ttbl_t *ttbl, uint32_t i);


/*
 * Composition variant
 * - w1 stores the  truth table for a function f(x0 .... x_k)
 * - ttbl stores the truth table for a functioon g(y0...)
 * - x is a variable
 *
 * If x occurs in x0 ... x_k, then this replaces x by g(y0...) in f and store the
 * result in w. Otherwise,  this copies w1 into w.
 *
 * The function returns false if the composition can't be stored
 * in w (because it requires more variables than w->size).
 * It returns true otherwise.
 */
extern bool wide_ttbl_var_compose(wide_ttbl_t *w, const wide_ttbl_t *w1, const ttbl_t *ttbl, bvar_t x);


/*
 * Normalize w1 and store the result in w
 * - remove the redundant variables of w1
 * - return true if w1 is large enough to contain the result, false otherwise
 */
extern bool wide_ttbl_normalize(wide_ttbl_t *w, const wide_ttbl_t *w1);



#endif /* __WIDE_TRUTH_TABLES_H */
