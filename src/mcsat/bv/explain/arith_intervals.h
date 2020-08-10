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

#include "terms/bv_constants.h"
#include "terms/term_utils.h"
#include "mcsat/bv/bv_explainer.h"
#include "arith_norm.h"

/**
   BV arithmetic intervals
**/

// Type for bvconstant intervals. An interval is a set of consecutive numbers modulo 2^n:
// [ 3; 1 [ is not empty but contains 3 and 0.
// Upper bound is always *excluded* from interval.
// Convention: the type cannot construct empty intervals: [ a ; a [ is the full set.

typedef struct {
  bvconstant_t lo;
  bvconstant_t hi;
  bvconstant_t length; // always hi - lo -1 (so technically it's not the length, but otherwise the full interval would have length 0, so now it has length -1, i.e. maximal)
  term_t lo_term;
  term_t hi_term; 
  term_t reason; // reason for being the full interval (NULL_TERM if not)
  ivector_t reasons; // other reasons for the interval to reflect its original constraint
  term_t var;  // The variable whose values are forbidden to be in this interval
} interval_t;

static inline
uint32_t interval_get_bitwidth(interval_t* i){
  return i->lo.bitsize;
}

static inline
bool interval_is_full(interval_t* i){
  return bvconstant_eq(&i->lo,&i->hi);
}

void interval_delete(interval_t* i);

// delete + free
void interval_destruct(interval_t* i);

void interval_print(FILE* out, term_table_t* terms, interval_t* i);

// Comparing bv_constants, with a baseline that serves as the zero
bool bvconst_le_base(const bvconstant_t* a, const bvconstant_t* b, const bvconstant_t* baseline);
bool bvconst_lt_base(const bvconstant_t* a, const bvconstant_t* b, const bvconstant_t* baseline);

// Determines if interval i contains value a. Happens if (a - i->lo) < (i->hi - i->lo)
bool interval_is_in(const bvconstant_t* a, const interval_t* i);

// Construct an atom that says "t \in interval"
term_t interval_is_in_term(arith_norm_t* norm, term_t t, const interval_t* i);

// Comparing two intervals: first look at bitwidth, then lower bound, then span.
// When lower bounds are compared, an optional baseline can be provided, in data,
// which must have the same bitwidth as x and y.
bool interval_cmp(void *data, void *x, void *y);

// inhabits output; lo and hi can be NULL, in which case they are computed from lo_term and hi_term
void interval_construct(bv_subexplainer_t* exp,
                        const bvconstant_t* lo,
                        const bvconstant_t* hi,
                        term_t lo_term,
                        term_t hi_term,
                        term_t var,
                        term_t reason,
                        interval_t* output);

// Returns a newly constructed interval on the heap
interval_t* interval_mk(bv_subexplainer_t* exp,
                        const bvconstant_t* lo,
                        const bvconstant_t* hi,
                        term_t lo_term,
                        term_t hi_term,
                        term_t var,
                        term_t reason);

// Returns a newly constructed full interval on the heap
interval_t* interval_full_mk(bv_subexplainer_t* exp, term_t reason, uint32_t width);


// If interval is an interval for var, then it becomes an interval for var - u
void interval_subtract(bv_subexplainer_t* exp, term_t u, interval_t* interval);

// If interval is an interval for var, then it becomes an interval for -var
void interval_negate(bv_subexplainer_t* exp, interval_t* interval);

// If interval is an interval for var,
// then it becomes an interval for concat(var,u) for any u extending the low bits of var
// w is the length of u. Function doesn't check the var,
// and sets it back to NULL_TERM if interval is modified.
void interval_downextend(bv_subexplainer_t* exp, uint32_t w, interval_t* interval);

// If interval is an interval for 0...0var, then it becomes an interval for var
// (of length w). Interval can become empty, in which case function outputs true
// (otherwise outputs false). Function doesn't check the var,
// and sets it back to NULL_TERM if interval is modified.
bool interval_uptrim(bv_subexplainer_t* exp, arith_norm_t* norm, uint32_t w, interval_t* interval);

// If interval is an interval for var0...0 (w is the number of extra zeros),
// then it becomes an interval for var
// (it doesn't check the var, and sets it back to NULL_TERM)
bool interval_downtrim(bv_subexplainer_t* exp, arith_norm_t* norm, uint32_t w, interval_t* interval);

