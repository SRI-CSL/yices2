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

#pragma once

#include "terms/term_manager.h"
#include "terms/term_utils.h"

/**
   Common arithmetic operations on terms that are not provided in terms or term manager
**/

bool arith_is_zero(term_table_t* terms, term_t t);
bool arith_is_one(term_table_t* terms, term_t t);
bool arith_is_minus_one(term_table_t* terms, term_t t);

// Zero term for given bitsize

term_t arith_zero(term_manager_t* tm, uint32_t bitsize);

// Adding 2 bv terms

term_t arith_add(term_manager_t* tm, term_t a, term_t b);

// Subtracting 2 bv terms

term_t arith_sub(term_manager_t* tm, term_t a, term_t b);

// Negating a bv term

term_t arith_negate(term_manager_t* tm, term_t t);

// Adding +1 to a bv term

term_t arith_add_one(term_manager_t* tm, term_t t);

// Adding +2^{w-1} to a bv term

term_t arith_add_half(term_manager_t* tm, term_t t);

// Make a hi-bits extension of t, the extra bits being copies of boolean term b.
// w is the final bitwidth.
term_t arith_upextension(term_manager_t* tm, term_t t, term_t b, uint32_t w);

// Make a low-bits extension of t, the extra bits being copies of boolean term b.
// w is the final bitwidth.
term_t arith_downextension(term_manager_t* tm, term_t t, term_t b, uint32_t w);
  
/**
   Making atoms.
**/

// This function returns (left == right), simplifying the result
term_t arith_eq0(term_manager_t* tm, term_t t);

// This function returns (left < right), simplifying the result
term_t arith_lt(term_manager_t* tm, term_t left, term_t right);

// This function returns (left <= right), simplifying the result
term_t arith_le(term_manager_t* tm, term_t left, term_t right);

/**
   Normalising sums so that coefficients are odd.
**/

// Outputs true if
// - not a bv_poly or bv64 poly, or;
// - if it is a bv_poly or bv64_poly, and none of the (non-constant) coefficients is even
bool arith_is_sum_norm(term_table_t* terms, term_t t);

// This normalizes the term by making sure that property above is satisfied (at the top-level, no recursion)
// if one of the (non-constant) coefficients is even it can be divided by 2 and the monomial's variable could be multiplied by 2 by a shift.
// This simplification is done iteratively until the property above is true.
term_t arith_sum_norm(term_manager_t* tm, term_t u);

/**
   Apparently useful somewhere.
**/

static inline
bool arith_is_no_triv(term_t t){
  assert(t != false_term);
  return (t != true_term);
}
