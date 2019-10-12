/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include "terms/term_manager.h"
#include "terms/term_utils.h"

/**
   Common arithmetic operations on terms that are not provided in terms or term manager
**/

bool bv_arith_is_zero(term_table_t* terms, term_t t);
bool bv_arith_is_one(term_table_t* terms, term_t t);
bool bv_arith_is_minus_one(term_table_t* terms, term_t t);

// Zero term for given bitsize

term_t bv_arith_zero(term_manager_t* tm, uint32_t bitsize);

// Adding 2 bv terms

term_t bv_arith_add_terms(term_manager_t* tm, term_t a, term_t b);

// Subtracting 2 bv terms

term_t bv_arith_sub_terms(term_manager_t* tm, term_t a, term_t b);

// Negating a bv term

term_t bv_arith_negate_terms(term_manager_t* tm, term_t t);

// Adding +1 to a bv term

term_t bv_arith_add_one_term(term_manager_t* tm, term_t t);

// Adding +2^{w-1} to a bv term

term_t bv_arith_add_half(term_manager_t* tm, term_t t);

// Make a hi-bits extension of t, the extra bits being copies of boolean term b.
// w is the final bitwidth.
term_t bv_arith_upextension(term_manager_t* tm, term_t t, term_t b, uint32_t w);

// Make a low-bits extension of t, the extra bits being copies of boolean term b.
// w is the final bitwidth.
term_t bv_arith_downextension(term_manager_t* tm, term_t t, term_t b, uint32_t w)
  
/**
   Making atoms. Assumption for these functions:
   the atom to be built evaluates to true according to the trail.
**/

// This function returns (left == right) unless it is trivially true, in which case it returns NULL_TERM
// Assumes the term to be built evaluates to true
term_t bv_arith_eq(term_manager_t* tm, term_t left, term_t right);

// This function returns (left < right) unless it is trivially true, in which case it returns NULL_TERM
// Simplifies (left < 1), (left < -1), (0 < right) into equalities/disequalities.
// Assumes the term to be built evaluates to true
term_t bv_arith_lt(term_manager_t* tm, term_t left, term_t right);

// This function returns (left <= right) unless it is trivially true, in which case it returns NULL_TERM
// Simplifies (left < 1), (left < -1), (0 < right) into equalities/disequalities.
// Assumes the term to be built evaluates to true
term_t bv_arith_le(term_manager_t* tm, term_t left, term_t right);
