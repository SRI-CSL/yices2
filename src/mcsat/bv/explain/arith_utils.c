/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include "mcsat/tracing.h"
#include "mcsat/value.h"
#include "terms/bvarith_buffer_terms.h"
#include "terms/bvarith64_buffer_terms.h"
#include "terms/bv_constants.h"
#include "terms/bv64_constants.h"
#include "terms/term_manager.h"
#include "terms/term_utils.h"

#include "mcsat/bv/bv_utils.h"
#include "arith_utils.h"

/**
   Common arithmetic operations on terms that are not provided in terms or term manager
**/

bool bv_arith_is_zero(term_table_t* terms, term_t t) {
  if (!is_const_term(terms, t)) return false;
  if (term_bitsize(terms,t) <= 64) {
    bvconst64_term_t* desc = bvconst64_term_desc(terms,t);
    return desc->value == 0;
  } else {
    bvconst_term_t* desc = bvconst_term_desc(terms,t);
    uint32_t k = (desc->bitsize + 31) >> 5; // number of words = ceil(bitsize/32)
    return bvconst_is_zero(desc->data, k);
  }
}

bool bv_arith_is_one(term_table_t* terms, term_t t) {
  if (!is_const_term(terms, t)) return false;
  if (term_bitsize(terms,t) <= 64) {
    bvconst64_term_t* desc = bvconst64_term_desc(terms,t);
    return desc->value == 1;
  } else {
    bvconst_term_t* desc = bvconst_term_desc(terms,t);
    uint32_t k = (desc->bitsize + 31) >> 5; // number of words = ceil(bitsize/32)
    return bvconst_is_one(desc->data, k);
  }
}

bool bv_arith_is_minus_one(term_table_t* terms, term_t t) {
  if (!is_const_term(terms, t)) return false;
  if (term_bitsize(terms,t) <= 64) {
    bvconst64_term_t* desc = bvconst64_term_desc(terms,t);
    return bvconst64_is_minus_one(desc->value, desc->bitsize);
  } else {
    bvconst_term_t* desc = bvconst_term_desc(terms,t);
    return bvconst_is_minus_one(desc->data, desc->bitsize);
  }
}

// Zero term for given bitsize

term_t bv_arith_zero(term_manager_t* tm, uint32_t bitsize) {
  bvconstant_t zero;
  init_bvconstant(&zero);
  bvconstant_set_all_zero(&zero, bitsize);
  term_t result = mk_bv_constant(tm, &zero);
  delete_bvconstant(&zero);
  return result;
}

// Adding 2 bv terms

term_t bv_arith_add(term_manager_t* tm, term_t a, term_t b) {
  term_table_t* terms = tm->terms;
  if (term_bitsize(terms,a) <= 64) {
    bvarith64_buffer_t *buffer = term_manager_get_bvarith64_buffer(tm);
    bvarith64_buffer_set_term(buffer, terms, a);
    bvarith64_buffer_add_term(buffer, terms, b);
    return mk_bvarith64_term(tm, buffer);
  } else {
    bvarith_buffer_t *buffer = term_manager_get_bvarith_buffer(tm);
    bvarith_buffer_set_term(buffer, terms, a);
    bvarith_buffer_add_term(buffer, terms, b);
    return mk_bvarith_term(tm, buffer);
  }
}

// Subtracting 2 bv terms

term_t bv_arith_sub(term_manager_t* tm, term_t a, term_t b) {
  term_table_t* terms = tm->terms;
  if (term_bitsize(terms,a) <= 64) {
    bvarith64_buffer_t *buffer = term_manager_get_bvarith64_buffer(tm);
    bvarith64_buffer_set_term(buffer, terms, a);
    bvarith64_buffer_sub_term(buffer, terms, b);
    return mk_bvarith64_term(tm, buffer);
  } else {
    bvarith_buffer_t *buffer = term_manager_get_bvarith_buffer(tm);
    bvarith_buffer_set_term(buffer, terms, a);
    bvarith_buffer_sub_term(buffer, terms, b);
    return mk_bvarith_term(tm, buffer);
  }
}

// Negating a bv term

term_t bv_arith_negate(term_manager_t* tm, term_t t) {
  term_table_t* terms = tm->terms;
  if (term_bitsize(terms,t) <= 64) {
    bvarith64_buffer_t *buffer = term_manager_get_bvarith64_buffer(tm);
    bvarith64_buffer_set_term(buffer, terms, t);
    bvarith64_buffer_negate(buffer);
    return mk_bvarith64_term(tm, buffer);
  } else {
    bvarith_buffer_t *buffer = term_manager_get_bvarith_buffer(tm);
    bvarith_buffer_set_term(buffer, terms, t);
    bvarith_buffer_negate(buffer);
    return mk_bvarith_term(tm, buffer);
  }
}

// Adding +1 to a bv term

term_t bv_arith_add_one(term_manager_t* tm, term_t t) {
  term_table_t* terms  = tm->terms;
  if (term_bitsize(terms,t) <= 64) {
    bvarith64_buffer_t *buffer = term_manager_get_bvarith64_buffer(tm);
    bvarith64_buffer_set_term(buffer, terms, t);
    bvarith64_buffer_add_pp(buffer, empty_pp);
    return mk_bvarith64_term(tm, buffer);
  } else {
    bvarith_buffer_t *buffer = term_manager_get_bvarith_buffer(tm);
    bvarith_buffer_set_term(buffer, terms, t);
    bvarith_buffer_add_pp(buffer, empty_pp);
    return mk_bvarith_term(tm, buffer);
  }
}

// Adding +2^{w-1} to a bv term

term_t bv_arith_add_half(term_manager_t* tm, term_t t) {
  term_table_t* terms  = tm->terms;
  if (term_bitsize(terms,t) <= 64) {
    bvarith64_buffer_t *buffer = term_manager_get_bvarith64_buffer(tm);
    bvarith64_buffer_set_term(buffer, terms, t);
    uint64_t half = min_signed64(buffer->bitsize);
    bvarith64_buffer_add_const(buffer, half);
    return mk_bvarith64_term(tm, buffer);
  } else {
    bvarith_buffer_t *buffer = term_manager_get_bvarith_buffer(tm);
    bvarith_buffer_set_term(buffer, terms, t);
    bvconstant_t half;
    init_bvconstant(&half);
    bvconstant_set_bitsize(&half, buffer->bitsize);
    bvconst_set_min_signed(half.data, buffer->bitsize);
    bvarith_buffer_add_const(buffer, half.data);
    delete_bvconstant(&half);
    return mk_bvarith_term(tm, buffer);
  }
}

// Make a hi-bits extension of t, the extra bits being copies of boolean term b.
// w is the final bitwidth.

term_t bv_arith_upextension(term_manager_t* tm, term_t t, term_t b, uint32_t w) {
  uint32_t n = term_bitsize(tm->terms, t);
  if (n == w) return t;
  term_t sbits[w];
  for (uint32_t k=0; k<w;k++){
    sbits[k] = (k < n) ?
      mk_bitextract(tm, t, k) :
      b;
  }
  return mk_bvarray(tm, w, sbits);
}

// Make a low-bits extension of t, the extra bits being copies of boolean term b.
// w is the final bitwidth.

term_t bv_arith_downextension(term_manager_t* tm, term_t t, term_t b, uint32_t w) {
  uint32_t n = term_bitsize(tm->terms, t);
  assert(n <= w);
  if (n == w) return t;
  term_t sbits[w];
  uint32_t extra = w-n;
  for (uint32_t k=0; k<w;k++){
    sbits[k] = (k < extra) ?
      b:
      mk_bitextract(tm, t, k-extra);
  }
  return mk_bvarray(tm, w, sbits);
}

/**
   Making atoms. Assumption for these functions:
   the atom to be built evaluates to true according to the trail.
**/

// This function returns (left == right) unless it is trivially true, in which case it returns NULL_TERM
// Assumes the term to be built evaluates to true
term_t bv_arith_eq(term_manager_t* tm, term_t left, term_t right) {
  if (left == right) { return NULL_TERM; }
  term_table_t* terms = tm->terms;
  if (is_const_term(terms, left) && is_const_term(terms, right)) {
    return NULL_TERM;
  }
  return bveq_atom(terms, left, right);
}

// This function returns (left < right) unless it is trivially true, in which case it returns NULL_TERM
// Simplifies (left < 1), (left < -1), (0 < right) into equalities/disequalities.
// Assumes the term to be built evaluates to true
term_t bv_arith_lt(term_manager_t* tm, term_t left, term_t right) {
  term_table_t* terms   = tm->terms;
  uint32_t w            = term_bitsize(terms, left);
  assert(term_bitsize(terms, right) == w);
  assert (left != right);
  assert (!bv_arith_is_zero(terms, right));
  assert (!bv_arith_is_minus_one(terms, left));
  if (is_const_term(terms, left) && is_const_term(terms, right)) {
    return NULL_TERM;
  }
  // (left < 1) turns into (left == 0)
  if (bv_arith_is_one(terms, right)) {
    return bveq_atom(terms, left, bv_arith_zero(tm, w));
  }
  // (left < -1) turns into (left+1 != 0)
  if (bv_arith_is_minus_one(terms, right)) {
    return not_term(terms, bveq_atom(terms, bv_arith_sub(tm, left, right),bv_arith_zero(tm, w)));
  }
  // (0 < right) turns into (right != 0)
  if (bv_arith_is_zero(terms, left)) {
    return not_term(terms, bveq_atom(terms, right, bv_arith_zero(tm, w)));
  }
  return not_term(terms, bvge_atom(terms, left, right));
}

// This function returns (left <= right) unless it is trivially true, in which case it returns NULL_TERM
// Simplifies (left < 1), (left < -1), (0 < right) into equalities/disequalities.
// Assumes the term to be built evaluates to true
term_t bv_arith_le(term_manager_t* tm, term_t left, term_t right) {
  term_table_t* terms   = tm->terms;
  uint32_t w            = term_bitsize(terms, left);
  assert(term_bitsize(terms, right) == w);
  if (left == right) {
    return NULL_TERM;
  }
  if (is_const_term(terms, left) && is_const_term(terms, right)) {
    return NULL_TERM;
  }
  // (left <= -1) and (0 <= right) turns into NULL (trivially true)
  if (bv_arith_is_minus_one(terms, right) || bv_arith_is_zero(terms, left)) {
    return NULL_TERM;
  }
  // (left <= 0) and (-1 <= right) turns into (left == right)
  if (bv_arith_is_zero(terms, right)) {
    return bveq_atom(terms, left, right);
  }
  // (1 <= right) turns into (right != 0)
  if (bv_arith_is_one(terms, left)) {
    return not_term(terms, bveq_atom(terms, right, bv_arith_zero(tm, w)));
  }
  return bvge_atom(terms, right, left);
}

