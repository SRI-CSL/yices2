/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include "mcsat/tracing.h"
#include "terms/bvarith_buffer_terms.h"
#include "terms/bvarith64_buffer_terms.h"
#include "terms/bv_constants.h"
#include "terms/bv64_constants.h"

#include "mcsat/bv/bv_utils.h"
#include "arith_utils.h"

/**
   Common arithmetic operations on terms that are not provided in terms or term manager
**/

bool arith_is_zero(term_table_t* terms, term_t t) {
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

bool arith_is_one(term_table_t* terms, term_t t) {
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

bool arith_is_minus_one(term_table_t* terms, term_t t) {
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

term_t arith_zero(term_manager_t* tm, uint32_t bitsize) {
  bvconstant_t zero;
  init_bvconstant(&zero);
  bvconstant_set_all_zero(&zero, bitsize);
  term_t result = mk_bv_constant(tm, &zero);
  delete_bvconstant(&zero);
  return result;
}

// Adding 2 bv terms

term_t arith_add(term_manager_t* tm, term_t a, term_t b) {
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

term_t arith_sub(term_manager_t* tm, term_t a, term_t b) {
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

term_t arith_negate(term_manager_t* tm, term_t t) {
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

term_t arith_add_one(term_manager_t* tm, term_t t) {
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

term_t arith_add_half(term_manager_t* tm, term_t t) {
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

term_t arith_upextension(term_manager_t* tm, term_t t, term_t b, uint32_t w) {
  uint32_t n = term_bitsize(tm->terms, t);
  if (n == w) return t;
  term_t sbits[w];
  for (uint32_t k=0; k<w;k++){
    sbits[k] = (k < n) ?
      bv_bitterm(tm->terms, mk_bitextract(tm, t, k)) :
      b;
  }
  return mk_bvarray(tm, w, sbits);
}

// Make a low-bits extension of t, the extra bits being copies of boolean term b.
// w is the final bitwidth.

term_t arith_downextension(term_manager_t* tm, term_t t, term_t b, uint32_t w) {
  uint32_t n = term_bitsize(tm->terms, t);
  assert(n <= w);
  if (n == w) return t;
  term_t sbits[w];
  uint32_t extra = w-n;
  for (uint32_t k=0; k<w;k++){
    sbits[k] = (k < extra) ?
      b:
      bv_bitterm(tm->terms, mk_bitextract(tm, t, k-extra));
  }
  return mk_bvarray(tm, w, sbits);
}

/**
   Making atoms.
**/

// This function returns (t == 0), simplifying the result
term_t arith_eq0(term_manager_t* tm, term_t t) {
  term_table_t* terms = tm->terms;

  if (arith_is_zero(terms, t))
    return true_term;

  uint32_t w = term_bitsize(terms, t);
  term_t left  = t;
  term_t right = arith_zero(tm, w);
  if (disequal_bitvector_terms(terms, left, right))
    return false_term;

  switch (term_kind(terms, t)) {
  case BV_POLY: {
    bvpoly_t* t_poly = bvpoly_term_desc(terms, t);
    // If we extract more than 64 bits, we use regular coefficients for the bv_poly to produce
    // we construct that bv_poly from a bvarith_buffer_t called buffer:
    bvarith_buffer_t* buffer = term_manager_get_bvarith_buffer(tm);
    bvarith_buffer_prepare(buffer, w); // Setting the desired width
    for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
      term_t monom_var = t_poly->mono[i].var;
      if (bvconst_tst_bit(t_poly->mono[i].coeff, w-1)) { // coefficient is positive
        if (monom_var == const_idx) // constant coefficient gets aded to the buffer bv_poly
          bvarith_buffer_add_const(buffer, t_poly->mono[i].coeff);
        else // Otherwise we add the w-bit monomial to the bv_poly
          bvarith_buffer_add_const_times_term(buffer, terms, t_poly->mono[i].coeff, monom_var);
      }
    }
    left = mk_bvarith_term(tm, buffer); // We turn the bv_poly into an actual term
    bvarith_buffer_prepare(buffer, w); // Setting the desired width
    for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
      term_t monom_var = t_poly->mono[i].var;
      if (!bvconst_tst_bit(t_poly->mono[i].coeff, w-1)) { // coefficient is negative
        bvconstant_t coeff;
        init_bvconstant(&coeff);
        bvconstant_copy(&coeff, w, t_poly->mono[i].coeff);
        bvconstant_negate(&coeff);
        if (monom_var == const_idx) // constant coefficient gets aded to the buffer bv_poly
          bvarith_buffer_add_const(buffer, coeff.data);
        else // Otherwise we add the w-bit monomial to the bv_poly
          bvarith_buffer_add_const_times_term(buffer, terms, coeff.data, monom_var);
        delete_bvconstant(&coeff);
      }
    }
    right = mk_bvarith_term(tm, buffer); // We turn the bv_poly into an actual term
    break;
  }
  case BV64_POLY: {
    bvpoly64_t* t_poly = bvpoly64_term_desc(terms, t);
    bvarith64_buffer_t* buffer = term_manager_get_bvarith64_buffer(tm);
    bvarith64_buffer_prepare(buffer, w); // Setting the desired width
    // Now going into each monomial
    for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
      term_t monom_var = t_poly->mono[i].var;
      if (tst_bit64(t_poly->mono[i].coeff, w-1)) { // coefficient is positive
        if (monom_var == const_idx) // constant coefficient gets added to the buffer bv_poly
          bvarith64_buffer_add_const(buffer, t_poly->mono[i].coeff);
        else // Otherwise we add the w-bit monomial to the bv_poly
          bvarith64_buffer_add_const_times_term(buffer, terms, t_poly->mono[i].coeff, monom_var);
      }
    }
    left = mk_bvarith64_term(tm, buffer); // We turn the bv_poly into an actual term
    bvarith64_buffer_prepare(buffer, w); // Setting the desired width
    for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
      term_t monom_var = t_poly->mono[i].var;
      if (!tst_bit64(t_poly->mono[i].coeff, w-1)) { // coefficient is negative
        if (monom_var == const_idx)
          bvarith64_buffer_add_const(buffer, - t_poly->mono[i].coeff); // constant coefficient gets added to the buffer bv_poly
        else
          bvarith64_buffer_add_const_times_term(buffer, terms, - t_poly->mono[i].coeff, monom_var);
      }
    }
    right = mk_bvarith64_term(tm, buffer); // We turn the bv_poly into an actual term
    break;
  }
  default: {
  }
  }
  return bveq_atom(terms, left, right);
}

// This function returns (left < right), simplifying the result
term_t arith_lt(term_manager_t* tm, term_t left, term_t right) {
  term_table_t* terms   = tm->terms;
  assert(term_bitsize(terms, left) == term_bitsize(terms, right));
  if (left == right
      || arith_is_zero(terms, right)
      || arith_is_minus_one(terms, left))
    return false_term;
  // (left < 1) turns into (left == 0)
  if (arith_is_one(terms, right)) {
    return arith_eq0(tm, left);
  }
  // (left < -1) turns into (left+1 != 0)
  if (arith_is_minus_one(terms, right)) {
    return not_term(terms, arith_eq0(tm, arith_sub(tm, left, right)));
  }
  // (0 < right) turns into (right != 0)
  if (arith_is_zero(terms, left)) {
    return not_term(terms, arith_eq0(tm, right));
  }
  return mk_bvlt(tm, left, right);
}

// This function returns (left <= right), simplifying the result
term_t arith_le(term_manager_t* tm, term_t left, term_t right) {
  term_table_t* terms   = tm->terms;
  assert(term_bitsize(terms, left) == term_bitsize(terms, right));
  if (left == right) {
    return true_term;
  }
  // (left <= -1) and (0 <= right) turns into true
  if (arith_is_minus_one(terms, right) || arith_is_zero(terms, left)) {
    return true_term;
  }
  // (left <= 0) and (-1 <= right) turns into (left == right)
  if (arith_is_zero(terms, right)) {
    return arith_eq0(tm, left);
  }
  // (1 <= right) turns into (right != 0)
  if (arith_is_one(terms, left)) {
    return not_term(terms, arith_eq0(tm, right));
  }
  return mk_bvle(tm, left, right);
}

