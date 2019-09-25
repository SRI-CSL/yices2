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
#include "utils/int_hash_map.h"
#include "utils/ptr_array_sort2.h"
#include "utils/ptr_heap.h"
#include "utils/ptr_queues.h"

#include "mcsat/bv/bv_utils.h"
#include "arith.h"

/**
   Subexplainer type
**/

// In what follows, there's a notion of normalisation via which
// t<w> propagates the lower bit extraction down to variables if t is not evaluable

typedef struct arith_s {

  /** Interfact of the subexplainer */
  bv_subexplainer_t super;

  bv_csttrail_t csttrail; // Where we keep some cached values

  // Cache of term normalisations (key is non-evaluable term, value is normalised form);
  int_hmap_t norm_cache;

  // Cache of normalised terms such that conflict monomial is 1*v;
  // key is the term, value is v
  int_hmap_t coeff1_cache;
  // Cache of normalised terms such that conflict monomial is -1*v;
  // key is the term, value is v
  int_hmap_t coeffm1_cache;
} arith_t;

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

term_t bv_arith_add_terms(term_manager_t* tm, term_t a, term_t b) {
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

term_t bv_arith_sub_terms(term_manager_t* tm, term_t a, term_t b) {
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

term_t bv_arith_negate_terms(term_manager_t* tm, term_t t) {
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

term_t bv_arith_add_one_term(term_manager_t* tm, term_t t) {
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

// Make a 0-extension of t. w is the final bitwidth.

term_t bv_arith_extension(term_manager_t* tm, term_t t, uint32_t w) {
  uint32_t n = term_bitsize(tm->terms, t);
  term_t sbits[w];
  for (uint32_t k=0; k<w;k++){
    sbits[k] = (k < n) ?
      mk_bitextract(tm, t, k) :
      bool2term(false);
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
    return not_term(terms, bveq_atom(terms, bv_arith_sub_terms(tm, left, right),bv_arith_zero(tm, w)));
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

/**
   Extracting bits and coefficients from terms.
**/

// Check if term t<w> (not necessarily normalised)
// is of the form A, or B, or neither.
//
// Form A: concat(head,base<bits>),
// with bits+bitwidth(head)=w, head are evaluable bits, and base is term not evaluable.
// in that case the function
// - returns base,
// - places bits in argument bits
// - places concat(head,0...0) in argument head
// Particular cases:
// a) if bits is w, it means head is empty; returns t, (0...0) is placed in arg. head
// b) if bits is zero, it means t<w> is evaluable; returns t, t<w> is placed in arg. head
//
// Form B:  sign-ext(base<bits>) (bits cannot be 0)
// in that case the function
// - returns base,
// - places bits in argument bits
// - argument head is NULL_TERM
// Note: base[bits-1] is the sign bit that's repeated
//
// If neither of the above 2 cases, must be another bv_array, returns NULL_TERM (contents of head and bits unspecified)

term_t lower_bit_extract_base(arith_t* exp, term_t t, uint32_t w, term_t* head, uint32_t* bits){

  plugin_context_t* ctx = exp->super.ctx;
  term_manager_t* tm    = ctx->tm;
  term_table_t* terms   = ctx->terms;
  
  if (term_kind(terms, t) == BV_ARRAY) {  // Concatenated boolean terms
    // To be in the fragment, t<w> has to be of the form concat(head,base<bits>) (*)
    composite_term_t* concat_desc = bvarray_term_desc(terms, t);
    term_t base = NULL_TERM;
    term_t sbits[w];

    uint32_t i = 0;
    assert(0 < w);
    term_t signbit = NULL_TERM;
    term_t false_bit = bool2term(false);
    
    while (i < w) {
      term_t t_i = concat_desc->arg[i]; // The Boolean term that constitutes that bit
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "bit %d is ",i);
        ctx_trace_term(ctx, t_i);
      }
      if (t_i == signbit) break; // 2 consecutive bits are the same term
      if (term_kind(terms, t_i) != BIT_TERM) break; // not a bit term
      if (is_neg_term(t_i)) break;                  // bit term but it's negated
      // OK, this is a good bit term. It defines a base, if we don't already have it
      if (base == NULL_TERM) base = bit_term_arg(terms, t_i);
      uint32_t selected_bit = bit_term_index(terms, t_i); // Get selected bit in it
      if (base != bit_term_arg(terms, t_i)) break;        // Would falsify (*)
      if (selected_bit != i) break;                       // Would falsify (*)
      sbits[i] = false_bit;
      signbit = t_i;
      i++;
    }

    if (bits != NULL) bits[0] = i; // how many times we reached the end of the loop's body
    // Whether it's a sign-extension can be tested by:
    bool is_signext = (i < w) && (signbit == concat_desc->arg[i]);
    
    while (i < w) {
      term_t t_i = concat_desc->arg[i]; // The Boolean term that constitutes that bit

      if (!is_signext) {
        // Unless it's a sign-extension, the rest of this BV_ARRAY must be evaluable
        bool ignore_this_bool;
        if (!bv_evaluator_is_evaluable(&exp->csttrail, t_i, &ignore_this_bool)) {
          return NULL_TERM;
        }
        if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
          FILE* out = ctx_trace_out(ctx);
          fprintf(out, "bit %d is evaluable: ",i);
          ctx_trace_term(ctx, t_i);
        }
        sbits[i] = t_i;
      } else { // The rest of this BV_ARRAY must be repeating the sign bit (sign-extension)
        if (signbit != t_i) return NULL_TERM;
      }
      i++; 
    }

    if (head != NULL) head[0] = is_signext ? NULL_TERM : mk_bvarray(tm, w, sbits);
    if (base==NULL_TERM) return t;
    return base;
  }

  if (bits != NULL) bits[0] = w;
  if (head != NULL) head[0] = bv_arith_zero(tm, w);
  return t;
}

// Lower bits extraction: extracting the w lowest bits of t, normalising on the way
term_t extract(arith_t* exp, term_t t, uint32_t w){

  // standard abbreviations
  term_t conflict_var   = exp->csttrail.conflict_var_term;
  plugin_context_t* ctx = exp->super.ctx;
  term_manager_t* tm    = ctx->tm;
  term_table_t* terms   = ctx->terms;

  uint32_t original_bitsize = term_bitsize(terms, t);
  assert(w <= original_bitsize);
  
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Extracting %d lower bits of ",w);
    term_print_to_file(out, terms, t);
    fprintf(out, "\n");
  }

  bool ignore_this_bool;
  if (t == conflict_var
      || bv_evaluator_is_evaluable(&exp->csttrail, t, &ignore_this_bool)) {
    return term_extract(tm, t, 0, w);
  }

  // If we are not trying to reduce the bitwidth,
  // we can look at whether the value is cached
  if (w == original_bitsize) {
    int_hmap_pair_t* t_norm = int_hmap_find(&exp->norm_cache,t);
    if (t_norm != NULL) return t_norm->val;
  }

  term_t result; // This is what we return at the end, unless we exit prematurely

  switch (term_kind(terms, t)) {
  case BV_ARRAY: { // Concatenated boolean terms
    // we start extracting the bits of interest at the top-level
    term_t superficial = term_extract(tm, t, 0, w);
    // except now we want to normalise recursively
    term_t head;
    uint32_t variable_bits;
    term_t base = lower_bit_extract_base(exp, superficial, w, &head, &variable_bits);
    if (base == NULL_TERM) {// Not a good term
      return NULL_TERM;
    }
    if (variable_bits == 0) { // the w lowest bits of t were evaluable
      assert(w < original_bitsize); // otherwise t would be evaluable (already handled)
      return extract(exp, superficial, w); // we don't cache because w < original_bitsize
    }
    assert(variable_bits <= w);
    term_t base_norm = extract(exp, base, variable_bits); // Extracting from the base
    if (base_norm == NULL_TERM) return NULL_TERM; // recursion got outside fragment
    if (variable_bits == w) { // No head
      result = base_norm; // This is our final answer
    } else { // There's a head, we need to recompose the term
      term_t recompose[w];
      uint32_t i = 0;
      for (; i < variable_bits; i++) {
        recompose[i] = mk_bitextract(tm, base_norm, i);
      }
      for (; i < w; i++) {
        recompose[i] = (head == NULL_TERM) ?
          recompose[variable_bits-1] : // It's a sign-extend, we copy the sign bit
          mk_bitextract(tm, head, i);  // It's not
      }
      result = mk_bvarray(tm, w, recompose); // This is our final answer
    }
    break;
  }
  case BV_POLY: {
    // t is a bv-poly expression.
    // We use the fact that lower bits extraction distributes over arithmetic operations
    bvpoly_t* t_poly = bvpoly_term_desc(ctx->terms, t);
    term_t monomials[t_poly->nterms]; // where we recursively extract the monomials
    for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
      if (t_poly->mono[i].var != const_idx) {
        monomials[i] = extract(exp, t_poly->mono[i].var, w);
        if (monomials[i] == NULL_TERM) return NULL_TERM;
      }
    }
    if (w<65) {
      // If we extract fewer than 65 bits, we use uint64_t coefficients for the bv_poly to produce
      // we construct that bv_poly from a bvarith64_buffer_t called buffer:
      bvarith64_buffer_t* buffer = term_manager_get_bvarith64_buffer(tm);
      bvarith64_buffer_prepare(buffer, w); // Setting the desired width
      // Now going into each monomial
      for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
        uint64_t coeff = // projecting the monomial coefficient onto w bits
          (original_bitsize < 33) ? // requires an annoying case analysis, for some reason
          ( (uint64_t) bvconst_get32(t_poly->mono[i].coeff)) :
          bvconst_get64(t_poly->mono[i].coeff) ;
        if (t_poly->mono[i].var == const_idx) {
          bvarith64_buffer_add_const(buffer, coeff); // constant coefficient gets added to the buffer bv_poly
        } else {
          bvarith64_buffer_add_const_times_term(buffer, terms, coeff, monomials[i]); // Otherwise we add the w-bit monomial to the bv_poly
        }
      }
      result = mk_bvarith64_term(tm, buffer); // We turn the bv_poly into an actual term, and return it
    } else {
      // If we extract more than 64 bits, we use regular coefficients for the bv_poly to produce
      // we construct that bv_poly from a bvarith_buffer_t called buffer:
      bvarith_buffer_t* buffer = term_manager_get_bvarith_buffer(tm);
      bvarith_buffer_prepare(buffer, w); // Setting the desired width
      bvconstant_t coeff; // temp variable for the next loop
      init_bvconstant(&coeff);
      for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
        bvconstant_extract(&coeff, t_poly->mono[i].coeff, 0, w); // projecting the monomial coefficient onto w bits
        if (t_poly->mono[i].var == const_idx) {
          bvarith_buffer_add_const(buffer, coeff.data);// constant coefficient gets aded to the buffer bv_poly
        } else {
          bvarith_buffer_add_const_times_term(buffer, terms, coeff.data, monomials[i]); // Otherwise we add the w-bit monomial to the bv_poly
        }
      }
      delete_bvconstant(&coeff); //cleaning up
      result = mk_bvarith_term(tm, buffer); // We turn the bv_poly into an actual term, and return it
    }
    break;
  }
  case BV64_POLY: { // Same game, but now t is a bv64_poly, so w <= 64 and we also construct a bv64_poly
    bvpoly64_t* t_poly = bvpoly64_term_desc(ctx->terms, t);
    term_t monomials[t_poly->nterms]; // where we recursively extract the monomials
    for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
      if (t_poly->mono[i].var != const_idx) {
        monomials[i] = extract(exp, t_poly->mono[i].var, w);
        if (monomials[i] == NULL_TERM) return NULL_TERM;
      }
    }
    bvarith64_buffer_t* buffer = term_manager_get_bvarith64_buffer(tm);
    bvarith64_buffer_prepare(buffer, w);
    for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
      if (t_poly->mono[i].var == const_idx) {
        bvarith64_buffer_add_const(buffer, t_poly->mono[i].coeff);
      } else {
        bvarith64_buffer_add_const_times_term(buffer, terms, t_poly->mono[i].coeff, monomials[i]);
      }
    }
    result = mk_bvarith64_term(tm, buffer);
    break;
  }
  default: 
    return NULL_TERM;
  }

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Extracting the %d lower bits of ",w);
    term_print_to_file(out, terms, t);
    fprintf(out, " successfully gave ");
    term_print_to_file(out, terms, result);
    fprintf(out, "\n");
  }

  // We know what we are returning, now we just check if we cache it for later
  if (w == original_bitsize) {
    int_hmap_add(&exp->norm_cache, t, result);
  }
  return result; 

}

// Function returns coefficient of conflict monomial in u (-1, 0, or 1)
// If -1 or 1, places the conflict monomial variable in argument monom.
// It uses cached values, and caches new values.
// if u is not a good term for the fragment:
// if !assume_fragment, function will return 2,
// if assume_fragment, function has unspecified behaviour (but runs faster)

int32_t bv_arith_coeff(arith_t* exp, term_t u, term_t* monom, bool assume_fragment) {

  plugin_context_t* ctx = exp->super.ctx;
  term_t conflict_var = exp->csttrail.conflict_var_term;
  term_table_t* terms   = ctx->terms;

  uint32_t w = term_bitsize(terms, u);

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Extracting coefficient of conflict variable in ");
    ctx_trace_term(ctx, u);
  }

  term_t t = extract(exp, u, w);
  if (t == NULL_TERM) return 2;
  
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Normalisation successfully produced ");
    ctx_trace_term(ctx, t);
  }

  // Looking at whether the value is cached
  bool ignore_this_bool;
  if (bv_evaluator_is_evaluable(&exp->csttrail, t, &ignore_this_bool)) return 0;
  int_hmap_pair_t* hmap_res = int_hmap_find(&exp->coeff1_cache,t);
  if (hmap_res != NULL) {
    if (monom != NULL) monom[0] = hmap_res->val;
    return 1;
  }
  hmap_res = int_hmap_find(&exp->coeffm1_cache,t);
  if (hmap_res != NULL) {
    if (monom != NULL) monom[0] = hmap_res->val;
    return -1;
  }

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Not evaluable and not cached\n");
  }

  term_t base = lower_bit_extract_base(exp,t,w,NULL,NULL);
  if (base == NULL_TERM) return 2;

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "top-level base is ");
    ctx_trace_term(ctx, base);
  }

  if (!assume_fragment // If we don't know we are in the fragment
      && base != t // and base is a subterm of t, we recursively check
      && (bv_arith_coeff(exp, base, NULL, false) == 2)) { // whether base is in the fragment
    return 2; // We're outside the fragment
  }

  term_t monom_var = NULL_TERM;
  int32_t result   = 0;
  
  if ((base != t) || (t == conflict_var)) {
    // OK, now we know or we assume we are in the fragment
    monom_var = t;  // the monom_var is t
    result = 1;     // with coeff 1
  } else {

    // Now head and base are unspecified and useless, we can re-cycle those variables

    switch (term_kind(ctx->terms, t)) {
    case BV_POLY: {
      bvpoly_t* t_poly = bvpoly_term_desc(ctx->terms, t);
      for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
        term_t this_monom_var = t_poly->mono[i].var;
        if (this_monom_var == const_idx) continue;
        if (!assume_fragment
            && (bv_arith_coeff(exp, this_monom_var, NULL, false) == 2)) {
          return 2; // We're outside the fragment
        }
        if (!bv_evaluator_is_evaluable(&exp->csttrail,this_monom_var, &ignore_this_bool)) {
          if (result != 0) { // second unevaluable monomial?
            return 2; // -> we're outside the fragment
          }
          if (bvconst_is_one(t_poly->mono[i].coeff, t_poly->width)) {
            result = 1;
            monom_var = this_monom_var;
          } else {
            if (bvconst_is_minus_one(t_poly->mono[i].coeff, t_poly->bitsize)) {
              result = -1;
              monom_var = this_monom_var;
            }
            else return 2;
          }
          if (assume_fragment) break; // If in fragment, need not look at other monomials
        }
      }
      break;
    }
    case BV64_POLY: {
      bvpoly64_t* t_poly = bvpoly64_term_desc(ctx->terms, t);
      for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
        term_t this_monom_var = t_poly->mono[i].var;
        if (this_monom_var == const_idx) continue;
        if (!assume_fragment
            && (bv_arith_coeff(exp, this_monom_var, NULL, false) == 2)) {
          return 2; // We're outside the fragment
        }
        if (!bv_evaluator_is_evaluable(&exp->csttrail,this_monom_var, &ignore_this_bool)) {
          if (result != 0) { // second unevaluable monomial?
            return 2; // -> we're outside the fragment
          }
          if (t_poly->mono[i].coeff == 1) {
            result = 1;
            monom_var = this_monom_var;
          } else {
            if (bvconst64_is_minus_one(t_poly->mono[i].coeff,term_bitsize(ctx->terms,t))) {
              result = -1;
              monom_var = this_monom_var;
            }
            else return 2;
          }
          if (assume_fragment) break; // If in fragment, need not look at other monomials
        }
      }
      break;
    }
    default:
      return 2;
    }
  }
  assert(monom_var != NULL_TERM);
  
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Coefficient is %d\n",result);
  }
  int_hmap_add((result == 1)? (&exp->coeff1_cache):(&exp->coeffm1_cache), t, monom_var);
  if (monom != NULL) monom[0] = monom_var;
  return result;
}




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

static
uint32_t get_bitwidth(interval_t* i){
  return i->lo.bitsize;
}

static
bool is_full(interval_t* i){
  return bvconstant_eq(&i->lo,&i->hi);
}

void bv_arith_interval_delete(interval_t* i) {
  delete_bvconstant(&i->lo);
  delete_bvconstant(&i->hi);
  delete_bvconstant(&i->length);
  delete_ivector(&i->reasons);
}

void bv_arith_interval_destruct(interval_t* i) {
  bv_arith_interval_delete(i);
  safe_free(i);
}

void bv_arith_interval_print(FILE* out, term_table_t* terms, interval_t* i) {
  if (i->var != NULL_TERM) {
    term_print_to_file(out, terms, i->var);
    fprintf(out, " \\not\\in ");
  }
  fprintf(out, "[ ");
  bvconst_print(out, i->lo.data, i->lo.bitsize);
  fprintf(out, " ( ");
  term_print_to_file(out, terms, i->lo_term);
  fprintf(out, " ) ; ");
  bvconst_print(out, i->hi.data, i->hi.bitsize);
  fprintf(out, " ( ");
  term_print_to_file(out, terms, i->hi_term);
  fprintf(out, " ) [");
}

// Comparing bv_constants, with a baseline that serves as the zero
static
bool bvconst_le_base(const bvconstant_t* a, const bvconstant_t* b, const bvconstant_t* baseline){
  bvconstant_t a_base, b_base;
  init_bvconstant(&a_base);
  init_bvconstant(&b_base);
  bvconstant_copy(&a_base, a->bitsize, a->data);
  bvconstant_copy(&b_base, b->bitsize, b->data);
  bvconstant_sub(&a_base, baseline);
  bvconstant_sub(&b_base, baseline);
  bvconstant_normalize(&a_base);
  bvconstant_normalize(&b_base);
  bool result = bvconstant_le(&a_base, &b_base);
  delete_bvconstant(&a_base);
  delete_bvconstant(&b_base);
  return result;
}

static
bool bvconst_lt_base(const bvconstant_t* a, const bvconstant_t* b, const bvconstant_t* baseline){
  return !bvconst_le_base(b, a, baseline);
}

// Determines if interval i contains value a. Happens if (a - i->lo) < (i->hi - i->lo)
static
bool is_in_interval(const bvconstant_t* a, const interval_t* i){
  return bvconst_lt_base(a, &i->hi, &i->lo);
}

// Comparing two intervals: first look at bitwidth, then lower bound, then span.
// When lower bounds are compared, an optional baseline can be provided, in data,
// which must have the same bitwidth as x and y.
bool cmp_base(void *data, void *x, void *y){
  bvconstant_t* baseline = (bvconstant_t*) data;
  interval_t* i1 = (interval_t*) x;
  interval_t* i2 = (interval_t*) y;
  if (x == NULL) return false; // NULL is not smaller than anyone (strict order)
  if (y == NULL) return true;  // NULL is strictly bigger than anyone but NULL
  if (get_bitwidth(i1) == get_bitwidth(i2)) {
    if (bvconstant_eq(&i1->lo,&i2->lo))
      return bvconst_lt_base(&i1->hi,&i2->hi,&i1->lo);
    return (baseline==NULL) ?
      bvconstant_lt(&i1->lo,&i2->lo) :
      bvconst_lt_base(&i1->lo,&i2->lo,baseline) ;
  }
  return (get_bitwidth(i2) < get_bitwidth(i1));
}

// inhabits output
static
void interval_construct(arith_t* exp,
                        const bvconstant_t* lo,
                        const bvconstant_t* hi,
                        term_t lo_term,
                        term_t hi_term,
                        term_t var,
                        term_t reason,
                        interval_t* output) {
  
  /* plugin_context_t* ctx = exp->super.ctx; */
  /* if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) { */
  /*   FILE* out = ctx_trace_out(ctx); */
  /*   fprintf(out, "Constructing interval from lo = "); */
  /*   bvconst_print(out, lo->data, lo->bitsize); */
  /*   fprintf(out, ", hi = "); */
  /*   bvconst_print(out, hi->data, hi->bitsize); */
  /*   fprintf(out, ", lo_term = "); */
  /*   term_print_to_file(out, ctx->terms, lo_term); */
  /*   fprintf(out, ", hi_term = "); */
  /*   term_print_to_file(out, ctx->terms, hi_term); */
  /*   fprintf(out, "\n"); */
  /* } */

  init_bvconstant(&output->lo);
  init_bvconstant(&output->hi);
  init_bvconstant(&output->length);
  output->lo_term = lo_term;
  output->hi_term = hi_term;
  output->var     = var;
  output->reason  = reason;
  init_ivector(&output->reasons,0);

  uint32_t ignore_this_int = 0;
  const bvconstant_t* tmp;
  bv_evaluator_t* eval = exp->super.eval;
  
  if (hi != NULL) {
    tmp = hi;
  } else {
    const mcsat_value_t* v = bv_evaluator_evaluate_term(eval, hi_term, &ignore_this_int);
    assert(v->type == VALUE_BV);
    tmp = &v->bv_value;
  }
  assert(bvconstant_is_normalized(tmp));
  bvconstant_copy(&output->hi, tmp->bitsize, tmp->data);
  bvconstant_copy(&output->length, tmp->bitsize, tmp->data);

  if (lo != NULL) {
    tmp = lo;
  } else {
    const mcsat_value_t* v = bv_evaluator_evaluate_term(eval, lo_term, &ignore_this_int);
    assert(v->type == VALUE_BV);
    tmp = &v->bv_value;
  }
  assert(bvconstant_is_normalized(tmp));
  bvconstant_copy(&output->lo, tmp->bitsize, tmp->data);
  bvconstant_sub(&output->length, tmp);
  bvconstant_normalize(&output->length);
  bvconstant_sub_one(&output->length);
  bvconstant_normalize(&output->length);
  
  /* if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) { */
  /*   FILE* out = ctx_trace_out(ctx); */
  /*   fprintf(out, "bv_arith creates interval "); */
  /*   bv_arith_interval_print(out, ctx->terms, output); */
  /*   fprintf(out, "\n"); */
  /* } */
}

// Adds a newly constructed interval into the heap
interval_t* bv_arith_interval_mk(arith_t* exp,
                                 const bvconstant_t* lo,
                                 const bvconstant_t* hi,
                                 term_t lo_term,
                                 term_t hi_term,
                                 term_t var,
                                 term_t reason) {
  plugin_context_t* ctx = exp->super.ctx;
  interval_t* result = safe_malloc(sizeof(interval_t));
  
  interval_construct(exp, lo, hi, lo_term, hi_term, var, reason, result);
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Creating interval, ");
    bv_arith_interval_print(out, ctx->terms, result);
    fprintf(out, "\n");
  }
  return result;
}

static inline
interval_t* bv_arith_full_interval_mk(arith_t* exp, term_t reason, uint32_t width) {
  plugin_context_t* ctx = exp->super.ctx;
  term_manager_t* tm    = ctx->tm;
  term_t zero_term   = bv_arith_zero(tm, width);
  interval_t* result = bv_arith_interval_mk(exp,NULL,NULL,zero_term,zero_term,NULL_TERM,reason);
  return result;
}


/**
   Explanation mechanism. First for 1 constraint. Then for the whole conflict
**/

// Analyses one side of an atom, assumed to be in the fragment.
// t is the side, coeff is the coeff in the conflict monom, var[0] is its var, cc is a non-initialised bv_constant
// returns the "rest of the term" (monomial of the conflict var is removed), and places the result of its evaluation in cc
term_t bv_arith_init_side(arith_t* exp, term_t t, int32_t coeff, term_t* var, bvconstant_t* cc) {

  // Standard abbreviations
  plugin_context_t* ctx = exp->super.ctx;
  term_manager_t* tm    = ctx->tm;

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Initialising constraint_side ");
    term_print_to_file(out, ctx->terms, t);
    fprintf(out, "\n");
  }

  assert(var != NULL);
  
  term_t result; // The term without the unevaluable monomial

  if (var[0] == NULL_TERM) {
    assert(coeff == 0);
    result = t;
  } else {
    uint32_t w = term_bitsize(tm->terms, var[0]);
    term_t head;
    uint32_t variable_bits;
    lower_bit_extract_base(exp, var[0], w, &head, &variable_bits);
    result = (coeff > 0) ?
      bv_arith_sub_terms(tm, t, var[0]) :
      bv_arith_add_terms(tm, t, var[0]) ;
    if (head != NULL_TERM) {
      result =
        (coeff > 0) ?
        bv_arith_add_terms(tm, result, head) :
        bv_arith_sub_terms(tm, result, head) ;
      var[0] = bv_arith_extension(tm, term_extract(tm,var[0],0,variable_bits), w);
    }
  }
  
  // We evaluate this...
  uint32_t eval_level = 0;
  const mcsat_value_t* value = bv_evaluator_evaluate_term(exp->super.eval, result, &eval_level);
  assert(value->type == VALUE_BV);

  /// ...copy it into cc
  init_bvconstant(cc);
  bvconstant_copy(cc, value->bv_value.bitsize, value->bv_value.data);

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "We have c: ");
    term_print_to_file(out, ctx->terms, result);
    fprintf(out, " with value cc: ");
    bvconst_print(out, cc->data, cc->bitsize);
    fprintf(out, "\n");
  }

  return result;  // ...and output the term
}


// Treat a constraint of the form lhs <= rhs
interval_t* bv_arith_unit_le(arith_t* exp, term_t lhs_raw, term_t rhs_raw, bool b) {
  // Standard abbreviations
  plugin_context_t* ctx = exp->super.ctx;
  term_manager_t* tm    = ctx->tm;
  term_table_t* terms   = ctx->terms;
  uint32_t w = term_bitsize(terms, lhs_raw);
  assert(w == term_bitsize(terms, rhs_raw));
  interval_t* result = NULL;
  
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "\nTreating unit_constraint (lhs <= rhs) where lhs is\n");
    ctx_trace_term(ctx, lhs_raw);
    fprintf(out, " and rhs is\n");
    ctx_trace_term(ctx, rhs_raw);
    fprintf(out, "\n");
  }

  term_t lhs = extract(exp, lhs_raw, term_bitsize(terms, lhs_raw));
  term_t rhs = extract(exp, rhs_raw, term_bitsize(terms, rhs_raw));

  term_t left_var     = NULL_TERM;
  term_t right_var    = NULL_TERM;
  int32_t left_coeff  = bv_arith_coeff(exp, lhs, &left_var, true);
  int32_t right_coeff = bv_arith_coeff(exp, rhs, &right_var, true);
    
  if ((left_coeff == -1) || (right_coeff == -1)) {
    // if coeff is negative, we add one, negate and swap sides.
    term_t nlhs = bv_arith_negate_terms(tm, bv_arith_add_one_term(tm, lhs));
    term_t nrhs = bv_arith_negate_terms(tm, bv_arith_add_one_term(tm, rhs));
    return bv_arith_unit_le(exp, nrhs, nlhs, b);
  }

  // Setting c1 and c2 to be 2 terms representing the left polynomial and the right polynomial,
  // from which the confict variable (if present) was removed,
  // and evaluating those polynomials c1 and c2 (whose variables should all have values on the trail)
  bvconstant_t cc1, cc2;
  term_t c1 = bv_arith_init_side(exp, lhs, left_coeff, &left_var, &cc1);
  term_t c2 = bv_arith_init_side(exp, rhs, right_coeff, &right_var, &cc2);

  assert(left_var == NULL_TERM || right_var == NULL_TERM || left_var == right_var);
  term_t var = (left_var == NULL_TERM) ? right_var : left_var;

  if (var != NULL_TERM && ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "\nMonomial variable is\n");
    ctx_trace_term(ctx, var);
    fprintf(out, "\n");
  }


  // Now we are sure that on both sides, coefficient is either 0 or 1
  // we check which one:
  bool left_has  = (left_coeff == 1);
  bool right_has = (right_coeff == 1);

  term_t lo_term, hi_term;
  bvconstant_t lo, hi;
  init_bvconstant(&lo);
  init_bvconstant(&hi);

  if (right_has) { // lo is going to be -c2
    bvconstant_copy(&lo, cc2.bitsize, cc2.data);
    bvconstant_negate(&lo);
    bvconstant_normalize(&lo);
    lo_term = bv_arith_negate_terms(tm,c2);
    
    if (left_has) { // then hi is -c1
      bvconstant_copy(&hi, cc1.bitsize, cc1.data);
      bvconstant_negate(&hi);
      bvconstant_normalize(&hi);
      hi_term = bv_arith_negate_terms(tm,c1);
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "Case <=: has_right, has_left, lo = ");
        bvconst_print(out, lo.data, lo.bitsize);
        fprintf(out, ", hi = ");
        bvconst_print(out, hi.data, hi.bitsize);
        fprintf(out, "\n");
      }
      if (b && !bvconstant_eq(&lo,&hi))
        result = bv_arith_interval_mk(exp, &lo, &hi, lo_term, hi_term, var, NULL_TERM);
      if (!b) {
        if (!bvconstant_eq(&lo,&hi))
          result = bv_arith_interval_mk(exp, &hi, &lo, hi_term, lo_term, var, NULL_TERM);
        else {
          term_t reason = bv_arith_eq(tm, lo_term, hi_term);
          result = bv_arith_full_interval_mk(exp, reason, w);
        }
      }
    } else { // No conflict variable on the left, then hi is (c1 - c2)
      bvconstant_copy(&hi, cc1.bitsize, cc1.data);
      bvconstant_sub(&hi, &cc2);
      bvconstant_normalize(&hi);
      hi_term = bv_arith_sub_terms(tm,c1,c2);
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "Case <=: has_right, !has_left, lo = ");
        bvconst_print(out, lo.data, lo.bitsize);
        fprintf(out, ", hi = ");
        bvconst_print(out, hi.data, hi.bitsize);
        fprintf(out, "\n");
      }
      if (b && !bvconstant_eq(&lo,&hi))
        result = bv_arith_interval_mk(exp, &lo, &hi, lo_term, hi_term, var, NULL_TERM);
      if (!b) {
        if (!bvconstant_eq(&lo,&hi))
          result = bv_arith_interval_mk(exp, &hi, &lo, hi_term, lo_term, var, NULL_TERM);
        else {
          term_t reason = bv_arith_eq(tm, lo_term, hi_term);
          result = bv_arith_full_interval_mk(exp, reason, w);
        }
      }
    }
  } else {
    if (left_has) { // lo = c2 - c1 + 1, and hi = -c1
      bvconstant_copy(&lo, cc2.bitsize, cc2.data);
      bvconstant_sub(&lo, &cc1);
      bvconstant_normalize(&lo);
      bvconstant_add_one(&lo);
      bvconstant_normalize(&lo);
      lo_term = bv_arith_add_one_term(tm, bv_arith_sub_terms(tm,c2,c1));

      bvconstant_copy(&hi, cc1.bitsize, cc1.data);
      bvconstant_negate(&hi);
      bvconstant_normalize(&hi);
      hi_term = bv_arith_negate_terms(tm,c1);
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "Case <=: !has_right, has_left, lo = ");
        bvconst_print(out, lo.data, lo.bitsize);
        fprintf(out, ", hi = ");
        bvconst_print(out, hi.data, hi.bitsize);
        fprintf(out, "\n");
      }
      if (b && !bvconstant_eq(&lo,&hi))
        result = bv_arith_interval_mk(exp, &lo, &hi, lo_term, hi_term, var, NULL_TERM);
      if (!b) {
        if (!bvconstant_eq(&lo,&hi))
          result = bv_arith_interval_mk(exp, &hi, &lo, hi_term, lo_term, var, NULL_TERM);
        else {
          term_t reason = bv_arith_eq(tm, lo_term, hi_term);
          result = bv_arith_full_interval_mk(exp, reason, w);
        }
      }
    } else { // x appears on neither sides
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "Case <=: !has_right, !has_left");
      }
      if (b && bvconstant_lt(&cc2,&cc1)) { // If c2 < c1, we forbid everything, otherwise we forbid nothing
        term_t reason = bv_arith_lt(tm, c2, c1);
        result = bv_arith_full_interval_mk(exp, reason, w);
      }
      if (!b && bvconstant_le(&cc1,&cc2)) { // If c2 < c1, we forbid everything, otherwise we forbid nothing
        term_t reason = bv_arith_le(tm, c1, c2);
        result = bv_arith_full_interval_mk(exp, reason, w);
      }
    }
  }
  
  delete_bvconstant(&cc1);
  delete_bvconstant(&cc2);
  delete_bvconstant(&lo);
  delete_bvconstant(&hi);
  return result;
}


// Adds interval to conflict
void bv_arith_add2conflict(arith_t* exp,
                           term_t min_saved_term,
                           interval_t* i,
                           ivector_t* conflict) {

  plugin_context_t* ctx = exp->super.ctx;
  term_manager_t* tm    = ctx->tm;

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Adding to conflict interval ");
    bv_arith_interval_print(out, ctx->terms, i);
    fprintf(out, "  hooking up with ( ");
    term_print_to_file(out, tm->terms, min_saved_term);
    fprintf(out, " )\n");
  }

  assert(!bvconstant_eq(&i->lo, &i->hi));

  term_t small = bv_arith_sub_terms(tm, min_saved_term, i->lo_term);
  term_t big   = bv_arith_sub_terms(tm, i->hi_term, i->lo_term);
  
  term_t continuity_reason = bv_arith_lt(tm, small, big);
  if (continuity_reason != NULL_TERM) {
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Adding continuity_reason ");
      term_print_to_file(out, tm->terms, small);
      fprintf(out, " < ");
      term_print_to_file(out, tm->terms, big);
      fprintf(out, ", i.e. ");
      term_print_to_file(out, tm->terms, continuity_reason);
      fprintf(out, "\n");
    }
    /* uint32_t eval_level = 0; */
    /* assert(!bv_evaluator_evaluate_term(exp->super.eval, not_term(tm->terms,continuity_reason), &eval_level)->b); */
    ivector_push(conflict, continuity_reason);
  }

  ivector_add(conflict, i->reasons.data, i->reasons.size);
}

// Returns the index of the longest interval in an array of (non-empty) interval pointers
static inline
uint32_t get_longest(interval_t** intervals, uint32_t number_intervals){
  assert(number_intervals != 0);
  uint32_t result = 0;

  for (uint32_t i = 1; i < number_intervals; i++){
    assert(intervals[i] != NULL);
    assert(get_bitwidth(intervals[i]) == get_bitwidth(intervals[0]));
    // If it is longer than the previous longest, we update the latter
    if (bvconstant_lt(&intervals[0]->length, &intervals[i]->length)){
      result = i;
    }
  }
  return result;
}

static inline
void print_intervals(plugin_context_t* ctx, interval_t** intervals, uint32_t number_intervals){
  FILE* out = ctx_trace_out(ctx);
  for (uint32_t i = 0; i < number_intervals; i++) {
    bv_arith_interval_print(out, ctx->terms, intervals[i]);
    fprintf(out, "\n");
  }
}

static inline
interval_t* get_interval(interval_t** intervals, interval_t* inherited, int32_t index_inherited, uint32_t j){
  if (index_inherited<0 || j<index_inherited) return intervals[j];
  if (j==index_inherited) return inherited;
  return intervals[j-1];
}

// Argument intervals[0] is a non-empty array of (non-empty) interval pointers
// of a common bitwidth w, which is also the bitwidth of optional argument inherited.
// Computes from intervals[0] and inherited a coverage of all values of bitwidth w.
// Places the chaining conditions (literals) in output,
// and outputs whether or not inherited has been used in the coverage
static
bool cover(arith_t* exp,
           ivector_t* output,       // Where we dump our literals in the end
           uint32_t bitwidths,      // Number of distinct bitwidths remaining after this
           interval_t*** intervals, // Array of size bitwidths
           uint32_t* numbers,       // Array of size bitwidths
           interval_t* inherited,   // First interval of coverage, can be NULL
           term_t* substitution     // Term used for substitution of the variable in case of propagation
           ){
  assert(intervals[0] != NULL);
  assert(intervals[0][0] != NULL);
  
  plugin_context_t* ctx = exp->super.ctx;
  term_manager_t* tm    = ctx->tm;
  term_table_t* terms   = ctx->terms;
  uint32_t w            = get_bitwidth(intervals[0][0]); // Bitwidth currently being treated
  uint32_t n = numbers[0]; // Number of intervals of bitwidth w to consider

  // We start by computing the longest interval in intervals[0]
  interval_t* longest = intervals[0][get_longest(intervals[0], n)];

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "\nCall to cover for a ");
    if (substitution != NULL) {
      fprintf(out, "propagation, with ");
    } else {
      fprintf(out, "conflict, with ");
    }
    fprintf(out, "%d intervals of bitwidth %d:\n",n,w);
    print_intervals(ctx, intervals[0], n);
    fprintf(out, "Longest one is ");
    bv_arith_interval_print(out, terms, longest);
    fprintf(out, "\n");
  }

  if (is_full(longest)) { // if interal is full, we're done, we just add the reason
    if (longest->reason != NULL_TERM) {
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "Using 1 full interval with internal reason ");
        term_print_to_file(out, tm->terms, longest->reason);
        fprintf(out, "\n");
      }
      uint32_t eval_level = 0;
      assert(bv_evaluator_evaluate_term(exp->super.eval, longest->reason, &eval_level)->b);
      (void) eval_level;
      ivector_push(output, longest->reason);
      ivector_add(output, longest->reasons.data, longest->reasons.size);
    }
    return false;
  }

  if (inherited != NULL && bvconstant_lt(&longest->length,&inherited->length)) {
    longest = inherited;
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Interval inherited from bigger bitwidths is longer. It becomes \"longest\" ");
      bv_arith_interval_print(out, terms, longest);
      fprintf(out, "\n");
    }
  }
  
  ptr_array_sort2((void **)intervals[0], n, &longest->lo, cmp_base);

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "After sorting with baseline: ");
    bvconst_print(out, longest->lo.data, longest->lo.bitsize);
    fprintf(out, "\n");
    print_intervals(ctx, intervals[0], n);
  }

  // Positionning inherited in the array
  bool result = false; // As far as we know, we are not using inherited
  int32_t inherited_index = -1; //
  if (inherited != NULL) {
    inherited_index++;
    for(uint32_t j = 0; j < n; j++){
      if (cmp_base(&longest->lo, intervals[0][j], inherited)) {
        inherited_index++;
      }
    }
    n++; // one more interval to consider
  }

  // The elements saved in output so far forbid conflict_var[w] to be in [saved_lo; saved_hi[
  interval_t* first = NULL;
  bvconstant_t* saved_hi = &longest->hi;
  term_t saved_hi_term = longest->hi_term;

  // The best interval found so far in intervals[0], but not yet saved in output,
  // that can be used to forbid the greatest number of bv values beyond saved_hi
  // We know that we can forbid conflict_var[w] to be in [longest->lo; best_so_far->hi[,
  // which contains [first->lo; saved_hi[

  interval_t* best_so_far = NULL;
  bool notdone = true;

  // We loop over all intervals of that bitwidth
  for(uint32_t j = 0; notdone && j <= n; ){

    interval_t* i = get_interval(intervals[0],inherited,inherited_index,j%n);

    if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "\nbv_arith looks at interval of index %d among %d (inherited has index %d) ",j,n,inherited_index);
      bv_arith_interval_print(out, terms, i);
      fprintf(out, "\n");
    }

    if (is_in_interval(saved_hi,i)) { // In continuity of previously forbidden range
      // Does i eliminate more values than best_so_far?
      if ((best_so_far == NULL)
          || ((best_so_far != NULL) && is_in_interval(&best_so_far->hi, i))) { // i becomes best_so_far
        if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
          FILE* out = ctx_trace_out(ctx);
          fprintf(out, "becomes best_so_far\n");
        }
        best_so_far = i;
      } else {
        if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
          FILE* out = ctx_trace_out(ctx);
          fprintf(out, "is useless\n");
        }
      }
      j++;

    } else { // Not in continuity of previously forbidden range

      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "is in discontinuity\n");
      }

      if (best_so_far != NULL) { // We record best_so_far

        if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
          FILE* out = ctx_trace_out(ctx);
          fprintf(out, "Best interval so far is recorded ");
          bv_arith_interval_print(out, terms, best_so_far);
          fprintf(out, "\n");
        }
        if (first == NULL && is_in_interval(&longest->hi,best_so_far)) {
          first = best_so_far;
          if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
            FILE* out = ctx_trace_out(ctx);
            fprintf(out, "First interval, delaying recording of the hook\n");
          }
        } else { // Otherwise we record best_so_far and its hook
          bv_arith_add2conflict(exp, saved_hi_term, best_so_far, output);
          if (best_so_far == inherited) { result = true; } // inherited was used
        }
        saved_hi      = &best_so_far->hi;
        saved_hi_term = best_so_far->hi_term;
        if (is_in_interval(&best_so_far->hi,longest)) {
          // best_so_far actually closes the circle
          if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
            FILE* out = ctx_trace_out(ctx);
            fprintf(out, "...and it closes the circle!\n");
          }
          break;
        }
        best_so_far = NULL;
        continue;
      }

      if (j < n && bvconst_lt_base(&i->lo, saved_hi, &longest->lo)) { // i is actually included in the previously forbidden values
        if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
          FILE* out = ctx_trace_out(ctx);
          fprintf(out, "Interval is included in previously forbidden values.\n");
        }
        j++; // Go get next interval
        continue;
      }

      // Discontinuity in intervals! There's a hole!

      // First situation: there are no smaller bitwidths
      if (bitwidths == 0) {
        // The hole had better be of size 1, and we'd better be doing a propagation!
        assert(substitution != NULL);
        assert(substitution[0] == NULL_TERM);
        bvconstant_t saved_hi_copy;
        init_bvconstant(&saved_hi_copy);
        bvconstant_copy(&saved_hi_copy, saved_hi->bitsize, saved_hi->data);
        bvconstant_normalize(&saved_hi_copy);
        bvconstant_add_one(&saved_hi_copy);
        bvconstant_normalize(&saved_hi_copy);
        assert(bvconstant_eq(&saved_hi_copy,&i->lo));
        delete_bvconstant(&saved_hi_copy);
        // OK, seems fine. We add to the conflict the fact that the hole has size 1:
        term_t literal = bv_arith_eq(tm, i->lo_term, bv_arith_add_one_term(tm, saved_hi_term));
        if (literal != NULL_TERM) ivector_push(output, literal);
        // We output the term in the substitution pointer
        substitution[0] = saved_hi_term;
        if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
          FILE* out = ctx_trace_out(ctx);
          fprintf(out, "Found one possible value: ");
          term_print_to_file(out, terms, saved_hi_term);
          fprintf(out, "\n");
        }
        saved_hi = &i->lo;
        saved_hi_term = i->lo_term;
        if (is_in_interval(saved_hi,longest)) notdone = false;
        continue; // We skip the rest of the loop
      }
      
      // The hole must be filled by lower levels, as done by a recursive call to cover
      assert(bitwidths != 0); // There'd better be at least one more level of smaller bitwidths
      uint32_t next_bitwidth = get_bitwidth(intervals[1][0]);
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "Next bitwidth is %d.\n",next_bitwidth);
      }
      assert(next_bitwidth < w); // it'd better be a smaller bitwidth
      // We now prepare the arguments of the recursive call
      ivector_t rec_output;      // where the recursive call should place literals
      init_ivector(&rec_output, 0);
      // Now we prepare the construction of the hole [ lo (lo_term) , hi (hi_term) [
      term_t lo_term = saved_hi_term;
      term_t hi_term = i->lo_term;
      bvconstant_t lo,hi,smaller_values; // smaller_values: how many values of the next bitwidth?
      init_bvconstant(&lo);
      init_bvconstant(&hi);
      init_bvconstant(&smaller_values);
      bvconstant_copy(&lo, saved_hi->bitsize, saved_hi->data);
      bvconstant_copy(&hi, i->lo.bitsize, i->lo.data);
      bvconstant_set_all_zero(&smaller_values, w);
      bvconst_set_bit(smaller_values.data, next_bitwidth); 
      bvconstant_normalize(&smaller_values);
      term_t smaller_values_term = mk_bv_constant(tm, &smaller_values);
      bvconstant_sub_one(&smaller_values); // We subtract 1 so as to compare it to the length of the hole
      bvconstant_normalize(&smaller_values);
      interval_t hole; // Defining hole to be filled by the next level(s)
      interval_construct(exp, &lo, &hi, lo_term, hi_term, NULL_TERM, NULL_TERM, &hole);
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "OK, now there is a hole: ");
        bv_arith_interval_print(out, terms, &hole);
        fprintf(out, " for which (length-1) is ");
        bvconst_print(out, hole.length.data, hole.length.bitsize);
      }
      // We will record whether the (complement of the) hole is used by the smaller bitwidths
      bool hole_used;
      // We project lo_term and hi_term into the domain of smaller bitwidth
      term_t lo_proj_term = extract(exp, lo_term, next_bitwidth);
      term_t hi_proj_term = extract(exp, hi_term, next_bitwidth);
      // Where the recursive call can return the substitution term (if we are explaining a propagation)
      term_t rec_substitution = NULL_TERM;
      // Now, there two cases for the recursive call: small hole or big hole
      if (bvconstant_lt(&hole.length, &smaller_values)) {
        // Hole is smaller than number of values in smaller bitwidth -> we project
        bvconstant_t lo_proj,hi_proj;
        init_bvconstant(&lo_proj);
        init_bvconstant(&hi_proj);
        bvconstant_extract(&lo_proj, lo.data, 0, next_bitwidth);
        bvconstant_extract(&hi_proj, hi.data, 0, next_bitwidth);
        bvconstant_normalize(&lo_proj);
        bvconstant_normalize(&hi_proj);
        interval_t hole_complement; // at the smaller bitwidth
        interval_construct(exp, &hi_proj, &lo_proj, hi_proj_term, lo_proj_term, NULL_TERM, NULL_TERM, &hole_complement);
        if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
          FILE* out = ctx_trace_out(ctx);
          fprintf(out, " < ");
          bvconst_print(out, smaller_values.data, smaller_values.bitsize);
          fprintf(out, "\nHole is smaller than the domain of the next bitwidth, we recursively call cover on complemented and projected hole: ");
          bv_arith_interval_print(out, terms, &hole_complement);
          fprintf(out, "\n");
        }
        hole_used = cover(exp, &rec_output,
                          bitwidths-1, &intervals[1], &numbers[1],
                          &hole_complement,
                          (substitution != NULL && rec_substitution == NULL_TERM) ? &rec_substitution : NULL);
        bv_arith_interval_delete(&hole_complement);
        delete_bvconstant(&lo_proj);
        delete_bvconstant(&hi_proj);
        delete_bvconstant(&smaller_values);
      } else { // Hole is bigger -> lower level(s) must forbid everything
        if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
          FILE* out = ctx_trace_out(ctx);
          fprintf(out, " >= ");
          bvconst_print(out, smaller_values.data, smaller_values.bitsize);
          fprintf(out, "\nHole is at least as big as the domain of the next bitwidth, we recursively call cover on that whole domain.\n");
        }
        cover(exp, &rec_output, bitwidths-1, &intervals[1], &numbers[1], NULL,
              (substitution != NULL && rec_substitution == NULL_TERM) ? &rec_substitution : NULL);
        hole_used = false;
      }

      // Now we analyse what the recursive call returned to us
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "Back to bitwidth %d!\n",w);
      }
      // If we are explaining a propagation and got a feasible value in the hole:
      if (substitution != NULL && rec_substitution != NULL_TERM) {
        term_t diff = bv_arith_sub_terms(tm, rec_substitution, lo_proj_term);
        substitution[0] = bv_arith_add_terms(tm, lo_term, bv_arith_extension(tm, diff, w));
        if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
          FILE* out = ctx_trace_out(ctx);
          fprintf(out, "Hole was from ");
          term_print_to_file(out, terms, lo_term);
          fprintf(out, " to ");
          term_print_to_file(out, terms, hi_term);
          fprintf(out, " and the only possible value at bitwidth %d is ",w);
          term_print_to_file(out, terms, substitution[0]);
          fprintf(out, "\n");
        }
      }
      if (!hole_used && rec_substitution == NULL_TERM) {
        // If the hole was not used and the recusive call did not output a term,
        // the intervals of the present bitwith were really useless, we return!
        if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
          FILE* out = ctx_trace_out(ctx);
          fprintf(out, "The recursive call covered the hole without our help, we return.\n");
        }
        assert(substitution == NULL); // We can't be explaining a propagation
        ivector_reset(output); // if hole wasn't used, this bitwidth is useless
        notdone = false;
        result  = false;
        saved_hi_term = NULL_TERM;
      } else {
        // otherwise we need to push to output that the hole was small
        if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
          FILE* out = ctx_trace_out(ctx);
          fprintf(out, "The recursive call used the hole we left uncovered at bitwidth %d and/or found 1 feasible value .\n",w);
        }
        term_t literal = (hole_used) ?
          bv_arith_lt(tm, bv_arith_sub_terms(tm, hi_term, lo_term), smaller_values_term) :
          bv_arith_le(tm, bv_arith_sub_terms(tm, hi_term, substitution[0]), smaller_values_term);
        if (literal != NULL_TERM) {
          if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
            FILE* out = ctx_trace_out(ctx);
            fprintf(out, "The literal is ");
            term_print_to_file(out, terms, literal);
            fprintf(out, "\n");
          }
          ivector_push(output, literal);
        }
        saved_hi = &i->lo;
        saved_hi_term = i->lo_term;
        if (is_in_interval(saved_hi,longest)) notdone = false;
      }
      ivector_add(output, rec_output.data, rec_output.size);
      delete_ivector(&rec_output);
      delete_bvconstant(&lo);
      delete_bvconstant(&hi);
      bv_arith_interval_delete(&hole);
    }
  }

  if (saved_hi_term != NULL_TERM) {
    if (best_so_far != NULL && first != NULL && is_in_interval(saved_hi,first)) {
      // We didn't actually need longest, best_so_far plays the role of longest
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "No need for longest interval, as saved_hi is ");
        bvconst_print(out, saved_hi->data, saved_hi->bitsize);
        fprintf(out, "\nand first is ");
        bv_arith_interval_print(out, terms, first);
        fprintf(out, "\n");
      }
      bv_arith_add2conflict(exp, saved_hi_term, first, output);
      if (first == inherited) { result = true; } // inherited was used
    } else {
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "Adding to conflict longest interval ");
        bv_arith_interval_print(out, terms, longest);
        fprintf(out, "\n");
      }
      bv_arith_add2conflict(exp, saved_hi_term, longest, output);
      if (longest == inherited) { result = true; } // inherited was used
      // Now treating the delayed recording of first hook, if it exists:
      if (first == NULL) {
        if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
          FILE* out = ctx_trace_out(ctx);
          fprintf(out, "No delayed hook to record, nothing to do here.\n");
        }
      } else {
        if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
          FILE* out = ctx_trace_out(ctx);
          fprintf(out, "Delayed hook to record\n");
          bv_arith_interval_print(out, terms, longest);
          fprintf(out, "\n");
          bv_arith_interval_print(out, terms, first);
          fprintf(out, "\n");
        }
        bv_arith_add2conflict(exp, longest->hi_term, first, output);
        if (first == inherited) { result = true; } // inherited was used
      }
    }
  }
  ivector_remove_duplicates(output);
  return result;
}

void transform_interval(arith_t* exp, interval_t** interval) {

  plugin_context_t* ctx = exp->super.ctx;
  bv_evaluator_t* eval  = exp->super.eval;
  term_manager_t* tm    = ctx->tm;
  term_table_t* terms   = ctx->terms;

  if (!is_full(interval[0])) {
  
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Transforming interval ");
      bv_arith_interval_print(out, ctx->terms, interval[0]);
      fprintf(out, "\n");
    }

    uint32_t w = term_bitsize(terms, interval[0]->var);

    // We analyse the shape of the variable whose value is forbidden to be in interval[0]
    term_t head = NULL_TERM;
    uint32_t variable_bits;
    term_t base = lower_bit_extract_base(exp,interval[0]->var,w,&head,&variable_bits);
    assert(base != NULL_TERM);

    if (head == NULL_TERM) { // It's a sign-extend
      // We re-express the problem with 0-extend
      assert(variable_bits < w);
      bvconstant_t half; // Half of the number of values in the small bitwidth
      init_bvconstant(&half);
      bvconstant_set_all_zero(&half, w);
      bvconst_set_bit(half.data, variable_bits-1); 
      bvconstant_normalize(&half);
      term_t half_term = mk_bv_constant(tm, &half);
      term_t lo_term = bv_arith_add_terms(tm, interval[0]->lo_term, half_term); // new lo
      term_t hi_term = bv_arith_add_terms(tm, interval[0]->hi_term, half_term); // new hi
      base = bv_arith_add_half(tm,extract(exp, base, variable_bits));          // new base
      interval_t* result =
        bv_arith_interval_mk(exp,NULL,NULL,lo_term,hi_term,NULL_TERM,NULL_TERM);
      ivector_add(&result->reasons, interval[0]->reasons.data, interval[0]->reasons.size);
      bv_arith_interval_destruct(interval[0]);
      interval[0] = result;
      head = bv_arith_zero(tm, w);
      delete_bvconstant(&half);
    }
    
    assert(!is_full(interval[0]));

    if (variable_bits < w) {
      // The variable is a proper extension of something (otherwise we do nothing)
      bvconstant_t smaller_width; // smaller_width: how many values of bitwidth variable_bits?
      init_bvconstant(&smaller_width);
      bvconstant_set_all_zero(&smaller_width, w);
      bvconst_set_bit(smaller_width.data, variable_bits); 
      bvconstant_normalize(&smaller_width);
      term_t smaller_width_term = mk_bv_constant(tm, &smaller_width);
      term_t t0 = bv_arith_sub_terms(tm, interval[0]->lo_term, head);
      term_t t1 = bv_arith_sub_terms(tm, interval[0]->hi_term, head);

      uint32_t ignore_this_int = 0;

      const mcsat_value_t* v0 = bv_evaluator_evaluate_term(eval, t0, &ignore_this_int);
      assert(v0->type == VALUE_BV);
      term_t lo_term, lo_reason;
      if (bvconstant_lt(&v0->bv_value,&smaller_width)) {
        lo_term   = term_extract(tm, interval[0]->lo_term, 0, variable_bits);
        lo_reason = bv_arith_lt(tm, t0, smaller_width_term);
      } else {
        lo_term   = bv_arith_zero(tm, variable_bits);
        lo_reason = bv_arith_le(tm, smaller_width_term, t0);
      }

      const mcsat_value_t* v1 = bv_evaluator_evaluate_term(eval, t1, &ignore_this_int);
      assert(v1->type == VALUE_BV);
      term_t hi_term, hi_reason;
      if (bvconstant_lt(&v1->bv_value,&smaller_width)) {
        hi_term   = term_extract(tm, interval[0]->hi_term, 0, variable_bits);
        hi_reason = bv_arith_lt(tm, t1, smaller_width_term);
      } else {
        hi_term   = bv_arith_zero(tm, variable_bits);
        hi_reason = bv_arith_le(tm, smaller_width_term, t1);
      }

      delete_bvconstant(&smaller_width);

      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "variable_bits is %d and head is ",variable_bits);
        term_print_to_file(out, tm->terms, head);
        fprintf(out, "\nand lo - head is ");
        term_print_to_file(out, tm->terms, t0);
        fprintf(out, "\nand hi - head is ");
        term_print_to_file(out, tm->terms, t1);
        fprintf(out, "\nand smaller_width_term is ");
        term_print_to_file(out, tm->terms, smaller_width_term);
        fprintf(out, "\nand lo_term (on smaller bitwidth) is ");
        term_print_to_file(out, tm->terms, lo_term);
        fprintf(out, "\nand hi_term (on smaller bitwidth) is ");
        term_print_to_file(out, tm->terms, hi_term);
        fprintf(out, "\n");
      }

      interval_t* result =
        bv_arith_interval_mk(exp,NULL,NULL,lo_term,hi_term,NULL_TERM,NULL_TERM);
      // We don't really care about the variable if that interval is really the result

      if (is_full(result)) { // Interval on smaller bitwidth is full or empty
        bv_arith_interval_destruct(result);
        const mcsat_value_t* head_v =
          bv_evaluator_evaluate_term(eval, head, &ignore_this_int);
        assert(head_v->type == VALUE_BV);
        if (is_in_interval(&head_v->bv_value, interval[0])) {
          term_t reason = bv_arith_lt(tm,
                                      bv_arith_sub_terms(tm, head, interval[0]->lo_term),
                                      bv_arith_sub_terms(tm, interval[0]->hi_term, interval[0]->lo_term)
                                      );
          result = bv_arith_full_interval_mk(exp, reason, variable_bits);
        } else {
          assert(false);
          result = NULL;
        }
      }

      ivector_add(&result->reasons, interval[0]->reasons.data, interval[0]->reasons.size);
      bv_arith_interval_destruct(interval[0]);
      interval[0] = result;

      if (interval[0] == NULL) { return; } // Interval is empty, will not be used
    
      // Adding reasons to interval[0]:
      if (lo_reason != NULL_TERM) {
        ivector_push(&interval[0]->reasons, lo_reason);
        if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
          FILE* out = ctx_trace_out(ctx);
          fprintf(out, "  adding lo_reason ");
          term_print_to_file(out, tm->terms, lo_reason);
          fprintf(out, "\n");
        }
      }
      if (hi_reason != NULL_TERM) {
        ivector_push(&interval[0]->reasons, hi_reason);
        if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
          FILE* out = ctx_trace_out(ctx);
          fprintf(out, "  adding hi_reason ");
          term_print_to_file(out, tm->terms, hi_reason);
          fprintf(out, "\n");
        }
      }

      if (is_full(interval[0])) { return; } // Interval is full, we're done

      // The new variable that shouldn't be in interval[0] is base
      // with one of two situations:
      // - base is y<variable_bits> where y is the conflict variable itself
      // - base is a bv_poly (lower bits extraction has been pushed)
      // We only have to do something if it is a bv_poly
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "New variable is ");
        term_print_to_file(out, tm->terms, base);
        fprintf(out, "\n");
      }

      switch (term_kind(terms, base)) {
      case BV_POLY:
      case BV64_POLY: {
        assert(term_bitsize(terms,base) == variable_bits);
        assert(term_bitsize(terms,interval[0]->lo_term) == variable_bits);
        assert(term_bitsize(terms,interval[0]->hi_term) == variable_bits);
        term_t new_var = NULL_TERM;
        int32_t coeff = bv_arith_coeff(exp, base, &new_var, true);
        assert(coeff == 1 || coeff == -1);
        bvconstant_t cc;
        term_t rest = bv_arith_init_side(exp, base, coeff, &new_var, &cc);
        assert(term_bitsize(terms,rest) == variable_bits);
        delete_bvconstant(&cc);
        lo_term = bv_arith_sub_terms(tm, interval[0]->lo_term, rest);
        hi_term = bv_arith_sub_terms(tm, interval[0]->hi_term, rest);
        if (coeff == 1) {
          result = bv_arith_interval_mk(exp,NULL,NULL,lo_term,hi_term,new_var,NULL_TERM);
        } else {
          term_t new_lo_term =
            bv_arith_add_one_term(tm,bv_arith_negate_terms(tm, hi_term));
          term_t new_hi_term =
            bv_arith_add_one_term(tm,bv_arith_negate_terms(tm, lo_term));
          result = bv_arith_interval_mk(exp,NULL,NULL,new_lo_term,new_hi_term,new_var,NULL_TERM);
        }

        ivector_add(&result->reasons, interval[0]->reasons.data, interval[0]->reasons.size);
        bv_arith_interval_destruct(interval[0]);
        interval[0] = result;

        transform_interval(exp, interval);
        break;
      }
      default: {
      }
      }

    }

  }
}


static
void bvarith_explain(bv_subexplainer_t* this,
                     const ivector_t* reasons_in,
                     variable_t var,
                     ivector_t* reasons_out,
                     term_t* substitution) {

  arith_t* exp = (arith_t*) this;
  plugin_context_t* ctx = this->ctx;
  bv_evaluator_t* eval = this->eval;
  
  bv_evaluator_clear_cache(eval);

  // Standard abbreviations
  term_table_t* terms        = ctx->terms;
  const mcsat_trail_t* trail = ctx->trail;
  term_manager_t* tm         = ctx->tm;
  assert(exp->csttrail.conflict_var == var); 

  // Each constraint from reasons_in will be translated into 1 forbidden interval
  // We keep them in an array of the same size as reasons_in
  uint32_t n = reasons_in->size;
  assert(n!=0);
  interval_t* intervals[n];

  // Variables that are going to be re-used for every item in reasons_in
  variable_t atom_i_var;
  bool       atom_i_value;
  term_t     atom_i_term;

  // We go through reasons_in
  for (uint32_t i = 0; i < n; i++) {
    
    atom_i_var   = reasons_in->data[i];
    atom_i_value = trail_get_boolean_value(trail, atom_i_var);
    atom_i_term  = variable_db_get_term(ctx->var_db, atom_i_var);

    assert(good_term(terms,atom_i_term) && is_pos_term(atom_i_term));
    assert(is_boolean_term(terms, atom_i_term));
    
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "\nbv_arith treats core constraint (%s): ",atom_i_value?"T":"F");
      ctx_trace_term(ctx, atom_i_term);
    }

    // reasons_out always contains reasons_in:
    ivector_push(reasons_out, atom_i_value?atom_i_term:not_term(terms, atom_i_term));

    composite_term_t* atom_i_comp = composite_term_desc(terms, atom_i_term);
    assert(atom_i_comp->arity == 2);
    term_t t0 = atom_i_comp->arg[0];
    term_t t1 = atom_i_comp->arg[1];
    assert(is_pos_term(t0));
    assert(is_pos_term(t1));
    uint32_t w = term_bitsize(terms, t0);
    t0 = extract(exp, t0, w);
    t1 = extract(exp, t1, w);
    term_t t0prime = NULL_TERM;
    term_t t1prime = NULL_TERM;

    switch (term_kind(terms, atom_i_term)) {
    case BV_GE_ATOM: {  
      t0prime = t0;
      t1prime = t1;
      break;
    }
    case BV_SGE_ATOM: {  // (t0 >=s t1) is equivalent to (t0+2^{w-1} >=u t1+2^{w-1})
      t0prime = bv_arith_add_half(tm, t0);
      t1prime = bv_arith_add_half(tm, t1);
      break;
    }
    case EQ_TERM :     
    case BV_EQ_ATOM: { // equality
      t0prime = bv_arith_zero(tm, w);
      t1prime = bv_arith_sub_terms(tm, t0, t1);
      break;
    }
    default:
      assert(false);
    }

    intervals[i] = bv_arith_unit_le(exp, t1prime, t0prime, atom_i_value);

    term_t var = NULL_TERM;
    bv_arith_coeff(exp, t0prime, &var, true);
    if (var == NULL_TERM) {
      bv_arith_coeff(exp, t1prime, &var, true);
    }
    if (var != NULL_TERM && intervals[i] != NULL) {
      transform_interval(exp, &intervals[i]);
    }
  }

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "\nFinished creating the intervals. Here they are before they are sorted:\n");
    for (uint32_t i = 0; i < n; i++) {
      fprintf(out, "Scanning interval ");
      if (intervals[i] == NULL) {
        fprintf(out, "EMPTY");
      } else {
        bv_arith_interval_print(out, ctx->terms, intervals[i]);
      }
      fprintf(out, "\n");
    }
    fprintf(out, "And now after we sort them:\n");
  }

  ptr_array_sort2((void**)intervals, n, NULL, cmp_base); // We sort the intervals  
  assert(intervals[0] != NULL); // There should be at least one non-empty interval
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Looking at interval ");
    bv_arith_interval_print(out, ctx->terms, intervals[0]);
    fprintf(out, "\n");
  }
  uint32_t nonemptys = 1; // Total number of non-empty intervals is about to get computed
  uint32_t bitwidths = 1; // Total number of distinct bitwidths is about to get computed
  for (; (nonemptys < n) && (intervals[nonemptys] != NULL); nonemptys++) {
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Looking at interval ");
      bv_arith_interval_print(out, ctx->terms, intervals[nonemptys]);
      fprintf(out, "\n");
    }
    if (get_bitwidth(intervals[nonemptys-1]) != get_bitwidth(intervals[nonemptys])){
      bitwidths++;
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "Found new bitwidth %d (old was %d)\n",get_bitwidth(intervals[nonemptys]),get_bitwidth(intervals[nonemptys-1]));
      }
    }
  }

  // For each of the bitwidths we have, we record
  // - the pointer to the first interval pointer that has that bitwidth
  // - how many intervals we have of that bitwidth
  interval_t** bitwidth_intervals[bitwidths];
  uint32_t bitwidth_numbers[bitwidths];
  bitwidth_intervals[0] = intervals;
  uint32_t j = 0;
  uint32_t tmp = 1;
  for (uint32_t i = 1; i < nonemptys; i++) {
    if (get_bitwidth(intervals[i-1]) != get_bitwidth(intervals[i])) {
      bitwidth_numbers[j] = tmp; // We have tmp intervals in the jth bitwidth
      j++; // Going into the next j
      bitwidth_intervals[j] = &intervals[i];// First interval of the jth bitwidth is this
      tmp = 0; // Re-initialising counter for the new bitwidth
    }
    tmp++;
  }
  bitwidth_numbers[j] = tmp; // We have tmp intervals of the smallest bitwidth
  
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "\nWe now look at the %d forbidden intervals we have collected (of %d different bitwidths), which are\n",nonemptys,bitwidths);
    for (uint32_t j = 0; j < bitwidths; j++) { // Looping on different bitwidths
      fprintf(out, "%d intervals of bitwidth %d:\n",
              bitwidth_numbers[j], get_bitwidth(bitwidth_intervals[j][0]));
      for (uint32_t i = 0; i < bitwidth_numbers[j]; i++) {
        bv_arith_interval_print(out, ctx->terms, bitwidth_intervals[j][i]);
        fprintf(out, "\n");
      }
    }
    fprintf(out, "\n");
  }

  /* All atoms in reasons_in have been treated, the resulting forbidden intervals for the
  var have been pushed in the heap. It's now time to look at what's in the heap. */

  ivector_t cover_output; // where the call to cover should place literals
  init_ivector(&cover_output, 0);
  cover(exp, &cover_output, bitwidths-1, bitwidth_intervals, bitwidth_numbers, NULL, substitution);
  ivector_add(reasons_out, cover_output.data, cover_output.size);
  delete_ivector(&cover_output);
  
  // Now we destruct all intervals
  for (uint32_t i = 0; i < nonemptys; i++) {
    bv_arith_interval_destruct(intervals[i]);
  }

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Returned reasons are:\n");
    for (uint32_t i = 0; i < reasons_out->size; i++) {
      fprintf(out,"[%d]",i);
      ctx_trace_term(ctx, reasons_out->data[i]);
      /* if (i>0) fprintf(out,", "); */
      /* term_print_to_file(out, terms, reasons_out->data[i]); */
    }
    fprintf(out,"\n");
  }
}

static
void explain_conflict(bv_subexplainer_t* this, const ivector_t* conflict_core, variable_t conflict_var, ivector_t* conflict) {
  bvarith_explain(this, conflict_core, conflict_var, conflict, NULL);
}

/**
   Detection of whether a conflict is within the fragment, and external API
**/

static
bool can_explain_conflict(bv_subexplainer_t* this, const ivector_t* conflict_core, variable_t conflict_var) {
  
  // Standard abbreviations
  arith_t* exp               = (arith_t*) this;
  bv_csttrail_t* csttrail    = &exp->csttrail;
  plugin_context_t* ctx      = this->ctx;
  term_table_t* terms        = ctx->terms;

  // We're facing a new problem, with a trail we don't know
  // We must reset the cache & co.
  // which date back from a previous conflict or propagation
  bv_evaluator_csttrail_reset(csttrail, conflict_var);
  int_hmap_reset(&exp->norm_cache);
  int_hmap_reset(&exp->coeff1_cache);
  int_hmap_reset(&exp->coeffm1_cache);

  
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "bv_arith looks at new conflict of size %d\n\n",conflict_core->size);
  }


  // We go through the conflict core
  for (uint32_t i = 0; i < conflict_core->size; i++) {
      
    // Atom and its term
    variable_t atom_var   = conflict_core->data[i];
    term_t     atom_term  = variable_db_get_term(ctx->var_db, atom_var);

    assert(is_pos_term(atom_term));

    if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "bv_arith looks at whether constraint %d is in the fragment: ",i);
      ctx_trace_term(ctx, atom_term);
      fprintf(out, "with the conflict_variable being ");
      ctx_trace_term(ctx, csttrail->conflict_var_term);
    }

    switch (term_kind(terms, atom_term)) {
    case EQ_TERM : 
    case BV_EQ_ATOM:
    case BV_GE_ATOM: 
    case BV_SGE_ATOM: {
      composite_term_t* atom_comp = composite_term_desc(terms, atom_term);
      assert(atom_comp->arity == 2);
      term_t t0 = atom_comp->arg[0];
      term_t t1 = atom_comp->arg[1];
      if (!is_pos_term(t0) || !is_pos_term(t1))
        return false;
      // OK, maybe we can treat the constraint atom_term. We first scan the atom (collecting free variables and co.)
      bv_evaluator_csttrail_scan(csttrail, atom_var);
      
      // Now that we have collected the free variables, we look into the constraint structure
      term_t var0 = NULL_TERM;
      term_t var1 = NULL_TERM;
      int32_t t0_coeff = bv_arith_coeff(exp, t0, &var0, false);
      int32_t t1_coeff = bv_arith_coeff(exp, t1, &var1, false);
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "can_explain gets coefficients %d and %d\n", t0_coeff, t1_coeff);
      }
      if ((t0_coeff == 2) || (t1_coeff == 2) || (t0_coeff * t1_coeff == -1)) {
        // Turns out we actually can't deal with the constraint. We stop
        return false;
      }
      if ((t0_coeff * t1_coeff == 1) && (var0 != var1)) {
        if ((term_kind(terms,var0) != BV_ARRAY) || (term_kind(terms,var1) != BV_ARRAY)) {
          return false;
        }
        uint32_t w = term_bitsize(terms, t0);
        var0 = extract(exp, var0, w);
        var1 = extract(exp, var1, w);
        uint32_t varbits0, varbits1;
        term_t head0, head1;
        lower_bit_extract_base(exp,var0,w,&head0,&varbits0);
        lower_bit_extract_base(exp,var1,w,&head1,&varbits1);
        if (varbits0 != varbits1) return false;
        if (head0 == NULL_TERM && head1 != NULL_TERM) return false;
        if (head1 == NULL_TERM && head0 != NULL_TERM) return false;
        composite_term_t* desc0 = bvarray_term_desc(terms, var0);
        composite_term_t* desc1 = bvarray_term_desc(terms, var1);
        for (uint32_t u = 0; u < varbits0; u++){
          if (desc0->arg[u] != desc1->arg[u]) return false;
        }
      }
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "with monom variables\n");
        if (t0_coeff != 0) ctx_trace_term(ctx, var0);
        fprintf(out, "and\n");
        if (t1_coeff != 0) ctx_trace_term(ctx, var1);
      }
      break;
    }
    default:
      return false;
    } 
  }
  return true;
}

static
bool can_explain_propagation(bv_subexplainer_t* this, const ivector_t* reasons, variable_t x) {
  // Just use the conflict filter
  return can_explain_conflict(this, reasons, x);
}

static
term_t explain_propagation(bv_subexplainer_t* this, const ivector_t* reasons_in, variable_t x, ivector_t* reasons_out) {
  term_t result = NULL_TERM ;
  bvarith_explain(this, reasons_in, x, reasons_out, &result);
  return result;
}

static
void destruct(bv_subexplainer_t* this) {
  arith_t* exp = (arith_t*) this;
  bv_evaluator_csttrail_destruct(&exp->csttrail);
  delete_int_hmap(&exp->norm_cache);
  delete_int_hmap(&exp->coeff1_cache);
  delete_int_hmap(&exp->coeffm1_cache);
}

/** Allocate the sub-explainer and setup the methods */
bv_subexplainer_t* arith_new(plugin_context_t* ctx, watch_list_manager_t* wlm, bv_evaluator_t* eval) {

  arith_t* exp = safe_malloc(sizeof(arith_t));

  bv_subexplainer_construct(&exp->super, "mcsat::bv::explain::arith", ctx, wlm, eval);
  bv_evaluator_csttrail_construct(&exp->csttrail, ctx, wlm);
                                
  exp->super.can_explain_conflict = can_explain_conflict;
  exp->super.explain_conflict = explain_conflict;
  exp->super.can_explain_propagation = can_explain_propagation;
  exp->super.explain_propagation = explain_propagation;
  exp->super.destruct = destruct;

  init_int_hmap(&exp->norm_cache, 0);
  init_int_hmap(&exp->coeff1_cache, 0);
  init_int_hmap(&exp->coeffm1_cache, 0);

  return (bv_subexplainer_t*) exp;
}
