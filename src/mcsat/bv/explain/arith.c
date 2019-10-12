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
#include "utils/ptr_stack.h"
#include "utils/int_hash_map.h"
#include "utils/int_hash_map2.h"
#include "utils/pair_hash_map.h"
#include "utils/ptr_array_sort2.h"

#include "mcsat/bv/bv_utils.h"
#include "arith_utils.h"
#include "bv_intervals.h"
#include "arith.h"


/**
   Extracting bits and coefficients from terms.
**/

// The following structure is produced by function analyse below,
// which analyses a term t (that is NOT a BV_POLY or a BV64_POLY)
// on its w lowest bits.
// Those w bits split into 3 sections: prefix . central_section . suffix
// In (a normalised version of) t's lowest w bits,
// the bits in prefix and suffix are all evaluable in the current context,
// while the first and last bit of the central section aren't.
// In case all bits are evaluable, the central section has length 0 and,
// by convention, the w bits form the suffix (while the prefix also has length 0).

typedef struct termstruct_s {

  // Field suffix is the length of the suffix section.
  // i.e. t[suffix] is the lowest bit of t that isn't evaluable.
  // suffix is w if all bits below w are evaluable
  uint32_t suffix;
  
  // Field length is the length of the central section.
  // t[suffix+length-1] is the highest bit of t that isn't evaluable.
  // length is 0 if all bits below w are evaluable
  uint32_t length;

  // Term e has bitwidth w and contains the prefix, the suffix, while all bits of the central section are set to 0.
  // More precisely (and assuming that t is normalised):
  // - the suffix bits e[0] ... e[suffix-1] are the bits t[0] ... t[suffix-1]
  // - the length bits e[suffix] ... e[suffix+length-1] are 0 ... 0
  // - the remaining bits e[suffix+length] ... e[w-1] are the bits t[suffix+length] ... t[w-1]
  term_t e; 
  
  // Term base has bitwidth at least length
  // Bits base[start] ... base[start+length-1] are (equal to, in the BV-theory) t[suffix] ... t[suffix+length-1]
  term_t base;  
  uint32_t start;

  bool intros;  // whether new constructs have been introduced because negated bits or sign-extensions were found in the original t's central section
  bool nobueno; // if true, term t (in its lowest w bits) is outside the fragment of this explainer.

} termstruct_t;

// Data resulting from the analysis (as performed by bv_arith_coeff) of a bv polynomial where only one monomial is unevaluable

typedef struct polypair_s {
  term_t var;      // Only monomial that is not evaluable (is NULL_TERM iff coeff==0 iff all monomials are evaluable)
  int32_t coeff;   // Coeff of that monomial (1,-1,0)
  term_t polyrest; // Rest of the polynomial, so that original term is coeff*var + polyrest; can be 0, but is never NULL_TERM unless t was a bad term
} polypair_t;

/**
   Subexplainer type
**/

// In what follows, there's a notion of normalisation via which
// t<w> propagates the lower bit extraction down to variables if t is not evaluable

typedef struct arith_s {

  /** Interfact of the subexplainer */
  bv_subexplainer_t super;

  bv_csttrail_t csttrail; // Where we keep some cached values

  // Cache of variable analyses (function analyse below): for a pair of keys (t,w), the value is the termstruct_t resulting from analysing t up to w
  pmap_t var_cache;
  // Cache of term normalisations (function extract below): for a pair of keys (t,w), the value is the normal form of t<w>
  int_hmap2_t norm_cache;
  // Cache of polynomial analyses (function bv_arith_coeff below): for a (normalised) term t (the key), the value is the polypair_t resulting from analysing t
  ptr_hmap_t coeff_cache;

} arith_t;

// Two of those hash maps (var_cache and coeff_cache) have dynamically allocated values
// So before resetting or deleting those hash maps, one must free the memory of the stored values
// which the following function does

static inline void freeval(arith_t* exp) {
  for (pmap_rec_t* current = pmap_first_record(&exp->var_cache);
       current != NULL;
       current = pmap_next_record(&exp->var_cache, current)) {
    safe_free((termstruct_t*) current->val);
  }
  for (ptr_hmap_pair_t* current = ptr_hmap_first_record(&exp->coeff_cache);
       current != NULL;
       current = ptr_hmap_next_record(&exp->coeff_cache, current)) {
    safe_free((polypair_t*) current->val);
  }
}

// The following two functions are mutually recursive

term_t extract(arith_t* exp, term_t t, uint32_t w);

termstruct_t* analyse(arith_t* exp, term_t t, uint32_t w){

  plugin_context_t* ctx = exp->super.ctx;
  term_manager_t* tm    = ctx->tm;
  term_table_t* terms   = ctx->terms;

  assert(w <= term_bitsize(terms, t));

  pmap_rec_t* entry = pmap_get(&exp->var_cache, t, w);
  assert(entry != NULL);
  termstruct_t* result = (termstruct_t*) entry->val;
  if (result != DEFAULT_PTR) {
    assert (result != NULL);
    return result;
  }

  result = safe_malloc(sizeof(termstruct_t));
  entry->val = (void*) result;
  result->suffix  = w;
  result->length  = 0;
  result->start   = 0;
  result->base    = NULL_TERM;
  result->intros  = false;
  result->nobueno = false;
  bool ignore_this_bool;

  switch (term_kind(terms, t)) {
  case BV_POLY:
  case BV64_POLY:
    assert(false);
  case BV_ARRAY: {  // Concatenated boolean terms
    composite_term_t* concat_desc = bvarray_term_desc(terms, t);

    // Hand-made hash map (we want it light, non-redimensionable,
    // and we can do so because we know the max size is w).
    // In each cell i, there are 4 integers:
    // preproc[i][0] is the key, which is a term_t, let's call it k
    // preproc[i][1] is the maximum i such that k[i] is a bit of this bv_array, let's call it top; then:
    // preproc[i][1] is the term_t extract(k,top+1) (normalised version of k over the lowest top+1 bits), let's call it norm
    // preproc[i][2] is the value returned by bv_evaluator_is_evaluable_topbit(norm)
    // preproc[i][3] is the term_t extract(norm,maxeval), if maxeval is not 0
    uint32_t preproc[w][4];
    // We initialise the hashmap
    for (uint32_t i = 1; i <= w; i++) {
      preproc[i][0] = NULL_TERM;
    }

    // Now we range over the bits of the t bv_array of the form base[index], and we fill-in preproc[*][0] and preproc[*][1]
    for (uint32_t i = 0; i < w; i++) {
      term_t t_i = concat_desc->arg[i];        // The Boolean term that constitutes bit i of t
      if (term_kind(terms, t_i) == BIT_TERM) { // Is it of the form base[index] ?
        uint32_t index = bit_term_index(terms, t_i);  // Get selected bit
        term_t base    = bit_term_arg(terms, t_i);    // Get the base
        uint32_t key_index = base % w;
        while (preproc[key_index][0] != NULL_TERM && preproc[key_index][0] != base) {
          // We look for the cell containing information of key "base", or the first empty cell
          key_index++;
          key_index = key_index % w;
        }
        if (preproc[key_index][0] == NULL_TERM
            || preproc[key_index][1] < index)
          preproc[key_index][1] = index;
        if (preproc[key_index][0] == NULL_TERM)
          preproc[key_index][0] = base;
      }
    }

    // Now we fill-in preproc[*][1], preproc[*][2], preproc[*][3]
    for (uint32_t i = 0; i < w; i++) {
      if (preproc[i][0] != NULL_TERM) {
        uint32_t size = preproc[i][1] + 1;
        preproc[i][1] = extract(exp, preproc[i][0], size);
        preproc[i][2] = bv_evaluator_is_evaluable_topbit(&exp->csttrail, preproc[i][1], &ignore_this_bool);
        if (preproc[i][2] > 0) {
          preproc[i][3] = (preproc[i][2] == size) ? preproc[i][1] : extract(exp, preproc[i][0], preproc[i][2]);
        }
      }
    }
    
    term_t ebits[w]; // Where we build result->e
    term_t cbits[w]; // Where we build the central section, if the term is bad
    uint32_t shortlength  = 0;         // Number of bits of the central section of t, excluding sign-extension bits
    term_t signbit        = NULL_TERM; // The sign bit of the central section of t
    bool is_negated       = false; // whether the first bit of the central section is negated
    
    // We inspect each bit of the bv_array
    for (uint32_t i = 0; i < w; i++) {

      term_t t_i = concat_desc->arg[i]; // The Boolean term that constitutes that bit

      if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "bit %d is ",i);
        ctx_trace_term(ctx, t_i);
      }

      bool isneg = is_neg_term(t_i); // Whether the boolean term is negated

      // We'll test whether this bit can be evaluated
      bool evaluable;

      if (term_kind(terms, t_i) != BIT_TERM) {
        evaluable = bv_evaluator_is_evaluable(&exp->csttrail, t_i, &ignore_this_bool);
        if (!evaluable) // Ouch, a bit that's not a bit-select and that's not evaluable makes the whole term BAD
          result->base = NULL_TERM;
      } else {
        uint32_t index = bit_term_index(terms, t_i); // Get selected bit
        term_t base    = bit_term_arg(terms, t_i);   // Get the base
        uint32_t key_index = base % w;
        while (preproc[key_index][0] != base) {
          // We look for the cell containing information of key "base"
          key_index++;
          key_index = key_index % w;
        }
        evaluable = (index < preproc[key_index][2]);
        if (evaluable) { // If it is evaluable up to index,
          base = preproc[key_index][3]; // then the normalised base is this
        } else {         // If it is not evaluable up to that index...
          base = preproc[key_index][1]; // then the normalised base is this
          if (result->length == 0) { // This is the first unevaluable bit
            result->base  = base;
            result->start = index;
          }
          // Now we look at whether this bit, necessarily from the central section, is good
          if (base != result->base                                   // Not the right base
              || (index - result->start) != (i - result->suffix) ) { // Not the right index
            result->base = NULL_TERM;    // in both cases, the term is BAD
          }
        }
        t_i = mk_bitextract(tm, base, index);
        if (isneg) t_i = not_term(terms, t_i); // Same polarity as the original t_i
      }

      if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "bit %d is simplified (and is %s) to ", i, evaluable ? "evaluable" : "non-evaluable");
        ctx_trace_term(ctx, t_i);
      }

      // Now we look at whether that bit can be evaluated
      if (evaluable) {
        if (result->length == 0) // Still in suffix
          result->suffix ++;     // We increase suffix
      } else {
        if (result->length == 0) // This is the first unevaluable bit
          is_negated = isneg;   // It defines the polarity of the central section
        if (is_negated != isneg)   // Not the right polarity
          result->base = NULL_TERM; // The term is bad
        result->length = i;
        if (signbit != t_i) {
          shortlength = i;
          signbit = t_i;
        }
      }

      ebits[i] = t_i;
      if (result->length != 0)
        cbits[i] = is_negated ? not_term(terms, t_i) : t_i;
    }

    result->length = result->length - result->suffix;;
    shortlength = shortlength - result->suffix;;

    // Now we look at the central section between suffix and suffix+shortlength,
    // and try to build result->base and result->start
    
    if (result->base == NULL_TERM) { // If the term is bad
      result->base = mk_bvarray(tm, shortlength, &cbits[result->suffix]);
      result->start = 0;
      result->nobueno = true;
    }

    if (is_negated) { // The central cbits have flipped polarity
      result->base   = bv_arith_negate_terms(tm, bv_arith_add_one_term(tm, result->base));
      result->intros = true;
    }

    if (shortlength != result->length) {
      // This is a sign-extension,
      // base to return is (0extend(base+half(shortlength)) - 0extend(half(shortlength)))
      term_t tmp1 = bv_arith_extension(tm,
                                       bv_arith_add_half(tm, result->base),
                                       result->length);
      term_t tmp2 = bv_arith_extension(tm,
                                       bv_arith_add_half(tm, bv_arith_zero(tm, shortlength)),
                                       result->length);
      result->base   = bv_arith_sub_terms(tm, tmp1, tmp2);
      result->intros = true;
    }

    // Now we can construct the evaluable field of the result
    // We first set to 0 all bits in the central section
    for (uint32_t i = 0; i < result->length; i++)
      ebits[i+result->suffix] = false_term;
    result->e = mk_bvarray(tm, w, ebits);
    break;
  }

  default: { // Term t is now not a bv_array, nor a bv_poly nor a bv64_poly
    // There is no recursive normalization to perform
    term_t tmp = term_extract(tm, t, 0, w);
    if (bv_evaluator_is_evaluable(&exp->csttrail, t, &ignore_this_bool)) {
      result->e = tmp;
      result->suffix = w;
      result->length = 0;
      result->start  = 0;
      result->base = NULL_TERM;
    } else {
      result->e = bv_arith_zero(tm, w);
      result->suffix = 0;
      result->length = w;
      result->start  = 0;
      result->base   = tmp;
    }
  }
  }

  return result;  // Note that the result is automatically memoised
  
}

// Extracting the w lowest bits of t, normalising on the way
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
    fprintf(out, "Extracting %d lowest bits of ",w);
    term_print_to_file(out, terms, t);
    fprintf(out, "\n");
  }

  if (t == conflict_var)
    return term_extract(tm, t, 0, w);
    
  // We first look at whether the value is cached
  int_hmap2_rec_t* t_norm = int_hmap2_find(&exp->norm_cache, t, w);
  if (t_norm != NULL) return t_norm->val;

  term_t result; // This is what we return at the end, unless we exit prematurely

  // Now the result will be a sum; first first compute the number of summands
  uint32_t n_monom;
  bvpoly_t* t_poly = NULL;
  bvpoly64_t* t_poly64 = NULL;
  
  switch (term_kind(terms, t)) {
  case BV_POLY: {
    t_poly = bvpoly_term_desc(ctx->terms, t);
    n_monom = t_poly->nterms;
    break;
  }
  case BV64_POLY: {
    t_poly64 = bvpoly64_term_desc(ctx->terms, t);
    n_monom = t_poly64->nterms;
    break;
  }
  default: {
    n_monom = 1;
  }
  }

  term_t monom[n_monom]; // where we place the monomials
  bvconstant_t coeff[n_monom]; // where we place the monomials' coefficients
  uint64_t coeff64[n_monom];   // where we place the monomials' coefficients

  switch (term_kind(terms, t)) {
  case BV_POLY: {
    for (uint32_t i = 0; i < n_monom; ++ i) {
      if (w<65) {
        // If we extract fewer than 65 bits, we use uint64_t coefficients for the bv_poly to produce
        coeff64[i] = // projecting the monomial coefficient onto w bits
          (original_bitsize < 33) ? // requires an annoying case analysis, for some reason
          ( (uint64_t) bvconst_get32(t_poly->mono[i].coeff)) :
          bvconst_get64(t_poly->mono[i].coeff) ;
      } else {
        init_bvconstant(&coeff[i]);
        bvconstant_extract(&coeff[i], t_poly->mono[i].coeff, 0, w); // projecting the monomial coefficient onto w bits
      }
      monom[i] = (t_poly->mono[i].var != const_idx) ? t_poly->mono[i].var : NULL_TERM;
    }
    break;
  }
  case BV64_POLY: { // Same game, but now t is a bv64_poly, so w <= 64
    for (uint32_t i = 0; i < n_monom; ++ i) {
      coeff64[i] = t_poly64->mono[i].coeff;
      monom[i] = (t_poly64->mono[i].var != const_idx) ? t_poly64->mono[i].var : NULL_TERM;
    }
    break;
  }
  default: {
    if (w<65) {
      coeff64[0] = 1;
    } else {
      init_bvconstant(coeff);
      bvconstant_set_bitsize(coeff, w);
      bvconstant_set_one(coeff);
    }
    monom[0] = t;
  }
  }

  // Now we proceed to recursively extract the monomials

  const term_t zero_w = bv_arith_zero(tm, w);
  term_t evaluables[n_monom];
  for (uint32_t i = 0; i < n_monom; ++ i) {
    if (monom[i] != NULL_TERM) {
      assert(monom[i] <= t);
      termstruct_t* s = analyse(exp, monom[i], w);
      evaluables[i] = s->e;
      if (s->length == 0) { // The monomial is evaluable
        monom[i] = zero_w;  // The monomial should be 0
      } else {
        term_t variable[w]; // We reconstitute the variable
        uint32_t i = 0;
        for (; i < s->suffix; i++)
          variable[i] = false_bit; // suffix is 0...0
        for (; i < s->suffix + s->length; i++) // central section extracted from the base
          variable[i] = mk_bitextract(tm, s->base, i - s->suffix + s->start);
        for (; i < w; i++)
          variable[i] = false_bit; // prefix is 0...0
        monom[i] = mk_bvarray(tm, w, variable);
      }
    }
  }
      
  if (w<65) {
    // If we extract fewer than 65 bits, we use uint64_t coefficients for the bv_poly to produce
    // we construct that bv_poly from a bvarith64_buffer_t called buffer:
    bvarith64_buffer_t* buffer = term_manager_get_bvarith64_buffer(tm);
    bvarith64_buffer_prepare(buffer, w); // Setting the desired width
    // Now going into each monomial
    for (uint32_t i = 0; i < n_monom; ++ i) {
      if (monom[i] == NULL_TERM) {
        bvarith64_buffer_add_const(buffer, coeff64[i]); // constant coefficient gets added to the buffer bv_poly
      } else {
        bvarith64_buffer_add_const_times_term(buffer, terms, coeff64[i], monom[i]); // Otherwise we add the w-bit monomial to the bv_poly
        bvarith64_buffer_add_const_times_term(buffer, terms, coeff64[i], evaluables[i]); // Otherwise we add the w-bit monomial to the bv_poly
      }
    }
    result = mk_bvarith64_term(tm, buffer); // We turn the bv_poly into an actual term, and return it
  } else {
    // If we extract more than 64 bits, we use regular coefficients for the bv_poly to produce
    // we construct that bv_poly from a bvarith_buffer_t called buffer:
    bvarith_buffer_t* buffer = term_manager_get_bvarith_buffer(tm);
    bvarith_buffer_prepare(buffer, w); // Setting the desired width
    for (uint32_t i = 0; i < n_monom; ++ i) {
      if (monom[i] == NULL_TERM) {
        bvarith_buffer_add_const(buffer, coeff[i].data);// constant coefficient gets aded to the buffer bv_poly
      } else {
        bvarith_buffer_add_const_times_term(buffer, terms, coeff[i].data, monom[i]); // Otherwise we add the w-bit monomial to the bv_poly
        bvarith_buffer_add_const_times_term(buffer, terms, coeff[i].data, evaluables[i]); // Otherwise we add the w-bit monomial to the bv_poly
      }
      delete_bvconstant(&coeff[i]); //cleaning up
    }
    result = mk_bvarith_term(tm, buffer); // We turn the bv_poly into an actual term, and return it
  }
  
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Extracting %d lowest bits of ",w);
    term_print_to_file(out, terms, t);
    fprintf(out, " successfully gave ");
    term_print_to_file(out, terms, result);
    fprintf(out, "\n");
  }

  // We know what we are returning, now we just cache it for later
  int_hmap2_add(&exp->norm_cache, t, w, result);

  return result; 

}

// Function returns the polypair_t (variable, coefficient, polyrest) of (normalised) u
// if u is not a good term for the fragment:
// if !assume_fragment, function will return NULL,
// if assume_fragment, function has unspecified behaviour (but runs faster)

polypair_t* bv_arith_coeff(arith_t* exp, term_t u, bool assume_fragment) {

  plugin_context_t* ctx = exp->super.ctx;
  term_t conflict_var   = exp->csttrail.conflict_var_term;
  term_manager_t* tm    = ctx->tm;
  term_table_t* terms   = ctx->terms;

  uint32_t w = term_bitsize(terms, u);

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Extracting coefficient of unevaluable monomial in ");
    ctx_trace_term(ctx, u);
  }

  // We start by normalising the input term
  term_t t = extract(exp, u, w);
  assert(t != NULL_TERM);
  
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Normalisation successfully produced ");
    ctx_trace_term(ctx, t);
  }

  // Looking at whether the value is cached
  ptr_hmap_pair_t* entry = ptr_hmap_get(&exp->coeff_cache, t);
  assert(entry != NULL);
  polypair_t* result = (polypair_t*) entry->val;
  if (result != NULL) {
    assert(result->polyrest != NULL_TERM); // It is not marked for deletion
    return result;
  }

  result = safe_malloc(sizeof(polypair_t));
  entry->val = (void*) result;
  
  if (t == conflict_var) {
    result->var = t;
    result->coeff = 1;
    result->polyrest = bv_arith_zero(tm, w);
    return result;
  }

  bool ignore_this_bool;
  if (bv_evaluator_is_evaluable(&exp->csttrail, t, &ignore_this_bool)) {
    result->var = NULL_TERM;
    result->coeff = 0;
    result->polyrest = t;
    return result;
  }

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Not evaluable and not cached\n");
  }

  result->var   = NULL_TERM;
  result->coeff = 0;
  result->polyrest = NULL_TERM; 

  switch (term_kind(ctx->terms, t)) {
  case BV_POLY: {
    bvpoly_t* t_poly = bvpoly_term_desc(ctx->terms, t);
    for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
      term_t monom_var = t_poly->mono[i].var;
      if (monom_var == const_idx) continue;
      if (!assume_fragment
          && (bv_arith_coeff(exp, monom_var, false) == NULL)) {
        return NULL; // We're outside the fragment
      }
      if (!bv_evaluator_is_evaluable(&exp->csttrail,monom_var, &ignore_this_bool)) {
        if (result->coeff != 0) { // second unevaluable monomial?
          return NULL; // -> we're outside the fragment
        }
        if (bvconst_is_one(t_poly->mono[i].coeff, t_poly->width)) {
          result->coeff = 1;
          result->var   = monom_var;
        } else {
          if (bvconst_is_minus_one(t_poly->mono[i].coeff, t_poly->bitsize)) {
            result->coeff = -1;
            result->var   = monom_var;
          }
          else
            return NULL;
        }
        if (assume_fragment) break; // If in fragment, need not look at other monomials
      }
    }
    break;
  }
  case BV64_POLY: {
    bvpoly64_t* t_poly = bvpoly64_term_desc(ctx->terms, t);
    for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
      term_t monom_var = t_poly->mono[i].var;
      if (monom_var == const_idx) continue;
      if (!assume_fragment
          && (bv_arith_coeff(exp, monom_var, false) == NULL)) {
        return NULL; // We're outside the fragment
      }
      if (!bv_evaluator_is_evaluable(&exp->csttrail,monom_var, &ignore_this_bool)) {
        if (result->coeff != 0) { // second unevaluable monomial?
          return NULL; // -> we're outside the fragment
        }
        if (t_poly->mono[i].coeff == 1) {
          result->coeff = 1;
          result->var   = monom_var;
        } else {
          if (bvconst64_is_minus_one(t_poly->mono[i].coeff,term_bitsize(ctx->terms,t))) {
            result->coeff = -1;
            result->var   = monom_var;
          }
          else
            return NULL;
        }
        if (assume_fragment) break; // If in fragment, need not look at other monomials
      }
    }
    break;
  }
  case BV_ARRAY: {
    termstruct_t* ts = analyse(exp,t,w);
    if (ts->nobueno) return NULL;
    assert(ts->length > 0); // Otherwise t would be evaluable (already checked)
    assert(ts->base != NULL_TERM);
    assert(bv_arith_is_zero(terms, ts->e));
    assert(!ts->intros);    // Should not have introduced new constructs
    
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "top-level base is ");
      ctx_trace_term(ctx, ts->base);
    }

    if (ts->base == t)
      return NULL;

    if (!assume_fragment // If we don't know we are in the fragment
        && ts->base != t // and base is a subterm of t, we recursively check
        && (bv_arith_coeff(exp, ts->base, false) == NULL)) { // whether base is in the fragment
      assert(ts->base < t);
      return NULL; // We're outside the fragment
    }

    // OK, now we know or we assume we are in the fragment
    result->var = t;   // the result->var is t
    result->coeff = 1; // with coeff 1
    break;
  }
  default: {
    return NULL;
  }
  }
  
  assert(result->var != NULL_TERM);
  assert(result->coeff == 1 || result->coeff == -1);

  result->polyrest = (result->coeff == 1) ?
    bv_arith_sub_terms(tm, t, result->var) :
    bv_arith_add_terms(tm, t, result->var) ;
  
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Coefficient is %d\n",result->coeff);
    fprintf(out, "Variable is ");
    ctx_trace_term(ctx, result->var);
    fprintf(out, "Polyrest is ");
    ctx_trace_term(ctx, result->polyrest);
  }
  return result; // Memoisation automatically done
}




/**
   Explanation mechanism. First for 1 constraint. Then for the whole conflict
**/

// Analyses one side of an atom, assumed to be in the fragment.
// polyrest is the polyrest of the side, cc is a non-initialised bv_constant that is the evaluation of polyrest
void bv_arith_init_side(arith_t* exp, term_t polyrest, bvconstant_t* cc) {

  // Standard abbreviations
  plugin_context_t* ctx = exp->super.ctx;

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Initialising constraint_side ");
    term_print_to_file(out, ctx->terms, polyrest);
    fprintf(out, "\n");
  }

  // We evaluate this...
  uint32_t eval_level = 0;
  const mcsat_value_t* value = bv_evaluator_evaluate_term(exp->super.eval, polyrest, &eval_level);
  assert(value->type == VALUE_BV);

  /// ...copy it into cc
  init_bvconstant(cc);
  bvconstant_copy(cc, value->bv_value.bitsize, value->bv_value.data);

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "We have c: ");
    term_print_to_file(out, ctx->terms, polyrest);
    fprintf(out, " with value cc: ");
    bvconst_print(out, cc->data, cc->bitsize);
    fprintf(out, "\n");
  }

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
  polypair_t* left  = bv_arith_coeff(exp, lhs, true);
  polypair_t* right = bv_arith_coeff(exp, rhs, true);
    
  if ((left->coeff == -1) || (right->coeff == -1)) {
    // if coeff is negative, we add one, negate and swap sides.
    term_t nlhs = bv_arith_negate_terms(tm, bv_arith_add_one_term(tm, lhs));
    term_t nrhs = bv_arith_negate_terms(tm, bv_arith_add_one_term(tm, rhs));
    return bv_arith_unit_le(exp, nrhs, nlhs, b);
  }

  // Setting c1 and c2 to be 2 terms representing the left polynomial and the right polynomial,
  // from which the confict variable (if present) was removed,
  // and evaluating those polynomials c1 and c2 (whose variables should all have values on the trail)
  term_t c1 = left->polyrest;
  term_t c2 = right->polyrest;
  bvconstant_t cc1, cc2;
  bv_arith_init_side(exp, c1, &cc1);
  bv_arith_init_side(exp, c2, &cc2);

  assert(left->var == NULL_TERM || right->var == NULL_TERM || left->var == right->var);
  term_t var = (left->var == NULL_TERM) ? right->var : left->var;

  if (var != NULL_TERM && ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "\nMonomial variable is\n");
    ctx_trace_term(ctx, var);
    fprintf(out, "\n");
  }


  // Now we are sure that on both sides, coefficient is either 0 or 1
  // we check which one:
  bool left_has  = (left->coeff == 1);
  bool right_has = (right->coeff == 1);

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
        result = bv_interval_mk(&exp->super, &lo, &hi, lo_term, hi_term, var, NULL_TERM);
      if (!b) {
        if (!bvconstant_eq(&lo,&hi))
          result = bv_interval_mk(&exp->super, &hi, &lo, hi_term, lo_term, var, NULL_TERM);
        else {
          term_t reason = bv_arith_eq(tm, lo_term, hi_term);
          result = bv_interval_full_mk(&exp->super, reason, w);
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
        result = bv_interval_mk(&exp->super, &lo, &hi, lo_term, hi_term, var, NULL_TERM);
      if (!b) {
        if (!bvconstant_eq(&lo,&hi))
          result = bv_interval_mk(&exp->super, &hi, &lo, hi_term, lo_term, var, NULL_TERM);
        else {
          term_t reason = bv_arith_eq(tm, lo_term, hi_term);
          result = bv_interval_full_mk(&exp->super, reason, w);
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
        result = bv_interval_mk(&exp->super, &lo, &hi, lo_term, hi_term, var, NULL_TERM);
      if (!b) {
        if (!bvconstant_eq(&lo,&hi))
          result = bv_interval_mk(&exp->super, &hi, &lo, hi_term, lo_term, var, NULL_TERM);
        else {
          term_t reason = bv_arith_eq(tm, lo_term, hi_term);
          result = bv_interval_full_mk(&exp->super, reason, w);
        }
      }
    } else { // x appears on neither sides
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "Case <=: !has_right, !has_left");
      }
      if (b && bvconstant_lt(&cc2,&cc1)) { // If c2 < c1, we forbid everything, otherwise we forbid nothing
        term_t reason = bv_arith_lt(tm, c2, c1);
        result = bv_interval_full_mk(&exp->super, reason, w);
      }
      if (!b && bvconstant_le(&cc1,&cc2)) { // If c2 < c1, we forbid everything, otherwise we forbid nothing
        term_t reason = bv_arith_le(tm, c1, c2);
        result = bv_interval_full_mk(&exp->super, reason, w);
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
    bv_interval_print(out, ctx->terms, i);
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
    /* assert(!bv_evaluator_evaluate_term(&exp->super.eval, not_term(tm->terms,continuity_reason), &eval_level)->b); */
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
    bv_interval_print(out, ctx->terms, intervals[i]);
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
    bv_interval_print(out, terms, longest);
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
      bv_interval_print(out, terms, longest);
      fprintf(out, "\n");
    }
  }

  // The lower bound of the longest interval, &longest->lo, will serve as the baseline of the domain for the rest of this function.
  // We sort intervals according to that baseline:
  // as all intervals here have the same bitwidth, the first intervals are those whose lower bound is just after the baseline.
  ptr_array_sort2((void **)intervals[0], n, &longest->lo, bv_interval_cmp);
  
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "After sorting with baseline: ");
    bvconst_print(out, longest->lo.data, longest->lo.bitsize);
    fprintf(out, "\n");
    print_intervals(ctx, intervals[0], n);
  }

  // If we have an interval inherited from bigger bitwidths, we "insert it" in the now sorted array, so that the result is sorted.
  // we never actually construct the resulting array in memory: we leave the sorted array untouched,
  // identify which index the inherited interval would have if inserted,
  // and then in the rest of this function we use the custom access function get_interval to access the virtual array.
  bool result = false; // As far as we know, we are not using inherited
  int32_t inherited_index = -1; //
  if (inherited != NULL) {
    inherited_index++;
    for(uint32_t j = 0; j < n; j++){
      if (bv_interval_cmp(&longest->lo, intervals[0][j], inherited)) {
        inherited_index++;
      }
    }
    n++; // one more interval to consider
  }

  // First interval in the virtual array is always the longest.
  // It is the first one we consider in the upcoming loop.
  assert(longest == get_interval(intervals[0],inherited,inherited_index,0));

  // The elements saved in output so far forbid conflict_var[w] to be in [first->lo; saved_hi[
  interval_t* first = NULL;
  bvconstant_t* saved_hi = &longest->hi;
  term_t saved_hi_term = longest->hi_term;

  // The best interval found so far in intervals[0], but not yet saved in output,
  // that can be used to forbid the greatest number of bv values beyond saved_hi
  // We know that we can forbid conflict_var[w] to be in [longest->lo; best_so_far->hi[,
  // which contains [first->lo; saved_hi[

  interval_t* best_so_far = NULL;
  bool notdone = true;

  // We loop over all intervals of that bitwidth, starting with the longest.
  for(uint32_t j = 0; notdone && j <= n; ){

    interval_t* i = get_interval(intervals[0],inherited,inherited_index,j%n);

    if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "\nbv_arith looks at interval of index %d among %d (inherited has index %d) ",j,n,inherited_index);
      bv_interval_print(out, terms, i);
      fprintf(out, "\n");
    }

    if (bv_interval_is_in(saved_hi,i)) { // In continuity of previously forbidden range
      // Does i eliminate more values than best_so_far?
      if ((best_so_far == NULL)
          || ((best_so_far != NULL) && bv_interval_is_in(&best_so_far->hi, i))) { // i becomes best_so_far
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
          bv_interval_print(out, terms, best_so_far);
          fprintf(out, "\n");
        }
        if (first == NULL && bv_interval_is_in(&longest->hi,best_so_far)) {
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
        if (bv_interval_is_in(&best_so_far->hi,longest)) {
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
        if (bv_interval_is_in(saved_hi,longest)) notdone = false;
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
      bv_interval_construct(&exp->super, &lo, &hi, lo_term, hi_term, NULL_TERM, NULL_TERM, &hole);
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "OK, now there is a hole: ");
        bv_interval_print(out, terms, &hole);
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
        bv_interval_construct(&exp->super, &hi_proj, &lo_proj, hi_proj_term, lo_proj_term, NULL_TERM, NULL_TERM, &hole_complement);
        if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
          FILE* out = ctx_trace_out(ctx);
          fprintf(out, " < ");
          bvconst_print(out, smaller_values.data, smaller_values.bitsize);
          fprintf(out, "\nHole is smaller than the domain of the next bitwidth, we recursively call cover on complemented and projected hole: ");
          bv_interval_print(out, terms, &hole_complement);
          fprintf(out, "\n");
        }
        hole_used = cover(exp, &rec_output,
                          bitwidths-1, &intervals[1], &numbers[1],
                          &hole_complement,
                          (substitution != NULL && rec_substitution == NULL_TERM) ? &rec_substitution : NULL);
        bv_interval_delete(&hole_complement);
        delete_bvconstant(&lo_proj);
        delete_bvconstant(&hi_proj);
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
        if (bv_interval_is_in(saved_hi,longest)) notdone = false;
      }
      ivector_add(output, rec_output.data, rec_output.size);
      delete_ivector(&rec_output);
      delete_bvconstant(&lo);
      delete_bvconstant(&hi);
      delete_bvconstant(&smaller_values);
      bv_interval_delete(&hole);
    }
  }

  if (saved_hi_term != NULL_TERM) {
    if (best_so_far != NULL && first != NULL && bv_interval_is_in(saved_hi,first)) {
      // We didn't actually need longest, best_so_far plays the role of longest
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "No need for longest interval, as saved_hi is ");
        bvconst_print(out, saved_hi->data, saved_hi->bitsize);
        fprintf(out, "\nand first is ");
        bv_interval_print(out, terms, first);
        fprintf(out, "\n");
      }
      bv_arith_add2conflict(exp, saved_hi_term, first, output);
      if (first == inherited) { result = true; } // inherited was used
    } else {
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "Adding to conflict longest interval ");
        bv_interval_print(out, terms, longest);
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
          bv_interval_print(out, terms, longest);
          fprintf(out, "\n");
          bv_interval_print(out, terms, first);
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
  bv_evaluator_t* eval  = &exp->super.eval;
  term_manager_t* tm    = ctx->tm;
  term_table_t* terms   = ctx->terms;

  if (!is_full(interval[0])) {
  
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Transforming interval ");
      bv_interval_print(out, ctx->terms, interval[0]);
      fprintf(out, "\nNow analysing the shape of the conflict variable:\n");
    }

    uint32_t w = term_bitsize(terms, interval[0]->var);

    // We analyse the shape of the variable whose value is forbidden to be in interval[0]
    termstruct_t ts;
    analyse(exp,interval[0]->var,0,w,&ts);
    assert(ts.length != 0);
    assert(ts.base != NULL_TERM);

    if (ts.length < w) {
      // The variable is a proper extension of something (otherwise we do nothing)
      bvconstant_t smaller_width; // smaller_width: how many values of bitwidth ts.length?
      init_bvconstant(&smaller_width);
      bvconstant_set_all_zero(&smaller_width, w);
      bvconst_set_bit(smaller_width.data, ts.length); 
      bvconstant_normalize(&smaller_width);
      term_t smaller_width_term = mk_bv_constant(tm, &smaller_width);
      term_t t0 = bv_arith_sub_terms(tm, interval[0]->lo_term, head);
      term_t t1 = bv_arith_sub_terms(tm, interval[0]->hi_term, head);

      uint32_t ignore_this_int = 0;

      const mcsat_value_t* v0 = bv_evaluator_evaluate_term(eval, t0, &ignore_this_int);
      assert(v0->type == VALUE_BV);
      term_t lo_term, lo_reason;
      if (bvconstant_lt(&v0->bv_value,&smaller_width)) {
        lo_term   = term_extract(tm, interval[0]->lo_term, 0, ts.length);
        lo_reason = bv_arith_lt(tm, t0, smaller_width_term);
      } else {
        lo_term   = bv_arith_zero(tm, ts.length);
        lo_reason = bv_arith_le(tm, smaller_width_term, t0);
      }

      const mcsat_value_t* v1 = bv_evaluator_evaluate_term(eval, t1, &ignore_this_int);
      assert(v1->type == VALUE_BV);
      term_t hi_term, hi_reason;
      if (bvconstant_lt(&v1->bv_value,&smaller_width)) {
        hi_term   = term_extract(tm, interval[0]->hi_term, 0, ts.length);
        hi_reason = bv_arith_lt(tm, t1, smaller_width_term);
      } else {
        hi_term   = bv_arith_zero(tm, ts.length);
        hi_reason = bv_arith_le(tm, smaller_width_term, t1);
      }

      delete_bvconstant(&smaller_width);

      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "ts.length is %d and head is ",ts.length);
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

      interval_t* result = bv_interval_mk(&exp->super,NULL,NULL,lo_term,hi_term,NULL_TERM,NULL_TERM);

      if (is_full(result)) { // Interval on smaller bitwidth is full or empty
        bv_interval_destruct(result);
        const mcsat_value_t* head_v =
          bv_evaluator_evaluate_term(eval, head, &ignore_this_int);
        assert(head_v->type == VALUE_BV);
        if (bv_interval_is_in(&head_v->bv_value, interval[0])) {
          term_t reason = bv_arith_lt(tm,
                                      bv_arith_sub_terms(tm, head, interval[0]->lo_term),
                                      bv_arith_sub_terms(tm, interval[0]->hi_term, interval[0]->lo_term)
                                      );
          result = bv_interval_full_mk(&exp->super, reason, ts.length);
        } else {
          assert(false);
          result = NULL;
        }
      }

      ivector_add(&result->reasons, interval[0]->reasons.data, interval[0]->reasons.size);
      bv_interval_destruct(interval[0]);
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

      // The new variable that shouldn't be in interval[0] is ts.base
      // with one of two situations:
      // - ts.base is y<ts.length> where y is the conflict variable itself
      // - ts.base is a bv_poly (lower bits extraction has been pushed)
      // - or in case the original variable was a sign-extension,
      // we could get back a BV_ARRAY again in some very specific cases (see bug#142)
      // We only have to do something if it is a bv_poly or a bv_array
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "New variable is ");
        term_print_to_file(out, tm->terms, ts.base);
        fprintf(out, "\n");
      }

      switch (term_kind(terms, ts.base)) {
      case BV_ARRAY:
      case BV_POLY:
      case BV64_POLY: {
        assert(term_bitsize(terms,ts.base) == ts.length);
        assert(term_bitsize(terms,interval[0]->lo_term) == ts.length);
        assert(term_bitsize(terms,interval[0]->hi_term) == ts.length);
        term_t new_var = NULL_TERM;
        int32_t coeff = bv_arith_coeff(exp, ts.base, &new_var, true);
        assert(coeff == 1 || coeff == -1);
        bvconstant_t cc;
        term_t rest = bv_arith_init_side(exp, ts.base, coeff, &new_var, &cc);
        assert(term_bitsize(terms,rest) == ts.length);
        delete_bvconstant(&cc);
        lo_term = bv_arith_sub_terms(tm, interval[0]->lo_term, rest);
        hi_term = bv_arith_sub_terms(tm, interval[0]->hi_term, rest);
        if (coeff == 1) {
          result = bv_interval_mk(&exp->super,NULL,NULL,lo_term,hi_term,new_var,NULL_TERM);
        } else {
          term_t new_lo_term =
            bv_arith_add_one_term(tm,bv_arith_negate_terms(tm, hi_term));
          term_t new_hi_term =
            bv_arith_add_one_term(tm,bv_arith_negate_terms(tm, lo_term));
          result = bv_interval_mk(&exp->super,NULL,NULL,new_lo_term,new_hi_term,new_var,NULL_TERM);
        }

        ivector_add(&result->reasons, interval[0]->reasons.data, interval[0]->reasons.size);
        bv_interval_destruct(interval[0]);
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
        bv_interval_print(out, ctx->terms, intervals[i]);
      }
      fprintf(out, "\n");
    }
    fprintf(out, "And now after we sort them:\n");
  }

  ptr_array_sort2((void**)intervals, n, NULL, bv_interval_cmp); // We sort the intervals  
  assert(intervals[0] != NULL); // There should be at least one non-empty interval
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Looking at interval ");
    bv_interval_print(out, ctx->terms, intervals[0]);
    fprintf(out, "\n");
  }
  uint32_t nonemptys = 1; // Total number of non-empty intervals is about to get computed
  uint32_t bitwidths = 1; // Total number of distinct bitwidths is about to get computed
  for (; (nonemptys < n) && (intervals[nonemptys] != NULL); nonemptys++) {
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Looking at interval ");
      bv_interval_print(out, ctx->terms, intervals[nonemptys]);
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
        bv_interval_print(out, ctx->terms, bitwidth_intervals[j][i]);
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
    bv_interval_destruct(intervals[i]);
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
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::count")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "A job well done\n");
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

  uint32_t result = true;
  
  // We're facing a new problem, with a trail we don't know
  // We must reset the cache & co.
  // which date back from a previous conflict or propagation
  bv_evaluator_csttrail_reset(csttrail, conflict_var);
  freeval(exp);
  pmap_reset(&exp->var_cache);
  reset_int_hmap2(&exp->norm_cache);
  ptr_hmap_reset(&exp->coeff_cache);
  
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::count")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "bv_arith looks at new conflict of size %d with conflict variable ",conflict_core->size);
    term_t conflict_var_term = variable_db_get_term(ctx->var_db, conflict_var);
    ctx_trace_term(ctx, conflict_var_term);
    fprintf(out, "\n");
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
      if (!is_pos_term(t0) || !is_pos_term(t1)) {
        result = false;
        break;
      }
      // OK, maybe we can treat the constraint atom_term. We first scan the atom (collecting free variables and co.)
      bv_evaluator_csttrail_scan(csttrail, atom_var);
      
      // Now that we have collected the free variables, we look into the constraint structure
      term_t var0 = NULL_TERM;
      term_t var1 = NULL_TERM;
      int32_t t0_coeff = bv_arith_coeff(exp, t0, &var0, false);
      int32_t t1_coeff = bv_arith_coeff(exp, t1, &var1, false);
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "can_explain gets coefficients %d and %d for variables ", t0_coeff, t1_coeff);
        term_print_to_file(out, terms, var0);
        fprintf(out, " and ");
        term_print_to_file(out, terms, var1);
        fprintf(out, "\n");
      }
      if (t0_coeff == 2) {
        // Turns out we actually can't deal with the constraint. We stop
        if (ctx_trace_enabled(ctx, "mcsat::bv::arith::fail")) {
          FILE* out = ctx_trace_out(ctx);
          fprintf(out, "Left-hand no good for ");
          ctx_trace_term(ctx, csttrail->conflict_var_term);
          ctx_trace_term(ctx, atom_term);
        }
        result = false;
        break;
      }
      if (t1_coeff == 2) {
        // Turns out we actually can't deal with the constraint. We stop
        if (ctx_trace_enabled(ctx, "mcsat::bv::arith::fail")) {
          FILE* out = ctx_trace_out(ctx);
          fprintf(out, "Right-hand no good for ");
          ctx_trace_term(ctx, csttrail->conflict_var_term);
          ctx_trace_term(ctx, atom_term);
        }
        return false;
      }
      if (t0_coeff * t1_coeff == -1) {
        // Turns out we actually can't deal with the constraint. We stop
        if (ctx_trace_enabled(ctx, "mcsat::bv::arith::fail")) {
          FILE* out = ctx_trace_out(ctx);
          fprintf(out, "Coeff of different signs for ");
          ctx_trace_term(ctx, csttrail->conflict_var_term);
          ctx_trace_term(ctx, atom_term);
        }
        result = false;
        break;
      }
      if ((t0_coeff * t1_coeff == 1) && (var0 != var1)) {
        if ((term_kind(terms,var0) != BV_ARRAY) || (term_kind(terms,var1) != BV_ARRAY)) {
          result = false;
          break;
        }
        uint32_t w = term_bitsize(terms, t0);
        var0 = extract(exp, var0, w);
        var1 = extract(exp, var1, w);
        uint32_t varbits0, varbits1;
        term_t head0, head1;
        lower_bit_extract_base(exp,var0,w,&head0,&varbits0);
        lower_bit_extract_base(exp,var1,w,&head1,&varbits1);
        if (varbits0 != varbits1) {
          result = false;
          break;
        }
        if (head0 == NULL_TERM && head1 != NULL_TERM) {
          result = false;
          break;
        }
        if (head1 == NULL_TERM && head0 != NULL_TERM) {
          result = false;
          break;
        }
        composite_term_t* desc0 = bvarray_term_desc(terms, var0);
        composite_term_t* desc1 = bvarray_term_desc(terms, var1);
        for (uint32_t u = 0; u < varbits0; u++){
          if (desc0->arg[u] != desc1->arg[u]) {
            result = false;
            break;
          }
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
    default: {
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith::fail")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "Can't understand predicate:\n");
        ctx_trace_term(ctx, atom_term);
      }
      result = false;
      break;
    }
    }
    if (!result) {
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith::count")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "I am le tired\n");
      }
      break;
    }
  }
  return result;
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
  freeval(exp);
  delete_pmap(&exp->var_cache);
  delete_int_hmap2(&exp->norm_cache);
  delete_ptr_hmap(&exp->coeff_cache);
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

  init_pmap(&exp->var_cache, 0);
  init_int_hmap2(&exp->norm_cache, 0);
  init_ptr_hmap(&exp->coeff_cache, 0);

  return (bv_subexplainer_t*) exp;
}
