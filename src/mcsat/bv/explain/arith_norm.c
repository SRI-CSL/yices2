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

#include "mcsat/tracing.h"
#include "terms/bvarith_buffer_terms.h"
#include "terms/bvarith64_buffer_terms.h"
#include "terms/bv_constants.h"
#include "terms/bv64_constants.h"

#include "mcsat/bv/bv_utils.h"
#include "arith_norm.h"

// var_cache hash map has dynamically allocated values
// So before resetting or deleting it, one must free the memory of the stored values
// which the following function does

void arith_norm_freeval(arith_norm_t* norm) {
  for (pmap_rec_t* current = pmap_first_record(&norm->var_cache);
       current != NULL;
       current = pmap_next_record(&norm->var_cache, current)) {
    safe_free((arith_analyse_t*) current->val);
  }
}

void init_analysis(arith_analyse_t* result){
  result->suffix  = 0;
  result->length  = 0;
  result->start   = 0;
  result->base    = NULL_TERM;
  result->eval    = NULL_TERM;
  result->var     = NULL_TERM;
  result->garbage = NULL_TERM;
  result->intros  = false;
}


void print_analyse(plugin_context_t* ctx, arith_analyse_t*  analysis){
  FILE* out = ctx_trace_out(ctx);
  fprintf(out, "analyse produces suffix = %d, length = %d, base = ", analysis->suffix, analysis->length);
  if (analysis->base != NULL_TERM){
    ctx_trace_term(ctx, analysis->base);
    fprintf(out, "starting at start = %d,", analysis->start);
  }
  else 
    fprintf(out, "NO_BASE,");
  fprintf(out, " with evaluable = ");    
  ctx_trace_term(ctx, analysis->eval);
  fprintf(out, "garbage = ");    
  ctx_trace_term(ctx, analysis->garbage);
  fprintf(out, "and var = ");    
  ctx_trace_term(ctx, analysis->var);
}

static inline
void analyse_array(arith_norm_t* norm,
                   uint32_t n,     // length of array
                   term_t* monom,  // terms to analyse (can have some NULL_TERMs); after this function: contains variable part of original value
                   term_t* evaluables, // where we place the evaluable part of the terms
                   term_t* garbage) {  // where we place the garbage part of the terms
  for (uint32_t i = 0; i < n; ++ i) {
    if (monom[i] != NULL_TERM) {
      arith_analyse_t* s = arith_analyse(norm, monom[i]);
      evaluables[i] = s->eval;
      garbage[i]    = s->garbage;
      monom[i]      = s->var;
    }
  }
}
                
static inline
void analyse_BV(arith_norm_t* norm,
                uint32_t w,          // bitwidth we're working at
                uint32_t n_monom,    // Number of monomials
                bvconstant_t* coeff, // monomials' coefficients; THEY ARE DELETED BY THIS FUNCTION
                term_t* monom,       // monomials (NULL_TERM for polynomial constants); ARRAY IS MODIFIED BY THE FUNCTION - UNUSABLE AFTER THAT
                arith_analyse_t* result) { // Where we place result (assumption: number fields have 0, term fields have NULL_TERM)
  plugin_context_t* ctx = norm->csttrail.ctx;
  term_manager_t* tm    = ctx->tm;
  term_table_t* terms   = ctx->terms;
  term_t evaluables[n_monom]; // where we place the evaluable part of the monomials
  term_t garbage[n_monom];    // where we place the garbage part of the monomials
  analyse_array(norm, n_monom, monom, evaluables, garbage);
  bvarith_buffer_t* buffer = term_manager_get_bvarith_buffer(tm);
  bvarith_buffer_prepare(buffer, w); // Setting the desired width
  for (uint32_t i = 0; i < n_monom; ++ i) {
    if (monom[i] != NULL_TERM)
      bvarith_buffer_add_const_times_term(buffer, terms, coeff[i].data, monom[i]); // Otherwise we add the w-bit monomial to the bv_poly
  }
  result->var = arith_sum_norm(tm, mk_bvarith_term(tm, buffer)); // We turn the bv_poly into an actual term
  bvarith_buffer_prepare(buffer, w); // Setting the desired width
  for (uint32_t i = 0; i < n_monom; ++ i) {
    if (monom[i] != NULL_TERM)
      bvarith_buffer_add_const_times_term(buffer, terms, coeff[i].data, garbage[i]); // Otherwise we add the w-bit monomial to the bv_poly
  }
  result->garbage = arith_sum_norm(tm, mk_bvarith_term(tm, buffer)); // We turn the bv_poly into an actual term
  bvarith_buffer_prepare(buffer, w); // Setting the desired width
  for (uint32_t i = 0; i < n_monom; ++ i) {
    if (monom[i] == NULL_TERM)
      bvarith_buffer_add_const(buffer, coeff[i].data);// constant coefficient gets aded to the buffer bv_poly
    else
      bvarith_buffer_add_const_times_term(buffer, terms, coeff[i].data, evaluables[i]); // Otherwise we add the w-bit monomial to the bv_poly
    delete_bvconstant(&coeff[i]);
  }
  result->eval = arith_sum_norm(tm, mk_bvarith_term(tm, buffer)); // We turn the bv_poly into an actual term
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "analyse_BV finished treating %d monomials\n",n_monom);
  }
}

static inline
void analyse_BV64(arith_norm_t* norm,
                  uint32_t w,          // bitwidth we're working at
                  uint32_t n_monom,    // Number of monomials
                  uint64_t* coeff,     // monomials' coefficients
                  term_t* monom,       // monomials (NULL_TERM for polynomial constants); ARRAY IS MODIFIED BY THE FUNCTION - UNUSABLE AFTER THAT
                  arith_analyse_t* result) { // Where we place result (assumption: number fields have 0, term fields have NULL_TERM)
  plugin_context_t* ctx = norm->csttrail.ctx;
  term_manager_t* tm    = ctx->tm;
  term_table_t* terms   = ctx->terms;
  term_t evaluables[n_monom]; // where we place the evaluable part of the monomials
  term_t garbage[n_monom];    // where we place the garbage part of the monomials
  analyse_array(norm, n_monom, monom, evaluables, garbage);
  bvarith64_buffer_t* buffer = term_manager_get_bvarith64_buffer(tm);
  bvarith64_buffer_prepare(buffer, w); // Setting the desired width
  // Now going into each monomial
  for (uint32_t i = 0; i < n_monom; ++ i) {
    if (monom[i] != NULL_TERM)
      bvarith64_buffer_add_const_times_term(buffer, terms, coeff[i], monom[i]);
  }
  result->var = arith_sum_norm(tm, mk_bvarith64_term(tm, buffer)); // We turn the bv_poly into an actual term
  bvarith64_buffer_prepare(buffer, w); // Setting the desired width
  for (uint32_t i = 0; i < n_monom; ++ i) {
    if (monom[i] != NULL_TERM)
      bvarith64_buffer_add_const_times_term(buffer, terms, coeff[i], garbage[i]);
  }
  result->garbage = arith_sum_norm(tm, mk_bvarith64_term(tm, buffer)); // We turn the bv_poly into an actual term
  bvarith64_buffer_prepare(buffer, w); // Setting the desired width
  for (uint32_t i = 0; i < n_monom; ++ i) {
    if (monom[i] == NULL_TERM)
      bvarith64_buffer_add_const(buffer, coeff[i]); // constant coefficient gets added to the buffer bv_poly
    else
      bvarith64_buffer_add_const_times_term(buffer, terms, coeff[i], evaluables[i]);
  }
  result->eval = arith_sum_norm(tm, mk_bvarith64_term(tm, buffer)); // We turn the bv_poly into an actual term
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "analyse_BV64 finished treating %d monomials\n",n_monom);
  }
}


static inline
void analyse_bvarray(arith_norm_t* norm,
                     uint32_t w,          // bitwidth we're working at
                     term_t* ebits,       // The bits (will be modified by this function!)
                     arith_analyse_t* result) { // Where we place result (assumption: number fields have 0, term fields have NULL_TERM)

  plugin_context_t* ctx = norm->csttrail.ctx;
  term_manager_t* tm    = ctx->tm;
  term_table_t* terms   = ctx->terms;

  term_t cbits[w]; // Where we build the central section, if the term is bad
  uint32_t shortlength  = 0;         // Number of bits of the central section of t, excluding sign-extension bits
  term_t signbit        = NULL_TERM; // The sign bit of the central section of t
  term_t lastbase       = NULL_TERM; // The base from the previous cell
  bool is_negated       = false; // whether the first bit of the central section is negated
  term_t zero = arith_zero(tm, w);
    
  // We inspect each bit of the bv_array
  for (uint32_t i = 0; i < w; i++) {

    term_t t_i = ebits[i]; // The Boolean term that constitutes that bit
    bool evaluable = bv_evaluator_is_evaluable(&norm->csttrail, t_i); // Whether this bit can be evaluated

    if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "analyse: bit %d is ",i);
      term_print_to_file(out, terms, t_i);
      fprintf(out, " and is %s, with current values suffix = %d, length = %d, shortlength = %d\n",
              evaluable ? "evaluable" : "non-evaluable", result->suffix,result->length, shortlength);
    }

    // Now we handle the fields suffix, length, base, start, etc of result
    if (evaluable) { // So we look at whether that bit can be evaluated
      lastbase = NULL_TERM;     // No base here
      signbit  = NULL_TERM;
      if (result->length == 0)  // If still in suffix
        result->suffix ++;      // We increase suffix
    } else {

      bool isneg = is_neg_term(t_i); // Whether the boolean term is negated
      if (result->length == 0) // This is the first unevaluable bit
        is_negated = isneg;    // It defines the polarity of the central section

      if (term_kind(terms, t_i) != BIT_TERM // not a bit-select
          || is_negated != isneg ) {        // or not the right polarity
        result->base = NULL_TERM; // Makes the whole term BAD (if not evaluable)
      } else {
        uint32_t index = bit_term_index(terms, t_i); // Get selected bit
        term_t base    = bit_term_arg(terms, t_i);   // Get the base
        assert(term_kind(terms, base) != BV_ARRAY);
        if (result->length == 0) { // This is the first unevaluable bit
          lastbase  = base;
          result->base  = base;
          result->start = index;
          if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
            FILE* out = ctx_trace_out(ctx);
            fprintf(out, "result->start set to %d with result->base being ", result->start);
            ctx_trace_term(ctx, result->base);
            fprintf(out, "and t_i being ");
            ctx_trace_term(ctx, t_i);
          }
        }
        // Now we look at whether this bit, necessarily from the central section, is good
        if (base != lastbase                                   // Not the right base
            || (index - result->start) != (i - result->suffix) ) { // Not the right index
          result->base = NULL_TERM;    // in both cases, the term is BAD
        }
      }
      result->length = i - result->suffix +1;
      if (signbit != t_i) {
        shortlength = result->length;
        signbit = t_i;
      }
      assert(result->length > 0);
    }
      
    if (result->length != 0) // The central bits are recorded, flipping polarity so that the first bit in there is positive
      cbits[i] = is_negated ? not_term(terms, t_i) : t_i;
  }

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Scanning bits led to suffix = %d, length = %d, shortlength = %d, and base%s is ",result->suffix,result->length, shortlength,(is_negated)?" (which is negated)":"");
    if (result->base != NULL_TERM)
      ctx_trace_term(ctx, result->base);
    else
      fprintf(out, "No base\n");
  }

  // Now we look at the central section between suffix and suffix+shortlength,
  // and try to build result->base and result->start
  bool nobueno = false;
    
  if (shortlength > 0) { // if the central section exists
    if (result->base == NULL_TERM) { // ...but the term is bad
      result->base = mk_bvarray(tm, shortlength, &cbits[result->suffix]); // build the central section anyways
      result->start = 0;
      nobueno = true;
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "Not a good term, creating base\n");
        ctx_trace_term(ctx, result->base);
      }
    }
  }

  if (is_negated) { // The central cbits have flipped polarity
    assert(shortlength > 0);
    assert(result->base != NULL_TERM);
    // Now let's make sure we do arithmetic on the right bitwidth
    result->base   = term_extract(tm, result->base, 0, result->start + shortlength);
    // ...and replace the bitwise negation by arithmetic operation
    result->base   = arith_negate(tm, arith_add_one(tm, result->base));
    result->intros = true;
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "First bit negated, changing base to\n");
      ctx_trace_term(ctx, result->base);
    }
  }
    
  if (shortlength != result->length) {
    // This is a sign-extension,
    // base to return is (0extend(base+half(shortlength)) - 0extend(half(shortlength)))
    term_t tmp1 = arith_upextension(tm,
                                    arith_add_half(tm, result->base),
                                    false_term,
                                    result->length);
    term_t tmp2 = arith_upextension(tm,
                                    arith_add_half(tm, arith_zero(tm, shortlength)),
                                    false_term,
                                    result->length);
    result->base   = arith_sub(tm, tmp1, tmp2);
    result->intros = true;
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Sign extension, changing base to\n");
      ctx_trace_term(ctx, result->base);
    }
  }

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Final result: suffix = %d, length = %d, shortlength = %d, and base is ",result->suffix,result->length, shortlength);
    if (result->base != NULL_TERM)
      ctx_trace_term(ctx, result->base);
    else
      fprintf(out, "No base\n");
  }

  // Now we can construct result->norm, result->eval and result->var
  // We first finish the normalisation of the central bits:
  for (uint32_t i = 0; i < result->length; i++)
    ebits[i + result->suffix] = bv_bitterm(terms, mk_bitextract(tm, result->base, i + result->start));
    
  // We distribute each bit recorded in ebits to either ebits (for result->eval) or cbits (for result->var)
  for (uint32_t i = 0; i < w; i++)
    if (i < result->suffix || i >= result->suffix + result->length)
      cbits[i] = false_term; // prefix and suffix are 0...0 for result->var
    else { // central section
      cbits[i] = ebits[i];
      ebits[i] = false_term;
    }
  result->eval    = mk_bvarray(tm, w, ebits);
  result->garbage = nobueno? mk_bvarray(tm, w, cbits) : zero;
  result->var     = nobueno? zero : mk_bvarray(tm, w, cbits);

}


arith_analyse_t* arith_analyse(arith_norm_t* norm, term_t t){

  term_t conflict_var   = norm->csttrail.conflict_var_term;
  plugin_context_t* ctx = norm->csttrail.ctx;
  term_manager_t* tm    = ctx->tm;
  term_table_t* terms   = ctx->terms;
  
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Starting analyse on ");
    ctx_trace_term(ctx, t);
  }

  assert(is_bitvector_term(terms, t));
  uint32_t w = term_bitsize(terms, t);

  pmap_rec_t* entry = pmap_find(&norm->var_cache, t, conflict_var);

  if (entry != NULL) {
    arith_analyse_t* result = (arith_analyse_t*) entry->val;
    assert(result != NULL);
    assert(result != DEFAULT_PTR);
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Found it in memoisation table!\n");
      print_analyse(ctx, result);
    }
    return result;
  }

  arith_analyse_t* result = safe_malloc(sizeof(arith_analyse_t));
  init_analysis(result);

  switch (term_kind(terms, t)) {
  case BV_POLY:{
    bvpoly_t* t_poly = bvpoly_term_desc(ctx->terms, t);
    uint32_t n_monom = t_poly->nterms;
    bvconstant_t coeff[n_monom]; // where we place the monomials' coefficients
    term_t monom[n_monom];       // where we place the monomials
    for (uint32_t i = 0; i < n_monom; ++ i) {
      init_bvconstant(&coeff[i]);
      bvconstant_copy(&coeff[i], w, t_poly->mono[i].coeff); // projecting the monomial coefficient onto w bits
      bvconstant_normalize(&coeff[i]);
      monom[i] = (t_poly->mono[i].var != const_idx) ? t_poly->mono[i].var : NULL_TERM;
    }
    analyse_BV(norm, w, n_monom, coeff, monom, result);
    break;
  }

  case BV64_POLY: {
    bvpoly64_t* t_poly64 = bvpoly64_term_desc(ctx->terms, t);
    uint32_t n_monom = t_poly64->nterms;
    uint64_t coeff[n_monom]; // where we place the monomials' coefficients
    term_t monom[n_monom];   // where we place the monomials
    for (uint32_t i = 0; i < n_monom; ++ i) {
      coeff[i] = t_poly64->mono[i].coeff;
      monom[i] = (t_poly64->mono[i].var != const_idx) ? t_poly64->mono[i].var : NULL_TERM;
    }
    analyse_BV64(norm, w, n_monom, coeff, monom, result);
    break;
  }

  case BV_ARRAY: {  // Concatenated boolean terms
    composite_term_t* concat_desc = bvarray_term_desc(terms, t);
    term_t ebits[w]; // Where we build result->eval
    // First, we copy the array of bits
    for (uint32_t i = 0; i < w; i++)
      ebits[i] = concat_desc->arg[i];
    analyse_bvarray(norm, w, ebits, result);
    break;
  }

  default: { // Term t is now not a bv_array, nor a bv_poly nor a bv64_poly
    term_t zero = arith_zero(tm, w);
    if (bv_evaluator_is_evaluable(&norm->csttrail, t)) {
      result->eval   = t;
      result->var    = zero;
      result->garbage= zero;
      result->suffix = w;
      result->length = 0;
      result->start  = 0;
      result->base = NULL_TERM;
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "Term is not a BV_POLY/BV64_POLY/BV_ARRAY, we just get evaluable ");
        ctx_trace_term(ctx, t);
      }
    } else {
      result->eval   = zero;
      result->var    = t;
      result->garbage= zero;
      result->suffix = 0;
      result->length = w;
      result->start  = 0;
      result->base   = t;
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "Term is not a BV_POLY/BV64_POLY/BV_ARRAY, we just get non-evaluable ");
        ctx_trace_term(ctx, t);
      }
    }
  }
  }

  entry = pmap_get(&norm->var_cache, t, conflict_var);
  assert(entry->val == NULL || entry->val == DEFAULT_PTR);
  entry->val = (void*) result;
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")){
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "When started on term ");
    ctx_trace_term(ctx, t);
    print_analyse(ctx, result);
  }
  return result;  // Note that the result is automatically memoised
  
}


#ifndef NDEBUG

static inline
term_t result_eval(bv_csttrail_t* csttrail, term_t result){

  plugin_context_t* ctx = csttrail->ctx;
  uint32_t ignore_this_int = 0;
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "input was evaluable, so I'm evaluating.\n");
  }
  bool b =
    (bv_evaluator_evaluate_term(csttrail->eval, result, &ignore_this_int)) != NULL;
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "yep, got a value.\n");
  }
  (void) ignore_this_int;
  return b;
}

#endif


static inline
term_t check_and_return(arith_norm_t* norm, term_t t, uint32_t w, term_t result){

  bv_csttrail_t* csttrail = &norm->csttrail;
  plugin_context_t* ctx   = csttrail->ctx;
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
    // standard abbreviations
    term_table_t* terms   = ctx->terms;
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Normalising (the %d lowest bits of)\n", w);
    /* term_print_to_file(out, terms, t); */
    ctx_trace_term(ctx, t);
    fprintf(out, " successfully gave ");
    if (result == t) {
      fprintf(out, "the same term!");
    } else {
      fprintf(out, "the following term of bitwidth %i:\n",bv_term_bitsize(terms, result));
      /* term_print_to_file(out, terms, result); */
      ctx_trace_term(ctx, result);
    }
    fprintf(out, "\n");
  }

  assert( (!bv_evaluator_is_evaluable(csttrail, t))
          || result_eval(csttrail,result));

  if (ctx_trace_enabled(ctx, "mcsat::bv::rewrite::check")) {
    assert( (bv_term_bitsize(ctx->tm->terms, t) > w)
            || check_rewrite(ctx, t, result));
    /* assert( (!bv_evaluator_is_evaluable(csttrail, term_extract(tm, t, 0, w))) */
    /*         || result_eval(csttrail,result)); */
    /* assert( (bv_term_bitsize(tm->terms, t) == w) */
    /*         || check_rewrite(ctx, term_extract(tm, t, 0, w), result)); */
  }
  // Maybe the following assert creates a loop. Dangerous.
  /* if (result != t) { */
  /*   assert(arith_normalise_upto(norm, result, bv_term_bitsize(ctx->terms, result)) == result); */
  /* } */
  
  /* bool a = bv_evaluator_is_evaluable(csttrail, t); */
  /* if (a) { */
  /*   bool b = result_eval(csttrail,result); */
  /*   assert(b); */
  /* } else { */
  /*   if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) { */
  /*     // standard abbreviations */
  /*     FILE* out = ctx_trace_out(ctx); */
  /*     fprintf(out, "Not supposed to be evaluable. Not evaluating.\n"); */
  /*   } */
  /* } */
  return result;
}

static inline
term_t finalise(arith_norm_t* norm, term_t original, arith_analyse_t* s){

  // standard abbreviations
  bv_csttrail_t* csttrail = &norm->csttrail;
  plugin_context_t* ctx = csttrail->ctx;
  term_manager_t* tm    = ctx->tm;
  term_table_t* terms   = ctx->terms;
  term_t result         = arith_add(tm, s->var, arith_add(tm, s->garbage, s->eval));
  uint32_t w            = bv_term_bitsize(terms, result);

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Building a result for the %d lowest bits of ",w);
    term_print_to_file(out, terms, original);
    fprintf(out, ", with var_term = ");
    term_print_to_file(out, terms, s->var);
    fprintf(out, ", garbage_term = ");
    term_print_to_file(out, terms, s->garbage);
    fprintf(out, ", eval_term = ");
    term_print_to_file(out, terms, s->eval);
    fprintf(out, ", adding up to ");
    term_print_to_file(out, terms, result);
    fprintf(out, "\n");
  }
  // We know what we are returning, now we just cache it for later
  int_hmap2_add(&norm->norm_cache, original, w, result);
  return check_and_return(norm, original, w, result);  
}


// Extracting the w lowest bits of t, normalising on the way
term_t arith_normalise_upto(arith_norm_t* norm, term_t u, uint32_t w){

  // standard abbreviations
  bv_csttrail_t* csttrail = &norm->csttrail;
  plugin_context_t* ctx = csttrail->ctx;
  term_t conflict_var   = csttrail->conflict_var_term;
  term_manager_t* tm    = ctx->tm;
  term_table_t* terms   = ctx->terms;
  term_t t                  = bv_bitterm(terms, u);
  uint32_t original_bitsize = bv_term_bitsize(terms, t);
  assert(0 < w);
  assert(w <= original_bitsize);
  
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Normalising %d lowest bits of ",w);
    term_print_to_file(out, terms, t);
    fprintf(out, " (bitsize is %d))\n",original_bitsize);
  }

  if (is_bitvector_term(terms, t)) {
    term_t new = arith_sum_norm(tm, t);
    assert(check_rewrite(ctx, t, new));
    t = new;
  }

  if (t == conflict_var) {
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Conflict variable, so it's already normalised\n");
    }
    term_t result = (is_boolean_term(terms,t)) ? t : term_extract(tm, t, 0, w);
    return check_and_return(norm, u, w, result);
  }

  uint32_t t_kind = term_kind(terms, t);
  switch (t_kind) { // Simple check for constants
  case CONSTANT_TERM:
  case BV_CONSTANT:
  case BV64_CONSTANT: {
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Constant, so it's already normalised\n");
    }
    term_t result = (is_boolean_term(terms,t)) ? t : term_extract(tm, t, 0, w);
    return check_and_return(norm, u, w, result);
  }
  default: {
  }
  }

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Not conflict var nor a constant. Negated Boolean term?\n");
  }

  if (is_neg_term(t)){
    assert(is_boolean_term(terms,t));
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Oh, this is a negative Boolean term, let's reduce underneath:\n");
    }
    term_t result = not_term(terms, arith_normalise_upto(norm, not_term(terms,t), 1));
    return check_and_return(norm, u, w, result);
  }

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Not negative Boolean term. Variable on the trail?\n");
  }

  variable_db_t* var_db = ctx->var_db; // standard abbreviations
  variable_t var        = variable_db_get_variable_if_exists(var_db, t); // term as a variable
  
  if (var != variable_null
      && int_hset_member(&norm->csttrail.free_var, var )) { // t is a variable other than y
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Oh, this is a variable on the trail, we return the extract of: ");
      ctx_trace_term(ctx, t);
    }
    term_t result = (is_boolean_term(terms,t)) ? t : term_extract(tm, t, 0, w);
    return check_and_return(norm, u, w, result);
  }

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Not a variable on trail. Now looking at memoisation table.\n");
  }

  // We first look at whether the value is cached
  int_hmap2_rec_t* t_norm = int_hmap2_find(&norm->norm_cache, t, w);
  if (t_norm != NULL) {
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Found in the memoisation table! It's ");
      ctx_trace_term(ctx, t_norm->val);
    }
    return t_norm->val;
  }

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Not memoised. We now look into the term.\n");
  }

  switch (t_kind) {

  case EQ_TERM:
  case OR_TERM:
  case XOR_TERM:
  case BV_EQ_ATOM:
  case BV_GE_ATOM:
  case BV_SGE_ATOM:
  case BV_DIV:
  case BV_REM:
  case BV_SDIV:
  case BV_SREM:
  case BV_SMOD:
  case BV_SHL:
  case BV_LSHR:
  case BV_ASHR: {
    composite_term_t* composite_desc = composite_term_desc(terms, t);
    uint32_t n = composite_desc->arity;
    term_t norms[n]; // Where we recursively normalise
    for (uint32_t i = 0; i < n; ++ i){
      term_t t_i = composite_desc->arg[i];
      uint32_t w_i = bv_term_bitsize(terms,t_i);
      norms[i] = arith_normalise_upto(norm, t_i, w_i);
    }
    term_t tmp = mk_bv_composite(tm, t_kind, n, norms);
    if (is_boolean_term(terms,t)) {
      assert(w == 1);
      int_hmap2_add(&norm->norm_cache, t, w, tmp);
      return check_and_return(norm, t, w, tmp);  
    } else {
      // tmp is not necessarily w-bit normalised (w was not involved); so we do a new pass
      if (t != tmp)
        tmp = arith_normalise_upto(norm, tmp, w);
      else
        tmp = term_extract(tm, tmp, 0, w);
      arith_analyse_t* analysis = arith_analyse(norm, tmp);
      return finalise(norm, t, analysis);
    }
  }

  case POWER_PRODUCT: {
    pprod_t* pprod_desc = pprod_term_desc(ctx->terms, t);
    uint32_t n = pprod_desc->len;
    term_t norms[n]; // Where we recursively normalise
    for (uint32_t i = 0; i < n; ++ i)
      norms[i] = arith_normalise_upto(norm, pprod_desc->prod[i].var, w);
    term_t tmp = mk_pprod(tm, pprod_desc, n, norms);
      arith_analyse_t* analysis = arith_analyse(norm, tmp);
      return finalise(norm, t, analysis);
  }

  case BIT_TERM: {
    assert(w == 1);
    uint32_t index = bit_term_index(terms, t);  // Get selected bit
    term_t base    = bit_term_arg(terms, t);    // Get the base
    base           = arith_normalise_upto(norm, base, index+1);
    term_t result  = bv_bitterm(terms, mk_bitextract(tm, base, index));
    // Here, result is 1-bit normalised
    int_hmap2_add(&norm->norm_cache, t, w, result);
    return check_and_return(norm, t, w, result);
  }

  case BV_POLY: {
    arith_analyse_t analysis; // Where we place the resulting analysis
    init_analysis(&analysis);
    bvpoly_t* t_poly = bvpoly_term_desc(ctx->terms, t);
    uint32_t n_monom = t_poly->nterms;
    term_t monom[n_monom]; // First, we inhabit the monomials, recursively normalising them
    for (uint32_t i = 0; i < n_monom; ++ i)
      monom[i] = (t_poly->mono[i].var != const_idx) ?
        arith_normalise_upto(norm, t_poly->mono[i].var, w) : NULL_TERM;
    if (w<65) { // If we extract fewer than 65 bits, we use uint64_t coefficients
      uint64_t coeff[n_monom];
      for (uint32_t i = 0; i < n_monom; ++ i)
        coeff[i] = // projecting the monomial coefficient onto w bits
          (original_bitsize < 33) ? // requires an annoying case analysis, for some reason
          ( (uint64_t) bvconst_get32(t_poly->mono[i].coeff)) :
          bvconst_get64(t_poly->mono[i].coeff) ;
      analyse_BV64(norm, w, n_monom, coeff, monom, &analysis);
    } else { // If not, we stick to bv_constants
      bvconstant_t coeff[n_monom];
      for (uint32_t i = 0; i < n_monom; ++ i) {
        init_bvconstant(&coeff[i]);
        bvconstant_extract(&coeff[i], t_poly->mono[i].coeff, 0, w); // projecting the monomial coefficient onto w bits
        bvconstant_normalize(&coeff[i]);
      }
      analyse_BV(norm, w, n_monom, coeff, monom, &analysis);
    }
    return finalise(norm, t, &analysis);
  }

  case BV64_POLY: {
    arith_analyse_t analysis; // Where we place the resulting analysis
    init_analysis(&analysis);
    bvpoly64_t* t_poly64 = bvpoly64_term_desc(ctx->terms, t);
    uint32_t n_monom     = t_poly64->nterms;
    term_t monom[n_monom];
    uint64_t coeff[n_monom];
    for (uint32_t i = 0; i < n_monom; ++ i) {
      monom[i] = (t_poly64->mono[i].var != const_idx) ?
        arith_normalise_upto(norm, t_poly64->mono[i].var, w) : NULL_TERM;
      coeff[i] = t_poly64->mono[i].coeff;
    }
    analyse_BV64(norm, w, n_monom, coeff, monom, &analysis);
    return finalise(norm, t, &analysis);
  }

  case BV_ARRAY: {  // Concatenated boolean terms
    composite_term_t* concat_desc = bvarray_term_desc(terms, t);
    term_t ebits[w]; // Where we build the result

    // First, we eliminate BIT_TERM-over-BV_ARRAYs:
    for (uint32_t i = 0; i < w; i++)
      ebits[i] = bv_bitterm(terms, concat_desc->arg[i]);
    
    // Hand-made hash map (we want it light, non-redimensionable,
    // and we can do so because we know the max size is w).
    // In each cell i, there are 4 integers:
    // preproc[0][i] is the key, which is a term_t, let's call it k
    // preproc[1][i] is the maximum i such that k[i] is a bit of this bv_array, let's call it top; then:
    // preproc[1][i] is the term_t arith_normalise_upto(k,top+1) (normalised version of k over the lowest top+1 bits), let's call it norm
    // preproc[2][i] is the value returned by bv_evaluator_not_free_up_to(norm), let's call it maxeval
    // preproc[3][i] is the term_t arith_normalise_upto(norm,maxeval), if maxeval is not 0
    term_t preproc[4][w];
    // We initialise the hashmap
    fix_htbl_init(preproc[0], w);
      
    // Now we range over the bits of the t bv_array of the form base[index], and we fill-in preproc[0][*] and preproc[1][*]
    for (uint32_t i = 0; i < w; i++) {
      term_t t_i = ebits[i];        // The Boolean term that constitutes bit i of t
      if (term_kind(terms, t_i) == BIT_TERM) { // Is it of the form base[index] ?
        uint32_t index = bit_term_index(terms, t_i);  // Get selected bit
        term_t base    = bit_term_arg(terms, t_i);    // Get the base
        assert(term_kind(terms, base) != BV_ARRAY);
        uint32_t key_index = fix_htbl_index(preproc[0],w,base);
        if (preproc[0][key_index] == NULL_TERM
            || preproc[1][key_index] < index)
          preproc[1][key_index] = index;
        if (preproc[0][key_index] == NULL_TERM)
          preproc[0][key_index] = base;
      }
    }

    // Now we fill-in preproc[1][*], preproc[2][*], preproc[3][*], normalising recursively
    for (uint32_t i = 0; i < w; i++) {
      if (preproc[0][i] != NULL_TERM) {
        uint32_t size = preproc[1][i] + 1;
        preproc[1][i] = arith_normalise_upto(norm, preproc[0][i], size);
        preproc[2][i] = bv_evaluator_not_free_up_to(&norm->csttrail, preproc[1][i]);
        if (preproc[2][i] > size)
          preproc[2][i] = size;
        if (preproc[2][i] > 0) {
          preproc[3][i] = (preproc[2][i] == size) ?
            preproc[1][i] :
            arith_normalise_upto(norm, preproc[1][i], preproc[2][i]);
        }
      }
    }

    if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Finished filling-in preproc with recursive normalisation, now going through the bits in order.\n");
    }

    // Now we range over the bits of the original bv_array
    for (uint32_t i = 0; i < w; i++) {

      term_t t_i = ebits[i]; // The Boolean term that constitutes that bit

      if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "bit %d is ",i);
        term_print_to_file(out, terms, t_i);
        fprintf(out, "\n");
      }

      // Then we normalise the bit t_i
      if (term_kind(terms, t_i) == BIT_TERM) {
        uint32_t index = bit_term_index(terms, t_i); // Get selected bit
        term_t base    = bit_term_arg(terms, t_i);   // Get the base
        assert(term_kind(terms, base) != BV_ARRAY);
        bool isneg     = is_neg_term(t_i);
        uint32_t key_index = fix_htbl_index(preproc[0],w,base);
        base = (index < preproc[2][key_index]) ?
          preproc[3][key_index] :
          preproc[1][key_index] ;
        ebits[i] = bv_bitterm(terms, mk_bitextract(tm, base, index));
        if (isneg) ebits[i] = not_term(terms, ebits[i]); // Same polarity as the original t_i
      } else {
        ebits[i] = arith_normalise_upto(norm, t_i, 1);
      }
    }
    /* term_t tmp = mk_bvarray(tm, w, ebits); */
    /* arith_analyse_t analysis = arith_analyse(norm, tmp); */
    arith_analyse_t analysis;
    init_analysis(&analysis);
    analyse_bvarray(norm, w, ebits, &analysis);
    return finalise(norm, t, &analysis);
  }

  default: {
    assert(false);
    return NULL_TERM; // Just to prevent compiler complaining
  }
  }
}
