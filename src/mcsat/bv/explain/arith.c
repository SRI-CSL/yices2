/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <inttypes.h>

#include "mcsat/tracing.h"
#include "mcsat/value.h"
#include "terms/bvarith_buffer_terms.h"
#include "terms/bvarith64_buffer_terms.h"
#include "terms/bv_constants.h"
#include "terms/bv64_constants.h"
#include "terms/term_manager.h"
#include "terms/term_utils.h"
#include "utils/int_hash_map.h"
#include "utils/int_hash_map2.h"
#include "utils/pair_hash_map.h"
#include "utils/ptr_array_sort2.h"

#include "mcsat/bv/bv_utils.h"
#include "arith_utils.h"
#include "arith_norm.h"
#include "arith_intervals.h"
#include "arith.h"


/**
   Extracting coefficients from terms.
**/


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

  arith_norm_t norm; // Environment for normalising terms

  // Cache of polynomial analyses (function bv_arith_coeff below): for a (normalised) term t (the key), the value is the polypair_t resulting from analysing t
  ptr_hmap_t coeff_cache;

} arith_t;

// coeff_cache has dynamically allocated values
// So before resetting or deleting those hash maps, one must free the memory of the stored values
// which the following function does

static inline void freeval(arith_t* exp) {
  for (ptr_hmap_pair_t* current = ptr_hmap_first_record(&exp->coeff_cache);
       current != NULL;
       current = ptr_hmap_next_record(&exp->coeff_cache, current)) {
    safe_free((polypair_t*) current->val);
  }
}

// Function returns the polypair_t (variable, coefficient, polyrest) of (normalised) u
// if u is not a good term for the fragment:
// if !assume_fragment, function will return NULL,
// if assume_fragment, function has unspecified behaviour (but runs faster)

polypair_t* bv_arith_coeff(arith_t* exp, term_t u, bool assume_fragment) {

  plugin_context_t* ctx = exp->super.ctx;
  term_t conflict_var   = exp->norm.csttrail.conflict_var_term;
  term_manager_t* tm    = ctx->tm;
  term_table_t* terms   = ctx->terms;

  uint32_t w = term_bitsize(terms, u);

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "bv_arith_coeff, extracting coefficient of unevaluable monomial in ");
    ctx_trace_term(ctx, u);
  }

  // We start by normalising the input term
  term_t t  = arith_normalise(&exp->norm, u);
  assert(t != NULL_TERM);
  assert(arith_is_sum_norm(terms,t));
  
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "bv_arith_coeff says normalisation successfully produced ");
    ctx_trace_term(ctx, t);
  }

  // Looking at whether the value is cached
  ptr_hmap_pair_t* entry = ptr_hmap_find(&exp->coeff_cache, t);
  if (entry != NULL) {
    polypair_t* result = (polypair_t*) entry->val;
    assert(result != NULL);
    assert(result->polyrest != NULL_TERM); // It is not marked for deletion
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "From memoisation table,\nCoefficient is %"PRId32"\n",result->coeff);
      fprintf(out, "Variable is ");
      if (result->var != NULL_TERM)
        ctx_trace_term(ctx, result->var);
      else 
        fprintf(out, "NOT PRESENT\n");
      fprintf(out, "Polyrest is ");
      ctx_trace_term(ctx, result->polyrest);
    }
    return result;
  }
  
  if (t == conflict_var) {
    entry = ptr_hmap_get(&exp->coeff_cache, t);
    polypair_t* result = safe_malloc(sizeof(polypair_t)); // We know we're successful, we malloc
    result->var = t;
    result->coeff = 1;
    result->polyrest = arith_zero(tm, w);
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Special case (conflict var),\nCoefficient is %"PRId32"\n",result->coeff);
      fprintf(out, "Variable is ");
      ctx_trace_term(ctx, result->var);
      fprintf(out, "Polyrest is ");
      ctx_trace_term(ctx, result->polyrest);
    }
    entry->val = (void*) result;
    return result;
  }

  if (bv_evaluator_is_evaluable(&exp->norm.csttrail, t)) {
    entry = ptr_hmap_get(&exp->coeff_cache, t);
    polypair_t* result = safe_malloc(sizeof(polypair_t)); // We know we're successful, we malloc
    result->var = NULL_TERM;
    result->coeff = 0;
    result->polyrest = t;
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Special case (evaluable),\nCoefficient is %"PRId32"\n",(int) result->coeff);
      fprintf(out, "No variable\n");
      fprintf(out, "Polyrest is ");
      ctx_trace_term(ctx, result->polyrest);
    }
    entry->val = (void*) result;
    return result;
  }

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Not evaluable and not cached\n");
  }

  arith_analyse_t* ts = arith_analyse(&exp->norm,t);
  if (!arith_is_zero(terms, ts->garbage)){
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Returning NULL because garbage was detected:\n");
      ctx_trace_term(ctx, ts->garbage);
    }
    return NULL;
  }

  polypair_t temp; // We don't know whether we'll be successful, we don't malloc
  temp.var      = NULL_TERM;
  temp.polyrest = ts->eval; 
  temp.coeff = 0;
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Setting polyrest to ");
    ctx_trace_term(ctx, temp.polyrest);
  }

  switch (term_kind(ctx->terms, ts->var)) {
  case BV_POLY: {
    bvpoly_t* t_poly = bvpoly_term_desc(ctx->terms, ts->var);
    assert(t_poly->bitsize == w);
    // If we extract more than 64 bits, we use regular coefficients for the bv_poly to produce
    // we construct that bv_poly from a bvarith_buffer_t called buffer:
    for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
      term_t monom_var = t_poly->mono[i].var;
      uint32_t* coeff  = t_poly->mono[i].coeff;
      if (monom_var != const_idx
          && !bv_evaluator_is_evaluable(&exp->norm.csttrail,monom_var)) {
        if (temp.coeff != 0) { // second unevaluable monomial?
          if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
            FILE* out = ctx_trace_out(ctx);
            fprintf(out, "Returning NULL because of at least two unevaluable monomials in BV_POLY, namely\n");
            ctx_trace_term(ctx, temp.var);
            fprintf(out, "and\n");
            ctx_trace_term(ctx, monom_var);
          }
          return NULL;       // -> we're outside the fragment
        }
        temp.var = monom_var;
        if (bvconst_is_one(coeff, t_poly->width)) {
          temp.coeff = 1;
        } else {
          if (bvconst_is_minus_one(coeff, w))
            temp.coeff = -1;
          else {
            if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
              FILE* out = ctx_trace_out(ctx);
              fprintf(out, "Returning NULL because coefficient of monomial\n");
              ctx_trace_term(ctx, temp.var);
              fprintf(out, "is not 1 or -1, but is\n");
              bvconst_print(out, coeff, w);
            }
            return NULL;
          }
        }
      }
    }
    break;
  }
  case BV64_POLY: {
    bvpoly64_t* t_poly = bvpoly64_term_desc(ctx->terms, ts->var);
    // Now going into each monomial
    for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
      term_t monom_var = t_poly->mono[i].var;
      if (monom_var != const_idx
          && !bv_evaluator_is_evaluable(&exp->norm.csttrail,monom_var)) {
        if (temp.coeff != 0) {// second unevaluable monomial?
          if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
            FILE* out = ctx_trace_out(ctx);
            fprintf(out, "Returning NULL because of at least two unevaluable monomials in BV64_POLY, namely\n");
            ctx_trace_term(ctx, temp.var);
            fprintf(out, "and\n");
            ctx_trace_term(ctx, monom_var);
          }
          return NULL;       // -> we're outside the fragment
        }
        temp.var = monom_var;
        if (t_poly->mono[i].coeff == 1) {
          temp.coeff = 1;
        } else {
          if (bvconst64_is_minus_one(t_poly->mono[i].coeff,w))
            temp.coeff = -1;
          else{
            if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
              FILE* out = ctx_trace_out(ctx);
              fprintf(out, "Returning NULL because coefficient of monomial\n");
              ctx_trace_term(ctx, temp.var);
              fprintf(out, "is not 1 or -1, but is %"PRIu64"\n",t_poly->mono[i].coeff);
            }
            return NULL;
          }
        }
      }
    }
    break;
  }
  case BV_ARRAY: {
    temp.var = ts->var;   // the temp.var is t
    temp.coeff = 1; // with coeff 1
    break;
  }
  default: {
    if (ts->var != conflict_var) return NULL;
    temp.var = ts->var;   // the temp.var is t
    temp.coeff = 1; // with coeff 1
  }
  }

  assert(temp.var != NULL_TERM);
  assert(temp.coeff == 1 || temp.coeff == -1);
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Identified variable as ");
    ctx_trace_term(ctx, temp.var);
    fprintf(out, "Now we analyse this variable.");
  }

  ts = arith_analyse(&exp->norm,temp.var);
  assert(arith_is_zero(terms, ts->eval));
  if (!arith_is_zero(terms, ts->garbage)
      || ts->var != temp.var)
    return NULL;

  assert(ts->length > 0); // Otherwise t would be evaluable (already checked)
  assert(ts->base != NULL_TERM);
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
    return NULL; // We're outside the fragment
  }

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Back to the bv_arith_coeff on ");
    ctx_trace_term(ctx, u);
  }

  // OK, now we know or we assume we are in the fragment

  entry = ptr_hmap_get(&exp->coeff_cache, t);
  polypair_t* result = safe_malloc(sizeof(polypair_t)); // We know we're successful, we malloc
  result[0] = temp; // We copy the three integer values from the stack variable

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Coefficient is %"PRId32"\n",temp.coeff);
    fprintf(out, "Variable is ");
    ctx_trace_term(ctx, temp.var);
    fprintf(out, "Polyrest is ");
    ctx_trace_term(ctx, temp.polyrest);
  }
  entry->val = (void*) result;
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
  /* assert(arith_normalise(&exp->norm, polyrest) == polyrest); // Not clear that it holds; can fail for stupid reasons */
  assert(bv_evaluator_is_evaluable(&exp->norm.csttrail, polyrest));

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
interval_t* bv_arith_unit_le(arith_t* exp, term_t lhs, term_t rhs, bool b) {
  // Standard abbreviations
  plugin_context_t* ctx = exp->super.ctx;
  term_manager_t* tm    = ctx->tm;
  term_table_t* terms   = ctx->terms;
  uint32_t w = term_bitsize(terms, lhs);
  assert(w == term_bitsize(terms, rhs));
  interval_t* result = NULL;
  
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "\nTreating unit_constraint (lhs <= rhs) where lhs is\n");
    ctx_trace_term(ctx, lhs);
    fprintf(out, " and rhs is\n");
    ctx_trace_term(ctx, rhs);
    fprintf(out, "\n");
  }

  // Not sure that it holds; can fail for stupid reasons
  /* assert(arith_normalise(&exp->norm, lhs) == lhs); */
  /* assert(arith_normalise(&exp->norm, rhs) == rhs); */
    
  polypair_t* left  = bv_arith_coeff(exp, lhs, true);
  assert(left != NULL);
  polypair_t* right = bv_arith_coeff(exp, rhs, true);
  assert(left != NULL);
    
  if ((left->coeff == -1) || (right->coeff == -1)) {
    // if coeff is negative, we add one, negate and swap sides.
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Coefficient is negative! let's start again with a positive coefficient.\n");
    }
    term_t nlhs = arith_negate(tm, arith_add_one(tm, lhs));
    term_t nrhs = arith_negate(tm, arith_add_one(tm, rhs));
    nlhs = arith_normalise(&exp->norm, nlhs);
    nrhs = arith_normalise(&exp->norm, nrhs);
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
    lo_term = arith_negate(tm,c2);
    
    if (left_has) { // then hi is -c1
      bvconstant_copy(&hi, cc1.bitsize, cc1.data);
      bvconstant_negate(&hi);
      bvconstant_normalize(&hi);
      hi_term = arith_negate(tm,c1);
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "Case <=: has_right, has_left, lo = ");
        bvconst_print(out, lo.data, lo.bitsize);
        fprintf(out, ", hi = ");
        bvconst_print(out, hi.data, hi.bitsize);
        fprintf(out, "\n");
      }
      if (b && !bvconstant_eq(&lo,&hi))
        result = interval_mk(&exp->super, &lo, &hi, lo_term, hi_term, var, NULL_TERM);
      if (!b) {
        if (!bvconstant_eq(&lo,&hi))
          result = interval_mk(&exp->super, &hi, &lo, hi_term, lo_term, var, NULL_TERM);
        else {
          term_t reason = arith_eq_norm(&exp->norm, lo_term, hi_term);
          result = interval_full_mk(&exp->super, reason, w);
        }
      }
    } else { // No conflict variable on the left, then hi is (c1 - c2)
      bvconstant_copy(&hi, cc1.bitsize, cc1.data);
      bvconstant_sub(&hi, &cc2);
      bvconstant_normalize(&hi);
      hi_term = arith_sub(tm,c1,c2);
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "Case <=: has_right, !has_left, lo = ");
        bvconst_print(out, lo.data, lo.bitsize);
        fprintf(out, ", hi = ");
        bvconst_print(out, hi.data, hi.bitsize);
        fprintf(out, "\n");
      }
      if (b && !bvconstant_eq(&lo,&hi))
        result = interval_mk(&exp->super, &lo, &hi, lo_term, hi_term, var, NULL_TERM);
      if (!b) {
        if (!bvconstant_eq(&lo,&hi))
          result = interval_mk(&exp->super, &hi, &lo, hi_term, lo_term, var, NULL_TERM);
        else {
          term_t reason = arith_eq_norm(&exp->norm, lo_term, hi_term);
          result = interval_full_mk(&exp->super, reason, w);
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
      lo_term = arith_add_one(tm, arith_sub(tm,c2,c1));

      bvconstant_copy(&hi, cc1.bitsize, cc1.data);
      bvconstant_negate(&hi);
      bvconstant_normalize(&hi);
      hi_term = arith_negate(tm,c1);
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "Case <=: !has_right, has_left, lo = ");
        bvconst_print(out, lo.data, lo.bitsize);
        fprintf(out, ", hi = ");
        bvconst_print(out, hi.data, hi.bitsize);
        fprintf(out, "\n");
      }
      if (b && !bvconstant_eq(&lo,&hi))
        result = interval_mk(&exp->super, &lo, &hi, lo_term, hi_term, var, NULL_TERM);
      if (!b) {
        if (!bvconstant_eq(&lo,&hi))
          result = interval_mk(&exp->super, &hi, &lo, hi_term, lo_term, var, NULL_TERM);
        else {
          term_t reason = arith_eq_norm(&exp->norm, lo_term, hi_term);
          result = interval_full_mk(&exp->super, reason, w);
        }
      }
    } else { // x appears on neither sides
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "Case <=: !has_right, !has_left");
      }
      if (b && bvconstant_lt(&cc2,&cc1)) { // If c2 < c1, we forbid everything, otherwise we forbid nothing
        term_t reason = arith_lt_norm(&exp->norm, c2, c1);
        result = interval_full_mk(&exp->super, reason, w);
      }
      if (!b && bvconstant_le(&cc1,&cc2)) { // If c2 < c1, we forbid everything, otherwise we forbid nothing
        term_t reason = arith_le_norm(&exp->norm, c1, c2);
        result = interval_full_mk(&exp->super, reason, w);
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
void arith_add2conflict(arith_t* exp,
                           term_t min_saved_term,
                           interval_t* i,
                           ivector_t* conflict) {

  plugin_context_t* ctx = exp->super.ctx;
  term_manager_t* tm    = ctx->tm;

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Adding to conflict interval ");
    interval_print(out, ctx->terms, i);
    fprintf(out, "  hooking up with ( ");
    term_print_to_file(out, tm->terms, min_saved_term);
    fprintf(out, " )\n");
  }

  assert(!bvconstant_eq(&i->lo, &i->hi));

  term_t small = arith_sub(tm, min_saved_term, i->lo_term);
  term_t big   = arith_sub(tm, i->hi_term, i->lo_term);
  
  term_t continuity_reason = arith_lt_norm(&exp->norm, small, big);
  if (arith_is_no_triv(continuity_reason)) {
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
    assert(interval_get_bitwidth(intervals[i]) == interval_get_bitwidth(intervals[0]));
    // If it is longer than the previous longest, we update the latter
    if (bvconstant_lt(&intervals[result]->length, &intervals[i]->length)){
      result = i;
    }
  }
  return result;
}

static inline
void print_intervals(plugin_context_t* ctx, interval_t** intervals, uint32_t number_intervals){
  FILE* out = ctx_trace_out(ctx);
  for (uint32_t i = 0; i < number_intervals; i++) {
    interval_print(out, ctx->terms, intervals[i]);
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
  uint32_t w            = interval_get_bitwidth(intervals[0][0]); // Bitwidth currently being treated
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
    fprintf(out, "%"PRId32" intervals of bitwidth %"PRId32":\n",n,w);
    print_intervals(ctx, intervals[0], n);
    fprintf(out, "Longest one is ");
    interval_print(out, terms, longest);
    fprintf(out, "\n");
  }

  if (interval_is_full(longest)) { // if interal is full, we're done, we just add the reason
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Using 1 full interval with internal reason ");
      if (longest->reason != NULL_TERM)
        term_print_to_file(out, tm->terms, longest->reason);
      else 
        fprintf(out, " NO_REASON");
      fprintf(out, " and %"PRId32" other reasons\n",longest->reasons.size);
    }
    if (longest->reason != NULL_TERM && arith_is_no_triv(longest->reason)) {
      ivector_push(output, longest->reason);
      uint32_t eval_level = 0;
      assert(bv_evaluator_evaluate_term(exp->super.eval, longest->reason, &eval_level)->b);
      (void) eval_level;
    }
    ivector_add(output, longest->reasons.data, longest->reasons.size);
    return false;
  }

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Longest is not full\n");
  }

  if (inherited != NULL && bvconstant_le(&longest->length,&inherited->length)) {
    longest = inherited;
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Interval inherited from bigger bitwidths is longer. It becomes \"longest\" ");
      interval_print(out, terms, longest);
      fprintf(out, "\n");
    }
  }

  // The lower bound of the longest interval, &longest->lo, will serve as the baseline of the domain for the rest of this function.
  // We sort intervals according to that baseline:
  // as all intervals here have the same bitwidth, the first intervals are those whose lower bound is just after the baseline.
  ptr_array_sort2((void **)intervals[0], n, &longest->lo, interval_cmp);
  
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
    while (inherited_index < n
           && interval_cmp(&longest->lo, intervals[0][inherited_index], inherited))
      inherited_index++;
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
      fprintf(out, "\nbv_arith looks at interval of index %"PRId32" among %"PRId32" (inherited has index %"PRId32") ",j,n,inherited_index);
      interval_print(out, terms, i);
      fprintf(out, "\n");
    }

    if (interval_is_in(saved_hi,i)) { // In continuity of previously forbidden range
      // Does i eliminate more values than best_so_far?
      if ((best_so_far == NULL)
          || ((best_so_far != NULL) && interval_is_in(&best_so_far->hi, i))) { // i becomes best_so_far
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
          interval_print(out, terms, best_so_far);
          fprintf(out, "\n");
        }
        if (first == NULL && interval_is_in(&longest->hi,best_so_far)) {
          first = best_so_far;
          if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
            FILE* out = ctx_trace_out(ctx);
            fprintf(out, "First interval, delaying recording of the hook\n");
          }
        } else { // Otherwise we record best_so_far and its hook
          arith_add2conflict(exp, saved_hi_term, best_so_far, output);
          if (best_so_far == inherited) { result = true; } // inherited was used
        }
        saved_hi      = &best_so_far->hi;
        saved_hi_term = best_so_far->hi_term;
        if (interval_is_in(&best_so_far->hi,longest)) {
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
        term_t literal = arith_eq_norm(&exp->norm, i->lo_term, arith_add_one(tm, saved_hi_term));
        if (arith_is_no_triv(literal))
          ivector_push(output, literal);
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
        if (interval_is_in(saved_hi,longest)) notdone = false;
        continue; // We skip the rest of the loop
      }
      
      // The hole must be filled by lower levels, as done by a recursive call to cover
      assert(bitwidths != 0); // There'd better be at least one more level of smaller bitwidths
      uint32_t next_bitwidth = interval_get_bitwidth(intervals[1][0]);
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "Next bitwidth is %"PRId32".\n",next_bitwidth);
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
      interval_construct(&exp->super, &lo, &hi, lo_term, hi_term, NULL_TERM, NULL_TERM, &hole);
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "OK, now there is a hole: ");
        interval_print(out, terms, &hole);
        fprintf(out, " for which (length-1) is ");
        bvconst_print(out, hole.length.data, hole.length.bitsize);
      }
      // We will record whether the (complement of the) hole is used by the smaller bitwidths
      bool hole_used;
      // We project lo_term and hi_term into the domain of smaller bitwidth
      term_t lo_proj_term = arith_normalise_upto(&exp->norm, lo_term, next_bitwidth);
      term_t hi_proj_term = arith_normalise_upto(&exp->norm, hi_term, next_bitwidth);
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
        interval_construct(&exp->super, &hi_proj, &lo_proj, hi_proj_term, lo_proj_term, NULL_TERM, NULL_TERM, &hole_complement);
        if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
          FILE* out = ctx_trace_out(ctx);
          fprintf(out, " < ");
          bvconst_print(out, smaller_values.data, smaller_values.bitsize);
          fprintf(out, "\nHole is smaller than the domain of the next bitwidth, we recursively call cover on complemented and projected hole: ");
          interval_print(out, terms, &hole_complement);
          fprintf(out, "\n");
        }
        hole_used = cover(exp, &rec_output,
                          bitwidths-1, &intervals[1], &numbers[1],
                          &hole_complement,
                          (substitution != NULL && rec_substitution == NULL_TERM) ? &rec_substitution : NULL);
        interval_delete(&hole_complement);
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
        fprintf(out, "Back to bitwidth %"PRId32"!\n",w);
      }
      // If we are explaining a propagation and got a feasible value in the hole:
      if (substitution != NULL && rec_substitution != NULL_TERM) {
        term_t diff = arith_sub(tm, rec_substitution, lo_proj_term);
        substitution[0] = arith_add(tm, lo_term, arith_upextension(tm, diff, false_term, w));
        if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
          FILE* out = ctx_trace_out(ctx);
          fprintf(out, "Hole was from ");
          term_print_to_file(out, terms, lo_term);
          fprintf(out, " to ");
          term_print_to_file(out, terms, hi_term);
          fprintf(out, " and the only possible value at bitwidth %"PRId32" is ",w);
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
          fprintf(out, "The recursive call used the hole we left uncovered at bitwidth %"PRId32" and/or found 1 feasible value .\n",w);
        }
        term_t literal = (hole_used) ?
          arith_lt_norm(&exp->norm, arith_sub(tm, hi_term, lo_term), smaller_values_term) :
          arith_le_norm(&exp->norm, arith_sub(tm, hi_term, substitution[0]), smaller_values_term);
        if (arith_is_no_triv(literal)) {
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
        if (interval_is_in(saved_hi,longest)) notdone = false;
      }
      ivector_add(output, rec_output.data, rec_output.size);
      delete_ivector(&rec_output);
      delete_bvconstant(&lo);
      delete_bvconstant(&hi);
      delete_bvconstant(&smaller_values);
      interval_delete(&hole);
    }
  }

  if (saved_hi_term != NULL_TERM) {
    if (best_so_far != NULL && first != NULL && interval_is_in(saved_hi,first)) {
      // We didn't actually need longest, best_so_far plays the role of longest
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "No need for longest interval, as saved_hi is ");
        bvconst_print(out, saved_hi->data, saved_hi->bitsize);
        fprintf(out, "\nand first is ");
        interval_print(out, terms, first);
        fprintf(out, "\n");
      }
      arith_add2conflict(exp, saved_hi_term, first, output);
      if (first == inherited) { result = true; } // inherited was used
    } else {
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "Adding to conflict longest interval ");
        interval_print(out, terms, longest);
        fprintf(out, "\n");
      }
      arith_add2conflict(exp, saved_hi_term, longest, output);
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
          interval_print(out, terms, longest);
          fprintf(out, "\n");
          interval_print(out, terms, first);
          fprintf(out, "\n");
        }
        arith_add2conflict(exp, longest->hi_term, first, output);
        if (first == inherited) { result = true; } // inherited was used
      }
    }
  }
  ivector_remove_duplicates(output);
  return result;
}

void transform_interval(arith_t* exp, interval_t** interval) {

  plugin_context_t* ctx = exp->super.ctx;
  term_manager_t* tm    = ctx->tm;
  term_table_t* terms   = ctx->terms;

  if (!interval_is_full(interval[0])) {
  
    uint32_t w = term_bitsize(terms, interval[0]->var);

    if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Transforming non-full interval ");
      interval_print(out, ctx->terms, interval[0]);
      fprintf(out, "\nNow analysing the shape of the interval's variable (of bitsize %"PRId32")\n",w);
    }

    // We analyse the shape of the variable whose value is forbidden to be in interval[0]
    arith_analyse_t* ts = arith_analyse(&exp->norm,interval[0]->var);
    assert(arith_is_zero(terms, ts->garbage));    // Otherwise it wouldn't be in the fragment
    assert(ts->length != 0); // Otherwise the term is evaluable
    assert(arith_is_zero(terms, ts->eval)); // The variable should only have zeros as evaluable bits
    assert(ts->base != NULL_TERM); // There should be a base
    assert(ts->base == exp->norm.csttrail.conflict_var_term // Either it's the conflict variable
           || term_bitsize(terms,ts->base) == ts->start + ts->length);
    // or the top pruning has been pushed further inside the base

    bool is_empty = interval_uptrim(&exp->super, &exp->norm, ts->suffix+ts->length, interval[0]);
    (void) is_empty; // Otherwise compilation warning
    assert(!is_empty);
    is_empty = interval_downtrim(&exp->super, &exp->norm, ts->suffix, interval[0]);
    assert(!is_empty);
    interval_downextend(&exp->super, ts->start, interval[0]);

    switch (term_kind(terms, ts->base)) {
    case BV_POLY:
    case BV64_POLY: {
      polypair_t* p = bv_arith_coeff(exp, ts->base, true);
      assert(p != NULL);
      assert(term_kind(terms, p->var) != BV_POLY
             && term_kind(terms, p->var) != BV64_POLY );
      assert(p->coeff == 1 || p->coeff == -1);
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "Base is ");
        ctx_trace_term(ctx, ts->base);
        fprintf(out, "Coeff is %"PRId32", while polyrest is ", (p->coeff == 1) ? 1 : -1);
        ctx_trace_term(ctx, p->polyrest);
      }
      interval_subtract(&exp->super,p->polyrest,interval[0]);
      if (p->coeff == -1)
        interval_negate(&exp->super,interval[0]);
      interval[0]->var = p->var;
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "New variable is ");
        ctx_trace_term(ctx, interval[0]->var);
      }
      transform_interval(exp, interval);
      break;
    }
    default: {
      assert(ts->base == exp->norm.csttrail.conflict_var_term);
      interval[0]->var = term_extract(tm, ts->base, 0, ts->start + ts->length);
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "New variable is ");
        term_print_to_file(out, tm->terms, interval[0]->var);
        fprintf(out, "\n");
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
  assert(exp->norm.csttrail.conflict_var == var); 

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

    term_t t0prime = NULL_TERM;
    term_t t1prime = NULL_TERM;

    if (term_kind(terms, atom_i_term) == BIT_TERM) {
      term_t t0 = arith_normalise(&exp->norm, atom_i_term);
      t0prime = term_extract(tm, t0, 0, 1);
      t1prime = arith_add_one(tm, arith_zero(tm, 1));
    } else {
      composite_term_t* atom_i_comp = composite_term_desc(terms, atom_i_term);
      assert(atom_i_comp->arity == 2);
      term_t t0 = atom_i_comp->arg[0];
      term_t t1 = atom_i_comp->arg[1];
      assert(is_pos_term(t0));
      assert(is_pos_term(t1));
      t0 = arith_normalise(&exp->norm, t0);
      t1 = arith_normalise(&exp->norm, t1);

      switch (term_kind(terms, atom_i_term)) {
      case BV_GE_ATOM: {  
        t0prime = t0;
        t1prime = t1;
        break;
      }
      case BV_SGE_ATOM: {  // (t0 >=s t1) is equivalent to (t0+2^{w-1} >=u t1+2^{w-1})
        t0prime = arith_add_half(tm, t0);
        t1prime = arith_add_half(tm, t1);
        break;
      }
      case EQ_TERM :     
      case BV_EQ_ATOM: { // equality
        uint32_t w = term_bitsize(terms, t0);
        t0prime = arith_zero(tm, w);
        t1prime = arith_sub(tm, t0, t1);
        break;
      }
      default:
        assert(false);
      }
    }
    t0prime = arith_normalise(&exp->norm, t0prime);
    t1prime = arith_normalise(&exp->norm, t1prime);
    intervals[i] = bv_arith_unit_le(exp, t1prime, t0prime, atom_i_value);

    if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "explain: created one interval, let's see if it needs transforming\n");
    }
    if (intervals[i] != NULL) {
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
        interval_print(out, ctx->terms, intervals[i]);
      }
      fprintf(out, "\n");
    }
    fprintf(out, "And now after we sort them:\n");
  }

  ptr_array_sort2((void**)intervals, n, NULL, interval_cmp); // We sort the intervals  
  assert(intervals[0] != NULL); // There should be at least one non-empty interval
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Looking at interval ");
    interval_print(out, ctx->terms, intervals[0]);
    fprintf(out, "\n");
  }
  uint32_t nonemptys = 1; // Total number of non-empty intervals is about to get computed
  uint32_t bitwidths = 1; // Total number of distinct bitwidths is about to get computed
  for (; (nonemptys < n) && (intervals[nonemptys] != NULL); nonemptys++) {
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Looking at interval ");
      interval_print(out, ctx->terms, intervals[nonemptys]);
      fprintf(out, "\n");
    }
    if (interval_get_bitwidth(intervals[nonemptys-1]) != interval_get_bitwidth(intervals[nonemptys])){
      bitwidths++;
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "Found new bitwidth %"PRId32" (old was %"PRId32")\n",interval_get_bitwidth(intervals[nonemptys]),interval_get_bitwidth(intervals[nonemptys-1]));
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
    if (interval_get_bitwidth(intervals[i-1]) != interval_get_bitwidth(intervals[i])) {
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
    fprintf(out, "\nWe now look at the %"PRId32" forbidden intervals we have collected (of %"PRId32" different bitwidths), which are\n",nonemptys,bitwidths);
    for (uint32_t j = 0; j < bitwidths; j++) { // Looping on different bitwidths
      fprintf(out, "%"PRId32" intervals of bitwidth %"PRId32":\n",
              bitwidth_numbers[j], interval_get_bitwidth(bitwidth_intervals[j][0]));
      for (uint32_t i = 0; i < bitwidth_numbers[j]; i++) {
        interval_print(out, ctx->terms, bitwidth_intervals[j][i]);
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
    interval_destruct(intervals[i]);
  }

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Returned reasons are:\n");
    for (uint32_t i = 0; i < reasons_out->size; i++) {
      fprintf(out,"[%"PRId32"]",i);
      ctx_trace_term(ctx, reasons_out->data[i]);
    }
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
  arith_t* exp            = (arith_t*) this;
  bv_csttrail_t* csttrail = &exp->norm.csttrail;
  plugin_context_t* ctx   = this->ctx;
  term_manager_t* tm      = ctx->tm;
  term_table_t* terms     = ctx->terms;
  uint32_t result         = true;
  
  // We're facing a new problem, with a trail we don't know
  // We must reset the cache & co.
  // which date back from a previous conflict or propagation
  bv_evaluator_csttrail_reset(csttrail, conflict_var, 2); // 2 is the level of optimisation fit for the arith explainer
  freeval(exp);
  reset_arith_norm(&exp->norm);
  ptr_hmap_reset(&exp->coeff_cache);
  
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::count")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "bv_arith looks at new conflict of size %"PRId32" with conflict variable ",conflict_core->size);
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
      fprintf(out, "bv_arith looks at whether constraint %"PRId32" is in the fragment: ",i);
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
      assert(is_pos_term(t0) && is_pos_term(t1));
      // OK, maybe we can treat the constraint atom_term. We first scan the atom (collecting free variables and co.)
      bv_evaluator_csttrail_scan(csttrail, atom_var);
      
      // Now that we have collected the free variables, we look into the constraint structure
      polypair_t* p0 = bv_arith_coeff(exp, t0, false);
      polypair_t* p1 = bv_arith_coeff(exp, t1, false);
      if (p0 == NULL) {
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
      if (p1 == NULL) {
        // Turns out we actually can't deal with the constraint. We stop
        if (ctx_trace_enabled(ctx, "mcsat::bv::arith::fail")) {
          FILE* out = ctx_trace_out(ctx);
          fprintf(out, "Right-hand no good for ");
          ctx_trace_term(ctx, csttrail->conflict_var_term);
          ctx_trace_term(ctx, atom_term);
        }
        result = false;
        break;
      }
      term_t var0 = p0->var;
      term_t var1 = p1->var;
      int32_t t0_coeff = p0->coeff;
      int32_t t1_coeff = p1->coeff;
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "can_explain gets coefficients %"PRId32" and %"PRId32" for monomial variables ", t0_coeff, t1_coeff);
        if (var0 != NULL_TERM)
          term_print_to_file(out, terms, var0);
        else 
          fprintf(out, "NOT_PRESENT");
        fprintf(out, " and ");
        if (var1 != NULL_TERM)
          term_print_to_file(out, terms, var1);
        else 
          fprintf(out, "NOT_PRESENT");
        fprintf(out, "\n");
      }
      if (var0 != NULL_TERM && var1 != NULL_TERM && var0 != var1) {
        // Turns out we actually can't deal with the constraint. We stop
        if (ctx_trace_enabled(ctx, "mcsat::bv::arith::fail")) {
          FILE* out = ctx_trace_out(ctx);
          fprintf(out, "Unevaluable monomials are different");
        }
        result = false;
        break;
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
      break;
    }
    case BIT_TERM: {
      assert(is_pos_term(bit_term_arg(terms, atom_term)));
      // OK, maybe we can treat the constraint atom_term. We first scan the atom (collecting free variables and co.)
      bv_evaluator_csttrail_scan(csttrail, atom_var);
      
      // Now that we have collected the free variables, we look into the constraint structure
      polypair_t* p = bv_arith_coeff(exp, term_extract(tm, atom_term, 0, 1), false);
      if (p == NULL) {
        // Turns out we actually can't deal with the constraint. We stop
        if (ctx_trace_enabled(ctx, "mcsat::bv::arith::fail")) {
          FILE* out = ctx_trace_out(ctx);
          fprintf(out, "Atom no good for ");
          ctx_trace_term(ctx, csttrail->conflict_var_term);
          ctx_trace_term(ctx, atom_term);
        }
        result = false;
        break;
      }
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "can_explain gets coefficient %"PRId32" for variable ", p->coeff);
        if (p->var != NULL_TERM)
          term_print_to_file(out, terms, p->var);
        else 
          fprintf(out, "NOT_PRESENT");
        fprintf(out, "\n");
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
  bv_evaluator_csttrail_destruct(&exp->norm.csttrail);
  arith_norm_freeval(&exp->norm);
  freeval(exp);
  delete_arith_norm(&exp->norm);
  delete_ptr_hmap(&exp->coeff_cache);
}

/** Allocate the sub-explainer and setup the methods */
bv_subexplainer_t* arith_new(plugin_context_t* ctx, watch_list_manager_t* wlm, bv_evaluator_t* eval) {

  arith_t* exp = safe_malloc(sizeof(arith_t));

  bv_subexplainer_construct(&exp->super, "mcsat::bv::explain::arith", ctx, wlm, eval);
  bv_evaluator_csttrail_construct(&exp->norm.csttrail, ctx, wlm, eval);
                                
  exp->super.can_explain_conflict = can_explain_conflict;
  exp->super.explain_conflict = explain_conflict;
  exp->super.can_explain_propagation = can_explain_propagation;
  exp->super.explain_propagation = explain_propagation;
  exp->super.destruct = destruct;

  init_arith_norm(&exp->norm);
  init_ptr_hmap(&exp->coeff_cache, 0);

  return (bv_subexplainer_t*) exp;
}
