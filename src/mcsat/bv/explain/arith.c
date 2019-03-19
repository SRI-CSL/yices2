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
#include "terms/bv64_constants.h"
#include "terms/term_manager.h"
#include "terms/term_utils.h"
#include "utils/int_hash_sets.h"
#include "utils/ptr_heap.h"
#include "utils/ptr_queues.h"

#include "arith.h"

/**
   Subexplainer type
**/

typedef struct arith_s {

  /** Interfact of the subexplainer */
  bv_subexplainer_t super;

  bv_csttrail_t csttrail; // Where we keep some cached values
  int_hset_t coeff1_cache; // Cache of terms whose coeff for conflict_var is 1
  int_hset_t coeffm1_cache; // Cache of terms whose coeff for conflict_var is -1

} arith_t;


// Function returns coefficient of conflict_variable in t (-1, 0, or 1)
// It uses cached values, and caches new values.
// if t is not a good term for the fragment:
// if !assume_fragment, function will return 2,
// if assume_fragment, function has unspecified behaviour (but runs faster)

int32_t bv_arith_coeff(arith_t* exp, term_t t, term_t conflict_var, bool assume_fragment) {

  plugin_context_t* ctx = exp->super.ctx;
    
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "extracting coefficient of conflict variable in ");
    ctx_trace_term(ctx, t);
  }

  // Looking at whether the value is cached
  if (int_hset_member(&exp->coeff1_cache,t)) return 1;
  if (t == conflict_var) {
    int_hset_add(&exp->coeff1_cache, t);
    return 1;
  }
  if (int_hset_member(&exp->coeffm1_cache,t)) return -1;
  bool ignore_this_bool;
  if (bv_evaluator_is_evaluable(&exp->csttrail, t, &ignore_this_bool)) return 0;

  int32_t result = 0;

  switch (term_kind(ctx->terms, t)) {
  case BV_POLY: {
    bvpoly_t* t_poly = bvpoly_term_desc(ctx->terms, t);
    for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
      if (t_poly->mono[i].var == const_idx) continue;
      if (t_poly->mono[i].var == conflict_var) { // Monomial variable is the conflict var
        assert (result == 0); // in theory, the conflict variable shouldn't be seen twice
        if (bvconst_is_one(t_poly->mono[i].coeff, t_poly->width)) result = 1;
        else {
          if (bvconst_is_minus_one(t_poly->mono[i].coeff, t_poly->bitsize)) result = -1;
          else return 2;
        };
        if (assume_fragment) break; // If in fragment, need not look at other monomials
      } else { // The monomial variable is not the conflict var itself
        if (!assume_fragment
            && !bv_evaluator_is_evaluable(&exp->csttrail, t_poly->mono[i].var, &ignore_this_bool)) {
          return 2;
        }
      }
    }
    break;
  }
  case BV64_POLY: {
    bvpoly64_t* t_poly = bvpoly64_term_desc(ctx->terms, t);
    for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
      if (t_poly->mono[i].var == const_idx) continue;
      if (t_poly->mono[i].var == conflict_var) { // Monomial variable is the conflict var
        assert (result == 0); // in theory, the conflict variable shouldn't be seen twice
        if (t_poly->mono[i].coeff == 1) result = 1;
        else {
          if (bvconst64_is_minus_one(t_poly->mono[i].coeff,term_bitsize(ctx->terms,t))) result = -1;
          else return 2;
        }
        if (assume_fragment) break; // If in fragment, need not look at other monomials
      } else { // The monomial variable is not the conflict var itself
        if (!assume_fragment
            && !bv_evaluator_is_evaluable(&exp->csttrail, t_poly->mono[i].var, &ignore_this_bool)) {
          return 2;
        }
      }
    }
    break;
  }
  default:
    return 2;
  }
  
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Coefficient is %d\n",result);
  }
  int_hset_add((result == 1)? (&exp->coeff1_cache):(&exp->coeffm1_cache), t);
  return result;
}



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
  term_t lo_term;
  term_t hi_term; 
  term_t reason;
} bvconst_interval_t;


// Comparing two intervals: just comparing their lower bound. Used by the interval heap datastructure
bool cmp(void *x, void *y){
  bvconst_interval_t* i1 = (bvconst_interval_t*) x;
  bvconst_interval_t* i2 = (bvconst_interval_t*) y;
  if (bvconstant_eq(&i1->lo,&i2->lo))
    return bvconstant_le(&i2->hi,&i1->hi);
  return bvconstant_le(&i1->lo,&i2->lo);
}

void bv_arith_interval_destruct(bvconst_interval_t* i) {
  delete_bvconstant(&i->lo);
  delete_bvconstant(&i->hi);
  safe_free(i);
}

void bv_arith_interval_print(FILE* out, term_table_t* terms, bvconst_interval_t* i) {
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


/**
   Local context for each conflict explanation instance, and how it manipulates intervals
**/

// Local context
typedef struct {
  arith_t* exp;
  bvconstant_t zero; // Because we don't like recomputing this too many times
  term_t zero_term;  // Because we don't like recomputing this too many times
  ptr_heap_t heap;   // Heap of forbidden intervals, ordered by lower bounds
  bvconst_interval_t* longest; // Longest interval the heap has ever seen
  bvconstant_t length; // Its length
  ptr_queue_t queue; // Where we may store intervals popped from the heap
} bv_arith_ctx_t;


// Adds a newly constructed interval into the heap
void bv_arith_interval_push(bv_arith_ctx_t* lctx,
                            const bvconstant_t* lo,
                            const bvconstant_t* hi,
                            term_t lo_term,
                            term_t hi_term,
                            term_t reason) {
  plugin_context_t* ctx = lctx->exp->super.ctx;
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Creating interval from lo = ");
    bvconst_print(out, lo->data, lo->bitsize);
    fprintf(out, ", hi = ");
    bvconst_print(out, hi->data, hi->bitsize);
    fprintf(out, ", lo_term = ");
    term_print_to_file(out, ctx->terms, lo_term);
    fprintf(out, ", hi_term = ");
    term_print_to_file(out, ctx->terms, hi_term);
    fprintf(out, "\n");
  }
  
  assert(bvconstant_is_normalized(lo));
  assert(bvconstant_is_normalized(hi));

  bvconst_interval_t* result = safe_malloc(sizeof(bvconst_interval_t));
  init_bvconstant(&result->lo);
  init_bvconstant(&result->hi);
  result->lo_term = lo_term;
  result->hi_term = hi_term;
  result->reason  = reason;

  bvconstant_copy(&result->lo, lo->bitsize, lo->data);
  bvconstant_copy(&result->hi, hi->bitsize, hi->data);

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "bv_arith creates interval ");
    bv_arith_interval_print(out, ctx->terms, result);
    fprintf(out, "\n");
  }

  ptr_heap_add(&lctx->heap, (void *) result);

  // Now we compute the length of the interval
  bvconstant_t length;
  init_bvconstant(&length);
  bvconstant_copy(&length, hi->bitsize, hi->data);
  bvconstant_sub(&length, lo);
  bvconstant_normalize(&length);
  // If it is longer than the previous longest, we update the latter
  if (bvconstant_lt(&lctx->length, &length)){
    lctx->longest = result;
    bvconstant_copy(&lctx->length, length.bitsize, length.data);
  }
  delete_bvconstant(&length);
}

static inline
void bv_arith_full_interval_push(bv_arith_ctx_t* lctx, term_t reason) {
  bvconstant_t* zero = &lctx->zero;
  bv_arith_interval_push(lctx,zero,zero,lctx->zero_term,lctx->zero_term,reason);
}

void bv_arith_singleton_push(bv_arith_ctx_t* lctx,
                             const bvconstant_t* lo,
                             term_t lo_term,
                             term_t reason) {
  plugin_context_t* ctx = lctx->exp->super.ctx;
  term_manager_t* tm    = &ctx->var_db->tm;
  bvconstant_t hi;
  init_bvconstant(&hi);
  bvconstant_copy(&hi, lo->bitsize, lo->data);
  bvconstant_add_one(&hi);
  bvconstant_normalize(&hi);
  term_t hi_term = bv_arith_add_one_term(tm, lo_term);
  bv_arith_interval_push(lctx,lo,&hi,lo_term,hi_term,reason);
  delete_bvconstant(&hi);
}


/**
   Making atoms. Assumption for these functions:
   the atom to be build evaluates to true according to the trail.
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
term_t bv_arith_lt(bv_arith_ctx_t* lctx, term_t left, term_t right) {
  plugin_context_t* ctx = lctx->exp->super.ctx;
  term_manager_t* tm    = &ctx->var_db->tm;
  term_table_t* terms   = tm->terms;
  assert (left != right);
  assert (!bv_arith_is_zero(terms, right));
  assert (!bv_arith_is_minus_one(terms, left));
  if (is_const_term(terms, left) && is_const_term(terms, right)) {
    return NULL_TERM;
  }
  // (left < 1) turns into (left == 0)
  if (bv_arith_is_one(terms, right)) {
    return bveq_atom(terms, left,lctx->zero_term);
  }
  // (left < -1) turns into (left+1 != 0)
  if (bv_arith_is_minus_one(terms, right)) {
    return not_term(terms, bveq_atom(terms, bv_arith_sub_terms(tm, left, right),lctx->zero_term));
  }
  // (0 < right) turns into (right != 0)
  if (bv_arith_is_zero(terms, left)) {
    return not_term(terms, bveq_atom(terms, right,lctx->zero_term));
  }
  return not_term(terms, bvge_atom(terms, left, right));
}


/**
   Explanation mechanism. First for 1 constraint. Then for the whole conflict
**/

// Analyses one side of an atom, assumed to be in the fragment.
// t is the side, coeff is the coeff of the conflict var, cc is a non-initialised bv_constant
// returns the "rest of the term" (monomial of the conflict var is removed), and places the result of its evaluation in cc
term_t bv_arith_init_side(bv_arith_ctx_t* lctx, term_t t, uint32_t coeff, bvconstant_t* cc) {

  // Standard abbreviations
  term_t conflict_var   = lctx->exp->csttrail.conflict_var_term;
  plugin_context_t* ctx = lctx->exp->super.ctx;
  term_manager_t* tm    = &ctx->var_db->tm;

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Initialising constraint_side ");
    term_print_to_file(out, ctx->terms, t);
    fprintf(out, "\n");
  }

  term_t result = // The term without the unevaluable monomial
    (coeff > 0) ?
    bv_arith_sub_terms(tm, t, conflict_var) :
    ((coeff < 0) ?
     bv_arith_add_terms(tm, t, conflict_var) : t);

  // We evaluate this...
  uint32_t eval_level = 0;
  const mcsat_value_t* value = bv_evaluator_evaluate_term(lctx->exp->super.eval, result, &eval_level);
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
void bv_arith_unit_le(bv_arith_ctx_t* lctx, term_t lhs, term_t rhs, bool b) {
  // Standard abbreviations
  term_t conflict_var   = lctx->exp->csttrail.conflict_var_term;
  plugin_context_t* ctx = lctx->exp->super.ctx;
  term_manager_t* tm    = &ctx->var_db->tm;

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "\nTreating unit_constraint (lhs <= rhs) where lhs is ");
    term_print_to_file(out, ctx->terms, lhs);
    fprintf(out, " and rhs is ");
    term_print_to_file(out, ctx->terms, rhs);
    fprintf(out, "\n");
  }

  int32_t left_coeff  = bv_arith_coeff(lctx->exp, lhs, conflict_var, true);
  int32_t right_coeff = bv_arith_coeff(lctx->exp, rhs, conflict_var, true);
    
  if ((left_coeff == -1) || (right_coeff == -1)) {
    // if coeff is negative, we add one, negate and swap sides.
    term_t nlhs = bv_arith_negate_terms(tm, bv_arith_add_one_term(tm, lhs));
    term_t nrhs = bv_arith_negate_terms(tm, bv_arith_add_one_term(tm, rhs));
    return bv_arith_unit_le(lctx, nrhs, nlhs, b);
  }

  // Setting c1 and c2 to be 2 terms representing the left polynomial and the right polynomial,
  // from which the confict variable (if present) was removed,
  // and evaluating those polynomials c1 and c2 (whose variables should all have values on the trail)
  bvconstant_t cc1, cc2;
  term_t c1 = bv_arith_init_side(lctx, lhs, left_coeff, &cc1);
  term_t c2 = bv_arith_init_side(lctx, rhs, right_coeff, &cc2);

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
        bv_arith_interval_push(lctx, &lo, &hi, lo_term, hi_term, NULL_TERM);
      if (!b) {
        if (!bvconstant_eq(&lo,&hi))
          bv_arith_interval_push(lctx, &hi, &lo, hi_term, lo_term, NULL_TERM);
        else {
          term_t reason = bv_arith_eq(tm, lo_term, hi_term);
          bv_arith_full_interval_push(lctx, reason);
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
        bv_arith_interval_push(lctx, &lo, &hi, lo_term, hi_term, NULL_TERM);
      if (!b) {
        if (!bvconstant_eq(&lo,&hi))
          bv_arith_interval_push(lctx, &hi, &lo, hi_term, lo_term, NULL_TERM);
        else {
          term_t reason = bv_arith_eq(tm, lo_term, hi_term);
          bv_arith_full_interval_push(lctx, reason);
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
        bv_arith_interval_push(lctx, &lo, &hi, lo_term, hi_term, NULL_TERM);
      if (!b) {
        if (!bvconstant_eq(&lo,&hi))
          bv_arith_interval_push(lctx, &hi, &lo, hi_term, lo_term, NULL_TERM);
        else {
          term_t reason = bv_arith_eq(tm, lo_term, hi_term);
          bv_arith_full_interval_push(lctx, reason);
        }
      }
    } else { // x appears on neither sides
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "Case <=: !has_right, !has_left");
      }
      if (b && bvconstant_lt(&cc2,&cc1)) { // If c2 < c1, we forbid everything, otherwise we forbid nothing
        term_t reason = bv_arith_lt(lctx, c2, c1);
        bv_arith_full_interval_push(lctx, reason);
      }
      if (!b && !bvconstant_lt(&cc2,&cc1)) { // If c2 < c1, we forbid everything, otherwise we forbid nothing
        term_t reason = not_term(tm->terms,bv_arith_lt(lctx, c2, c1));
        bv_arith_full_interval_push(lctx, reason);
      }
    }
  }
  
  delete_bvconstant(&cc1);
  delete_bvconstant(&cc2);    
  delete_bvconstant(&lo);
  delete_bvconstant(&hi);    
}


// Shift interval down by base and base_term
void bv_arith_ishift(plugin_context_t* ctx,
                     bvconst_interval_t* i,
                     bvconstant_t* base,
                     term_t base_term) {
  /* term_manager_t* tm = &ctx->var_db->tm; */
  bvconstant_sub(&i->lo, base);
  bvconstant_normalize(&i->lo);
  /* i->lo_term = bv_arith_sub_terms(tm, i->lo_term, base_term);   */
  bvconstant_sub(&i->hi, base);
  bvconstant_normalize(&i->hi);
  /* i->hi_term = bv_arith_sub_terms(tm, i->hi_term, base_term); */
}


// Adds interval to conflict, and destructs it
void bv_arith_add2conflict(bv_arith_ctx_t* lctx,
                           term_t min_saved_term,
                           bvconst_interval_t* i,
                           ivector_t* conflict) {

  arith_t* exp          = lctx->exp;
  plugin_context_t* ctx = exp->super.ctx;
  term_manager_t* tm    = &ctx->var_db->tm;

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
  
  term_t continuity_reason = bv_arith_lt(lctx, small, big);
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
  
  bv_arith_interval_destruct(i);
}

// Popping the longest interval in the heap,
// then the next ones in order of increasing lower bound, modulo 2^n
// (once this function starts being called, do not push anything in the heap any more)
bvconst_interval_t* bv_arith_pop(bv_arith_ctx_t* lctx){
  bvconst_interval_t* i = ptr_heap_get_min(&lctx->heap);
  if (i == NULL) { // Heap is empty. We now get elements from the queue.
    if (ptr_queue_is_empty(&lctx->queue)) return NULL; // ...unless there are none
    else return ptr_queue_pop(&lctx->queue);
  }
  // Heap is not empty.
  if (lctx->longest == NULL) return i; // Longest interval has been popped.
  // Longest interval has not been popped.
  if (lctx->longest == i) { // This is the longest interval
    lctx->longest = NULL; // we mark it as popped
    return i; // and return it
  }
  ptr_queue_push(&lctx->queue, i); // It's not the longest, we stash it in the queue
  return bv_arith_pop(lctx);
}


static
void explain_conflict(bv_subexplainer_t* this, const ivector_t* conflict_core, variable_t conflict_var, ivector_t* conflict) {

  arith_t* exp = (arith_t*) this;
  plugin_context_t* ctx = this->ctx;
  bv_evaluator_t* eval = this->eval;
  
  bv_evaluator_clear_cache(eval);

  // Standard abbreviations
  term_table_t* terms        = ctx->terms;
  const mcsat_trail_t* trail = ctx->trail;
  term_manager_t* tm         = &ctx->var_db->tm;
  uint32_t bitsize = term_bitsize(terms, exp->csttrail.conflict_var_term);

  // We initialise the local context
  bv_arith_ctx_t lctx;
  lctx.exp          = exp;
  lctx.longest      = NULL;
  init_ptr_heap(&lctx.heap, 0, &cmp);
  init_ptr_queue(&lctx.queue, 0);

  init_bvconstant(&lctx.zero);
  bvconstant_set_all_zero(&lctx.zero, bitsize);

  lctx.zero_term = mk_bv_constant(tm, &lctx.zero);

  init_bvconstant(&lctx.length);
  bvconstant_set_all_zero(&lctx.length, bitsize);
  
  // Variables that are going to be re-used for every item in the conflict core
  variable_t atom_i_var;
  bool       atom_i_value;
  term_t     atom_i_term;

  // We go through the conflict core
  
  for (uint32_t i = 0; i < conflict_core->size; i++) {
    
    atom_i_var   = conflict_core->data[i];
    atom_i_value = trail_get_boolean_value(trail, atom_i_var);
    atom_i_term  = variable_db_get_term(ctx->var_db, atom_i_var);

    assert(good_term(terms,atom_i_term) && is_pos_term(atom_i_term));
    assert(is_boolean_term(terms, atom_i_term));
    
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "\nbv_arith treats core constraint (%s): ",atom_i_value?"T":"F");
      ctx_trace_term(ctx, atom_i_term);
    }

    // The output conflict always contains the conflict core:
    ivector_push(conflict, atom_i_value?atom_i_term:not_term(terms, atom_i_term));

    composite_term_t* atom_i_comp = composite_term_desc(terms, atom_i_term);
    assert(atom_i_comp->arity == 2);
    term_t t0 = atom_i_comp->arg[0];
    term_t t1 = atom_i_comp->arg[1];
    assert(is_pos_term(t0));
    assert(is_pos_term(t1));

    switch (term_kind(terms, atom_i_term)) {
    case BV_GE_ATOM: {  
      bv_arith_unit_le(&lctx, t1, t0, atom_i_value);
      break;
    }
    case BV_SGE_ATOM: {  // (t0 >=s t1) is equivalent to (t0+2^{w-1} >=u t1+2^{w-1}) // TODO: check this
      term_t t0prime = bv_arith_add_half(tm, t0);
      term_t t1prime = bv_arith_add_half(tm, t1);
      bv_arith_unit_le(&lctx, t1prime, t0prime, atom_i_value);
      break;
    }
    case EQ_TERM :     
    case BV_EQ_ATOM: { // equality
      bv_arith_unit_le(&lctx, bv_arith_sub_terms(tm, t0, t1), lctx.zero_term, atom_i_value);
      break;
    }
    default:
      assert(false);
    }
  }

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "\nWe now look at what's in the heap\n\n");
  }

  /* All conflicting atoms have been treated, the resulting forbidden intervals for the
  conflict_var have been pushed in the heap. It's now time to look at what's in the heap. */
  
  bvconst_interval_t* longest = bv_arith_pop(&lctx);
  assert(longest!=NULL);

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Longest interval is ");
    bv_arith_interval_print(out, ctx->terms, longest);
    fprintf(out, "\n");
  }
  
  if (longest->lo_term == longest->hi_term) { // it's the full interval
    if (longest->reason != NULL_TERM) {
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "Using 1 full interval with internal reason ");
        term_print_to_file(out, tm->terms, longest->reason);
        fprintf(out, "\n");
      }
      uint32_t eval_level = 0;
      assert(bv_evaluator_evaluate_term(exp->super.eval, longest->reason, &eval_level)->b);
      ivector_push(conflict, longest->reason);
    }
    bv_arith_interval_destruct(longest);
  }
  else {  // Saving longest interval's lower bound.
    bvconstant_t base;
    init_bvconstant(&base);
    bvconstant_copy(&base, longest->lo.bitsize, longest->lo.data);
    term_t base_term = longest->lo_term; 

    // We will now shift down every interval by that quantity, to change where our 0 is.
    bv_arith_ishift(ctx, longest, &base, base_term); // longest is now of the form [0 ; ... [

    // The elements saved in &conflict so far force the first feasible value for conflict_var to be at least min_saved
    bvconstant_t min_save;
    init_bvconstant(&min_save);
    bvconstant_copy(&min_save, longest->hi.bitsize, longest->hi.data);
    term_t min_saved_term = longest->hi_term; // The term behind this lower bound of feasible values

    // The best interval found so far in the heap, but not yet saved in &conflict,
    // that can be used to forbid the greatest number of bv values beyond min_saved
    bvconst_interval_t* best_so_far = NULL;

    bvconst_interval_t* i = bv_arith_pop(&lctx);
    bv_arith_ishift(ctx, i, &base, base_term);

    // Now we treat the heap
    while (i != NULL && !bvconstant_is_zero(&min_save)) {
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "bv_arith pops from the heap ");
        bv_arith_interval_print(out, terms, i);
        fprintf(out, "\n");
      }
      if (bvconstant_le(&i->lo, &min_save)) { // In continuity of previously forbidden range
        if (bvconstant_le(&i->hi, &i->lo)) { // Yeah! interval forbids all remaining values
          if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
            FILE* out = ctx_trace_out(ctx);
            fprintf(out, "finished the job\n");
          }
          if (best_so_far != NULL) bv_arith_interval_destruct(best_so_far);
          term_t previous_min_saved_term = min_saved_term;
          min_saved_term = i->hi_term;
          bv_arith_add2conflict(&lctx, previous_min_saved_term, i, conflict); // record and destruct the interval i that finished the job
          best_so_far = NULL;
          i = NULL; // We exit the while loop
        } else { // interval doesn't forbid all remaining values;
          // does is eliminate more values than best_so_far?
          if (((best_so_far == NULL) && bvconstant_lt(&min_save, &i->hi))
              || ((best_so_far != NULL) && bvconstant_lt(&best_so_far->hi, &i->hi))) { // i becomes best_so_far
            if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
              FILE* out = ctx_trace_out(ctx);
              fprintf(out, "becomes best_so_far\n");
            }
            if (best_so_far != NULL) bv_arith_interval_destruct(best_so_far);
            best_so_far = i;
          } else {
            if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
              FILE* out = ctx_trace_out(ctx);
              fprintf(out, "is useless\n");
            }
            bv_arith_interval_destruct(i); // i is not interesting enough
          }
          i = bv_arith_pop(&lctx); // either way, we get next element in heap
          bv_arith_ishift(ctx, i, &base, base_term);
        }
      } else { // Not in continuity of previously forbidden range
        if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
          FILE* out = ctx_trace_out(ctx);
          fprintf(out, "is in discontinuity\n");
        }
        if (best_so_far != NULL) { // We need to save best_so_far in &conflict
          bvconstant_copy(&min_save, best_so_far->hi.bitsize, best_so_far->hi.data);
          term_t previous_min_saved_term = min_saved_term;
          min_saved_term = best_so_far->hi_term;
          bv_arith_add2conflict(&lctx, previous_min_saved_term, best_so_far, conflict); // records and destructs best_so_far
          best_so_far = NULL;
        } else { // Discontinuity in intervals, shouldn't happen if in conflict
          assert(false);
        }
      }
    }

    assert(best_so_far == NULL);
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Adding to conflict longest interval\n");
    }
    bv_arith_add2conflict(&lctx, min_saved_term, longest, conflict); // hooking up the first interval pulled out (the longest), destructing it
    delete_bvconstant(&base);
    delete_bvconstant(&min_save);
  }

  // Now we empty the heap
  longest = bv_arith_pop(&lctx);
  while (longest != NULL) {
    bv_arith_interval_destruct(longest);
    longest = bv_arith_pop(&lctx);
  }

  assert(ptr_heap_is_empty(&lctx.heap));
  assert(ptr_queue_is_empty(&lctx.queue));

  delete_bvconstant(&lctx.zero);
  delete_bvconstant(&lctx.length);
  delete_ptr_heap(&lctx.heap);
  delete_ptr_queue(&lctx.queue);

  if (ctx_trace_enabled(ctx, "mcsat::bv::conflict")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Returned conflict is: ");
    for (uint32_t i = 0; i < conflict->size; i++) {
      if (i>0) fprintf(out,", ");
      term_print_to_file(out, terms, conflict->data[i]);
    }
    fprintf(out,"\n");
  }

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

  // Resetting the cache & co.
  bv_evaluator_csttrail_reset(csttrail, conflict_var);
  int_hset_reset(&exp->coeff1_cache);
  int_hset_reset(&exp->coeffm1_cache);

  // Variables that are going to be re-used for every item in the conflict core
  variable_t atom_i_var;
  term_t     atom_i_term;
  composite_term_t* atom_i_comp;
  
  // We go through the conflict core
  for (uint32_t i = 0; i < conflict_core->size; i++) {
      
    atom_i_var   = conflict_core->data[i];
    atom_i_term  = variable_db_get_term(ctx->var_db, atom_i_var);

    assert(is_pos_term(atom_i_term));

    if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "bv_arith looks whether this is in the fragment: ");
      ctx_trace_term(ctx, atom_i_term);
      fprintf(out, "with the conflict_variable being ");
      ctx_trace_term(ctx, csttrail->conflict_var_term);
    }

    switch (term_kind(terms, atom_i_term)) {
    case EQ_TERM : 
    case BV_EQ_ATOM:
    case BV_GE_ATOM: 
    case BV_SGE_ATOM: {
      atom_i_comp = composite_term_desc(terms, atom_i_term);
      assert(atom_i_comp->arity == 2);
      term_t t0 = atom_i_comp->arg[0];
      term_t t1 = atom_i_comp->arg[1];
      if (!is_pos_term(t0) || !is_pos_term(t1))
        return false;
      // OK, maybe we can treat the constraint atom_i_term. We first scan the atom (collecting free variables and co.)
      bv_evaluator_csttrail_scan(csttrail, atom_i_var);
      
      // Now that we have collected the free variables, we look into the constraint structure
      int32_t t0_good = bv_arith_coeff(exp, t0, csttrail->conflict_var_term, false);
      int32_t t1_good = bv_arith_coeff(exp, t1, csttrail->conflict_var_term, false);
      if ((t0_good == 2) || (t1_good == 2) || (t0_good * t1_good == -1)
          /* || (t0_good == -1) || ( t1_good == -1) */
          ) { // Turns out we actually can't deal with the constraint. We stop
        return false; // i+1 because exp->free_var[i] has been initialised
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
void destruct(bv_subexplainer_t* this) {
  arith_t* exp = (arith_t*) this;
  bv_evaluator_csttrail_destruct(&exp->csttrail);
  delete_int_hset(&exp->coeff1_cache);
  delete_int_hset(&exp->coeffm1_cache);
}

/** Allocate the sub-explainer and setup the methods */
bv_subexplainer_t* arith_new(plugin_context_t* ctx, watch_list_manager_t* wlm, bv_evaluator_t* eval) {

  arith_t* exp = safe_malloc(sizeof(arith_t));

  bv_subexplainer_construct(&exp->super, "mcsat::bv::explain::arith", ctx, wlm, eval);
  bv_evaluator_csttrail_construct(&exp->csttrail, ctx, wlm);
                                
  exp->super.can_explain_conflict = can_explain_conflict;
  exp->super.explain_conflict = explain_conflict;
  exp->super.destruct = destruct;

  init_int_hset(&exp->coeff1_cache, 0);
  init_int_hset(&exp->coeffm1_cache, 0);

  return (bv_subexplainer_t*) exp;
}
