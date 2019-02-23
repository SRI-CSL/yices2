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

#include "arith.h"

typedef struct arith_s {

  /** Interfact of the subexplainer */
  bv_subexplainer_t super;

} arith_t;

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


// Check if term t is a constant term of bv
// (all bv variables & foreign terms have been assigned values in the trail)

bool bv_arith_is_constant(plugin_context_t* ctx, int_hset_t* cst_terms_cache, term_t t) {

  assert(is_pos_term(t));

  // Answer right away in case already found to be constant
  if (int_hset_member(cst_terms_cache, t)) {
    /* if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) { */
    /*   FILE* out = ctx_trace_out(ctx); */
    /*   fprintf(out, "This term was already found to have a value "); */
    /*   ctx_trace_term(ctx, t); */
    /* } */
    return true;
  }

  /* if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) { */
  /*   FILE* out = ctx_trace_out(ctx); */
  /*   fprintf(out, "Looking at whether this term has a value "); */
  /*   ctx_trace_term(ctx, t); */
  /* } */

  variable_db_t* var_db = ctx->var_db; // standard abbreviations
  term_table_t* terms   = ctx->terms;
  const mcsat_trail_t* trail  = ctx->trail;

  variable_t var = variable_db_get_variable_if_exists(var_db, t); // term as a variable

  if ((var == variable_null) || !trail_has_value(trail, var)) {
  
    switch (term_kind(terms, t)) {
    case CONSTANT_TERM:
    case BV_CONSTANT:
    case BV64_CONSTANT:
      break;
    case EQ_TERM:
    case BV_EQ_ATOM:
    case BV_GE_ATOM:
    case BV_SGE_ATOM:
    case BV_ARRAY:
    case OR_TERM:
    case BV_DIV:
    case BV_REM:
    case BV_SDIV:
    case BV_SREM:
    case BV_SMOD:
    case BV_SHL:
    case BV_LSHR:
    case BV_ASHR: {
      composite_term_t* composite_desc = composite_term_desc(terms, t);
      for (uint32_t i = 0; i < composite_desc->arity; ++ i) {
        term_t t_i = composite_desc->arg[i];
        term_t t_i_pos = unsigned_term(t_i);
        if (!bv_arith_is_constant(ctx, cst_terms_cache, t_i_pos)) return false;
      }
      break;
    }
    case BIT_TERM: {
      term_t arg = bit_term_arg(terms, t);
      term_t arg_pos = unsigned_term(arg);
      if (!bv_arith_is_constant(ctx, cst_terms_cache, arg_pos)) return false;
      break;
    }
    case BV_POLY: {
      bvpoly_t* t_poly = bvpoly_term_desc(terms, t);
      for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
        if (t_poly->mono[i].var == const_idx) continue;
        if (!bv_arith_is_constant(ctx, cst_terms_cache, t_poly->mono[i].var)) return false;
      }
      break;
    }
    case BV64_POLY: {
      bvpoly64_t* t_poly = bvpoly64_term_desc(terms, t);
      for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
        if (t_poly->mono[i].var == const_idx) continue;
        if (!bv_arith_is_constant(ctx, cst_terms_cache, t_poly->mono[i].var)) return false;
      }
      break;
    }
    case POWER_PRODUCT: {
      pprod_t* t_pprod = pprod_term_desc(terms, t);
      for (uint32_t i = 0; i < t_pprod->len; ++ i) {
        if (!bv_arith_is_constant(ctx, cst_terms_cache, t_pprod->prod[i].var)) return false;
      }
      break;
    }
    default:
      return false;
    }
  }
  int_hset_add(cst_terms_cache, t);
  /* if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) { */
  /*   FILE* out = ctx_trace_out(ctx); */
  /*   fprintf(out, "It does !\n"); */
  /* } */
  return true;
}


// Local context
typedef struct {
  plugin_context_t* ctx;
  bv_evaluator_t* eval;
  term_t conflict_var;
  bvconstant_t zero; // Because we don't like recomputing this too many times
  term_t zero_term;  // Because we don't like recomputing this too many times
  ptr_heap_t heap;   // Heap of forbidden intervals, ordered by lower bounds
  int_hset_t cst_terms_cache; // terms already found to be constant
} bv_arith_ctx_t;



// checks whether term conflict_var is one of the variables of the polynomial bv expression t
bool bv_arith_has_conflict_var(bv_arith_ctx_t* lctx, term_t t) {

  plugin_context_t* ctx = lctx->ctx;
  
  /* if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) { */
  /*   FILE* out = ctx_trace_out(ctx); */
  /*   fprintf(out, "Looking at whether this term has the conflict_var "); */
  /*   ctx_trace_term(ctx, t); */
  /* } */

  if (t == lctx->conflict_var) return true;
  /* if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) { */
  /*   FILE* out = ctx_trace_out(ctx); */
  /*   fprintf(out, "Not variable itself\n"); */
  /* } */
  if (bv_arith_is_constant(lctx->ctx, &lctx->cst_terms_cache, t)) return false;
  /* if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) { */
  /*   FILE* out = ctx_trace_out(ctx); */
  /*   fprintf(out, "Not constant\n"); */
  /* } */

  switch (term_kind(ctx->terms, t)) {
  case BV_POLY: {
    bvpoly_t* t_poly = bvpoly_term_desc(ctx->terms, t);
    for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
      /* if (t_poly->mono[i].var == const_idx) continue; */
      if (t_poly->mono[i].var == lctx->conflict_var) return true;
    }
    break;
  }
  case BV64_POLY: {
    bvpoly64_t* t_poly = bvpoly64_term_desc(ctx->terms, t);
    for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
      /* if (t_poly->mono[i].var == const_idx) continue; */
      if (t_poly->mono[i].var == lctx->conflict_var) return true;
    }
    break;
  }
  default:
    assert(false);
  }
  /* if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) { */
  /*   FILE* out = ctx_trace_out(ctx); */
  /*   fprintf(out, "This term does not have the conflict_var "); */
  /*   ctx_trace_term(ctx, t); */
  /* } */
  return false;
}

// Type for bvconstant intervals.
// Upper bound is always *excluded* from interval.
// Invariant: (lo < hi) should always hold, except if hi = 0, which means hi = 2^n.
// We DO NOT construct empty intervals, we return null for them.

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



// interval construction:
// lo is always in [0 ; 2^n-1], and may or may not be excluded
// hi is in [1 ; 2^n-1] union {0}, with 0 meaning 0 is hi is included, and 0 meaning 2^n is hi is excluded
// => an interval where hi = 0 is excluded is always non-empty, except if lo = 2^n-1 and it is excluded.

bvconst_interval_t* bv_arith_interval_construct(plugin_context_t* ctx,
                                                const bvconstant_t* lo,
                                                bool lo_incl,
                                                const bvconstant_t* hi,
                                                bool hi_incl,
                                                term_t lo_term,
                                                term_t hi_term,
                                                term_t reason) {

  term_manager_t* tm   = &ctx->var_db->tm;
  assert(bvconstant_is_normalized(lo));
  assert(bvconstant_is_normalized(hi));
  
  // Quick detection of cases where the interval will be empty (so we return null)
  // Otherwise we malloc the interval and if we later realise it is empty we free it.
  if (lo_incl && hi_incl && bvconstant_lt(hi,lo)) return NULL;
  //When hi is excluded, hi=0 means hi=2^n, and threfore the interval cannot be empty
  if (lo_incl && !hi_incl && !bvconstant_is_zero(hi) && bvconstant_le(hi,lo)) return NULL;
  if (!lo_incl && hi_incl && bvconstant_le(hi,lo)) return NULL; //This forgets the case when lo+1=2^n, treated "the slow way"
  // if !lo_incl && !hi_incl, we cannot escape a +1 or -1 computation:
  // so we treat the case "the slow way": we'll malloc and then free if the interval is empty.  

  bvconst_interval_t* result = safe_malloc(sizeof(bvconst_interval_t));
  init_bvconstant(&result->lo);
  init_bvconstant(&result->hi);
  result->lo_term = lo_term;
  result->hi_term = hi_term;
  result->reason = reason;

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Creating interval from lo = ");
    bvconst_print(out, lo->data, lo->bitsize);
    fprintf(out, " %s, hi = ",lo_incl?"incl":"excl");
    bvconst_print(out, hi->data, hi->bitsize);
    fprintf(out, " %s, lo_term = ",hi_incl?"incl":"excl");
    term_print_to_file(out, ctx->terms, lo_term);
    fprintf(out, ", hi_term = ");
    term_print_to_file(out, ctx->terms, hi_term);
    fprintf(out, "\n");
  }
  
  bvconstant_copy(&result->lo, lo->bitsize, lo->data);
  if (!lo_incl) {
    bvconstant_add_one(&result->lo);
    bvconstant_normalize(&result->lo);
    if (bvconstant_is_zero(&result->lo)) { // lo+1=2^n, interval is empty
      bv_arith_interval_destruct(result);
      return NULL;
    }
    result->lo_term = bv_arith_add_one_term(tm, lo_term);
  }
  
  bvconstant_copy(&result->hi, hi->bitsize, hi->data);
  if (hi_incl) {
    bvconstant_add_one(&result->hi);
    bvconstant_normalize(&result->hi);
    result->hi_term = bv_arith_add_one_term(tm, hi_term);
  }

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "bv_arith creates provisional interval ");
    bv_arith_interval_print(out, ctx->terms, result);
    fprintf(out, "\n");
  }

  if (!bvconstant_is_zero(&result->hi)
      && bvconstant_le(&result->hi,&result->lo)) { // interval is empty
    bv_arith_interval_destruct(result);
    return NULL;
  }

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "bv_arith creates interval ");
    bv_arith_interval_print(out, ctx->terms, result);
    fprintf(out, "\n");
  }

  return result;
}


// Treat a constraint of the form lhs <= rhs (is_neq == false) of lhs != rhs (is_neq == true)

void bv_arith_unit_constraint(bv_arith_ctx_t* lctx, term_t lhs, term_t rhs, bool is_neq) {
  // Standard abbreviations
  plugin_context_t* ctx = lctx->ctx;
  term_manager_t* tm    = &lctx->ctx->var_db->tm;

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "\nTreating unit_constraint (lhs %s rhs) where lhs is ", is_neq?"!=":"<=");
    term_print_to_file(out, ctx->terms, lhs);
    fprintf(out, " and rhs is ");
    term_print_to_file(out, ctx->terms, rhs);
    fprintf(out, "\n");
  }

  // Check if conflict variable is a variable of the left polynomial / right polynomial
  bool left_has  = bv_arith_has_conflict_var(lctx, lhs);
  bool right_has = bv_arith_has_conflict_var(lctx, rhs);

  // Setting c1 and c2 to be 2 terms representing the left polynomial and the right polynomial,
  // from which the confict variable (if present) was removed
  term_t c1 = (left_has) ? bv_arith_sub_terms(tm, lhs, lctx->conflict_var) : lhs;
  term_t c2 = (right_has) ? bv_arith_sub_terms(tm, rhs, lctx->conflict_var) : rhs;

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "We have c1: ");
    term_print_to_file(out, ctx->terms, c1);
    fprintf(out, " and c2: ");
    ctx_trace_term(ctx, c2);
  }

  // Evaluating the polynomials c1 and c2 whose variables should all have values on the trail  
  bvconstant_t cc1, cc2;
  uint32_t eval_level = 0; // What is this level ?!? Let's say it's 0 :-)
  bv_evaluator_run_term(lctx->eval, c1, &cc1, &eval_level);
  eval_level = 0;
  bv_evaluator_run_term(lctx->eval, c2, &cc2, &eval_level);
  bvconstant_is_normalized(&cc1);
  bvconstant_is_normalized(&cc2);

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "as well as cc1: ");
    bvconst_print(out, cc1.data, cc1.bitsize);
    fprintf(out, " and cc2: ");
    bvconst_print(out, cc2.data, cc2.bitsize);
    fprintf(out, "\n");
  }

  // Now we go through Table 1 of SMT 2016 paper
  // We are going to create one or two intervals of forbidden values, using these intermediate bv_constants
  bvconst_interval_t* i;
  term_t lo_term, hi_term, reason;
  bvconstant_t lo, hi;
  init_bvconstant(&lo);
  init_bvconstant(&hi);

  if (is_neq) { // case of inequality (lhs != rhs)
    if ((right_has && left_has) || ((!right_has) && (!left_has))) { // x appears on both sides or on neither sides
      if (bvconstant_eq(&cc1,&cc2)) { // If c1 == c2, we forbid everything, otherwise we forbid nothing
        reason = mk_bveq(tm, c1, c2);
        i = bv_arith_interval_construct(ctx, &lctx->zero, true, &lctx->zero, false, lctx->zero_term, lctx->zero_term, reason);
        ptr_heap_add(&lctx->heap, i);
      }
    }
    if (right_has && !left_has) { // case (c1 != c2 + x), forbidden interval is [ c1-c2 ; c1-c2 ]
      bvconstant_copy(&lo, cc1.bitsize, cc1.data);
      bvconstant_sub(&lo, &cc2);
      bvconstant_normalize(&lo);
      lo_term = bv_arith_sub_terms(tm,c1,c2);
      i = bv_arith_interval_construct(ctx, &lo, true, &lo, true, lo_term, lo_term, NULL_TERM);
      ptr_heap_add(&lctx->heap, i);
    }
    if (left_has && !right_has) { // case of inequality (c1 + x != c2): forbidden interval is [ c2-c1 ; c2-c1 ]
      bvconstant_copy(&lo, cc2.bitsize, cc2.data);
      bvconstant_sub(&lo, &cc1);
      bvconstant_normalize(&lo);
      lo_term = bv_arith_sub_terms(tm,c2,c1);
      i = bv_arith_interval_construct(ctx, &lo, true, &lo, true, lo_term, lo_term, NULL_TERM);
      ptr_heap_add(&lctx->heap, i);
    }
  }
  
  else { // case of less than (lhs <= rhs)
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
      
        if (bvconstant_lt(&cc1,&cc2)) { // If c1 < c2, we forbid [ -c2 ; -c1 [
          reason = mk_bvlt(tm, c1, c2);
          i = bv_arith_interval_construct(ctx, &lo, true, &hi, false, lo_term, hi_term, reason);
          if (i != NULL) ptr_heap_add(&lctx->heap, i);
        }
        else {
          if (bvconstant_lt(&cc2,&cc1)) { // If c2 < c1, we forbid [ 0 ; -c1 [, then [ -c2 ; 2^n [
            reason = mk_bvlt(tm, c2, c1);
            i = bv_arith_interval_construct(ctx, &lctx->zero, true, &hi, false, lctx->zero_term, hi_term, reason);
            if (i != NULL) ptr_heap_add(&lctx->heap, i);
            i = bv_arith_interval_construct(ctx, &lo, true, &lctx->zero, false, lo_term, lctx->zero_term, reason);
            if (i != NULL) ptr_heap_add(&lctx->heap, i);
          }
        }
      } else { // No conflict variable on the left, then hi is (c1 - c2)
        bvconstant_copy(&hi, cc1.bitsize, cc1.data);
        bvconstant_sub(&hi, &cc2);
        bvconstant_normalize(&hi);
        hi_term = bv_arith_sub_terms(tm,c1,c2);

        if (bvconstant_le(&cc1,&cc2)) { // If c1 <= c2, we forbid [ -c2 ; c1 - c2 [
          reason = mk_bvle(tm, c1, c2);
          i = bv_arith_interval_construct(ctx, &lo, true, &hi, false, lo_term, hi_term, reason);
          if (i != NULL) ptr_heap_add(&lctx->heap, i);
        }
        else { // else we must have c2 < c1, and we forbid both [ 0 ; c1 - c2 [ and [ -c2 ; 2^n [
          reason = mk_bvlt(tm, c2, c1);
          i = bv_arith_interval_construct(ctx, &lctx->zero, true, &hi, false, lctx->zero_term, hi_term, reason);
          if (i != NULL) ptr_heap_add(&lctx->heap, i);
          i = bv_arith_interval_construct(ctx, &lo, true, &lctx->zero, false, lo_term, lctx->zero_term, reason);
          if (i != NULL) ptr_heap_add(&lctx->heap, i);
        }
      }
    } else {
      if (left_has) { // lo = c2 - c1, and hi = -c1
        bvconstant_copy(&lo, cc2.bitsize, cc2.data);
        bvconstant_sub(&lo, &cc1);
        bvconstant_normalize(&lo);
        lo_term = bv_arith_sub_terms(tm,c2,c1);

        bvconstant_copy(&hi, cc1.bitsize, cc1.data);
        bvconstant_negate(&hi);
        bvconstant_normalize(&hi);
        hi_term = bv_arith_negate_terms(tm,c1);

        if (bvconstant_le(&cc1,&cc2)) { // If c1 <= c2, we forbid ] c2 - c1 ; -c1 [
          reason = mk_bvle(tm, c1, c2);
          i = bv_arith_interval_construct(ctx, &lo, false, &hi, false, lo_term, hi_term, reason);
          if (i != NULL) ptr_heap_add(&lctx->heap, i);
        }
        else { // else we must have c2 < c1, and we forbid both [ 0 ; -c1 [ and ] c2 - c1 ; 2^n [
          reason = mk_bvlt(tm, c2, c1);
          i = bv_arith_interval_construct(ctx, &lctx->zero, true, &hi, false, lctx->zero_term, hi_term, reason);
          if (i != NULL) ptr_heap_add(&lctx->heap, i);
          i = bv_arith_interval_construct(ctx, &lo, false, &lctx->zero, false, lo_term, lctx->zero_term, reason);
          if (i != NULL) ptr_heap_add(&lctx->heap, i);
        }
      } else { // x appears on neither sides
        if (bvconstant_lt(&cc2,&cc1)) { // If c2 < c1, we forbid everything, otherwise we forbid nothing
          reason = mk_bvlt(tm, c2, c1);
          i = bv_arith_interval_construct(ctx, &lctx->zero, true, &lctx->zero, false, lctx->zero_term, lctx->zero_term, reason);
          ptr_heap_add(&lctx->heap, i);
        }
      }
    }
  }
    
  delete_bvconstant(&cc1);
  delete_bvconstant(&cc2);    
  delete_bvconstant(&lo);
  delete_bvconstant(&hi);    
}

// Adds interval to conflict, and destructs it
void bv_arith_add2conflict(plugin_context_t* ctx, term_t min_saved_term, bvconst_interval_t* i, ivector_t* conflict) {
  term_manager_t* tm = &ctx->var_db->tm;

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Adding to conflict interval ");
    bv_arith_interval_print(out, ctx->terms, i);
    fprintf(out, "\n");
  }

  if (!bvterm_is_zero(tm->terms, i->lo_term)) {
    term_t continuity_reason = mk_bvle(tm, i->lo_term, min_saved_term);
    ivector_push(conflict, continuity_reason);
  }
  if (i->reason !=  NULL_TERM) ivector_push(conflict, i->reason);
  bv_arith_interval_destruct(i);
}


static
void explain_conflict(bv_subexplainer_t* this, const ivector_t* conflict_core, variable_t conflict_var, ivector_t* conflict) {

  plugin_context_t* ctx = this->ctx;
  bv_evaluator_t* eval = this->eval;
  
  bv_evaluator_clear_cache(eval);

  // Standard abbreviations
  term_table_t* terms  = ctx->terms;
  const mcsat_trail_t* trail = ctx->trail;
  term_manager_t* tm = &ctx->var_db->tm;

  bv_arith_ctx_t lctx;
  lctx.ctx  = ctx;
  lctx.eval = eval;
  lctx.conflict_var = variable_db_get_term(ctx->var_db, conflict_var);
  init_ptr_heap(&lctx.heap, 0, &cmp);
  init_bvconstant(&lctx.zero);
  bvconstant_set_all_zero(&lctx.zero, term_bitsize(terms, lctx.conflict_var));
  lctx.zero_term = mk_bv_constant(tm, &lctx.zero);
  init_int_hset(&lctx.cst_terms_cache, 0);
  
  // Variables that are going to be re-used for every item in the conflict core
  variable_t atom_i_var;
  bool       atom_i_value;
  term_t     atom_i_term;
  term_kind_t atom_i_kind;

  // We go through the conflict core
  
  for (uint32_t i = 0; i < conflict_core->size; i++) {
    
    atom_i_var   = conflict_core->data[i];
    atom_i_value = trail_get_boolean_value(trail, atom_i_var);
    atom_i_term  = variable_db_get_term(ctx->var_db, atom_i_var);

    assert(is_pos_term(atom_i_term));

    if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "\nbv_arith treats core constraint (%s): ",atom_i_value?"T":"F");
      ctx_trace_term(ctx, atom_i_term);
    }

    // The output conflict always contains the conflict core:
    ivector_push(conflict, atom_i_value?atom_i_term:opposite_term(atom_i_term));

    composite_term_t* atom_i_comp = composite_term_desc(terms, atom_i_term);
    assert(atom_i_comp->arity == 2);
    term_t t0 = atom_i_comp->arg[0];
    term_t t1 = atom_i_comp->arg[1];
    assert(is_pos_term(t0));
    assert(is_pos_term(t1));

    atom_i_kind  = term_kind(terms, atom_i_term);

    switch (atom_i_kind) {
    case BV_GE_ATOM: {  
      if (atom_i_value) { // Constraint is (t0 >=u t1) -> True (with atom_i_term = (t0 >=u t1))
        bv_arith_unit_constraint(&lctx, t1, t0, false);
      }
      else { // Constraint is (t0 >=u t1) -> False (with atom_i_term = (t0 >=u t1)),
        // which is equivalent to the 2 constraints (t1 >=u t0+1) AND (t0+1 != 0)
        term_t t0_plus1 = bv_arith_add_one_term(tm, t0);
        bv_arith_unit_constraint(&lctx, t0_plus1, t1, false);
        bv_arith_unit_constraint(&lctx, t0_plus1, lctx.zero_term, true);
      }
      break;
    }
    case BV_SGE_ATOM: {  // (t0 >=s t1) is equivalent to (t0+2^{w-1} >=u t1+2^{w-1}) // TODO: check this
      term_t t0prime = bv_arith_add_half(tm, t0);
      term_t t1prime = bv_arith_add_half(tm, t1);
      if (atom_i_value) { // Constraint is (t0' >=u t1') -> True
        bv_arith_unit_constraint(&lctx, t1prime, t0prime, false);
      }
      else { // Constraint is (t0' >=u t1') -> False,
        // which is equivalent to the 2 constraints (t1' >=u t0'+1) AND (t0'+1 != 0)
        term_t t0prime_plus1 = bv_arith_add_one_term(tm, t0prime);
        bv_arith_unit_constraint(&lctx, t0prime_plus1, t1prime, false);
        bv_arith_unit_constraint(&lctx, t0prime_plus1, lctx.zero_term, true);
      }
      break;
    }
    case EQ_TERM :     
    case BV_EQ_ATOM: { // equality
      if (atom_i_value) {
        // Constraint is (t0 == t1) -> True (with atom_i_term = (t0 == t1)),
        // Turn into 2 constraints (t0 >=u t1) AND (t1 >=u t0)
        bv_arith_unit_constraint(&lctx, t0, t1, false);
        bv_arith_unit_constraint(&lctx, t1, t0, false);
      }
      else {
        // Constraint is (t0 == t1) -> False (with atom_i_term = (t0 == t1)),
        bv_arith_unit_constraint(&lctx, t0, t1, true);
      }
      break;
    }
    default:
      assert(false);
    }
  }

  // The elements saved in &conflict so far force the first feasible value for conflict_var to be at least min_saved
  bvconstant_t min_save;
  init_bvconstant(&min_save);
  bvconstant_copy(&min_save, lctx.zero.bitsize, lctx.zero.data);
  term_t min_saved_term = lctx.zero_term; // The term behind this lower bound of feasible values

  // The best interval found so far in the heap, but not yet saved in &conflict,
  // that can be used to forbid the greatest number of bv values beyond min_saved
  bvconst_interval_t* best_so_far = NULL;
  // tmp name for the next element popped from the heap
  bvconst_interval_t* i = ptr_heap_get_min(&lctx.heap);

  // Now we treat the heap
  while (i != NULL) {
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "bv_arith pops from the stack ");
      bv_arith_interval_print(out, terms, i);
      fprintf(out, "\n");
    }
    if (bvconstant_le(&i->lo, &min_save)) { // In continuity of previously forbidden range
      if (bvconstant_is_zero(&i->hi)) { // Yeah! interval forbids all remaining values
        if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
          FILE* out = ctx_trace_out(ctx);
          fprintf(out, "finished the job\n");
        }
        if (best_so_far != NULL) bv_arith_interval_destruct(best_so_far);
        best_so_far = i;
        // Now we empty the heap
        i = ptr_heap_get_min(&lctx.heap);
        while (i != NULL) {
          bv_arith_interval_destruct(i);
          i = ptr_heap_get_min(&lctx.heap);
        }
      } else { // interval doesn't forbid all remaining values;
        // does is eliminate more values than best_so_far?
        if (((best_so_far == NULL) && bvconstant_lt(&min_save, &i->hi))
            || bvconstant_lt(&best_so_far->hi, &i->hi)) { // i becomes best_so_far
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
        i = ptr_heap_get_min(&lctx.heap); // either way, we get next element in heap
      }
    } else { // Not in continuity of previously forbidden range
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "is in discontinuity\n");
      }
      if (best_so_far != NULL) { // We need to save best_so_far in &conflict
        bvconstant_copy(&min_save, best_so_far->hi.bitsize, best_so_far->hi.data);
        min_saved_term = best_so_far->hi_term;
        bv_arith_add2conflict(ctx, min_saved_term, best_so_far, conflict);
        best_so_far = NULL;
      } else { // Discontinuity in intervals, shouldn't happen if in conflict
        assert(false);
      }
    }
  }

  assert(best_so_far != NULL);
  if (!bvterm_is_zero(terms, best_so_far->hi_term)) {
    term_t continuity_reason = mk_bveq(tm, best_so_far->hi_term, lctx.zero_term);
    ivector_push(conflict, continuity_reason);
  }
  bv_arith_add2conflict(ctx, min_saved_term, best_so_far, conflict);
  
  assert(ptr_heap_is_empty(&lctx.heap));

  delete_bvconstant(&min_save);

  delete_bvconstant(&lctx.zero);
  delete_ptr_heap(&lctx.heap);
  delete_int_hset(&lctx.cst_terms_cache);

  bv_evaluator_clear_cache(eval);

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




// checks whether term t is a good inequality side for fragment
bool bv_arith_is_good_side(plugin_context_t* ctx, int_hset_t* cst_terms_cache, term_t t, term_t conflict_var) {

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "bv_arith looks whether this is a good side ");
    ctx_trace_term(ctx, t);
  }

  if (t == conflict_var) return true;
  if (bv_arith_is_constant(ctx, cst_terms_cache, t)) return true;

  switch (term_kind(ctx->terms, t)) {
  case BV_POLY: {
    bvpoly_t* t_poly = bvpoly_term_desc(ctx->terms, t);
    bool conflict_var_seen = false;
    for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
      if (t_poly->mono[i].var == const_idx) continue;
      if (t_poly->mono[i].var == conflict_var) {
        if (conflict_var_seen) return false; // in theory, the conflict variable shouldn't be seen twice, but...
        if (!bvconst_is_one(t_poly->mono[i].coeff, t_poly->width)) {
          return false;
        }
        conflict_var_seen = true;
      } else {
        if (!bv_arith_is_constant(ctx, cst_terms_cache, t_poly->mono[i].var)) {
          return false;
        }
      }
    }
    return true;
  }
  case BV64_POLY: {
    bvpoly64_t* t_poly = bvpoly64_term_desc(ctx->terms, t);
    bool conflict_var_seen = false;
    for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
      if (t_poly->mono[i].var == const_idx) continue;
      if (t_poly->mono[i].var == conflict_var) {
        if (conflict_var_seen) return false; // in theory, the conflict variable shouldn't be seen twice, but...
        if (t_poly->mono[i].coeff != 1) {
          return false;
        }
        conflict_var_seen = true;
      } else {
        if (!bv_arith_is_constant(ctx, cst_terms_cache, t_poly->mono[i].var)) {
          return false;
        }
      }
    }
    return true;
  }
  default:
    return false;
  }
}


static
bool can_explain_conflict(bv_subexplainer_t* this, const ivector_t* conflict_core, variable_t conflict_var) {

  plugin_context_t* ctx = this->ctx;
  
  // Standard abbreviations
  term_table_t* terms  = ctx->terms;
  term_t conflict_var_term = variable_db_get_term(ctx->var_db, conflict_var);
  
  // Variables that are going to be re-used for every item in the conflict core
  variable_t atom_i_var;
  term_t     atom_i_term;
  term_kind_t atom_i_kind;
  composite_term_t* atom_i_comp;
  
  int_hset_t cst_terms_cache;
  init_int_hset(&cst_terms_cache, 0);

  // We go through the conflict core
  
  for (uint32_t i = 0; i < conflict_core->size; i++) {
    
    atom_i_var   = conflict_core->data[i];
    atom_i_term  = variable_db_get_term(ctx->var_db, atom_i_var);

    assert(is_pos_term(atom_i_term));

    if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "bv_arith looks whether this is in the fragment: ");
      ctx_trace_term(ctx, atom_i_term);
    }

    atom_i_kind  = term_kind(terms, atom_i_term);

    switch (atom_i_kind) {
    case EQ_TERM : 
    case BV_EQ_ATOM:
    case BV_GE_ATOM: 
    case BV_SGE_ATOM:
      break;
    default: {
      delete_int_hset(&cst_terms_cache);
      return false;
    }
    }

    // Now we are sure it is EQ_TERM, BV_EQ_ATOM, BV_SGE_ATOM, or BV_GE_ATOM
    atom_i_comp = composite_term_desc(terms, atom_i_term);
    assert(atom_i_comp->arity == 2);
    term_t t0 = atom_i_comp->arg[0];
    term_t t1 = atom_i_comp->arg[1];
    assert(is_pos_term(t0));
    assert(is_pos_term(t1));

    bool is_in_fragment = true;
    
    switch (atom_i_kind) {
    case EQ_TERM :
    case BV_EQ_ATOM:
    case BV_SGE_ATOM: // This line assumes that a <=s b iff (a + 2^{w-1}) <=u (b + 2^{w-1}). Check whether this is true.
    case BV_GE_ATOM: { // Both sides must be good
      is_in_fragment = is_in_fragment
        && bv_arith_is_good_side(ctx, &cst_terms_cache, t0, conflict_var_term)
        && bv_arith_is_good_side(ctx, &cst_terms_cache, t1, conflict_var_term);
      break;
    }
    /* case BV_SGE_ATOM: { // One side must be the conflict variable, the other side must be constant */
    /*   is_in_fragment = */
    /*     ((t0 == conflict_var_term) && bv_arith_is_constant(ctx, &cst_terms_cache, t1)) */
    /*     || ((t1 == conflict_var_term) && bv_arith_is_constant(ctx, &cst_terms_cache, t0)); */
    /*   break; */
    /* } */
    default: { // We can't be in any other case because of the first switch
      assert(false);
    }
    }

    if (!is_in_fragment) { // If we are not in the fragment we stop
      delete_int_hset(&cst_terms_cache);
      return false;
    }
  }

  delete_int_hset(&cst_terms_cache);
  return true;

}

/** Allocate the sub-explainer and setup the methods */
bv_subexplainer_t* arith_new(plugin_context_t* ctx, watch_list_manager_t* wlm, bv_evaluator_t* eval) {

  arith_t* exp = safe_malloc(sizeof(arith_t));

  bv_subexplainer_construct(&exp->super, "mcsat::bv::explain::eq_ext_con", ctx, wlm, eval);

  exp->super.can_explain_conflict = can_explain_conflict;
  exp->super.explain_conflict = explain_conflict;

  return (bv_subexplainer_t*) exp;
}
