/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include "mcsat/tracing.h"
#include "mcsat/value.h"
#include "terms/bvarith_buffer_terms.h"
#include "terms/term_manager.h"
#include "terms/term_utils.h"
#include "utils/ptr_heap.h"

#include "bv_evaluator.h"
#include "bv_arith.h"

// Adding 2 bv terms

term_t bv_arith_add_terms(term_manager_t* tm, term_t a, term_t b) {
  term_table_t* terms = tm->terms;
  bvarith_buffer_t *buffer = term_manager_get_bvarith_buffer(tm);
  bvarith_buffer_set_term(buffer, terms, a);
  // bvarith_buffer_normalize(buffer); // should not be needed
  bvarith_buffer_add_term(buffer, terms, b);
  return mk_bvarith_term(tm, buffer);
}

// Subtracting 2 bv terms

term_t bv_arith_sub_terms(term_manager_t* tm, term_t a, term_t b) {
  term_table_t* terms = tm->terms;
  bvarith_buffer_t *buffer = term_manager_get_bvarith_buffer(tm);
  bvarith_buffer_set_term(buffer, terms, a);
  // bvarith_buffer_normalize(buffer); // should not be needed
  bvarith_buffer_sub_term(buffer, terms, b);
  return mk_bvarith_term(tm, buffer);
}

// Negating a bv term

term_t bv_arith_negate_terms(term_manager_t* tm, term_t t) {
  term_table_t* terms = tm->terms;
  bvarith_buffer_t *buffer = term_manager_get_bvarith_buffer(tm);
  bvarith_buffer_set_term(buffer, terms, t);
  // bvarith_buffer_normalize(buffer); // should not be needed
  bvarith_buffer_negate(buffer);
  return mk_bvarith_term(tm, buffer);
}

// Adding +1 to a bv term

term_t bv_arith_add_one_term(term_manager_t* tm, term_t t) {
  term_table_t* terms  = tm->terms;
  bvarith_buffer_t *buffer = term_manager_get_bvarith_buffer(tm);
  bvarith_buffer_set_term(buffer, terms, t);
  bvarith_buffer_add_pp(buffer, empty_pp);
  return mk_bvarith_term(tm, buffer);
}


// checks whether term conflict_var is one of the variables of the polynomial bv expression t
bool bv_arith_has_conflict_var(plugin_context_t* ctx, term_t t, term_t conflict_var) {

  if (t == conflict_var) return true;

  switch (term_kind(ctx->terms, t)) {
  case BV_POLY: {
    bvpoly_t* t_poly = bvpoly_term_desc(ctx->terms, t);
    for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
      if (t_poly->mono[i].var == conflict_var) return true;
    }
    return false;
  }
  default:
    assert(false);
  }
}

// Local context
typedef struct {
  plugin_context_t* ctx;
  bv_evaluator_t* eval;
  term_t conflict_var;
  bvconstant_t zero; // Because we don't like recomputing this too many times
  term_t zero_term;  // Because we don't like recomputing this too many times
  ptr_heap_t heap;   // Heap of forbidden intervals, ordered by lower bounds
} local_ctx_t;

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

// interval construction:
// lo is always in [0 ; 2^n-1], and may or may not be excluded
// hi is in [1 ; 2^n-1] union {0}, with 0 meaning 0 is hi is included, and 0 meaning 2^n is hi is excluded
// => an interval where hi = 0 is excluded is always non-empty, except if lo = 2^n-1 and it is excluded.

bvconst_interval_t* bv_arith_interval_construct(term_manager_t* tm,
                                                const bvconstant_t* lo,
                                                bool lo_incl,
                                                const bvconstant_t* hi,
                                                bool hi_incl,
                                                term_t lo_term,
                                                term_t hi_term,
                                                term_t reason) {

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
  
  bvconstant_copy(&result->lo, lo->bitsize, lo->data);
  if (!lo_incl) {
    bvconstant_add_one(&result->lo);
    if (bvconstant_is_zero(&result->lo)) { // lo+1=2^n, interval is empty
      bv_arith_interval_destruct(result);
      return NULL;
    }
    result->lo_term = bv_arith_add_one_term(tm, lo_term);
  }
  
  bvconstant_copy(&result->hi, hi->bitsize, hi->data);
  if (hi_incl) {
    bvconstant_add_one(&result->lo);
    result->hi_term = bv_arith_add_one_term(tm, hi_term);
  }
  
  if (!bvconstant_is_zero(hi) && bvconstant_le(hi,lo)) { // interval is empty
    bv_arith_interval_destruct(result);
    return NULL;
  }

  return result;
}





// Treat a constraint of the form lhs <= rhs

void bv_arith_le(local_ctx_t* lctx, term_t lhs, term_t rhs) {
  // Standard abbreviations
  term_manager_t* tm   = &lctx->ctx->var_db->tm;

  // Check if conflict variable is a variable of the left polynomial / right polynomial
  bool left_has  = bv_arith_has_conflict_var(lctx->ctx, lhs, lctx->conflict_var);
  bool right_has = bv_arith_has_conflict_var(lctx->ctx, rhs, lctx->conflict_var);

  // Setting c1 and c2 to be 2 terms representing the left polynomial and the right polynomial,
  // from which the confict variable (if present) was removed
  term_t c1 = (left_has) ? bv_arith_sub_terms(tm, lhs, lctx->conflict_var) : lhs;
  term_t c2 = (right_has) ? bv_arith_sub_terms(tm, rhs, lctx->conflict_var) : rhs;

  // Evaluating the polynomials c1 and c2 whose variables should all have values on the trail  
  uint32_t eval_level = 0; // What is this level ?!? Let's say it's 0 :-)
  const mcsat_value_t* c1_v = bv_evaluator_evaluate_term(lctx->eval, c1, &eval_level);
  eval_level = 0;
  const mcsat_value_t* c2_v = bv_evaluator_evaluate_term(lctx->eval, c2, &eval_level);

  assert(c1_v->type == VALUE_BV);
  assert(c2_v->type == VALUE_BV);
  bvconstant_t cc1 = c1_v->bv_value;
  bvconstant_t cc2 = c2_v->bv_value;

  // Now we go through Table 1 of SMT 2016 paper
  // We are going to create one or two intervals of forbidden values, using these intermediate bv_constants
  bvconst_interval_t* i;
  term_t lo_term, hi_term, reason;
  bvconstant_t lo, hi;
  init_bvconstant(&lo);
  init_bvconstant(&hi);
  
  if (right_has) { // lo is going to be -c2
    bvconstant_copy(&lo, cc2.bitsize, cc2.data);
    bvconstant_negate(&lo);
    lo_term = bv_arith_negate_terms(tm,c2);
    
    if (left_has) { // then hi is -c1
      bvconstant_copy(&hi, cc1.bitsize, cc1.data);
      bvconstant_negate(&hi);
      hi_term = bv_arith_negate_terms(tm,c1);
      
      if (bvconstant_lt(&cc1,&cc2)) { // If c1 < c2, we forbid [ -c2 ; -c1 [
        reason = mk_bvlt(tm, c1, c2);
        i = bv_arith_interval_construct(tm, &lo, true, &hi, false, lo_term, hi_term, reason);
        if (i != NULL) ptr_heap_add(&lctx->heap, i);
      }
      else {
        if (bvconstant_lt(&cc2,&cc1)) { // If c2 < c1, we forbid [ 0 ; -c1 [, then [ -c2 ; 2^n [
          reason = mk_bvlt(tm, c2, c1);
          i = bv_arith_interval_construct(tm, &lctx->zero, true, &hi, false, lctx->zero_term, hi_term, reason);
          if (i != NULL) ptr_heap_add(&lctx->heap, i);
          i = bv_arith_interval_construct(tm, &lo, true, &lctx->zero, false, lo_term, lctx->zero_term, reason);
          if (i != NULL) ptr_heap_add(&lctx->heap, i);
        }
      }
    } else { // No conflict variable on the left, then hi is (c1 - c2)
      bvconstant_copy(&hi, cc1.bitsize, cc1.data);
      bvconstant_sub(&hi, &cc2);
      hi_term = bv_arith_sub_terms(tm,c1,c2);

      if (bvconstant_le(&cc1,&cc2)) { // If c1 <= c2, we forbid [ -c2 ; c1 - c2 [
        reason = mk_bvle(tm, c1, c2);
        i = bv_arith_interval_construct(tm, &lo, true, &hi, false, lo_term, hi_term, reason);
        if (i != NULL) ptr_heap_add(&lctx->heap, i);
      }
      else { // else we must have c2 < c1, and we forbid both [ 0 ; c1 - c2 [ and [ -c2 ; 2^n [
        reason = mk_bvlt(tm, c2, c1);
        i = bv_arith_interval_construct(tm, &lctx->zero, true, &hi, false, lctx->zero_term, hi_term, reason);
        if (i != NULL) ptr_heap_add(&lctx->heap, i);
        i = bv_arith_interval_construct(tm, &lo, true, &lctx->zero, false, lo_term, lctx->zero_term, reason);
        if (i != NULL) ptr_heap_add(&lctx->heap, i);
      }
    }
  } else {
    assert(left_has); // otherwise !left_has && !right_has - conflict variable appears on neither side - not sure that could happen
    // lo = c2 - c1, and hi = -c1
    bvconstant_copy(&lo, cc2.bitsize, cc2.data);
    bvconstant_sub(&lo, &cc1);
    lo_term = bv_arith_sub_terms(tm,c2,c1);
    bvconstant_copy(&hi, cc1.bitsize, cc1.data);
    bvconstant_negate(&hi);
    hi_term = bv_arith_negate_terms(tm,c1);

    if (bvconstant_le(&cc1,&cc2)) { // If c1 <= c2, we forbid ] c2 - c1 ; -c1 [
      reason = mk_bvle(tm, c1, c2);
      i = bv_arith_interval_construct(tm, &lo, false, &hi, false, lo_term, hi_term, reason);
      if (i != NULL) ptr_heap_add(&lctx->heap, i);
    }
    else { // else we must have c2 < c1, and we forbid both [ 0 ; c1 [ and [ c2 - c1 ; 2^n [
      reason = mk_bvlt(tm, c2, c1);
      i = bv_arith_interval_construct(tm, &lctx->zero, true, &hi, false, lctx->zero_term, hi_term, reason);
      if (i != NULL) ptr_heap_add(&lctx->heap, i);
      i = bv_arith_interval_construct(tm, &lo, true, &lctx->zero, false, lo_term, lctx->zero_term, reason);
      if (i != NULL) ptr_heap_add(&lctx->heap, i);
    }
  }
    
  delete_bvconstant(&lo);
  delete_bvconstant(&hi);    
}

// Adds interval to conflict, and destructs it
void bv_arith_add2conflict(term_manager_t* tm, term_t min_saved_term, bvconst_interval_t* i, ivector_t* conflict) {
  if (!bvterm_is_zero(tm->terms, i->lo_term)) {
    term_t continuity_reason = mk_bvle(tm, i->lo_term, min_saved_term);
    ivector_push(conflict, continuity_reason);
  }
  ivector_push(conflict, i->reason);
  bv_arith_interval_destruct(i);
}


void bv_arith_get_conflict(plugin_context_t* ctx, bv_evaluator_t* eval, const ivector_t* conflict_core, term_t conflict_var, ivector_t* conflict) {
  // Standard abbreviations
  term_table_t* terms  = ctx->terms;
  const mcsat_trail_t* trail = ctx->trail;
  term_manager_t* tm = &ctx->var_db->tm;
  
  local_ctx_t lctx;
  lctx.ctx  = ctx;
  lctx.eval = eval;
  lctx.conflict_var = conflict_var;
  init_ptr_heap(&lctx.heap, 0, &cmp);
  init_bvconstant(&lctx.zero);
  bvconstant_set_all_zero(&lctx.zero, term_bitsize(terms, conflict_var));
  lctx.zero_term = mk_bv_constant(tm, &lctx.zero);
  
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
      fprintf(out, "bv_arith treats core constraint ");
      ctx_trace_term(ctx, atom_i_term);
    }

    // The output conflict always contains the conflict core:
    ivector_push(conflict, atom_i_value?atom_i_term:opposite_term(atom_i_term));
    
    atom_i_kind  = term_kind(terms, atom_i_term);

    switch (atom_i_kind) {
    case BV_GE_ATOM: {  // Constraint is (t0 >= t1) -> True (with atom_i_term = (t0 >= t1)),
      composite_term_t* atom_i_comp = bvge_atom_desc(terms, atom_i_term);
      assert(atom_i_comp->arity == 2);
      term_t t0 = atom_i_comp->arg[0];
      term_t t1 = atom_i_comp->arg[1];
      assert(is_pos_term(t0));
      assert(is_pos_term(t1));
      if (atom_i_value) {
        bv_arith_le(&lctx, t1, t0);
      }
      else {
        // Constraint is (t0 >= t1) -> False (with atom_i_term = (t0 >= t1)),
        // It looks like we need to convert into 2 constraints (t1 >= t0+1) AND (t0+1 >= 1)
        // Create the term t0+1 using this?:
        // bvarith_buffer_add_term(bvarith_buffer_t *b, term_table_t *table, term_t t);
        assert(false);
      }
      break;
    }
    case EQ_TERM :     
    case BV_EQ_ATOM: { // equality
      composite_term_t* atom_i_comp = (atom_i_kind == EQ_TERM)?eq_term_desc(terms, atom_i_term): bveq_atom_desc(terms, atom_i_term);
      assert(atom_i_comp->arity == 2);
      term_t t0 = atom_i_comp->arg[0];
      term_t t1 = atom_i_comp->arg[1];
      assert(is_pos_term(t0));
      assert(is_pos_term(t1));
      if (atom_i_value) {
        // Constraint is (t0 == t1) -> True (with atom_i_term = (t0 == t1)),
        // Turn into 2 constraints (t0 >= t1) AND (t1 >= t0)
        // Careful there: one of the two may not be "in the core". Not problematic ?
        bv_arith_le(&lctx, t0, t1);
        bv_arith_le(&lctx, t1, t0);
      }
      else {
        // Constraint is (t0 == t1) -> False (with atom_i_term = (t0 == t1)),
        // The 2 constraints (t0 >= t1) -> False , (t1 >= t0) -> False are in a DISJUNCTION
        // Think about what to do then (check LRA or NRA plugins)
        assert(false);
      }
      break;
    }
    default:
      assert(false);
    }
  }

  // The elements saved in &conflict so far force the first feasible value for conflict_var to be at least min_saved
  const bvconstant_t* min_saved = &lctx.zero;
  term_t min_saved_term = lctx.zero_term; // The term behind this lower bound of feasible values

  // The best interval found so far in the heap, but not yet saved in &conflict,
  // that can be used to forbid the greatest number of bv values beyond min_saved
  bvconst_interval_t* best_so_far = NULL;
  // tmp name for the next element popped from the heap
  bvconst_interval_t* i = ptr_heap_get_min(&lctx.heap);

  // Now we treat the heap
  while (i != NULL) {
    if (bvconstant_le(&i->lo,min_saved)) { // In continuity of previously forbidden range
      if (bvconstant_is_zero(&i->hi)) { // Yeah! interval forbids all remaining values
        best_so_far = i;
        // Now we empty the heap
        i = ptr_heap_get_min(&lctx.heap);
        while (i != NULL) {
          bv_arith_interval_destruct(i);
          i = ptr_heap_get_min(&lctx.heap);
        }
      } else { // interval doesn't forbid all remaining values;
        // does is eliminate more values than best_so_far?
        if (((best_so_far == NULL) && bvconstant_lt(min_saved, &i->hi))
            || bvconstant_lt(&best_so_far->hi, &i->hi)) { // i becomes best_so_far
          if (best_so_far != NULL) bv_arith_interval_destruct(best_so_far);
          best_so_far = i;
        } else bv_arith_interval_destruct(i); // i is not interesting enough
        i = ptr_heap_get_min(&lctx.heap); // either way, we get next element in heap
      }
    } else { // Not in continuity of previously forbidden range
      if (best_so_far != NULL) { // We need to save best_so_far in &conflict
        bv_arith_add2conflict(tm, min_saved_term, best_so_far, conflict);
        min_saved      = &best_so_far->hi;
        min_saved_term = best_so_far->hi_term;
      } else { // Discontinuity in intervals, shouldn't happen if in conflict
        i = NULL;
        assert(false);
      }
    }
  }

  if (best_so_far != NULL)
    bv_arith_add2conflict(tm, min_saved_term, best_so_far, conflict);

  assert(ptr_heap_is_empty(&lctx.heap));

  delete_bvconstant(&lctx.zero);
  delete_ptr_heap(&lctx.heap);
}


