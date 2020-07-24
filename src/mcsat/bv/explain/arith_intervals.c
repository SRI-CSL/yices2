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
#include "mcsat/value.h"
#include "terms/bv_constants.h"
#include "terms/term_manager.h"

#include "mcsat/bv/bv_utils.h"
#include "arith_utils.h"
#include "arith_intervals.h"


/**
   BV arithmetic intervals
**/

void interval_delete(interval_t* i) {
  delete_bvconstant(&i->lo);
  delete_bvconstant(&i->hi);
  delete_bvconstant(&i->length);
  delete_ivector(&i->reasons);
}

void interval_destruct(interval_t* i) {
  interval_delete(i);
  safe_free(i);
}

void interval_print(FILE* out, term_table_t* terms, interval_t* i) {
  if (i == NULL) {
    fprintf(out, "EMPTY");
    return;
  }
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

bool bvconst_lt_base(const bvconstant_t* a, const bvconstant_t* b, const bvconstant_t* baseline){
  return !bvconst_le_base(b, a, baseline);
}

// Determines if interval i contains value a. Happens if (a - i->lo) < (i->hi - i->lo)
bool interval_is_in(const bvconstant_t* a, const interval_t* i){
  return bvconst_lt_base(a, &i->hi, &i->lo);
}

// Construct an atom that says "t \in interval"
term_t interval_is_in_term(arith_norm_t* norm, term_t t, const interval_t* i){
  plugin_context_t* ctx = norm->csttrail.ctx;
  term_manager_t* tm    = ctx->tm;
  term_t t0 = arith_sub(tm, t, i->lo_term);
  term_t t1 = arith_sub(tm, i->hi_term, i->lo_term);
  term_t result = arith_lt_norm(norm, t0, t1);
  return result;
}

// Comparing two intervals: first look at bitwidth, then lower bound, then span.
// When lower bounds are compared, an optional baseline can be provided, in data,
// which must have the same bitwidth as x and y.
bool interval_cmp(void *data, void *x, void *y){
  bvconstant_t* baseline = (bvconstant_t*) data;
  interval_t* i1 = (interval_t*) x;
  interval_t* i2 = (interval_t*) y;
  if (x == NULL) return false; // NULL is not smaller than anyone (strict order)
  if (y == NULL) return true;  // NULL is strictly bigger than anyone but NULL
  if (interval_get_bitwidth(i1) == interval_get_bitwidth(i2)) {
    if (bvconstant_eq(&i1->lo,&i2->lo))
      return bvconst_lt_base(&i2->hi,&i1->hi,&i1->lo);
    return (baseline==NULL) ?
      bvconstant_lt(&i1->lo,&i2->lo) :
      bvconst_lt_base(&i1->lo,&i2->lo,baseline) ;
  }
  return (interval_get_bitwidth(i2) < interval_get_bitwidth(i1));
}


static
void construct(bv_subexplainer_t* exp,
               const bvconstant_t* lo,
               const bvconstant_t* hi,
               term_t lo_term,
               term_t hi_term,
               interval_t* output) {

  output->lo_term = lo_term;
  output->hi_term = hi_term;

  uint32_t ignore_this_int = 0;
  const bvconstant_t* tmp;
  bv_evaluator_t* eval = exp->eval;
  
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

}

// inhabits output
void interval_construct(bv_subexplainer_t* exp,
                        const bvconstant_t* lo,
                        const bvconstant_t* hi,
                        term_t lo_term,
                        term_t hi_term,
                        term_t var,
                        term_t reason,
                        interval_t* output) {  
  assert(lo_term != NULL_TERM);
  assert(hi_term != NULL_TERM);
  init_bvconstant(&output->lo);
  init_bvconstant(&output->hi);
  init_bvconstant(&output->length);
  init_ivector(&output->reasons,0);
  output->var     = var;
  output->reason  = reason;
  construct(exp,lo,hi,lo_term,hi_term,output);
}

// Adds a newly constructed interval into the heap
interval_t* interval_mk(bv_subexplainer_t* exp,
                        const bvconstant_t* lo,
                        const bvconstant_t* hi,
                        term_t lo_term,
                        term_t hi_term,
                        term_t var,
                        term_t reason) {
  plugin_context_t* ctx = exp->ctx;
  interval_t* result = safe_malloc(sizeof(interval_t));
  
  interval_construct(exp, lo, hi, lo_term, hi_term, var, reason, result);
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Creating interval, ");
    interval_print(out, ctx->terms, result);
    fprintf(out, "\n");
  }
  return result;
}

interval_t* interval_full_mk(bv_subexplainer_t* exp, term_t reason, uint32_t width) {
  plugin_context_t* ctx = exp->ctx;
  term_manager_t* tm    = ctx->tm;
  term_t zero_term   = arith_zero(tm, width);
  interval_t* result = interval_mk(exp,NULL,NULL,zero_term,zero_term,NULL_TERM,reason);
  return result;
}

// If interval is an interval for var, then it becomes an interval for var - u
void interval_subtract(bv_subexplainer_t* exp, term_t u, interval_t* interval) {
  plugin_context_t* ctx = exp->ctx;
  term_manager_t* tm    = ctx->tm;
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Interval subtract ");
    interval_print(out, tm->terms, interval);
    fprintf(out, "\n");
  }

  if (interval != NULL) {
    if (!interval_is_full(interval)) {
      term_t lo_term = arith_sub(tm, interval->lo_term, u);
      term_t hi_term = arith_sub(tm, interval->hi_term, u);
      construct(exp, NULL, NULL, lo_term, hi_term, interval);
    }
    interval->var = NULL_TERM;
  }

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Interval subtract produces ");
    interval_print(out, tm->terms, interval);
    fprintf(out, "\n");
  }

}

// If interval is an interval for var, then it becomes an interval for - var
void interval_negate(bv_subexplainer_t* exp, interval_t* interval) {
  plugin_context_t* ctx = exp->ctx;
  term_manager_t* tm    = ctx->tm;
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Interval negate ");
    interval_print(out, tm->terms, interval);
    fprintf(out, "\n");
  }
  if (interval != NULL) {
    if (!interval_is_full(interval)) {
      term_t lo_term = arith_add_one(tm, arith_negate(tm, interval->hi_term));
      term_t hi_term = arith_add_one(tm, arith_negate(tm, interval->lo_term));
      construct(exp, NULL, NULL, lo_term, hi_term, interval);
    }
    interval->var = NULL_TERM;
  }
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Interval negate produces ");
    interval_print(out, tm->terms, interval);
    fprintf(out, "\n");
  }
}

// If interval is an interval for var,
// then it becomes an interval for concat(var,u) for any u extending the low bits of var
// w is the length of u. Function doesn't check the var,
// and sets it back to NULL_TERM if interval is modified.
void interval_downextend(bv_subexplainer_t* exp, uint32_t w, interval_t* interval) {
  plugin_context_t* ctx = exp->ctx;
  term_manager_t* tm    = ctx->tm;
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Down-extend ");
    interval_print(out, tm->terms, interval);
    fprintf(out, "\n");
  }
  if (0 < w && interval != NULL) {
    uint32_t n     = term_bitsize(tm->terms, interval->lo_term);
    term_t lo_term = arith_downextension(tm, interval->lo_term, false_term, n + w);
    term_t hi_term = arith_downextension(tm, interval->hi_term, false_term, n + w);
    construct(exp, NULL, NULL, lo_term, hi_term, interval);
    interval->var = NULL_TERM;
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Down-extend produces ");
      interval_print(out, tm->terms, interval);
      fprintf(out, "\n");
    }
  } else{
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Down-extend has no effect\n");
    }
  }
}

// If interval is a full interval,
// transforms it into a full interval on w bit domain and outputs true
// otherise doesn't touch interval and outputs false
static
bool full2full(bv_subexplainer_t* exp, uint32_t w, interval_t* interval) {
  plugin_context_t* ctx = exp->ctx;
  term_manager_t* tm    = ctx->tm;

  if (interval != NULL
      && interval_is_full(interval)) { // Interval on smaller bitwidth is full or empty
    term_t zero_term = arith_zero(tm, w);
    construct(exp, NULL, NULL, zero_term, zero_term, interval);
    return true;
  } else
    return false;

}

// If interval is an interval for 0...0var, then it becomes an interval for var
// (of length w). Interval can become empty, in which case function outputs true
// (otherwise outputs false). Function doesn't check the var,
// and sets it back to NULL_TERM if interval is modified.
bool interval_uptrim(bv_subexplainer_t* exp, arith_norm_t* norm, uint32_t w, interval_t* interval) {
  plugin_context_t* ctx = exp->ctx;
  term_manager_t* tm    = ctx->tm;

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Up-trimming ");
    interval_print(out, tm->terms, interval);
    fprintf(out, "\n");
  }

  if (interval == NULL){
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Up-trimming has no effect\n");
    }
    return true;
  }

  uint32_t n = term_bitsize(tm->terms, interval->lo_term);
  assert(w <= n);
  if (w < n) {

    if (full2full(exp, w, interval))
      return false; // interval was full, remains full on w-bit domain

    bvconstant_t aux; // auxiliary bv_constant on n bits, used in 2 ways
    init_bvconstant(&aux);
    bvconstant_set_all_zero(&aux, n);
    // aux is used in two ways. First, to check whether 0...0.0...0 is in interval
    bool zero_in = interval_is_in(&aux, interval);
    // then, as 0...01.0...0, i.e. the number of values of width w (expressed on n bits)
    bvconst_set_bit(aux.data, w); 
    bvconstant_normalize(&aux);
    term_t aux_term = mk_bv_constant(tm, &aux);
    term_t t0 = interval->lo_term;
    term_t t1 = interval->hi_term;

    term_t lo_term, lo_reason;
    if (bvconstant_lt(&interval->lo,&aux)) {
      lo_term   = term_extract(tm, t0, 0, w);
      lo_reason = arith_lt_norm(norm, t0, aux_term);
    } else {
      lo_term   = arith_zero(tm, w);
      lo_reason = arith_le_norm(norm, aux_term, t0);
    }
    if (arith_is_no_triv(lo_reason)) {
      ivector_push(&interval->reasons, lo_reason);
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "  adding lo_reason ");
        ctx_trace_term(ctx, lo_reason);
      }
    }

    term_t hi_term, hi_reason;
    if (bvconstant_lt(&interval->hi,&aux)) {
      hi_term   = term_extract(tm, t1, 0, w);
      hi_reason = arith_lt_norm(norm, t1, aux_term);
    } else {
      hi_term   = arith_zero(tm, w);
      hi_reason = arith_le_norm(norm, aux_term, t1);
    }
    if (arith_is_no_triv(hi_reason)) {
      ivector_push(&interval->reasons, hi_reason);
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "  adding hi_reason ");
        ctx_trace_term(ctx, hi_reason);
      }
    }

    delete_bvconstant(&aux);
    construct(exp, NULL, NULL, lo_term, hi_term, interval);

    if (full2full(exp, w, interval)) { // Interval on smaller bitwidth is full or empty
      if (!zero_in) {
        if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
          FILE* out = ctx_trace_out(ctx);
          fprintf(out, "Up-trimming produces EMPTY\n");
        }
        return true; // In that case the interval becomes empty
      }
      interval->reason = arith_lt_norm(norm,
                                       arith_negate(tm, t0),
                                       arith_sub(tm, t1, t0));
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "Adding reason4full ");
        ctx_trace_term(ctx, interval->reason);
      }
    }
    interval->var = NULL_TERM;
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Up-trimming produces ");
      interval_print(out, tm->terms, interval);
      fprintf(out, "\n");
    }
  } else {
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Up-trimming has no effect\n");
    }
  }

  return false;
}

// If interval is an interval for var0...0 (w is the number of extra zeros),
// then it becomes an interval for var
// (it doesn't check the var, and sets it back to NULL_TERM)
bool interval_downtrim(bv_subexplainer_t* exp, arith_norm_t* norm, uint32_t w, interval_t* interval) {
  plugin_context_t* ctx = exp->ctx;
  term_manager_t* tm    = ctx->tm;

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Down-trimming ");
    interval_print(out, tm->terms, interval);
    fprintf(out, "\n");
  }

  if (interval == NULL) {
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Down-trimming has no effect\n");
    }
    return true;
  }

  uint32_t n = term_bitsize(tm->terms, interval->lo_term);

  assert(w < n);
  if (0 < w && interval != NULL) {

    if (full2full(exp, n-w, interval))
      return false; // interval was full, remains full on (n-w)-bit domain

    // auxiliary bv_constant 0...0.1...1,
    // i.e. the number of values of width w minus 1 (expressed on n bits)
    bvconstant_t aux;
    init_bvconstant(&aux);
    bvconstant_set_all_zero(&aux, n);
    bvconst_set_bit(aux.data, w);
    bvconstant_sub_one(&aux);
    bvconstant_normalize(&aux);
    bool is_small = bvconstant_lt(&interval->length,&aux);

    term_t t0 = interval->lo_term;
    term_t t1 = interval->hi_term;
    term_t lo_term = term_extract(tm, t0, w, n); // higher bits extract of lower bound
    term_t hi_term = term_extract(tm, t1, w, n); // higher bits extract of higher bound
    bvconstant_t lo_light; // The w light bits of interval->lo, in the model
    bvconstant_t hi_light; // The w light bits of interval->hi, in the model
    init_bvconstant(&lo_light);
    init_bvconstant(&hi_light);
    bvconstant_extract(&lo_light,interval->lo.data, 0, w);
    bvconstant_extract(&hi_light,interval->hi.data, 0, w);
    bvconstant_normalize(&lo_light);
    bvconstant_normalize(&hi_light);

    term_t zero_w = arith_zero(tm, w);
    
    term_t lo_reason;
    if (bvconstant_is_zero(&lo_light)) {
      lo_reason = arith_eq_norm(norm, zero_w, term_extract(tm, t0, 0, w));
    } else {
      lo_term   = arith_add_one(tm, lo_term);
      lo_reason = arith_lt_norm(norm, zero_w, term_extract(tm, t0, 0, w));
    }
    if (arith_is_no_triv(lo_reason)) {
      ivector_push(&interval->reasons, lo_reason);
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "  adding lo_reason ");
        ctx_trace_term(ctx, lo_reason);
      }
    }

    term_t hi_reason;
    if (bvconstant_is_zero(&hi_light)) {
      hi_reason = arith_eq_norm(norm, zero_w, term_extract(tm, t1, 0, w));
    } else {
      hi_term   = arith_add_one(tm, hi_term);
      hi_reason = arith_lt_norm(norm, zero_w, term_extract(tm, t1, 0, w));
    }
    if (arith_is_no_triv(hi_reason)) {
      ivector_push(&interval->reasons, hi_reason);
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "  adding hi_reason ");
        ctx_trace_term(ctx, hi_reason);
      }
    }

    assert(!interval_is_full(interval));
    delete_bvconstant(&lo_light);
    delete_bvconstant(&hi_light);
    delete_bvconstant(&aux);
    term_t hi_trim0 = arith_downextension(tm, hi_term, false_term, n);
    term_t reason4full = interval_is_in_term(norm, hi_trim0, interval);
    // Now we modify the interval  
    construct(exp, NULL, NULL, lo_term, hi_term, interval);

    if (interval_is_full(interval)) { // Interval on smaller bitwidth is full or empty
      if (is_small) {// It has, in fact, reduced to the empty interval
        if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
          FILE* out = ctx_trace_out(ctx);
          fprintf(out, "Down-trimming has no effect\n");
        }
        return true;
      }
      assert(interval->reason == NULL_TERM);
      full2full(exp, n-w, interval);
      interval->reason = reason4full;
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "Adding reason4full ");
        ctx_trace_term(ctx, interval->reason);
      }
    }
    interval->var = NULL_TERM;
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Down-trimming produces ");
      interval_print(out, tm->terms, interval);
      fprintf(out, "\n");
    }
  } else {
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Down-trimming has no effect\n");
    }
  }
  return false;
}

