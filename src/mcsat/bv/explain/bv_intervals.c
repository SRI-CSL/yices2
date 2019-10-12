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
#include "arith_intervals.h"


/**
   BV arithmetic intervals
**/

void bv_interval_delete(interval_t* i) {
  delete_bvconstant(&i->lo);
  delete_bvconstant(&i->hi);
  delete_bvconstant(&i->length);
  delete_ivector(&i->reasons);
}

void bv_interval_destruct(interval_t* i) {
  bv_interval_delete(i);
  safe_free(i);
}

void bv_interval_print(FILE* out, term_table_t* terms, interval_t* i) {
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
bool bv_interval_is_in(const bvconstant_t* a, const interval_t* i){
  return bvconst_lt_base(a, &i->hi, &i->lo);
}

// Comparing two intervals: first look at bitwidth, then lower bound, then span.
// When lower bounds are compared, an optional baseline can be provided, in data,
// which must have the same bitwidth as x and y.
bool bv_interval_cmp(void *data, void *x, void *y){
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
void bv_interval_construct(bv_subexplainer_t* exp,
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
interval_t* bv_interval_mk(bv_subexplainer_t* exp,
                                 const bvconstant_t* lo,
                                 const bvconstant_t* hi,
                                 term_t lo_term,
                                 term_t hi_term,
                                 term_t var,
                                 term_t reason) {
  plugin_context_t* ctx = exp->super.ctx;
  interval_t* result = safe_malloc(sizeof(interval_t));
  
  bv_interval_construct(exp, lo, hi, lo_term, hi_term, var, reason, result);
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Creating interval, ");
    bv_interval_print(out, ctx->terms, result);
    fprintf(out, "\n");
  }
  return result;
}

interval_t* bv_interval_full_mk(bv_subexplainer_t* exp, term_t reason, uint32_t width) {
  plugin_context_t* ctx = exp->super.ctx;
  term_manager_t* tm    = ctx->tm;
  term_t zero_term   = bv_arith_zero(tm, width);
  interval_t* result = bv_interval_mk(exp,NULL,NULL,zero_term,zero_term,NULL_TERM,reason);
  return result;
}

