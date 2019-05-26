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

typedef struct arith_s {

  /** Interfact of the subexplainer */
  bv_subexplainer_t super;

  bv_csttrail_t csttrail; // Where we keep some cached values
  int_hmap_t coeff1_cache; // Cache of terms whose coeff for conflict_var is 1
  int_hmap_t coeffm1_cache; // Cache of terms whose coeff for conflict_var is -1

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


/**
   Extracting bits and coefficients from terms.
**/

// If term t is a lower bit extract, returns the base.
// If it is another bv_array, returns NULL_TERM.
// Otherwise returns t.
term_t lower_bit_extract_base(arith_t* exp, term_t t, uint32_t w){

  plugin_context_t* ctx = exp->super.ctx;
  term_table_t* terms   = ctx->terms;

  if (term_kind(terms, t) == BV_ARRAY) {
    // Concatenated boolean terms
    // t HAS to be a lower bit extract of some term "base" mentioning y (*)
    composite_term_t* concat_desc = bvarray_term_desc(terms, t);
    term_t base = NULL_TERM;
    
    for (uint32_t i = 0; i < w; i++) {
      term_t t_i = concat_desc->arg[i]; // The Boolean term that constitutes that bit
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "bit %d is ",i);
        ctx_trace_term(ctx, t_i);
      }
      if (term_kind(terms, t_i) != BIT_TERM) { // Would falsify (*)
        return NULL_TERM;
      }
      if (base == NULL_TERM) { // Initialising base
        base = bit_term_arg(terms, t_i);
      }
      select_term_t* desc   = bit_term_desc(terms, t_i);
      uint32_t selected_bit = desc->idx; // Get bit that is selected in it
      if ((base != bit_term_arg(terms, t_i)) // Would falsify (*)
          || (selected_bit != i)) {          // Would falsify (*)
        return NULL_TERM;
      }
    }
    return base;
  }

  return t;
}

// Lower bits extraction: extracting the w lowest bits of t
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
  if (t == conflict_var || bv_evaluator_is_evaluable(&exp->csttrail, t, &ignore_this_bool)) {
    if (w < original_bitsize) {
      return term_extract(tm, t, 0, w);
    } else {
      return t;
    }
  }
  
  switch (term_kind(terms, t)) {
  case BV_ARRAY: { // Concatenated boolean terms
    // To be in the fragment, t HAS to be a lower bit extract of some term "base" mentioning y (*)
    term_t base = lower_bit_extract_base(exp, t, w);
    if (base == NULL_TERM) { // Not a good term
      return NULL_TERM;
    }
    return extract(exp, base, w); // Extracting from the base
  }
  case BV_POLY: {
    // t is a bv-poly expression.
    // We use the fact that lower bits extraction distributes over arithmetic operations
    bvpoly_t* t_poly = bvpoly_term_desc(ctx->terms, t);
    if (w<65) {
      // If we extract fewer than 65 bits, we use uint64_t coefficients for the bv_poly to produce
      // we construct that bv_poly from a bvarith64_buffer_t called result:
      bvarith64_buffer_t* result = term_manager_get_bvarith64_buffer(tm);
      bvarith64_buffer_prepare(result, w); // Setting the desired width
      // Now going into each monomial
      for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
        uint64_t coeff = // projecting the monomial coefficient onto w bits
          (original_bitsize < 33) ? // requires an annoying case analysis, for some reason
          ( (uint64_t) bvconst_get32(t_poly->mono[i].coeff)) :
          bvconst_get64(t_poly->mono[i].coeff) ;
        if (t_poly->mono[i].var == const_idx) {
          bvarith64_buffer_add_const(result, coeff); // constant coefficient gets aded to the result bv_poly
        } else {
          term_t recurs = extract(exp, t_poly->mono[i].var, w); // recursively project the monomial variable onto w bits
          if (recurs == NULL_TERM) return NULL_TERM; // If it fails we fail
          bvarith64_buffer_add_const_times_term(result, terms, coeff, recurs); // Otherwise we add the w-bit monomial to the bv_poly
        }
      }
      return mk_bvarith64_term(tm, result); // We turn the bv_poly into an actual term, and return it
    } else {
      // If we extract more than 64 bits, we use regular coefficients for the bv_poly to produce
      // we construct that bv_poly from a bvarith_buffer_t called result:
      bvarith_buffer_t* result = term_manager_get_bvarith_buffer(tm);
      bvarith_buffer_prepare(result, w); // Setting the desired width
      bvconstant_t coeff; // temp variable for the next loop
      init_bvconstant(&coeff);
      for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
        bvconstant_extract(&coeff, t_poly->mono[i].coeff, 0, w); // projecting the monomial coefficient onto w bits
        if (t_poly->mono[i].var == const_idx) {
          bvarith_buffer_add_const(result, coeff.data);// constant coefficient gets aded to the result bv_poly
        } else {
          term_t recurs = extract(exp, t_poly->mono[i].var, w);// recursively project the monomial variable onto w bits
          if (recurs == NULL_TERM) return NULL_TERM;// If it fails we fail
          bvarith_buffer_add_const_times_term(result, terms, coeff.data, recurs); // Otherwise we add the w-bit monomial to the bv_poly
        }
      }
      delete_bvconstant(&coeff); //cleaning up
      return mk_bvarith_term(tm, result); // We turn the bv_poly into an actual term, and return it
    }
  }
  case BV64_POLY: { // Same game, but now t is a bv64_poly, so w <= 64 and we also construct a bv64_poly
    bvpoly64_t* t_poly         = bvpoly64_term_desc(ctx->terms, t);
    bvarith64_buffer_t* result = term_manager_get_bvarith64_buffer(tm);
    bvarith64_buffer_prepare(result, w);
    for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
      if (t_poly->mono[i].var == const_idx) {
        bvarith64_buffer_add_const(result, t_poly->mono[i].coeff);
      } else {
        term_t recurs = extract(exp, t_poly->mono[i].var, w);
        if (recurs == NULL_TERM) return NULL_TERM;
        bvarith64_buffer_add_const_times_term(result, terms, t_poly->mono[i].coeff, recurs);
      }
    }
    return mk_bvarith64_term(tm, result);
  }
  default: 
    return NULL_TERM;
  }

}


// Function returns coefficient of conflict_variable in u (-1, 0, or 1)
// It uses cached values, and caches new values.
// if u is not a good term for the fragment:
// if !assume_fragment, function will return 2,
// if assume_fragment, function has unspecified behaviour (but runs faster)

int32_t bv_arith_coeff(arith_t* exp, term_t u, bool assume_fragment) {

  plugin_context_t* ctx = exp->super.ctx;
  term_t conflict_var = exp->csttrail.conflict_var_term;
  term_table_t* terms   = ctx->terms;

  uint32_t w = term_bitsize(terms, u);
  term_t t   = extract(exp, u, w);

  if (t == NULL_TERM) return 2;
  
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "extracting coefficient of conflict variable in ");
    ctx_trace_term(ctx, t);
    fprintf(out, "obtained by normalisation of ");
    ctx_trace_term(ctx, u);
  }

  // Looking at whether the value is cached
  if (int_hmap_find(&exp->coeff1_cache,t) != NULL) return 1;
  if (lower_bit_extract_base(exp,t,w) == conflict_var) {
    int_hmap_add(&exp->coeff1_cache, t, t);
    return 1;
  }
  if (int_hmap_find(&exp->coeffm1_cache,t) != NULL) return -1;
  bool ignore_this_bool;
  if (bv_evaluator_is_evaluable(&exp->csttrail, t, &ignore_this_bool)) return 0;

  int32_t result = 0;

  switch (term_kind(ctx->terms, t)) {
  case BV_POLY: {
    bvpoly_t* t_poly = bvpoly_term_desc(ctx->terms, t);
    for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
      if (t_poly->mono[i].var == const_idx) continue;
      term_t base = lower_bit_extract_base(exp, t_poly->mono[i].var,w);
      if (base == conflict_var){ // Monomial variable is a lower bit extract of the conflict var
        assert (result == 0); // in theory, the conflict variable shouldn't be seen twice
        if (bvconst_is_one(t_poly->mono[i].coeff, t_poly->width)) result = 1;
        else {
          if (bvconst_is_minus_one(t_poly->mono[i].coeff, t_poly->bitsize)) result = -1;
          else return 2;
        };
        if (assume_fragment) break; // If in fragment, need not look at other monomials
      } else { // The monomial variable is not a lower bit extract of the conflict var
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
      term_t base = lower_bit_extract_base(exp, t_poly->mono[i].var,w);
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "base is ");
        ctx_trace_term(ctx, base);
      }
      if (base == conflict_var) { // Monomial variable is a lower bit extract of the conflict var
        assert (result == 0); // in theory, the conflict variable shouldn't be seen twice
        if (t_poly->mono[i].coeff == 1) result = 1;
        else {
          if (bvconst64_is_minus_one(t_poly->mono[i].coeff,term_bitsize(ctx->terms,t))) result = -1;
          else return 2;
        }
        if (assume_fragment) break; // If in fragment, need not look at other monomials
      } else { // The monomial variable is not a lower bit extract of the conflict var
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
  int_hmap_add((result == 1)? (&exp->coeff1_cache):(&exp->coeffm1_cache), t, t);
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
  term_t reason;
} interval_t;

static
uint32_t get_bitwidth(interval_t* i){
  return i->lo.bitsize;
}

static
bool is_full(interval_t* i){
  return bvconstant_eq(&i->lo,&i->hi);
}

void bv_arith_interval_destruct(interval_t* i) {
  delete_bvconstant(&i->lo);
  delete_bvconstant(&i->hi);
  delete_bvconstant(&i->length);
  safe_free(i);
}

void bv_arith_interval_print(FILE* out, term_table_t* terms, interval_t* i) {
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
  if (y == NULL) return true;  // NULL is bigger than anyone
  if (x == NULL) return false; // NULL is not smaller than anyone different from NULL
  if (get_bitwidth(i1) == get_bitwidth(i2)) {
    if (bvconstant_eq(&i1->lo,&i2->lo))
      return bvconst_le_base(&i1->hi,&i2->hi,&i1->lo);
    return (baseline==NULL) ?
      bvconstant_le(&i1->lo,&i2->lo) :
      bvconst_le_base(&i1->lo,&i2->lo,baseline) ;
  }
  return (get_bitwidth(i2) < get_bitwidth(i1));
}

bool cmp(void *x, void *y){
  return cmp_base(NULL,x,y);
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
  interval_t* longest; // Longest interval the heap has ever seen
  bvconstant_t length; // Its length
  ptr_queue_t queue; // Where we may store intervals popped from the heap
} bv_arith_ctx_t;

// inhabits output
static
void interval_construct(bv_arith_ctx_t* lctx,
                        const bvconstant_t* lo,
                        const bvconstant_t* hi,
                        term_t lo_term,
                        term_t hi_term,
                        term_t reason,
                        interval_t* output) {

  plugin_context_t* ctx = lctx->exp->super.ctx;
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Constructing interval from lo = ");
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

  init_bvconstant(&output->lo);
  init_bvconstant(&output->hi);
  init_bvconstant(&output->length);
  output->lo_term = lo_term;
  output->hi_term = hi_term;
  output->reason  = reason;

  bvconstant_copy(&output->lo, lo->bitsize, lo->data);
  bvconstant_copy(&output->hi, hi->bitsize, hi->data);
  bvconstant_copy(&output->length, hi->bitsize, hi->data);
  bvconstant_sub(&output->length, lo);
  bvconstant_normalize(&output->length);
  bvconstant_sub_one(&output->length);
  bvconstant_normalize(&output->length);
  
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "bv_arith creates interval ");
    bv_arith_interval_print(out, ctx->terms, output);
    fprintf(out, "\n");
  }
}

// Adds a newly constructed interval into the heap
interval_t* bv_arith_interval_push(bv_arith_ctx_t* lctx,
                                   const bvconstant_t* lo,
                                   const bvconstant_t* hi,
                                   term_t lo_term,
                                   term_t hi_term,
                                   term_t reason) {
  plugin_context_t* ctx = lctx->exp->super.ctx;
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Creating interval, ");
  }

  interval_t* result = safe_malloc(sizeof(interval_t));
  interval_construct(lctx, lo, hi, lo_term, hi_term, reason, result);
  // Adding the interval to the heap  
  ptr_heap_add(&lctx->heap, (void *) result);
  // If the length of the interval is longer than the previous longest, we update the latter
  if (bvconstant_lt(&lctx->length, &result->length)){
    lctx->longest = result;
    bvconstant_copy(&lctx->length, result->length.bitsize, result->length.data);
  }
  return result;
}

static inline
interval_t* bv_arith_full_interval_push(bv_arith_ctx_t* lctx, term_t reason, uint32_t width) {
  plugin_context_t* ctx = lctx->exp->super.ctx;
  term_manager_t* tm    = ctx->tm;
  bvconstant_t zero;
  init_bvconstant(&zero);
  bvconstant_extract(&zero,lctx->zero.data,0,width);
  term_t zero_term = term_extract(tm, lctx->zero_term, 0, width);
  interval_t* result = bv_arith_interval_push(lctx,&zero,&zero,zero_term,zero_term,reason);
  delete_bvconstant(&zero);
  return result;
}


/**
   Explanation mechanism. First for 1 constraint. Then for the whole conflict
**/

// Analyses one side of an atom, assumed to be in the fragment.
// t is the side, coeff is the coeff of the conflict var, cc is a non-initialised bv_constant
// returns the "rest of the term" (monomial of the conflict var is removed), and places the result of its evaluation in cc
term_t bv_arith_init_side(bv_arith_ctx_t* lctx, term_t t, int32_t coeff, bvconstant_t* cc) {

  // Standard abbreviations
  term_t conflict_var   = lctx->exp->csttrail.conflict_var_term;
  plugin_context_t* ctx = lctx->exp->super.ctx;
  term_manager_t* tm    = ctx->tm;
  uint32_t w            = term_bitsize(tm->terms, t);

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Initialising constraint_side ");
    term_print_to_file(out, ctx->terms, t);
    fprintf(out, "\n");
  }

  term_t result = // The term without the unevaluable monomial
    (coeff > 0) ?
    bv_arith_sub_terms(tm, t, term_extract(tm, conflict_var, 0, w)) :
    ((coeff < 0) ?
     bv_arith_add_terms(tm, t, term_extract(tm, conflict_var, 0, w)) : t);

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
interval_t* bv_arith_unit_le(bv_arith_ctx_t* lctx, term_t lhs_raw, term_t rhs_raw, bool b) {
  // Standard abbreviations
  plugin_context_t* ctx = lctx->exp->super.ctx;
  term_manager_t* tm    = ctx->tm;
  term_table_t* terms   = ctx->terms;
  uint32_t w = term_bitsize(terms, lhs_raw);
  assert(w == term_bitsize(terms, rhs_raw));
  interval_t* result;
  
  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "\nTreating unit_constraint (lhs <= rhs) where lhs is ");
    term_print_to_file(out, ctx->terms, lhs_raw);
    fprintf(out, " and rhs is ");
    term_print_to_file(out, ctx->terms, rhs_raw);
    fprintf(out, "\n");
  }

  term_t lhs = extract(lctx->exp, lhs_raw, term_bitsize(terms, lhs_raw));
  term_t rhs = extract(lctx->exp, rhs_raw, term_bitsize(terms, rhs_raw));
  
  int32_t left_coeff  = bv_arith_coeff(lctx->exp, lhs, true);
  int32_t right_coeff = bv_arith_coeff(lctx->exp, rhs, true);
    
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
        result = bv_arith_interval_push(lctx, &lo, &hi, lo_term, hi_term, NULL_TERM);
      if (!b) {
        if (!bvconstant_eq(&lo,&hi))
          result = bv_arith_interval_push(lctx, &hi, &lo, hi_term, lo_term, NULL_TERM);
        else {
          term_t reason = bv_arith_eq(tm, lo_term, hi_term);
          result = bv_arith_full_interval_push(lctx, reason, w);
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
          result = bv_arith_interval_push(lctx, &hi, &lo, hi_term, lo_term, NULL_TERM);
        else {
          term_t reason = bv_arith_eq(tm, lo_term, hi_term);
          result = bv_arith_full_interval_push(lctx, reason, w);
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
        result = bv_arith_interval_push(lctx, &lo, &hi, lo_term, hi_term, NULL_TERM);
      if (!b) {
        if (!bvconstant_eq(&lo,&hi))
          result = bv_arith_interval_push(lctx, &hi, &lo, hi_term, lo_term, NULL_TERM);
        else {
          term_t reason = bv_arith_eq(tm, lo_term, hi_term);
          result = bv_arith_full_interval_push(lctx, reason, w);
        }
      }
    } else { // x appears on neither sides
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "Case <=: !has_right, !has_left");
      }
      if (b && bvconstant_lt(&cc2,&cc1)) { // If c2 < c1, we forbid everything, otherwise we forbid nothing
        term_t reason = bv_arith_lt(tm, c2, c1);
        result = bv_arith_full_interval_push(lctx, reason, w);
      }
      if (!b && !bvconstant_lt(&cc2,&cc1)) { // If c2 < c1, we forbid everything, otherwise we forbid nothing
        term_t reason = not_term(tm->terms,bv_arith_lt(tm, c2, c1));
        result = bv_arith_full_interval_push(lctx, reason, w);
      }
    }
  }
  
  delete_bvconstant(&cc1);
  delete_bvconstant(&cc2);    
  delete_bvconstant(&lo);
  delete_bvconstant(&hi);

  return result;
}


// Shift interval down by base (leaves terms untouched)
void bv_arith_ishift(plugin_context_t* ctx,
                     interval_t* i,
                     bvconstant_t* base) {
  bvconstant_sub(&i->lo, base);
  bvconstant_normalize(&i->lo);
  bvconstant_sub(&i->hi, base);
  bvconstant_normalize(&i->hi);
}


// Adds interval to conflict, and destructs it
void bv_arith_add2conflict(bv_arith_ctx_t* lctx,
                           term_t min_saved_term,
                           interval_t* i,
                           ivector_t* conflict) {

  arith_t* exp          = lctx->exp;
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
  
  bv_arith_interval_destruct(i);
}

// Popping the longest interval in the heap,
// then the next ones in order of increasing lower bound, modulo 2^n
// (once this function starts being called, do not push anything in the heap any more)
interval_t* bv_arith_pop(bv_arith_ctx_t* lctx){
  interval_t* i = ptr_heap_get_min(&lctx->heap);
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

// Returns the index of the longest interval in an array of (non-empty) interval pointers
static inline
uint32_t get_longest(interval_t** intervals, uint32_t number_intervals){
  assert(number_intervals != 0);
  uint32_t bitwidth = get_bitwidth(intervals[0]);
  uint32_t result = 0;

  for (uint32_t i = 1; i < number_intervals; i++){
    assert(intervals[i] != NULL);
    assert(get_bitwidth(intervals[i]) == bitwidth);
    // If it is longer than the previous longest, we update the latter
    if (bvconstant_lt(&intervals[0]->length, &intervals[i]->length)){
      result = i;
    }
  }
  return result;
}

// Argument intervals[0] is a non-empty array of (non-empty) interval pointers
// of a common bitwidth w, which is also the bitwidth of optional argument start_arg.
// Computes from intervals[0] and start_arg a coverage of all values of bitwidth w.
// Places the chaining conditions (literals) in output,
// and outputs whether or not start_arg has been used in the coverage
static
bool cover(bv_arith_ctx_t* lctx,
           ivector_t* output,       // Where we dump our literals in the end
           uint32_t bitwidths,      // Number of distinct bitwidths remaining after this
           interval_t*** intervals, // Array of size bitwidths
           uint32_t* numbers,       // Array of size bitwidths
           interval_t* start_arg    // First interval of coverage, can be NULL
           ){
  assert(intervals[0] != NULL);
  assert(intervals[0][0] != NULL);
  
  plugin_context_t* ctx = lctx->exp->super.ctx;
  term_manager_t* tm    = ctx->tm;
  term_table_t* terms   = ctx->terms;
  uint32_t w            = get_bitwidth(intervals[0][0]); // Bitwidth currently being treated
  uint32_t n            = numbers[0]; // Number of intervals of bitwidth w

  // We start by computing the longest interval in intervals[0]
  interval_t* longest = intervals[0][get_longest(intervals[0], n)];

  if (is_full(longest)) { // if interal is full, we're done, we just add the reason
    if (longest->reason != NULL_TERM) {
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "Using 1 full interval with internal reason ");
        term_print_to_file(out, tm->terms, longest->reason);
        fprintf(out, "\n");
      }
      uint32_t eval_level = 0;
      assert(bv_evaluator_evaluate_term(lctx->exp->super.eval, longest->reason, &eval_level)->b);
      (void) eval_level;
      ivector_push(output, longest->reason);
    }
    return false;
  }

  bool result = false; // As far as we know, we are not using start_arg

  uint32_t j = 1; // We will use this variable to loop inside intervals[0]
  // if first interval of our coverage = longest of intervals[0]
  // (which after sorting will be intervals[0][0]),
  // then the next interval we look at will be intervals[0][1], hence j = 1
  if (start_arg != NULL && bvconstant_lt(&longest->length,&start_arg->length)) {
    longest = start_arg;
    result  = true; // We do end up using it, unless lower levels cover all
    j = 0; // if first interval of our coverage = start_arg
    // then the next interval we look at will be intervals[0][0], hence j = 0
  }  
  ptr_array_sort2((void **)intervals[0], n, &longest->lo, cmp_base);
  // The bv_constant we are trying to cover until
  bvconstant_t* base = &longest->lo;// as soon as we cover up to longest->lo, we have complete coverage
   
  // The elements saved in &conflict so far force the feasible value
  // for conflict_var[w] to be in [saved; base[
  // saved is initialise with start->hi, & will increase until reaching base (start->lo)
  bvconstant_t* saved = &longest->hi;
  term_t saved_term = longest->hi_term; // The term behind this lower bound of feasible values

  // The best interval found so far in intervals[0], but not yet saved in output,
  // that can be used to forbid the greatest number of bv values beyond saved
  interval_t* best_so_far = NULL;
  bool notdone = true;
  interval_t* i = intervals[0][j]; // We start with this interval
  // ...and we loop over the rest of the intervals
  while (notdone /* &&!bvconstant_eq(saved,base) */){

    if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "bv_arith looks at ");
      bv_arith_interval_print(out, terms, i);
      fprintf(out, "\n");
    }

    if (is_in_interval(saved,i)) { // In continuity of previously forbidden range
      if (is_in_interval(base,i)) { // Yeah! interval forbids all remaining values
        if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
          FILE* out = ctx_trace_out(ctx);
          fprintf(out, "finished the job\n");
        }
        notdone = false; // We completely exit the loop
        bv_arith_add2conflict(lctx, saved_term, i, output); // record the interval i that finished the job
        saved_term = i->hi_term;
      } else { // interval doesn't forbid all remaining values;
        // does is eliminate more values than best_so_far?
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
      }
      if (i != start_arg) j=(j+1)%n; // unless i is start_arg, we advance in the array
      i = intervals[0][j]; // next interval to consider
    } else { // Not in continuity of previously forbidden range
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "is in discontinuity\n");
      } // There's a hole, so we look at whether start_arg helps covering it
      if (start_arg != NULL
          && is_in_interval(saved,start_arg) // start_arg is in continuity
          && ((best_so_far == NULL) // either there's no best_so_far
              || ((best_so_far != NULL) // or start_arg does a better job than it
                  && is_in_interval(&best_so_far->hi, start_arg)))) {
        i = start_arg; // We are definitely going to use start_arg in the coverage
        result = true; // We will declare it as the return value
      } else {
        if (best_so_far != NULL) { // We need to save best_so_far in output
          bv_arith_add2conflict(lctx, saved_term, best_so_far, output);
          saved       = &best_so_far->hi;
          saved_term  = best_so_far->hi_term;
          best_so_far = NULL;
        } else { // Discontinuity in intervals!
          // The hole must be filled by lower levels, as done by recursive call to cover
          assert(bitwidths != 0); // There'd better be at least one more level
          uint32_t next_bitwidth = get_bitwidth(intervals[1][0]);
          assert(next_bitwidth < w); // it'd better be a smaller bitwidth
          ivector_t rec_output;      // where the recursive call should place literals
          init_ivector(&rec_output, 0);
          bvconstant_t lo,hi,smaller_values;
          init_bvconstant(&lo);
          init_bvconstant(&hi);
          init_bvconstant(&smaller_values);
          bvconstant_copy(&lo, saved->bitsize, saved->data);
          bvconstant_copy(&hi, i->lo.bitsize, i->lo.data);
          bvconstant_set_all_zero(&smaller_values, w);
          bvconst_set_bit(smaller_values.data, next_bitwidth); // how many values of the next bitwidth?
          term_t lo_term = saved_term;
          term_t hi_term = i->lo_term;
          interval_t hole; // Defining hole to be filled by the next level(s)
          interval_construct(lctx, &lo, &hi, lo_term, hi_term, NULL_TERM, &hole);
          bool hole_used;
          if (bvconstant_lt(&hole.length, &smaller_values)) {
            // Hole is smaller than number of values in smaller bitwidth -> we project
            bvconstant_t lo_proj,hi_proj;
            init_bvconstant(&lo_proj);
            init_bvconstant(&hi_proj);
            bvconstant_extract(&lo_proj, lo.data, 0, next_bitwidth);
            bvconstant_extract(&hi_proj, hi.data, 0, next_bitwidth);
            interval_t hole_complement; // at the smaller bitwidth
            interval_construct(lctx, &hi_proj, &lo_proj,
                               term_extract(tm, hi_term, 0, next_bitwidth),
                               term_extract(tm, lo_term, 0, next_bitwidth),
                               NULL_TERM, &hole_complement);
            hole_used = cover(lctx, &rec_output,
                              bitwidths-1, &intervals[1], &numbers[1],
                              &hole_complement);
            bv_arith_interval_destruct(&hole_complement);
            delete_bvconstant(&lo_proj);
            delete_bvconstant(&hi_proj);
          } else { // Hole is bigger -> lower level(s) must forbid everything
            hole_used = false;
            cover(lctx, &rec_output, bitwidths-1, &intervals[1], &numbers[1], NULL);
          }
          if (!hole_used) {
            ivector_reset(output); // if hole wasn't used, this bitwidth is useless
            notdone = false;
            result  = false;
            saved_term = NULL_TERM;
          } else { // otherwise we need to push to output that the hole was small
            term_t smaller_values_term = mk_bv_constant(tm, &smaller_values);
            term_t hole_length_term = bv_arith_sub_terms(tm, i->lo_term, saved_term);
            term_t literal = bv_arith_lt(tm, hole_length_term, smaller_values_term);
            if (literal != NULL_TERM) ivector_push(output, literal);
            saved = &i->lo;
            saved_term = i->lo_term;
          }
          ivector_add(output, rec_output.data, rec_output.size);
          delete_ivector(&rec_output);
          delete_bvconstant(&lo);
          delete_bvconstant(&hi);
          bv_arith_interval_destruct(&hole);
        }
      }
    }
  }
  if (saved_term != NULL_TERM) {
    bv_arith_add2conflict(lctx, saved_term, longest, output);
  }
  ivector_remove_duplicates(output);
  return result;
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
  term_manager_t* tm         = ctx->tm;
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

  // Each constraint from the conflict core will be translated into 1 forbidden interval
  // We keep them in an array of the same size as the conflict core
  uint32_t n = conflict_core->size;
  assert(n!=0);
  interval_t* intervals[n];

  // Variables that are going to be re-used for every item in the conflict core
  variable_t atom_i_var;
  bool       atom_i_value;
  term_t     atom_i_term;

  // We go through the conflict core
  for (uint32_t i = 0; i < n; i++) {
    
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
    uint32_t w = term_bitsize(terms, t0);
    t0 = extract(exp, t0, w);
    t1 = extract(exp, t1, w);

    switch (term_kind(terms, atom_i_term)) {
    case BV_GE_ATOM: {  
      intervals[i] = bv_arith_unit_le(&lctx, t1, t0, atom_i_value);
      break;
    }
    case BV_SGE_ATOM: {  // (t0 >=s t1) is equivalent to (t0+2^{w-1} >=u t1+2^{w-1})
      term_t t0prime = bv_arith_add_half(tm, t0);
      term_t t1prime = bv_arith_add_half(tm, t1);
      intervals[i] = bv_arith_unit_le(&lctx, t1prime, t0prime, atom_i_value);
      break;
    }
    case EQ_TERM :     
    case BV_EQ_ATOM: { // equality
      intervals[i] = bv_arith_unit_le(&lctx, bv_arith_sub_terms(tm, t0, t1),
                                      extract(exp, lctx.zero_term, w), atom_i_value);
      break;
    }
    default:
      assert(false);
    }
  }

  ptr_array_sort2((void **)&intervals, n, NULL, cmp_base); // We sort the intervals  
  assert(intervals[0] != NULL); // There should be at least one non-empty interval
  uint32_t nonemptys = 1; // Total number of non-empty intervals is about to get computed
  uint32_t bitwidths = 1; // Total number of distinct bitwidths is about to get computed
  for (; (nonemptys < n) && (intervals[nonemptys] != NULL); nonemptys++) {
    if (get_bitwidth(intervals[nonemptys-1]) != get_bitwidth(intervals[nonemptys])){
      bitwidths++;
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
    fprintf(out, "\nWe now look at the forbidden intervals we have collected, which are\n");
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

  /* All conflicting atoms have been treated, the resulting forbidden intervals for the
  conflict_var have been pushed in the heap. It's now time to look at what's in the heap. */
  
  interval_t* longest = bv_arith_pop(&lctx);
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
      (void) eval_level;
      ivector_push(conflict, longest->reason);
    }
    bv_arith_interval_destruct(longest);
  }
  else {  // Saving longest interval's lower bound.
    bvconstant_t base;
    init_bvconstant(&base);
    bvconstant_copy(&base, longest->lo.bitsize, longest->lo.data);

    // We will now shift down every interval by that quantity, to change where our 0 is.
    bv_arith_ishift(ctx, longest, &base); // longest is now of the form [0 ; ... [

    // The elements saved in &conflict so far force the first feasible value for conflict_var to be at least min_saved
    bvconstant_t min_save;
    init_bvconstant(&min_save);
    bvconstant_copy(&min_save, longest->hi.bitsize, longest->hi.data);
    term_t min_saved_term = longest->hi_term; // The term behind this lower bound of feasible values

    // The best interval found so far in the heap, but not yet saved in &conflict,
    // that can be used to forbid the greatest number of bv values beyond min_saved
    interval_t* best_so_far = NULL;

    interval_t* i = bv_arith_pop(&lctx);
    bv_arith_ishift(ctx, i, &base);

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
          bv_arith_ishift(ctx, i, &base);
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
  int_hmap_reset(&exp->coeff1_cache);
  int_hmap_reset(&exp->coeffm1_cache);

  // We go through the conflict core
  for (uint32_t i = 0; i < conflict_core->size; i++) {
      
    // Atom and its term
    variable_t atom_var   = conflict_core->data[i];
    term_t     atom_term  = variable_db_get_term(ctx->var_db, atom_var);

    assert(is_pos_term(atom_term));

    if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "bv_arith looks at whether this is in the fragment: ");
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
      int32_t t0_good = bv_arith_coeff(exp, t0, false);
      int32_t t1_good = bv_arith_coeff(exp, t1, false);
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "can_explain gets coefficients %d and %d\n", t0_good, t1_good);
      }
      if ((t0_good == 2) || (t1_good == 2) || (t0_good * t1_good == -1)) {
        // Turns out we actually can't deal with the constraint. We stop
        return false;
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
  return false;
}

static
term_t explain_propagation(bv_subexplainer_t* this, const ivector_t* reasons_in, variable_t x, ivector_t* reasons_out) {
  assert(false);
  return NULL_TERM;
}

static
void destruct(bv_subexplainer_t* this) {
  arith_t* exp = (arith_t*) this;
  bv_evaluator_csttrail_destruct(&exp->csttrail);
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

  init_int_hmap(&exp->coeff1_cache, 0);
  init_int_hmap(&exp->coeffm1_cache, 0);

  return (bv_subexplainer_t*) exp;
}
