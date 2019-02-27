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

  int_hset_t constant_cache; // Cache of terms that are constant
  int_hset_t coeff0_cache; // Cache of non-constant terms whose coeff for conflict_var is 0
  int_hset_t coeff1_cache; // Cache of terms whose coeff for conflict_var is 1
  int_hset_t coeffm1_cache; // Cache of terms whose coeff for conflict_var is -1
  int_hset_t free_var; // The free variables of the current conflict that have values on the trail (i.e. that are not the conflict variable)

} arith_t;


/**
   Two functions used for detecting whether conflict is in fragment
**/

// Checks whether term t evaluates, all its BV-variables having values on the trail.
// If it does not, use_trail is untouched. If it does, then use_trail is set to true
// if the trail is actually used (i.e. term has a BV-variable), otherwise it is set to false.

bool bv_arith_evaluates(arith_t* exp, term_t t, term_t conflict_var, bool* use_trail) {

  assert(is_pos_term(t));
  plugin_context_t* ctx = exp->super.ctx;

  if (t == conflict_var) return false;

  // Answer right away in case already found to be constant or if it evaluates
  if (int_hset_member(&exp->constant_cache, t)) {
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "This term has previously been found to have a value not using the trail ");
      ctx_trace_term(ctx, t);
    }
    *use_trail = false;
    return true;
  }
  if (int_hset_member(&exp->coeff0_cache, t)) {
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "This term has previously been found to have a value using the trail ");
      ctx_trace_term(ctx, t);
    }
    *use_trail = true;
    return true;
  }

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Looking at whether this term has a value ");
    ctx_trace_term(ctx, t);
  }

  variable_db_t* var_db = ctx->var_db; // standard abbreviations
  term_table_t* terms   = ctx->terms;

  variable_t var = variable_db_get_variable_if_exists(var_db, t); // term as a variable

  // If ((var != variable_null) && int_hset_member(&exp->free_var, var))
  // then the term does evaluate and use the trail: we don't look into its structure.

  if ((var != variable_null) && int_hset_member(&exp->free_var, var)) {
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "This term is a free variable of the conflict with a value on the trail: ");
      ctx_trace_term(ctx, t);
    }
    *use_trail = true;
  } else { // otherwise we look into it
    
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Looking at the kind of\n");
      ctx_trace_term(ctx, t);
    }

    bool output = false;

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
        bool recurs = false;
        if (!bv_arith_evaluates(exp, t_i_pos, conflict_var, &recurs)) return false;
        output = output || recurs;
      }
      break;
    }
    case BIT_TERM: {
      term_t arg = bit_term_arg(terms, t);
      term_t arg_pos = unsigned_term(arg);
      if (!bv_arith_evaluates(exp, arg_pos, conflict_var, &output)) return false;
      break;
    }
    case BV_POLY: {
      bvpoly_t* t_poly = bvpoly_term_desc(terms, t);
      for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
        if (t_poly->mono[i].var == const_idx) continue;
        bool recurs = false;
        if (!bv_arith_evaluates(exp, t_poly->mono[i].var, conflict_var, &recurs))
          return false;
        output = output || recurs;
      }
      break;
    }
    case BV64_POLY: {
      bvpoly64_t* t_poly = bvpoly64_term_desc(terms, t);
      for (uint32_t i = 0; i < t_poly->nterms; ++ i) {
        if (t_poly->mono[i].var == const_idx) continue;
        bool recurs = false;
        if (!bv_arith_evaluates(exp, t_poly->mono[i].var, conflict_var, &recurs))
          return false;
        output = output || recurs;
      }
      break;
    }
    case POWER_PRODUCT: {
      pprod_t* t_pprod = pprod_term_desc(terms, t);
      for (uint32_t i = 0; i < t_pprod->len; ++ i) {
        bool recurs = false;
        if (!bv_arith_evaluates(exp, t_pprod->prod[i].var, conflict_var, &recurs))
          return false;
      }
      break;
    }
    default:
      return false;
    }

    *use_trail = output;
  }

  if (*use_trail) {
    int_hset_add(&exp->coeff0_cache, t);
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
      FILE* out = ctx_trace_out(ctx);
      ctx_trace_term(ctx, t);
      fprintf(out, "...evaluates using the trail\n");
    }
  } else {
    int_hset_add(&exp->constant_cache, t);
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith::scan")) {
      FILE* out = ctx_trace_out(ctx);
      ctx_trace_term(ctx, t);
      fprintf(out, "...is found to be constant\n");
    }
  }
    
  return true;
}

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
  if (bv_arith_evaluates(exp, t, conflict_var, &ignore_this_bool)) return 0;

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
          if (bvconst_is_minus_one(t_poly->mono[i].coeff, t_poly->width)) result = -1;
          else return 2;
        };
        if (assume_fragment) break; // If in fragment, need not look at other monomials
      } else { // The monomial variable is not the conflict var itself
        if (!assume_fragment
            && !bv_arith_evaluates(exp, t_poly->mono[i].var, conflict_var, &ignore_this_bool)) {
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
            && !bv_arith_evaluates(exp, t_poly->mono[i].var, conflict_var, &ignore_this_bool)) {
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

// Making atoms. Assumption for these 3 functions:
// the atom to be build evaluates to true according to the trail.

// This function checks whether (left == right) would be a good term to add to a conflict
// (it is good if it is not trivially true).
// If it is, it returns the term (left == right). If not, it returns NULL_TERM.

term_t bv_arith_eq(arith_t* exp, term_t left, term_t right) {
  if (left == right) return NULL_TERM; // equality would be trivially true
  bool left_uses_trail, right_uses_trail, sanity;
  sanity = bv_arith_evaluates(exp, left, variable_null, &left_uses_trail);
  assert(sanity);
  sanity = bv_arith_evaluates(exp, right, variable_null, &right_uses_trail);
  assert(sanity);

  if (left_uses_trail || right_uses_trail)
    return bveq_atom(exp->super.ctx->terms, left, right);
  else // equality would be true by evaluation without involving the trail
    return NULL_TERM;
}

// This function checks whether (left < right) would be a good term to add to a conflict
// (it is good if it is not trivially true).
// If it is, it returns the term (left < right). If not, it returns NULL_TERM.

term_t bv_arith_lt(arith_t* exp, term_t left, term_t right) {
  term_table_t* terms = exp->super.ctx->terms;
  bool left_uses_trail, right_uses_trail, sanity;
  sanity = bv_arith_evaluates(exp, left, variable_null, &left_uses_trail);
  assert(sanity);
  sanity = bv_arith_evaluates(exp, right, variable_null, &right_uses_trail);
  assert(sanity);

  if (left_uses_trail || right_uses_trail)
    return not_term(terms, bvge_atom(terms, left, right));
  else // atom would be true by evaluation without involving the trail
    return NULL_TERM;
}

// This function checks whether (left <= right) would be a good term to add to a conflict
// (it is good if it is not trivially true).
// If it is, it returns the term (left <= right). If not, it returns NULL_TERM.

term_t bv_arith_le(arith_t* exp, term_t left, term_t right) {

  plugin_context_t* ctx = exp->super.ctx;

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "bv_arith_le: trying to produce ");
    term_print_to_file(out, ctx->terms, left);
    fprintf(out, " <= ");
    term_print_to_file(out, ctx->terms, right);
    fprintf(out, "\n");
  }

  if (left == right) return NULL_TERM; // inequality would be trivially true
  bool left_uses_trail, right_uses_trail, sanity;
  sanity = bv_arith_evaluates(exp, left, variable_null, &left_uses_trail);
  assert(sanity);
  sanity = bv_arith_evaluates(exp, right, variable_null, &right_uses_trail);
  assert(sanity);

  bool result = true; // whether we continue code or stop
  uint32_t ignore_this_int = 0;
  bvconstant_t eval;
  init_bvconstant(&eval);


  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "bv_arith_le: left_uses_trail = %d, right_uses_trail = %d\n", left_uses_trail, right_uses_trail);
  }

  // if left is 0, inequality would be trivially true
  if (!left_uses_trail) {
    bv_evaluator_run_term(exp->super.eval, left, &eval, &ignore_this_int);
    result = !bvconstant_is_zero(&eval);
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "left is zero = %d\n", result);
    }
  }

  // if right is 2^n-1, inequality would be trivially true
  if (result && !right_uses_trail) {
    bv_evaluator_run_term(exp->super.eval, right, &eval, &ignore_this_int);
    result = !bvconstant_is_minus_one(&eval);
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "left is zero or right is 2^n-1 = %d\n", result);
    }
  }

  delete_bvconstant(&eval);

  if (result && (left_uses_trail || right_uses_trail))
    return bvge_atom(exp->super.ctx->terms, right, left);
  else // inequality would be true by evaluation without involving the trail
    return NULL_TERM;
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
  term_t conflict_var;
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

void bv_arith_full_interval_push(bv_arith_ctx_t* lctx, term_t reason) {
  assert(reason != NULL_TERM);
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
   Explanation mechanism. First for 1 constraint. Then for the whole conflict
**/

// Treat a constraint of the form lhs <= rhs (is_neq == false) of lhs != rhs (is_neq == true)
void bv_arith_unit_constraint(bv_arith_ctx_t* lctx, term_t lhs, term_t rhs, bool is_neq) {
  // Standard abbreviations
  plugin_context_t* ctx = lctx->exp->super.ctx;
  term_manager_t* tm    = &ctx->var_db->tm;

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "\nTreating unit_constraint (lhs %s rhs) where lhs is ", is_neq?"!=":"<=");
    term_print_to_file(out, ctx->terms, lhs);
    fprintf(out, " and rhs is ");
    term_print_to_file(out, ctx->terms, rhs);
    fprintf(out, "\n");
  }

  int32_t left_coeff = bv_arith_coeff(lctx->exp, lhs, lctx->conflict_var, true);
  int32_t right_coeff = bv_arith_coeff(lctx->exp, rhs, lctx->conflict_var, true);
    
  if ((left_coeff == -1) || (right_coeff == -1)) {
    // if coeff is negative, we add one, negate and swap sides.
    term_t nlhs = bv_arith_negate_terms(tm, bv_arith_add_one_term(tm, lhs));
    term_t nrhs = bv_arith_negate_terms(tm, bv_arith_add_one_term(tm, rhs));
    return bv_arith_unit_constraint(lctx, nrhs, nlhs, is_neq);
  }
  
  // Now we are sure that on both sides, coefficient is either 0 or 1
  // we check which one:
  bool left_has  = (left_coeff == 1);
  bool right_has = (right_coeff == 1);

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
  init_bvconstant(&cc1);
  init_bvconstant(&cc2);
  uint32_t eval_level = 0; // What is this level ?!? Let's say it's 0 :-)
  bv_evaluator_run_term(lctx->exp->super.eval, c1, &cc1, &eval_level);
  eval_level = 0;
  bv_evaluator_run_term(lctx->exp->super.eval, c2, &cc2, &eval_level);
  assert(bvconstant_is_normalized(&cc1));
  assert(bvconstant_is_normalized(&cc2));

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "as well as cc1: ");
    bvconst_print(out, cc1.data, cc1.bitsize);
    fprintf(out, " and cc2: ");
    bvconst_print(out, cc2.data, cc2.bitsize);
    fprintf(out, "\n");
  }

  term_t lo_term, hi_term;
  bvconstant_t lo, hi;
  init_bvconstant(&lo);
  init_bvconstant(&hi);

  if (is_neq) { // case of inequality (lhs != rhs)
    if ((right_has && left_has) || ((!right_has) && (!left_has))) { // x appears on both sides or on neither sides
      if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "is_neq: present on both sides or neither\n");
      }
      if (bvconstant_eq(&cc1,&cc2)) // If c1 == c2, we forbid everything, otherwise we forbid nothing
        bv_arith_full_interval_push(lctx, bv_arith_eq(lctx->exp, c1, c2));
    }
    if (right_has && !left_has) { // case (c1 != c2 + x), forbidden interval is [ c1-c2 ; c1-c2 ]
      bvconstant_copy(&lo, cc1.bitsize, cc1.data);
      bvconstant_sub(&lo, &cc2);
      bvconstant_normalize(&lo);
      lo_term = bv_arith_sub_terms(tm,c1,c2);
      bv_arith_singleton_push(lctx, &lo, lo_term, NULL_TERM);
    }
    if (left_has && !right_has) { // case of inequality (c1 + x != c2): forbidden interval is [ c2-c1 ; c2-c1 ]
      bvconstant_copy(&lo, cc2.bitsize, cc2.data);
      bvconstant_sub(&lo, &cc1);
      bvconstant_normalize(&lo);
      lo_term = bv_arith_sub_terms(tm,c2,c1);
      bv_arith_singleton_push(lctx, &lo, lo_term, NULL_TERM);
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
        if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
          FILE* out = ctx_trace_out(ctx);
          fprintf(out, "Case <=: has_right, has_left, lo = ");
          bvconst_print(out, lo.data, lo.bitsize);
          fprintf(out, ", hi = ");
          bvconst_print(out, hi.data, hi.bitsize);
          fprintf(out, "\n");
        }
        if (!bvconstant_eq(&lo,&hi))
          bv_arith_interval_push(lctx, &lo, &hi, lo_term, hi_term, NULL_TERM);
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
        if (!bvconstant_eq(&lo,&hi))
          bv_arith_interval_push(lctx, &lo, &hi, lo_term, hi_term, NULL_TERM);
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
        if (!bvconstant_eq(&lo,&hi))
          bv_arith_interval_push(lctx, &lo, &hi, lo_term, hi_term, NULL_TERM);
      } else { // x appears on neither sides
        if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
          FILE* out = ctx_trace_out(ctx);
          fprintf(out, "Case <=: !has_right, !has_left");
        }
        if (bvconstant_lt(&cc2,&cc1)) { // If c2 < c1, we forbid everything, otherwise we forbid nothing
          bv_arith_full_interval_push(lctx, bv_arith_lt(lctx->exp, c2, c1));
        }
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
  term_manager_t* tm = &ctx->var_db->tm;
  bvconstant_sub(&i->lo, base);
  bvconstant_normalize(&i->lo);
  i->lo_term = bv_arith_sub_terms(tm, i->lo_term, base_term);  
  bvconstant_sub(&i->hi, base);
  bvconstant_normalize(&i->hi);
  i->hi_term = bv_arith_sub_terms(tm, i->hi_term, base_term);
}


// Adds interval to conflict, and destructs it
void bv_arith_add2conflict(arith_t* exp,
                           term_t min_saved_term,
                           bvconst_interval_t* i,
                           ivector_t* conflict) {
  plugin_context_t* ctx = exp->super.ctx;
  term_manager_t* tm = &ctx->var_db->tm;

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Adding to conflict interval ");
    bv_arith_interval_print(out, ctx->terms, i);
    fprintf(out, "  hooking up with ( ");
    term_print_to_file(out, tm->terms, min_saved_term);
    fprintf(out, " )\n");
  }

  term_t continuity_reason = bv_arith_le(exp, i->lo_term, min_saved_term);
  if (continuity_reason != NULL_TERM) {
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Adding continuity_reason ");
      term_print_to_file(out, tm->terms, i->lo_term);
      fprintf(out, " <= ");
      term_print_to_file(out, tm->terms, min_saved_term);
      fprintf(out, ", i.e. ");
      term_print_to_file(out, tm->terms, continuity_reason);
      fprintf(out, "\n");
    }
    uint32_t eval_level = 0;
    assert(bv_evaluator_run_atom(exp->super.eval, continuity_reason, &eval_level));
    ivector_push(conflict, continuity_reason);
  }

  if (i->reason != NULL_TERM) {
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Adding internal reason ");
      term_print_to_file(out, tm->terms, i->reason);
      fprintf(out, "\n");
    }
    uint32_t eval_level = 0;
    assert(bv_evaluator_run_atom(exp->super.eval, i->reason, &eval_level));
    ivector_push(conflict, i->reason);
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
  term_table_t* terms  = ctx->terms;
  const mcsat_trail_t* trail = ctx->trail;
  term_manager_t* tm = &ctx->var_db->tm;

  // We initialise the local context
  bv_arith_ctx_t lctx;
  lctx.exp          = exp;
  lctx.conflict_var = variable_db_get_term(ctx->var_db, conflict_var);
  lctx.longest      = NULL;
  init_ptr_heap(&lctx.heap, 0, &cmp);
  init_ptr_queue(&lctx.queue, 0);

  init_bvconstant(&lctx.zero);
  bvconstant_set_all_zero(&lctx.zero, term_bitsize(terms, lctx.conflict_var));

  lctx.zero_term = mk_bv_constant(tm, &lctx.zero);

  init_bvconstant(&lctx.length);
  bvconstant_set_all_zero(&lctx.length, term_bitsize(terms, lctx.conflict_var));
  
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

  if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "\nWe now look at what's in the heap\n\n");
  }

  /* All conflicting atoms have been treated, the resulting forbidden intervals for the
  conflict_var have been pushed in the heap. It's now time to look at what's in the heap.
  */
  
  bvconst_interval_t* i = bv_arith_pop(&lctx);
  assert(i!=NULL);
  
  // The elements saved in &conflict so far force the first feasible value for conflict_var to be at least min_saved
  bvconstant_t base, min_save;
  init_bvconstant(&base);
  bvconstant_copy(&base, i->lo.bitsize, i->lo.data);
  init_bvconstant(&min_save);
  bvconstant_copy(&min_save, lctx.zero.bitsize, lctx.zero.data);

  term_t base_term = i->lo_term; 
  term_t min_saved_term = lctx.zero_term; // The term behind this lower bound of feasible values

  // The best interval found so far in the heap, but not yet saved in &conflict,
  // that can be used to forbid the greatest number of bv values beyond min_saved
  bvconst_interval_t* best_so_far = NULL;
  bv_arith_ishift(ctx, i, &base, base_term);
 
  // Now we treat the heap
  while (i != NULL) {
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
        best_so_far = i;
        // Now we empty the heap
        i = bv_arith_pop(&lctx);
        while (i != NULL) {
          bv_arith_interval_destruct(i);
          i = bv_arith_pop(&lctx);
        }
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
        bv_arith_add2conflict(exp, previous_min_saved_term, best_so_far, conflict);
        best_so_far = NULL;
      } else { // Discontinuity in intervals, shouldn't happen if in conflict
        assert(false);
      }
    }
  }

  assert(best_so_far != NULL);
  term_t continuity_reason = bv_arith_lt(exp, best_so_far->hi_term, best_so_far->lo_term);
  if (!(bvconstant_eq(&best_so_far->hi, &best_so_far->lo))
      && continuity_reason != NULL_TERM) {
    if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Adding last continuity_reason ");
      term_print_to_file(out, terms, best_so_far->hi_term);
      fprintf(out, " <= ");
      term_print_to_file(out, terms, best_so_far->lo_term);
      fprintf(out, ", i.e. ");
      term_print_to_file(out, terms, continuity_reason);
      fprintf(out, "\n");
    }
    uint32_t eval_level = 0;
    assert(!bv_evaluator_run_atom(exp->super.eval,not_term(terms,continuity_reason), &eval_level));
    ivector_push(conflict, continuity_reason);
  }
  bv_arith_add2conflict(exp, min_saved_term, best_so_far, conflict);
  
  assert(ptr_heap_is_empty(&lctx.heap));
  assert(ptr_queue_is_empty(&lctx.queue));

  delete_bvconstant(&base);
  delete_bvconstant(&min_save);
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
  arith_t* exp = (arith_t*) this;
  plugin_context_t* ctx = this->ctx;
  term_table_t* terms  = ctx->terms;
  term_t conflict_var_term = variable_db_get_term(ctx->var_db, conflict_var);
  const mcsat_trail_t* trail = ctx->trail;

  // Resetting the cache & co.
  int_hset_reset(&exp->coeff0_cache);
  int_hset_reset(&exp->coeff1_cache);
  int_hset_reset(&exp->coeffm1_cache);
  int_hset_reset(&exp->free_var);

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
      ctx_trace_term(ctx, conflict_var_term);
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
      // OK, maybe we can treat the constraint atom_i_term. We first collect its free variables.
      // Getting them as a list:
      variable_list_ref_t list_ref = watch_list_manager_get_list_of(this->wlm, atom_i_var);
      variable_t* vars = watch_list_manager_get_list(this->wlm, list_ref);
      for (; *vars != variable_null; vars++) {
        variable_t var = *vars;
        if ((var != atom_i_var) && (var != conflict_var)) {
          assert(trail_has_value(trail, var));
          if (ctx_trace_enabled(ctx, "mcsat::bv::arith")) {
            FILE* out = ctx_trace_out(ctx);
            fprintf(out, "Found free variable with value on the trail: ");
            variable_db_print_variable(ctx->var_db, var, out);
            fprintf(out, "\n");
          }
          int_hset_add(&exp->free_var, var);
        }
      }
      // Now that we have collected the free variables, we look into the constraint structure
      int32_t t0_good = bv_arith_coeff(exp, t0, conflict_var_term, false);
      int32_t t1_good = bv_arith_coeff(exp, t1, conflict_var_term, false);
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
  delete_int_hset(&exp->constant_cache);
  delete_int_hset(&exp->coeff0_cache);
  delete_int_hset(&exp->coeff1_cache);
  delete_int_hset(&exp->coeffm1_cache);
  delete_int_hset(&exp->free_var);
}

/** Allocate the sub-explainer and setup the methods */
bv_subexplainer_t* arith_new(plugin_context_t* ctx, watch_list_manager_t* wlm, bv_evaluator_t* eval) {

  arith_t* exp = safe_malloc(sizeof(arith_t));

  bv_subexplainer_construct(&exp->super, "mcsat::bv::explain::arith", ctx, wlm, eval);

  exp->super.can_explain_conflict = can_explain_conflict;
  exp->super.explain_conflict = explain_conflict;
  exp->super.destruct = destruct;

  init_int_hset(&exp->constant_cache, 0);
  init_int_hset(&exp->coeff0_cache, 0);
  init_int_hset(&exp->coeff1_cache, 0);
  init_int_hset(&exp->coeffm1_cache, 0);
  init_int_hset(&exp->free_var, 0);

  return (bv_subexplainer_t*) exp;
}
