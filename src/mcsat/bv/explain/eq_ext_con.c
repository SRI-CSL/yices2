/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#if defined(CYGWIN) || defined(MINGW)
#ifndef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__ __declspec(dllexport)
#endif
#endif

#include "eq_ext_con.h"

#include "mcsat/tracing.h"
#include "mcsat/value.h"
#include "terms/term_manager.h"

#include "mcsat/bv/bv_utils.h"
#include "mcsat/eq/equality_graph.h"

#include "yices.h"

typedef struct eq_ext_con_s {

  /** Interfact of the subexplainer */
  bv_subexplainer_t super;
  bv_csttrail_t csttrail; // Where we keep some cached values
  int_hset_t good_terms_cache; // Cache of terms that can be treated by this explainer

} eq_ext_con_t;

typedef struct slice_s slice_t;

/* Pair of slices (equality or disequality) */
typedef struct {
  slice_t* lhs;
  slice_t* rhs;
  /** Whether it has been queued for treatment and deletion */
  bool queued;
  /**
   * Identifier of where in the conflict_core this pair appears / originates from.
   * 0 is the identifier for the set of equalities in the conflict core (a set of pairs).
   * Then each disequality in the conflict core gets an identifier between 1 and n,
   * and becomes a disjunction (a set of pairs) when sliced. Hence, if appearing_in is
   * 0, then the equality (lhs=rhs) is one of the constraints to satisfy,
   * and if appearing_in is i (1 <= i <= n), then the disequality (lhs!=rhs)
   * is one of the disjuncts of the disjunction number i, which needs to be satisfied.
   */
  uint32_t appearing_in;
} spair_t;

typedef struct splist_s splist_t;

/**
 * List of pairs of slices.
 *
 * When a pair (lhs,rhs) is created, it will be added (as main) to lhs's
 * list of pairs, and (as non-main) to rhs's list of pairs.
 */
struct splist_s {
  spair_t* pair;
  bool is_main;
  splist_t* next;
};

/** Slices: variable (or constant term) + extraction indices
    We avoid building the term to avoid cluttering the world with slices that may be short-lived
 */

typedef struct slice_base_s {
  /** Variable or constant term, from which the slice is extracted */
  term_t term;
  /** Low index */
  uint32_t lo;
  /** High index + 1 (that index is not in the slice), so that hi - low = slice length */
  uint32_t hi;
} slice_base_t;


/** The slices for a given variable form a binary tree; the leaves are the thinnest slices
 */

struct slice_s {
    /** Base of the slice, containing basic information */
  slice_base_t base;
  /** sub-slice towards the high indices, hi_sub->hi is the same as hi */
  slice_t* hi_sub;
  /** sub-slice towards the low indices, lo_sub->lo is the same as lo, lo_sub->hi is the same as hi_sub->lo */
  slice_t* lo_sub;
  /**
   * Other slices that this slice should be equal to or different from, as a
   * list of pairs (this slice is one side of each pair).
   */
  splist_t* paired_with;
};

// builds term from slice
static inline
term_t slice_mk_term(const slice_t* slice, term_manager_t* tm) {
  return term_extract(tm, slice->base.term, slice->base.lo, slice->base.hi);
}

/* List of slices */
typedef struct slist_s slist_t;

struct slist_s {
  slice_t* slice;
  slist_t* next;
};

// Main slicing algorithm

/** Type for a slicing = what is returned from a conflict core by the main function below */
typedef struct {
  /** Context, for utilities */
  eq_ext_con_t* exp;
  /**
   * Array of lists of pairs.
   * Cell 0 contains the list of slice equalities; then each cell contains a
   * list representing a disjunction of slice disequalities
   */
  splist_t** constraints;
  /** length of constraints */
  uint32_t nconstraints;
  /** Maps each involved variable (or constant term) to its slice-tree */
  ptr_hmap_t slices;
} bv_slicing_t;

/** pair construct */
spair_t* spair_new(slice_t* lhs, slice_t* rhs, uint32_t appearing_in) {
  assert(lhs != NULL);
  assert(rhs != NULL);
  spair_t* pair = safe_malloc(sizeof(spair_t));
  pair->lhs = lhs;
  pair->rhs = rhs;
  pair->queued = false;
  pair->appearing_in = appearing_in;
  return pair;
}

/** splist cons */
splist_t* splist_cons(spair_t* pair, bool is_main, splist_t* tail) {

  splist_t* result = safe_malloc(sizeof(splist_t));
  result->pair = pair;
  result->is_main = is_main;
  result->next = tail;
  return result;
}

/**
 * Delete a list of pairs, also deleting each pair if b == true.
 * In any case, not deleting slices that pairs consist of.
 */
void bv_slicing_spdelete(splist_t* spl, bool b) {
  splist_t* l = spl;
  splist_t* next;
  while (l != NULL) {
    next = l->next;
    if (b) safe_free(l->pair);
    safe_free(l);
    l = next;
  }
}

void slice_print(const slice_t* s, FILE* out) {
  fprintf(out, "[");
  if (s->lo_sub != NULL) {
    slice_print(s->hi_sub, out);
    slice_print(s->lo_sub, out);
  }
  else {
    if ((s->base.hi) == (s->base.lo)+1) {
      fprintf(out, "%i", s->base.lo);
    } else {
      fprintf(out, "%i:%i", (s->base.hi)-1, s->base.lo);
    }
  }
  fprintf(out, "]");
}

void ctx_print_slice(const plugin_context_t* ctx, const slice_t* s) {
  FILE* out = ctx_trace_out(ctx);
  term_table_t* terms = ctx->terms;
  term_print_to_file(out, terms, s->base.term);
  slice_print(s, out);
}

/** Prints a list of slices. */
void bv_slicing_print_slist(const plugin_context_t* ctx, slist_t* sl) {
  FILE* out = ctx_trace_out(ctx);
  slist_t* l = sl;
  while (l != NULL) {
    ctx_print_slice(ctx, l->slice);
    l = l->next;
    if (l != NULL) {
      fprintf(out, "::");
    }
  }
}

/** Prints a pairs. if b is true, as an equality, otherwise, as a disequality */
void ctx_print_spair(const plugin_context_t* ctx, spair_t* p, bool b) {
  FILE* out = ctx_trace_out(ctx);
  assert(p->lhs != NULL);
  assert(p->rhs != NULL);
  ctx_print_slice(ctx, p->lhs);
  fprintf(out, "%s", b?"=":"!=");
  ctx_print_slice(ctx, p->rhs);
}

/** Prints a list of pairs. if b is true, then these are equalities, otherwise, disequalities */
void ctx_print_splist(const plugin_context_t* ctx, splist_t* spl, bool b) {
  FILE* out = ctx_trace_out(ctx);
  splist_t* l = spl;
  while (l != NULL) {
    ctx_print_spair(ctx, l->pair, b);
    l = l->next;
    if (l != NULL) {
      fprintf(out, "%s", b?" && ":" || ");
    }
  }
}

/** Creates a leaf slice, no children */
slice_t* bv_slicing_slice_new(term_manager_t* tm, term_t term, uint32_t lo, uint32_t hi) {

  assert(lo < hi);
  slice_t* result = safe_malloc(sizeof(slice_t));

  result->base.term = term;
  result->base.lo  = lo;
  result->base.hi  = hi;
  result->paired_with = NULL;
  result->lo_sub  = NULL;
  result->hi_sub  = NULL;

  return result;
}

/**
 * Deletes a slice, recursively deleting children if they exist.
 * Also deletes the list of pairs involving the slice along the way, but not
 * deleting the pairs themselves.
 */
void bv_slicing_slice_delete(slice_t* s) {
  if (s->lo_sub != NULL) bv_slicing_slice_delete(s->lo_sub);
  if (s->hi_sub != NULL) bv_slicing_slice_delete(s->hi_sub);
  bv_slicing_spdelete(s->paired_with, false);
  safe_free(s);
}

/** slist cons */
slist_t* bv_slicing_scons(slice_t* s, slist_t* tail) {
  slist_t* result = safe_malloc(sizeof(slist_t));
  result->slice = s;
  result->next = tail;
  return result;
}

/** Slices slice s at index k, pushing resulting slicings to be performed in the "todo" queue */
void bv_slicing_split(const plugin_context_t* ctx, slice_t* s, uint32_t k, ptr_queue_t* todo) {

  if (ctx_trace_enabled(ctx, "mcsat::bv::slicing")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Splitting ");
    ctx_print_slice(ctx, s);
    fprintf(out, " at %d\n", k);
  }

  assert(s->lo_sub == NULL);
  assert(s->hi_sub == NULL);
  assert(k < s->base.hi);
  assert(s->base.lo < k);
  term_manager_t* tm = ctx->tm;
  s->lo_sub  = bv_slicing_slice_new(tm, s->base.term, s->base.lo, k);
  s->hi_sub  = bv_slicing_slice_new(tm, s->base.term, k, s->base.hi);

  splist_t *b = s->paired_with;
  splist_t *next;

  while (b != NULL) {
    spair_t* p = b->pair;
    /* fprintf(out, "Queueing "); */
    /* bv_slicing_print_spair(p, true, terms, out); */
    /* fprintf(out, "\n"); */
    if (!p->queued) {
      p->queued = true;
      ptr_queue_push(todo, p);
    }
    next = b->next;
    safe_free(b); // We delete the list nodes along the way (but not the pairs themselves)
    b = next;
  }
  s->paired_with = NULL;
}

/**
 * From a slice s and a stack of slices tail, stacks on tail consecutive
 * subslices of s that cover s (starting with low indices), with the property
 * that the first one is a leaf slice. Recursive function with tail being an
 * accumulator.
 */
slist_t* bv_slicing_as_list(slice_t* s, slist_t* tail) {
  assert(s != NULL);
  if (s->hi_sub == NULL) return bv_slicing_scons(s,tail);
  return bv_slicing_as_list(s->lo_sub, bv_slicing_scons(s->hi_sub, tail));
}

/**
 * Aligns 2 series l1 and l2 of slices, producing matching pairs (s1,s2) where
 * s1 and s2 have equal length. The alignment can trigger some future slicings
 * that are queued in todo. Destructs l1 and l2 along the way.
 */
void bv_slicing_align(const plugin_context_t* ctx, slist_t* l1, slist_t* l2, uint32_t appearing_in, ptr_queue_t* todo) {

  if (ctx_trace_enabled(ctx, "mcsat::bv::slicing")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out,"Aligning ");
    bv_slicing_print_slist(ctx, l1);
    fprintf(out," with ");
    bv_slicing_print_slist(ctx, l2);
    fprintf(out,"\n");
  }

  if (l1 == NULL) {
    return; // Reached the end of the lists. We stop.
  }

  assert(l2 != NULL);     // If l1 not empty then l2 not empty as the two lists must have the same total bitsize
  slice_t* h1 = l1->slice;
  slice_t* h2 = l2->slice;
  slist_t* t1 = l1->next;
  slist_t* t2 = l2->next;
  uint32_t w1 = h1->base.hi - h1->base.lo;
  uint32_t w2 = h2->base.hi - h2->base.lo;

  if ((h1->lo_sub == NULL) && (h2->lo_sub == NULL)) { // if both h1 and h2 are leaves
    if ( w1 < w2 ) {
      // h1 is shorter than h2, we slice h2
      bv_slicing_split(ctx, h2, h2->base.lo + w1, todo);
    }
    if ( w2 < w1 ) {
      // h2 is shorter than h1, we slice h1
      bv_slicing_split(ctx, h1, h1->base.lo + w2, todo);
    }
  }

  if (h2->lo_sub != NULL) { // head of l2 is not a leaf
    safe_free(l2); // l2 is not good, we free the node and recompute the list
    slist_t* slicing_list = bv_slicing_as_list(h2, t2);
    return bv_slicing_align(ctx, l1, slicing_list, appearing_in, todo);
  }

  if (h1->lo_sub != NULL) { // head of l1 is not a leaf
    safe_free(l1); // l1 is not good, we free the node and recompute the list
    slist_t* slicing_list = bv_slicing_as_list(h1, t1);
    return bv_slicing_align(ctx, slicing_list, l2, appearing_in, todo);
  }

  // OK, h1 and h2 have the same width; we can pair them.
  // We no longer need l1 and l2
  safe_free(l1);
  safe_free(l2);

  spair_t* p = spair_new(h1, h2, appearing_in); // We form the pair
  if (ctx_trace_enabled(ctx, "mcsat::bv::slicing")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out,"Forming pair ");
    ctx_print_spair(ctx, p, (appearing_in == 0));
    fprintf(out,"\n");
  }
  h1->paired_with = splist_cons(p, true, h1->paired_with);
  h2->paired_with = splist_cons(p, false, h2->paired_with);

  bv_slicing_align(ctx, t1, t2, appearing_in, todo);
}


/**
 * Stacks on argument tail consecutive sub-slices of s that cover s from lo to hi
 * (head of result is the lowest index slice). If either lo or hi does not coincide
 * with an existing slice point of s, they get created.
 * */
slist_t* bv_slicing_extracts(const plugin_context_t* ctx, slice_t* s, uint32_t hi, uint32_t lo, slist_t* tail, ptr_queue_t* todo) {

  /* fprintf(out, "Extracts %d to %d from ", hi, lo); */
  /* bv_slicing_print_slice(ctx, s, out); */
  /* fprintf(out, "\n"); */
  if ((hi <= s->base.lo) || (lo >= s->base.hi)) return tail; // Slice is disjoint from indices

  // We split the slice if need be (has to be a leaf,
  // and either hi or lo (or both) has to be a splitting index
  if (s->lo_sub == NULL) { // This slice is a leaf
    slice_t* s0 = s;
    if ((s0->base.lo < hi) && (hi < s0->base.hi)) {
      bv_slicing_split(ctx, s0, hi, todo);
      /* fprintf(out, "splitting at hi=%d, giving ", hi); */
      /* bv_slicing_print_slice(s, terms, out); */
      /* fprintf(out, "\n"); */
      s0 = s0->lo_sub;
    }
    if ((s0->base.lo < lo) && (lo < s0->base.hi)) {
      bv_slicing_split(ctx, s0, lo, todo);
      /* fprintf(out, "splitting at lo=%d, giving ", lo); */
      /* bv_slicing_print_slice(s, terms, out); */
      /* fprintf(out, "\n"); */
    }
  }

  // Now we create the list to return
  if (s->lo_sub == NULL) {// This slice is (still!) a leaf, we add it to the tail
    slist_t* result = bv_slicing_scons(s, tail);
    /* fprintf(out, "Extract returns "); */
    /* bv_slicing_print_slist(result, terms, out); */
    /* fprintf(out, "\n"); */
    return result;
  }

  // Otherwise it has two children and we call ourselves recursively
  slist_t* slicing_list = bv_slicing_extracts(ctx, s->hi_sub, hi, lo, tail, todo);
  slist_t* result = bv_slicing_extracts(ctx, s->lo_sub, hi, lo, slicing_list, todo);

  /* fprintf(out, "Extract returns "); */
  /* bv_slicing_print_slist(result, terms, out); */
  /* fprintf(out, "\n"); */

  return result;
}


/**
 * Wrapping up above function: stack on top of tail a slice with base t, from lo to hi
 */
slist_t* bv_slicing_sstack(const plugin_context_t* ctx, term_t t, uint32_t hi, uint32_t lo, slist_t* tail, ptr_queue_t* todo, ptr_hmap_t* slices) {

  if (ctx_trace_enabled(ctx, "mcsat::bv::slicing::norm")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Forming slice ");
    term_print_to_file(out, ctx->terms, t);
    fprintf(out, " between %d and %d\n", hi, lo);
  }

  // Getting that variable's top-level slice from global hashmap
  ptr_hmap_pair_t* p = ptr_hmap_get(slices, t);
  if (p->val == NULL) {
    // Create that slice if need be
    term_manager_t* tm = ctx->tm;
    p->val = bv_slicing_slice_new(tm, t, 0, bv_term_bitsize(ctx->terms, t));
  }
  // stack upon the tail list the relevant (series of) slice(s) covering lo to hi
  return bv_slicing_extracts(ctx, p->val, hi, lo, tail, todo);
}

static inline
term_t bit_over_extract(term_table_t* terms, term_t t) {
  if (term_kind(terms, t) == BIT_TERM) {
    select_term_t* desc   = bit_term_desc(terms, t);
    term_t arg            = desc->arg;
    uint32_t selected_bit = desc->idx; // Get bit that is selected in it
    if (term_kind(terms, arg) == BV_ARRAY) {
      composite_term_t* concat_desc = bvarray_term_desc(terms, arg);
      return bit_over_extract(terms,concat_desc->arg[selected_bit]);
    }
  }
  return t;
}

/** Normalises the hi-lo extraction of a term into a list of slices added to tail,
    which acts as an accumulator for this recursive function. */
slist_t* bv_slicing_norm(eq_ext_con_t* exp, term_t t, uint32_t hi, uint32_t lo, slist_t* tail, ptr_queue_t* todo, ptr_hmap_t* slices) {

  term_t conflict_var   = exp->csttrail.conflict_var_term;
  plugin_context_t* ctx = exp->super.ctx;
  term_manager_t* tm = ctx->tm;
    
  if (ctx_trace_enabled(ctx, "mcsat::bv::slicing")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Normalising ");
    term_print_to_file(out, ctx->terms, t);
    fprintf(out, " between %d and %d\n", hi, lo);
  }

  assert(lo < hi);
  term_table_t* terms = ctx->terms; // standard abbreviation

  // Now we determine whether we should descend into the term structure
  bool ignore_this_bool;
  // Whether term can be evaluated from trail
  bool is_evaluable = bv_evaluator_is_evaluable(&exp->csttrail, t, &ignore_this_bool);

  if ((!is_evaluable) && (term_kind(terms, t) == BV_ARRAY)) {

    // Concatenated boolean terms:
    composite_term_t* concat_desc = bvarray_term_desc(terms, t);
    assert(hi <= concat_desc->arity);
    /* fprintf(out, "This is a bv_array, where\n"); */

    // We go through the bits of the bv_array, starting from the end,
    // which represents the high bits.
    uint32_t total_width = hi - lo;

    // Variables that will evolve in the loop:
    slist_t* current = tail;  // the list constructed so far
    uint32_t width   = 0;     // bitwidth of current slice under construction
    bool     is_evaluable = true; // whether current slice is evaluable
    uint32_t low  = 0;           // if evaluable, must be 0, otherwise lo of current slice

    term_t bits[total_width];
    
    for (uint32_t j = 0; j < total_width; j++) {
      uint32_t i = hi - j -1;           // The bit we are dealing with
      term_t t_i = bit_over_extract(terms,concat_desc->arg[i]); // The Boolean term that constitutes that bit
      if (ctx_trace_enabled(ctx, "mcsat::bv::slicing::norm")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "bit %d is ",i);
        ctx_trace_term(ctx, t_i);
      }
      bits[i] = t_i;
      
      bool ignore_this_bool;
      // Whether term can be evaluated from trail
      bool has_value = bv_evaluator_is_evaluable(&exp->csttrail, t_i, &ignore_this_bool);

      if (!has_value) { // t_i is a bit of conflict_var
        assert(is_pos_term(t_i));
        uint32_t selected_bit = 0;
        assert(t_i == conflict_var || term_kind(terms, t_i) == BIT_TERM);
        if (term_kind(terms, t_i) == BIT_TERM) {
          select_term_t* desc = bit_term_desc(terms, t_i);
          assert(desc->arg == conflict_var);
          selected_bit = desc->idx; // Get bit that is selected in it
        }
        // We need to change slice if...
        if (is_evaluable                  //...slice so far was evaluable
            || selected_bit + 1 != low) { //...or new bit not in continuity
          // We create the term for the slice so far
          if (width != 0) { // If width == 0 then slice so far is inexistent
            term_t base;
            if (is_evaluable) {
              bvlogic_buffer_t* buffer = term_manager_get_bvlogic_buffer(tm);
              bvlogic_buffer_set_term_array(buffer, tm->terms, width, &bits[i+1]);
              base = mk_bvlogic_term(tm, buffer);
            } else {
              base = conflict_var;
            }
            // We close the slice so far, stack it upon the tail, and open a new slice
            current = bv_slicing_sstack(ctx, base, width+low, low, current, todo, slices);
          }
          width = 0; // We start a new slice
          is_evaluable = false; // ...which is not evaluable (slice of conflict_var)
        }
        low = selected_bit; // Whether we've close slice, selected_bit is the new low
      }
      else { // t_i is evaluable
        if (!is_evaluable) { // We need to change slice if slice so far is not evaluable
          // We close the slice so far, stack it upon the tail, and open a new slice
          assert(width != 0);
          current = bv_slicing_sstack(ctx, conflict_var, width+low, low, current, todo, slices);
          width = 0; // We start a new slice
          is_evaluable = true; // ...which is evaluable
        }
        low = 0;
      }
      width++; // Then in any case, bitwidth of current slice is incremented
    }
    // We have exited the loop, we now close the current (and last) slice
    if (is_evaluable) {
      bvlogic_buffer_t* buffer = term_manager_get_bvlogic_buffer(tm);
      bvlogic_buffer_set_term_array(buffer, tm->terms, width, bits);
      return bv_slicing_sstack(ctx, mk_bvlogic_term(tm, buffer), width, 0, current, todo, slices);
    }
    else {
      return bv_slicing_sstack(ctx, conflict_var, width+low, low, current, todo, slices);
    }
  }
  
  // The term is a variable or a constant, we immediately stack its relevant slices
  return bv_slicing_sstack(ctx, t, hi, lo, tail, todo, slices);
}

// Prints a slicing
void bv_slicing_print_slicing(const bv_slicing_t* slicing) {

  FILE* out = ctx_trace_out(slicing->exp->super.ctx);
  fprintf(out, "Slices:\n");
  // We go through all variables, and destroy all slices
  ptr_hmap_pair_t* hp = ptr_hmap_first_record((ptr_hmap_t*)&slicing->slices);
  while(hp != NULL) {
    ctx_print_slice(slicing->exp->super.ctx, hp->val);
    hp = ptr_hmap_next_record((ptr_hmap_t*)&slicing->slices, hp);
    fprintf(out, "\n");
  }
  fprintf(out, "Constraints:\n");
  for (uint32_t i = 0; i < slicing->nconstraints; i++) {
    if (i == 0)
      fprintf(out, "Equal.: ");
    else
      fprintf(out, "Dis.%d: ",i);
    ctx_print_splist(slicing->exp->super.ctx, slicing->constraints[i], (i == 0));
    fprintf(out, "\n");
  }
}

// Destructs a slicing. Everything goes.
void bv_slicing_slicing_destruct(bv_slicing_t* slicing) {

  // We go through all variables, and destroy all slices
  ptr_hmap_pair_t* hp = ptr_hmap_first_record(&slicing->slices);
  while(hp != NULL) {
    bv_slicing_slice_delete(hp->val);
    hp = ptr_hmap_next_record(&slicing->slices, hp);
  }

  delete_ptr_hmap(&slicing->slices);

  for (uint32_t i = 0; i < slicing->nconstraints; i++) {
    bv_slicing_spdelete(slicing->constraints[i], true);
  }

  safe_free(slicing->constraints);
}

/** At the end of the slicing algorithm, we go through each of the created slices,
    and perform 3 tasks: */
void bv_slicing_slice_treat(slice_t* s, splist_t** constraints, eq_ext_con_t* exp, eq_graph_t* egraph) {

  if (s->lo_sub == NULL) { // This is a leaf

    plugin_context_t* ctx = exp->super.ctx;
    term_manager_t* tm = ctx->tm;

    term_t s_term = s->base.term;

    if (ctx_trace_enabled(ctx, "mcsat::bv::slicing")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Treating slice ");
      ctx_print_slice(ctx, s);
    }

    // Task 1: we compute the value if we can & store it in value field

    bool ignore_this_bool;
    // Whether term can be evaluated from trail
    // (if true, use_trail indicates whether trail was used):
    bool has_value = bv_evaluator_is_evaluable(&exp->csttrail, s_term, &ignore_this_bool);

    if (has_value) {
      uint32_t ignore_that_int=0;
      term_t s_slice_term = slice_mk_term(s, tm);
      const mcsat_value_t* slice_term_value = bv_evaluator_evaluate_term(exp->super.eval, s_slice_term, &ignore_that_int);
      eq_graph_assign_term_value(egraph, s_slice_term, slice_term_value, s_slice_term);
      if (ctx_trace_enabled(ctx, "mcsat::bv::slicing")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, " which evaluates to ");
        mcsat_value_print(slice_term_value, out);
      }
    }

    if (ctx_trace_enabled(ctx, "mcsat::bv::slicing")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "\n");
    }

    // Task 3: we go through its pairs
    // For each equality pair, we stack it on constraint[0]
    // For each disequality pair, we stack it on constraint[i], the disjunction it belongs to

    spair_t* p;
    splist_t *current = s->paired_with;
    while (current != NULL) {
      if (current->is_main) {
        p = current->pair;
        uint32_t c = p->appearing_in;
        splist_t* old = constraints[c];
        constraints[c] = splist_cons(p, true, old);
      }
      current = current->next;
    }
  }
  else { // If the slice is not a leaf, we treat the sub-slices
    assert(s->paired_with == NULL);
    bv_slicing_slice_treat(s->lo_sub, constraints, exp, egraph);
    bv_slicing_slice_treat(s->hi_sub, constraints, exp, egraph);
  }
}

/**
 * Construct the slicing.
 *
 * Will slice conflict_core, and additionally the give var. If the var is
 * given it's slice_list will be returned, otherwise NULL is returned.
 */
slist_t* bv_slicing_construct(bv_slicing_t* slicing, eq_ext_con_t* exp, const ivector_t* conflict_core, term_t var_to_slice, eq_graph_t* egraph) {

  plugin_context_t* ctx = exp->super.ctx;
  slicing->exp = exp;
  slist_t* var_to_slice_slices = NULL; // BD: initialized to stop a compilation warning.

  // We initialize the hashmap in the result
  init_ptr_hmap(&slicing->slices, 0);

  // Standard abbreviations
  term_table_t* terms  = ctx->terms;
  const mcsat_trail_t* trail = ctx->trail;

  // We create a "to do" queue of matching slice pairs to align
  ptr_queue_t todo;
  init_ptr_queue(&todo, 0);

  // Variables that are going to be re-used for every item in the conflict core
  variable_t atom_i_var;
  bool       atom_i_value;
  term_t     atom_i_term;
  term_kind_t atom_i_kind;

  // A counter that records the next available identifier to assign to a disequality in the core.
  // That disequality turns into a disjunction when slicing
  uint32_t next_disjunction = 1;

  // Slice the term first, if any
  if (var_to_slice != NULL_TERM) {
    uint32_t width = bv_term_bitsize(terms, var_to_slice);
    var_to_slice_slices = bv_slicing_norm(exp, var_to_slice, width, 0, NULL, &todo, &slicing->slices);
  }

  // Now slice the conflict
  for (uint32_t i = 0; i < conflict_core->size; i++) {

    atom_i_var   = conflict_core->data[i];
    atom_i_value = trail_get_boolean_value(trail, atom_i_var);
    atom_i_term  = variable_db_get_term(ctx->var_db, atom_i_var);
    assert(is_pos_term(atom_i_term));
    atom_i_kind  = term_kind(terms, atom_i_term);

    if (ctx_trace_enabled(ctx, "mcsat::bv::slicing")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Slicing core constraint ");
      ctx_trace_term(ctx, atom_i_term);
    }

    switch (atom_i_kind) {
    case EQ_TERM :    // equality
    case BV_EQ_ATOM: { // We can only deal with equalities in this BV subtheory
      composite_term_t* atom_i_comp = composite_term_desc(terms, atom_i_term);
      assert(atom_i_comp->arity == 2);
      term_t t0 = atom_i_comp->arg[0];
      term_t t1 = atom_i_comp->arg[1];
      assert(is_pos_term(t0));
      assert(is_pos_term(t1));
      uint32_t constraint = 0;
      if (!atom_i_value) {
        constraint = next_disjunction;
        next_disjunction++;
      }
      uint32_t width = bv_term_bitsize(terms, t0);
      slist_t* l0 = bv_slicing_norm(exp, t0, width, 0, NULL, &todo, &slicing->slices);
      slist_t* l1 = bv_slicing_norm(exp, t1, width, 0, NULL, &todo, &slicing->slices);
      bv_slicing_align(ctx, l0, l1, constraint, &todo);
      break;
    }
    case BIT_TERM: { // That's also in the fragment...
      select_term_t* desc   = bit_term_desc(terms, atom_i_term);
      uint32_t selected_bit = desc->idx;
      term_t t0   = term_extract(ctx->tm, desc->arg, selected_bit, selected_bit+1);
      slist_t* l0 = bv_slicing_norm(exp, t0, 1, 0, NULL, &todo, &slicing->slices);

      term_t a1[1];
      a1[0] = bool2term(atom_i_value);
      term_t t1 = mk_bvarray(ctx->tm, 1, a1);
      slist_t* l1 = bv_slicing_norm(exp, t1, 1, 0, NULL, &todo, &slicing->slices);

      bv_slicing_align(ctx, l0, l1, 0, &todo);
      break;
    }
    default:
      assert(false);
    }
  }

  // Now we know how many constraints we have, so we can allocate them in the result
  slicing->nconstraints = next_disjunction;
  slicing->constraints = safe_malloc(sizeof(splist_t*) * next_disjunction);
  for (uint32_t i = 0; i < slicing->nconstraints; i++) {
    slicing->constraints[i] = NULL;
  }

  /* fprintf(out, "Finished treating core constraints, giving slicing:\n"); */
  /* bv_slicing_print_slicing(slicing_out, terms, out); */
  /* fprintf(out, "+ a \"to do\" queue.\n"); */

  /** While loop treating the queue of slicings to perform until the coarsest slicing has been produced */

  slist_t* l1;
  slist_t* l2;

  while (!ptr_queue_is_empty(&todo)) {
    spair_t* p = (spair_t*) ptr_queue_pop(&todo);
    assert(p->lhs != NULL);
    if (ctx_trace_enabled(ctx, "mcsat::bv::slicing")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Popping ");
      ctx_print_spair(ctx, p, true);
      fprintf(out, "\n");
    }
    l1 = bv_slicing_as_list(p->lhs, NULL);
    l2 = bv_slicing_as_list(p->rhs, NULL);
    if (ctx_trace_enabled(ctx, "mcsat::bv::slicing")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Now aligning\n");
    }
    bv_slicing_align(ctx, l1, l2, p->appearing_in, &todo); // l1 and l2 are freed
    safe_free(p);
  }

  // We destruct the todo queue
  assert(ptr_queue_is_empty(&todo));
  delete_ptr_queue(&todo);

  // Now we go through all variables, all of their leaf slices, and collect the
  // equalities / disequalities they are involved in into slicing_out->constraints

  ptr_hmap_pair_t* hp = ptr_hmap_first_record(&slicing->slices);
  while(hp != NULL) {
    bv_slicing_slice_treat(hp->val, slicing->constraints, exp, egraph);
    hp = ptr_hmap_next_record(&slicing->slices, hp);
  }

  return var_to_slice_slices;
}

static inline
bool term_is_ext_con(eq_ext_con_t* exp, term_t t) {

  plugin_context_t* ctx = exp->super.ctx;
  term_t conflict_var = exp->csttrail.conflict_var_term;
  term_table_t* terms         = ctx->terms;

  if (ctx_trace_enabled(ctx, "mcsat::bv::slicing::detect")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "term_is_ext_con with t = ");
    ctx_trace_term(ctx, t);
  }

  // Looking at whether the value is cached
  if (int_hset_member(&exp->good_terms_cache,t)) return true;

  if (ctx_trace_enabled(ctx, "mcsat::bv::slicing::detect")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Value not cached. Is it the conflict_var, something evaluable?\n");
  }

  bool ignore_this_bool;
  if (t == conflict_var
      || bv_evaluator_is_evaluable(&exp->csttrail, t, &ignore_this_bool)) {
    int_hset_add(&exp->good_terms_cache, t);
    return true;
  }

  if (ctx_trace_enabled(ctx, "mcsat::bv::slicing::detect")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Not evaluable. Is it at least positive?\n");
  }

  if (!is_pos_term(t))
    return false;

  // What kind of term is it
  term_kind_t t_kind = term_kind(terms, t);

  if (ctx_trace_enabled(ctx, "mcsat::bv::slicing::detect")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Doing case analysis on term\n");
  }

  // Bit-select over a variable
  if (t_kind == BIT_TERM) {
    term_t t_arg = bit_term_arg(terms, t);
    if (term_is_ext_con(exp, t_arg)) {
      int_hset_add(&exp->good_terms_cache, t);
      return true;
    } else {
      return false;
    }
  }

  if (ctx_trace_enabled(ctx, "mcsat::bv::slicing::detect")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Not Bit_term of conflict_var\n");
  }

  // Array of bits
  if (t_kind == BV_ARRAY) {
    composite_term_t* concat_desc = bvarray_term_desc(terms, t);
    for (uint32_t i = 0; i < concat_desc->arity; ++ i) {
      term_t arg = concat_desc->arg[i];
      if (!term_is_ext_con(exp, arg)) {
        return false;
      }
    }
    return true;
  }

  if (ctx_trace_enabled(ctx, "mcsat::bv::slicing::detect")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Not good BVarray, now returning false\n");
  }

  // Nothing else
  return false;
}

static
bool can_explain_conflict(bv_subexplainer_t* this, const ivector_t* conflict, variable_t conflict_var) {

  // Can explain equalities and dis-equalities among
  // - variable
  // - constant
  // - bvarray[v1, ..., vn, c1, ..., cn]
  // Additionally, bit-selects count too, if they are over a variable

  eq_ext_con_t* exp           = (eq_ext_con_t*) this;
  bv_csttrail_t* csttrail     = &exp->csttrail;
  const variable_db_t* var_db = this->ctx->var_db;
  term_table_t* terms         = this->ctx->terms;

  // Resetting the cache & co.
  bv_evaluator_csttrail_reset(csttrail, conflict_var);
  int_hset_reset(&exp->good_terms_cache);

  // We go through the conflict core
  for (uint32_t i = 0; i < conflict->size; ++ i) {

    // Atom and its term
    variable_t atom_var = conflict->data[i];
    term_t atom_term    = variable_db_get_term(var_db, atom_var);

    assert(is_pos_term(atom_term));

    bv_evaluator_csttrail_scan(csttrail, atom_var);

    if (ctx_trace_enabled(this->ctx, "mcsat::bv::slicing")) {
      FILE* out = ctx_trace_out(this->ctx);
      fprintf(out, "eq_ext_conc looks at whether this is in the fragment: ");
      ctx_trace_term(this->ctx, atom_term);
      fprintf(out, "with the conflict_variable being ");
      ctx_trace_term(this->ctx, csttrail->conflict_var_term);
    }

    // Now, see if it fits
    switch (term_kind(terms, atom_term)) {
    case BIT_TERM: {
      term_t atom_arg = bit_term_arg(terms, atom_term);
      if (!term_is_ext_con(exp, atom_arg)) {
        if (ctx_trace_enabled(this->ctx, "mcsat::bv::slicing::detect")) {
          FILE* out = ctx_trace_out(this->ctx);
          fprintf(out, "term_is_ext_con returned false\n");
        }
        return false;
      }
      break;
    }
    case BV_EQ_ATOM:
    case EQ_TERM: {
      composite_term_t* eq = composite_term_desc(terms, atom_term);
      if (!term_is_ext_con(exp, eq->arg[0])) {
        if (ctx_trace_enabled(this->ctx, "mcsat::bv::slicing::detect")) {
          FILE* out = ctx_trace_out(this->ctx);
          fprintf(out, "term_is_ext_con returned false\n");
        }
        return false;
      }
      if (!term_is_ext_con(exp, eq->arg[1])) {
        if (ctx_trace_enabled(this->ctx, "mcsat::bv::slicing::detect")) {
          FILE* out = ctx_trace_out(this->ctx);
          fprintf(out, "term_is_ext_con returned false\n");
        }
        return false;
      }
      break;
    }
    default: {
      if (ctx_trace_enabled(this->ctx, "mcsat::bv::slicing::detect")) {
        FILE* out = ctx_trace_out(this->ctx);
        fprintf(out, "Is neither bit_term nor bv_eq_atom nor eq_term, returning false\n");
      }
      // Cannot handle it
      return false;
    }
    }
  }

  if (ctx_trace_enabled(this->ctx, "mcsat::bv::slicing::detect")) {
    FILE* out = ctx_trace_out(this->ctx);
    fprintf(out, "Yes, it is in the ext_conc fragment!\n");
  }

  return true;
}

static
void explain_conflict(bv_subexplainer_t* this, const ivector_t* conflict_core, variable_t conflict_var, ivector_t* conflict_out) {
  eq_ext_con_t* exp = (eq_ext_con_t*) this;
  plugin_context_t* ctx = this->ctx;
  term_table_t* terms   = ctx->terms;
  term_manager_t* tm = ctx->tm;

  assert(conflict_var == exp->csttrail.conflict_var);
  if (ctx_trace_enabled(this->ctx, "mcsat::bv::conflict")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Eq-explaining conflict with conflict_variable");
    term_print_to_file(out, terms, exp->csttrail.conflict_var_term);
    fprintf(out, "\n");
  }

  // The output conflict always contains the conflict core:
  for (uint32_t i = 0; i < conflict_core->size; i++) {
    variable_t atom_var = conflict_core->data[i];
    term_t t = variable_db_get_term(ctx->var_db, atom_var);
    bool value = trail_get_boolean_value(ctx->trail, atom_var);
    ivector_push(conflict_out, value?t:opposite_term(t));
  }

  // Create the equality graph
  eq_graph_t eq_graph;
  eq_graph_construct(&eq_graph, this->ctx, "mcsat::bv::conflict");

  // Do the slicing
  bv_slicing_t slicing;
  bv_slicing_construct(&slicing, exp, conflict_core, NULL_TERM, &eq_graph);

  if (ctx_trace_enabled(this->ctx, "mcsat::bv::conflict")) {
    bv_slicing_print_slicing(&slicing);
  }

  // SMT'2017 paper

  spair_t* p;
  splist_t* current = slicing.constraints[0];

  // We send the equalities to the e-graph
  while (current != NULL) {
    assert(current->is_main);
    p = current->pair;
    term_manager_t* tm = this->ctx->tm;
    term_t lhs_slice_term = slice_mk_term(p->lhs, tm);
    term_t rhs_slice_term = slice_mk_term(p->rhs, tm);
    if (lhs_slice_term != rhs_slice_term) {
      eq_graph_assert_term_eq(&eq_graph, lhs_slice_term, rhs_slice_term, 0);
    }
    current = current->next;
  }

  ivector_t reasons; // where we collect the reasons why things happen in the e-graph
  init_ivector(&reasons,0);
  ivector_t reasons_types; // ...together with their associated types
  init_ivector(&reasons_types,0); // (i.e. why they are in the e-graph)

  // Case 1: conflict in e-graph
  if (eq_graph.in_conflict) { // Get conflict from e-graph
    if (ctx_trace_enabled(this->ctx, "mcsat::bv::conflict")) {
      FILE* out = ctx_trace_out(ctx);
      fprintf(out, "Conflict in egraph\n");
    }
    eq_graph_get_conflict(&eq_graph, &reasons, &reasons_types, NULL);
  } else { // e-graph not in conflict

    ivector_t interface_terms; // where we collect interface terms
    init_ivector(&interface_terms,0);

    // We go through the disjunctions of disequalities
    for (uint32_t i = 1; i < slicing.nconstraints; i++) {

      current = slicing.constraints[i]; // Get disjunction number i
      if (ctx_trace_enabled(this->ctx, "mcsat::bv::conflict")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "Looking at disjunction %d:\n",i);
      }
      // Go through disjuncts
      while (current != NULL) {
        p = current->pair;
        assert(p->appearing_in == i); // Check that this is indeed the right disequality
        term_t lhs = slice_mk_term(p->lhs, tm);
        term_t rhs = slice_mk_term(p->rhs, tm);

        if (lhs == rhs
            || (eq_graph_has_term(&eq_graph, lhs)
                && eq_graph_has_term(&eq_graph, rhs)
                && eq_graph_are_equal(&eq_graph, lhs, rhs))) {
          // adding the reason why this disequality is false
          if (lhs != rhs) {
            eq_graph_explain_eq(&eq_graph, lhs, rhs, &reasons, &reasons_types, NULL);
          }
          if (ctx_trace_enabled(this->ctx, "mcsat::bv::conflict")) {
            FILE* out = ctx_trace_out(ctx);
            fprintf(out, "Looking at why disequality ");
            term_print_to_file(out, terms, lhs);
            fprintf(out, " != ");
            term_print_to_file(out, terms, rhs);
            fprintf(out, " is false: ");
            for (uint32_t i = 0; i < reasons.size; i++) {
              if (i>0) fprintf(out,", ");
              fprintf(out,"%d", reasons.data[i]);
              if (reasons.data[i] !=0) {
                fprintf(out," [");
                term_print_to_file(out, terms, reasons.data[i]);
                fprintf(out,"]");
              }
            }
            fprintf(out,"\n");
          }
        }
        else{
          // We need to collect the interface term
          if (eq_graph_has_term(&eq_graph, lhs)
              && eq_graph_term_has_value(&eq_graph, lhs)){
            term_t iterm = eq_graph_explain_term_propagation(&eq_graph, lhs, &reasons, &reasons_types, NULL);
            ivector_push(&interface_terms, iterm);
            if (ctx_trace_enabled(this->ctx, "mcsat::bv::conflict")) {
              FILE* out = ctx_trace_out(ctx);
              fprintf(out, "Just added left interface term ");
              term_print_to_file(out, terms, iterm);
              fprintf(out, "\n");
            }
          }
          if (eq_graph_has_term(&eq_graph, rhs)
              && eq_graph_term_has_value(&eq_graph, rhs)){
            term_t iterm = eq_graph_explain_term_propagation(&eq_graph, rhs, &reasons, &reasons_types, NULL);
            ivector_push(&interface_terms, iterm);
            if (ctx_trace_enabled(this->ctx, "mcsat::bv::conflict")) {
              FILE* out = ctx_trace_out(ctx);
              fprintf(out, "Just added right interface term ");
              term_print_to_file(out, terms, iterm);
              fprintf(out, "\n");
            }
          }
          // Note that both "ifs" cannnot be true at the same time, otherwise the disequality could be evaluated:
          // if it evaluates to true, then the disjunction would evaluate to true, so the constraint from whence it came would not be in the core
          // if it evaluates to false, then lhs and rhs would be in the same class of the graph
        }
        current = current->next;
      }
    }

    // Now we build the the equalities / disequalities between interface terms
    for (uint32_t i = 0; i < interface_terms.size; i++) {
      for (uint32_t j = i+1; j < interface_terms.size; j++) {
        term_t lhs = interface_terms.data[i];
        term_t rhs = interface_terms.data[j];
        if (ctx_trace_enabled(this->ctx, "mcsat::bv::conflict")) {
          FILE* out = ctx_trace_out(ctx);
          fprintf(out, "Making eq or neq between interface terms (bitsize = %d) ",term_bitsize(terms,lhs));
          term_print_to_file(out, terms, lhs);
          fprintf(out, " and ");
          term_print_to_file(out, terms, rhs);
          fprintf(out, "\n");
        }

        if (term_bitsize(terms, lhs) == term_bitsize(terms, rhs)) {
          term_t t = (eq_graph_are_equal(&eq_graph, lhs, rhs))? mk_eq(tm, lhs, rhs):mk_neq(tm, lhs, rhs);
          ivector_push(conflict_out, t);
        }
      }
    }
    delete_ivector(&interface_terms);
  }

  assert(reasons.size == reasons_types.size);

  // We collect from the reasons the elements we haven't added
  for (uint32_t i = 0; i < reasons.size; i++) {
      if (ctx_trace_enabled(this->ctx, "mcsat::bv::conflict")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "Looking at reason %d whose type is %d\n",reasons.data[i],reasons_types.data[i]);
      }
    if (reasons_types.data[i] != REASON_IS_USER) {
      if (ctx_trace_enabled(this->ctx, "mcsat::bv::conflict")) {
        FILE* out = ctx_trace_out(ctx);
        fprintf(out, "Adding to conflict ");
        term_print_to_file(out, terms, reasons.data[i]);
        fprintf(out, "\n");
      }
      ivector_push(conflict_out, reasons.data[i]);
    }
  }

  // We clean up
  delete_ivector(&reasons_types);
  delete_ivector(&reasons);

  // Destructs egraph
  eq_graph_destruct(&eq_graph);

  // Destructs slicing
  bv_slicing_slicing_destruct(&slicing);

  if (ctx_trace_enabled(this->ctx, "mcsat::bv::conflict")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Returned conflict is: ");
    for (uint32_t i = 0; i < conflict_out->size; i++) {
      if (i>0) fprintf(out,", ");
      term_print_to_file(out, terms, conflict_out->data[i]);
    }
    fprintf(out,"\n");
  }
}

static
bool can_explain_propagation(bv_subexplainer_t* this, const ivector_t* reasons, variable_t x) {
  // Just use the conflict filter, we'll check if we can explain when time comes
  return can_explain_conflict(this, reasons, x);
}

static
bool explain_term_slice_propagation(const eq_graph_t* eq, slice_t* t_slice, ivector_t* to_concat, ivector_t* reasons, ivector_t* reasons_types, term_manager_t* tm) {
  term_t t_slice_term = slice_mk_term(t_slice, tm);
  if (eq_graph_has_term(eq, t_slice_term) && eq_graph_has_propagated_term_value(eq, t_slice_term)) {
    term_t s = eq_graph_explain_term_propagation(eq, t_slice_term, reasons, reasons_types, NULL);
    ivector_push(to_concat, s);
    return true;
  } else {
    if (t_slice->hi_sub != NULL) {
      return
        explain_term_slice_propagation(eq, t_slice->hi_sub, to_concat, reasons, reasons_types, tm) &&
        explain_term_slice_propagation(eq, t_slice->lo_sub, to_concat, reasons, reasons_types, tm);
    } else {
      return false;
    }
  }
}

static
term_t explain_propagation(bv_subexplainer_t* this, const ivector_t* reasons_in, variable_t x, ivector_t* reasons_out) {
  eq_ext_con_t* exp = (eq_ext_con_t*) this;
  plugin_context_t* ctx = this->ctx;
  term_table_t* terms = ctx->terms;

  term_t result_subst = NULL_TERM;

  assert(x == exp->csttrail.conflict_var); // TODO: This is too much sife-effect of can-explain function
  if (ctx_trace_enabled(this->ctx, "mcsat::bv::explain")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Eq-explaining propagation of ");
    term_print_to_file(out, terms, exp->csttrail.conflict_var_term);
    fprintf(out, "\n");
  }

  // The reason will always contains the original reasons:
  for (uint32_t i = 0; i < reasons_in->size; i++) {
    variable_t atom_var = reasons_in->data[i];
    term_t t = variable_db_get_term(ctx->var_db, atom_var);
    bool value = trail_get_boolean_value(ctx->trail, atom_var);
    ivector_push(reasons_out, value ? t : opposite_term(t));
  }

  // Create the equality graph
  eq_graph_t eq_graph;
  eq_graph_construct(&eq_graph, this->ctx, "mcsat::bv::explain");

  // Get the variable term and normalize to what's in the slicing/eq-graph
  term_t x_term = variable_db_get_term(ctx->var_db, x);

  // Do the slicing
  bv_slicing_t slicing;
  slist_t* x_term_slice = bv_slicing_construct(&slicing, exp, reasons_in, x_term, &eq_graph);
  if (ctx_trace_enabled(this->ctx, "mcsat::bv::explain")) {
    FILE* out = ctx_trace_out(ctx);
    bv_slicing_print_slicing(&slicing);
    fprintf(out, "x = ");
    term_print_to_file(out, terms, x_term);
    fprintf(out, "\n");
    fprintf(out, "x[] = ");
    slice_print(x_term_slice->slice, out);
    fprintf(out, "\n");
  }

  // Send the equalities to the e-graph
  spair_t* p;
  splist_t* current = slicing.constraints[0];
  while (current != NULL) {
    assert(current->is_main);
    p = current->pair;
    term_manager_t* tm = this->ctx->tm;
    term_t lhs_slice_term = slice_mk_term(p->lhs, tm);
    term_t rhs_slice_term = slice_mk_term(p->rhs, tm);
    if (lhs_slice_term != rhs_slice_term) {
      eq_graph_assert_term_eq(&eq_graph, lhs_slice_term, rhs_slice_term, 0);
    }
    current = current->next;
  }

  if (ctx_trace_enabled(this->ctx, "mcsat::bv::explain")) {
    FILE* out = ctx_trace_out(ctx);
    eq_graph_print(&eq_graph, out);
  }

  // If the variable is propagated with the graph, use it
  ivector_t reasons; // where we collect the reasons why things happen in the e-graph
  ivector_t reasons_types; // ...together with their associated types
  ivector_t to_concat;
  init_ivector(&reasons,0);
  init_ivector(&reasons_types,0); // (i.e. why they are in the e-graph)
  init_ivector(&to_concat, 0);
  // Explain with EQ graph
  bool ok = explain_term_slice_propagation(&eq_graph, x_term_slice->slice, &to_concat, &reasons, &reasons_types, this->ctx->tm);
  assert(x_term_slice->next == NULL);
  safe_free(x_term_slice);

  // Add the reasons
  if (ok) {
    // Concat the terms
    if (to_concat.size > 1) {
      result_subst = yices_bvconcat(to_concat.size, to_concat.data);
    } else {
      result_subst = to_concat.data[0];
    }
    // Collect the reasons of the elements we haven't added
    for (uint32_t i = 0; i < reasons.size; i++) {
      if (reasons_types.data[i] != REASON_IS_USER) {
        ivector_push(reasons_out, reasons.data[i]);
      }
    }
  }
  // Clean up
  delete_ivector(&reasons_types);
  delete_ivector(&reasons);
  delete_ivector(&to_concat);

  if (ctx_trace_enabled(this->ctx, "mcsat::bv::explain")) {
    FILE* out = ctx_trace_out(ctx);
    if (result_subst == NULL_TERM) {
      fprintf(out, "Eq-plugin can't explain propagation");
    } else {
      fprintf(out, "Eq-plugin explanation:\n");
      uint32_t i;
      for (i = 0; i < reasons_out->size; ++ i) {
        term_print_to_file(out, ctx->terms, reasons_out->data[i]);
        fprintf(out, "\n");
      }
      fprintf(out, "Subst:");
      term_print_to_file(out, ctx->terms, result_subst);
      fprintf(out, "\n");
    }
  }

  // Clean up
  eq_graph_destruct(&eq_graph);
  bv_slicing_slicing_destruct(&slicing);

  // If x is Boolean, our substitution will be a bitvector of size 1 that
  if (result_subst != NULL_TERM && is_boolean_term(terms, x_term)) {
    result_subst = bit_term(terms, 0, result_subst);
  }

  return result_subst;
}

static
void destruct(bv_subexplainer_t* this) {
  eq_ext_con_t* exp = (eq_ext_con_t*) this;
  bv_evaluator_csttrail_destruct(&exp->csttrail);
  delete_int_hset(&exp->good_terms_cache);
}

/** Allocate the sub-explainer and setup the methods */
bv_subexplainer_t* eq_ext_con_new(plugin_context_t* ctx, watch_list_manager_t* wlm, bv_evaluator_t* eval) {

  eq_ext_con_t* exp = safe_malloc(sizeof(eq_ext_con_t));

  bv_subexplainer_construct(&exp->super, "mcsat::bv::explain::eq_ext_con", ctx, wlm, eval);
  bv_evaluator_csttrail_construct(&exp->csttrail, ctx, wlm);

  exp->super.can_explain_conflict = can_explain_conflict;
  exp->super.explain_conflict = explain_conflict;
  exp->super.can_explain_propagation = can_explain_propagation;
  exp->super.explain_propagation = explain_propagation;
  exp->super.destruct = destruct;

  init_int_hset(&exp->good_terms_cache, 0);

  return (bv_subexplainer_t*) exp;
}

