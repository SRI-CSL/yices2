/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include "eq_ext_con.h"

#include "mcsat/tracing.h"
#include "mcsat/value.h"
#include "terms/term_manager.h"
#include "terms/bvlogic_buffers.h"

#include "mcsat/bv/bv_utils.h"
#include "mcsat/eq/equality_graph.h"

typedef struct eq_ext_con_s {

  /** Interfact of the subexplainer */
  bv_subexplainer_t super;
  bv_csttrail_t csttrail; // Where we keep some cached values

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

static inline
term_t slice_mk_term(const slice_t* slice, term_manager_t* tm) {
  bvlogic_buffer_t* buffer = term_manager_get_bvlogic_buffer(tm);
  bvlogic_buffer_set_slice_term(buffer, tm->terms, slice->base.lo, slice->base.hi-1, slice->base.term);
  return mk_bvlogic_term(tm, buffer);
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
  term_manager_t* tm = &ctx->var_db->tm;
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
 * Wrapping up above function: stack on top of tail a slice for variable t
 * (expressed as a term), from lo to hi
 */
slist_t* bv_slicing_sstack(const plugin_context_t* ctx, term_t t, uint32_t hi, uint32_t lo, slist_t* tail, ptr_queue_t* todo, ptr_hmap_t* slices) {
  // Getting that variable's top-level slice from global hashmap
  ptr_hmap_pair_t* p = ptr_hmap_get(slices, t);
  if (p->val == NULL) {
    // Create that slice if need be
    term_manager_t* tm = &ctx->var_db->tm;
    p->val = bv_slicing_slice_new(tm, t, 0, bv_term_bitsize(ctx->terms, t));
  }
  // stack upon the tail list the relevant (series of) slice(s) covering lo to hi
  return bv_slicing_extracts(ctx, p->val, hi, lo, tail, todo);
}

slist_t* bv_slicing_slice_close(const plugin_context_t* ctx,
                              term_t* tp,
                              uint32_t bitwidth,
                              slist_t* tail,
                              ptr_queue_t* todo,
                              ptr_hmap_t* slices) {


  /* FILE* out = ctx_trace_out(ctx); */
  /* fprintf(out, "Closing slice of width %d\n",bitwidth); */

  if (bitwidth == 0) {
    return tail;
  }

  term_table_t* terms = ctx->terms; // standard abbreviation
  term_t t0 = tp[0];

  switch (term_kind(terms, t0)) {

  case BIT_TERM: {
    select_term_t* desc   = bit_term_desc(terms, t0);
    term_t tvar           = desc->arg; // Get term variable
    uint32_t selected_bit = desc->idx; // Get bit that is selected in it
    return bv_slicing_sstack(ctx, tvar, selected_bit + bitwidth, selected_bit, tail, todo, slices);
  }

  case CONSTANT_TERM: {
    term_manager_t* tm = &ctx->var_db->tm;
    /* term_t cst = bvarray_term(terms, bitwidth, tp); // Primitive construction */
    term_t cst = mk_bvarray(tm, bitwidth, tp); // Smarter construction?
    return bv_slicing_sstack(ctx, cst, bitwidth, 0, tail, todo, slices);
  }

  default: {
    assert(bitwidth == 1);
    term_manager_t* tm = &ctx->var_db->tm;
    term_t cst = mk_bvarray(tm, 1, tp); // Smarter construction?
    return bv_slicing_sstack(ctx, cst, 1, 0, tail, todo, slices);
  }
  }

  return NULL;
}


/** Normalises the hi-lo extraction of a term into a list of slices added to tail,
    which acts as an accumulator for this recursive function. */
slist_t* bv_slicing_norm(const plugin_context_t* ctx, term_t t, uint32_t hi, uint32_t lo, slist_t* tail, ptr_queue_t* todo, ptr_hmap_t* slices) {

  /* FILE* out = ctx_trace_out(ctx); */
  /* fprintf(out, "Normalising "); */
  /* term_print_to_file(out, ctx->terms, t); */
  /* fprintf(out, " between %d and %d\n", hi, lo); */

  assert(lo < hi);
  term_table_t* terms = ctx->terms; // standard abbreviation

  switch (term_kind(terms, t)) {
  case BV_ARRAY: {
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
    bool     is_constant = true; // whether current slice is constant
    term_t   tvar = NULL_TERM;   // if not constant, variable term of current slice - value not used (initialised to suppress gcc warning)
    uint32_t low  = 0;           // if not constant, lo of current slice - value not used (initialised to suppress gcc warning)

    for (uint32_t j = 0; j < total_width; j++) {
      uint32_t i = hi - j -1;           // The bit we are dealing with
      term_t t_i = concat_desc->arg[i]; // The Boolean term that constitutes that bit
      /* fprintf(out, "bit %d is ",i); */
      /* ctx_trace_term(ctx, t_i); */

      switch (term_kind(terms, t_i)) { // We look at what it is

      case BIT_TERM: {
        select_term_t* desc   = bit_term_desc(terms, t_i);
        term_t tmp            = desc->arg; // Get term variable
        uint32_t selected_bit = desc->idx; // Get bit that is selected in it
        // We need to change slice if...
        if (is_constant                   // ...the current slice was constant
            || (tmp != tvar)              // or it wasn't but it had different variable
            || (selected_bit + 1 != low)) // or it was the same but new bit not in continuity
          { // We close the current slice, stack it upon the tail, and open a new slice
            current = bv_slicing_slice_close(ctx, concat_desc->arg + i + 1,width, current, todo, slices);
            width = 0; // We start a new slice
          }
        // Then in any case:
        width++;                    // bitwidth of current slice is incremented
        is_constant = false;        // current slice is not constant
        tvar        = tmp;          // current slice has tvar as variable (as a term)
        low         = selected_bit; // ...and selected_bit as its low index
        break;
      }
      case CONSTANT_TERM: { // or it's a boolean constant true or false
        // We need to change slice if current slice was not constant
        if (!is_constant) {
          current = bv_slicing_slice_close(ctx, concat_desc->arg + i + 1,width, current, todo, slices);
          width = 0; // We start a new slice
        }
        // Then in any case:
        width++;            // bitwidth of current slice is incremented
        is_constant = true; // current slice is constant
        break;
      }
      default: {// For anything else, we read it as a variable; that's a slice on its own.
        current = bv_slicing_slice_close(ctx, concat_desc->arg + i + 1,width, current, todo, slices);
        width = 1; // We start the new slice (will be of size 1.
        is_constant = false; // current slice is a variable
        tvar        = t_i;   // current slice has t_i as variable (as a term) Note that its type is bool
        low         = 0;     // there's no selected bit though by convention we can say it is 0
        // that will trigger a slice closing at the next step in every case
      }
      }
    }
    // We have exited the loop, we now close the current (and last) slice
    return bv_slicing_slice_close(ctx, concat_desc->arg,width, current, todo, slices);
  }
  default: // We consider the term is a variable or a constant, we immediately stack its relevant slices
    return bv_slicing_sstack(ctx, t, hi, lo, tail, todo, slices);
  }

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
    variable_db_t* var_db = ctx->var_db; // standard abbreviations
    term_manager_t* tm = &var_db->tm;

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
      uint32_t eval_level;
      term_t s_slice_term = slice_mk_term(s, tm);
      const mcsat_value_t* slice_term_value = bv_evaluator_evaluate_term(exp->super.eval, s_slice_term, &eval_level);
      eq_graph_assign_term_value(egraph, s_slice_term, slice_term_value, s_slice_term);
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

void bv_slicing_construct(bv_slicing_t* slicing, eq_ext_con_t* exp, const ivector_t* conflict_core, eq_graph_t* egraph) {

  plugin_context_t* ctx = exp->super.ctx;
  slicing->exp = exp;

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
      composite_term_t* atom_i_comp = (atom_i_kind == EQ_TERM)?eq_term_desc(terms, atom_i_term): bveq_atom_desc(terms, atom_i_term);
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
      slist_t* l0 = bv_slicing_norm(ctx, t0, width, 0, NULL, &todo, &slicing->slices);
      slist_t* l1 = bv_slicing_norm(ctx, t1, width, 0, NULL, &todo, &slicing->slices);
      bv_slicing_align(ctx, l0, l1, constraint, &todo);
      break;
    }
    case BIT_TERM: { // That's also in the fragment...

      term_t a0[1];
      a0[0] = atom_i_term;
      term_t t0 = mk_bvarray(&ctx->var_db->tm, 1, a0);
      slist_t* l0 = bv_slicing_norm(ctx, t0, 1, 0, NULL, &todo, &slicing->slices);

      term_t a1[1];
      a1[0] = bool2term(atom_i_value);
      term_t t1 = mk_bvarray(&ctx->var_db->tm, 1, a1);
      slist_t* l1 = bv_slicing_norm(ctx, t1, 1, 0, NULL, &todo, &slicing->slices);

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

}

static inline
bool variable_in_list(variable_t x, const variable_t* vars) {
  while (*vars != variable_null) {
    if (x == *vars) { return true; }
    vars ++;
  }
  return false;
}

static inline
bool term_is_ext_con(bv_subexplainer_t* this, term_t t, const variable_t* vars) {

  uint32_t i;

  const variable_db_t* var_db = this->ctx->var_db;
  term_table_t* terms = this->ctx->terms;

//  if (ctx_trace_enabled(this->ctx, "mcsat::bv::conflict")) {
//    FILE* out = ctx_trace_out(this->ctx);
//    fprintf(out, "t = ");
//    ctx_trace_term(this->ctx, t);
//  }

  // What kind of term is it
  term_kind_t t_kind = term_kind(terms, t);

  // MCSAT variables
  variable_t t_var = variable_db_get_variable_if_exists(var_db, t);
  if (t_var != variable_null) {
    if (variable_in_list(t_var, vars)) {
      return true;
    }
  }

  // Constants solo
  if (is_const_term(terms, t)) {
    return true;
  }

  // Bit-select over a variable
  if (t_kind == BIT_TERM) {
    term_t t_arg = bit_term_arg(terms, t);
    variable_t t_arg_var = variable_db_get_variable_if_exists(var_db, t_arg);
    if (t_arg_var != variable_null) {
      return variable_in_list(t_arg_var, vars);
    } else {
      return false;
    }
  }

  // Array of bits
  if (t_kind == BV_ARRAY) {
    composite_term_t* concat_desc = bvarray_term_desc(terms, t);
    for (i = 0; i < concat_desc->arity; ++ i) {
      term_t bit = concat_desc->arg[i];
      if (is_neg_term(bit)) {
        return false;
      }
      if (!term_is_ext_con(this, bit, vars)) {
        return false;
      }
    }
    return true;
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

  eq_ext_con_t* exp          = (eq_ext_con_t*) this;
  bv_csttrail_t* csttrail    = &exp->csttrail;
  const variable_db_t* var_db = this->ctx->var_db;
  term_table_t* terms = this->ctx->terms;
  bv_evaluator_csttrail_reset(csttrail, conflict_var);

  uint32_t i;

  for (i = 0; i < conflict->size; ++ i) {

    // Atom and it's term
    variable_t atom_var = conflict->data[i];
    term_t atom_term = variable_db_get_term(var_db, atom_var);

    bv_evaluator_csttrail_scan(csttrail, atom_var);

//    if (ctx_trace_enabled(this->ctx, "mcsat::bv::conflict")) {
//      FILE* out = ctx_trace_out(this->ctx);
//      fprintf(out, "atom_var = ");
//      ctx_trace_term(this->ctx, atom_term);
//    }

    // Get the variables of the constraint
    if (!watch_list_manager_has_constraint(this->wlm, atom_var)) {
      // No variables, it must be Boolean assignment, which is fine
      continue;
    }

    // List of variables in the atom (at registration time, and BDD creation time)
    variable_list_ref_t atom_var_wlist_ref = watch_list_manager_get_list_of(this->wlm, atom_var);
    const variable_t* atom_var_wlist = watch_list_manager_get_list(this->wlm, atom_var_wlist_ref);

    // Now, see if it fits
    term_kind_t atom_kind = term_kind(terms, atom_term);
    switch (atom_kind) {
    case BIT_TERM: {
      term_t atom_arg = bit_term_arg(terms, atom_term);
      variable_t atom_arg_var = variable_db_get_variable_if_exists(var_db, atom_arg);
      if (atom_arg_var != variable_null || !variable_in_list(atom_arg_var, atom_var_wlist)) {
        return false;
      }
      break;
    }
    case BV_EQ_ATOM:
    case EQ_TERM: {
      composite_term_t* eq = composite_term_desc(terms, atom_term);
      if (!term_is_ext_con(this, eq->arg[0], atom_var_wlist)) {
        return false;
      }
      if (!term_is_ext_con(this, eq->arg[1], atom_var_wlist)) {
        return false;
      }
      break;
    }
    default:
      // Cannot handle it
      return false;
    }
  }

  return true;
}

static
void explain_conflict(bv_subexplainer_t* this, const ivector_t* conflict_core, variable_t conflict_var, ivector_t* conflict_out) {
  eq_ext_con_t* exp = (eq_ext_con_t*) this;
  plugin_context_t* ctx = this->ctx;
  term_table_t* terms   = ctx->terms;
  term_manager_t* tm = &ctx->var_db->tm;

  assert(conflict_var == exp->csttrail.conflict_var);
  if (ctx_trace_enabled(this->ctx, "mcsat::bv::conflict")) {
    FILE* out = ctx_trace_out(ctx);
    fprintf(out, "Eq-explaining conflict with conflict_variable ");
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
  bv_slicing_construct(&slicing, exp, conflict_core, &eq_graph);

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
    term_manager_t* tm = &this->ctx->var_db->tm;
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
void destruct(bv_subexplainer_t* this) {
  eq_ext_con_t* exp = (eq_ext_con_t*) this;
  bv_evaluator_csttrail_destruct(&exp->csttrail);
}

/** Allocate the sub-explainer and setup the methods */
bv_subexplainer_t* eq_ext_con_new(plugin_context_t* ctx, watch_list_manager_t* wlm, bv_evaluator_t* eval) {

  eq_ext_con_t* exp = safe_malloc(sizeof(eq_ext_con_t));

  bv_subexplainer_construct(&exp->super, "mcsat::bv::explain::eq_ext_con", ctx, wlm, eval);
  bv_evaluator_csttrail_construct(&exp->csttrail, ctx, wlm);
  exp->super.destruct = destruct;

  exp->super.can_explain_conflict = can_explain_conflict;
  exp->super.explain_conflict = explain_conflict;

  return (bv_subexplainer_t*) exp;
}

